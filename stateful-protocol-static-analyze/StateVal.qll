import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking

//查找有限取值的状态变量, 确保此处与常量进行比较
predicate isConstStateVariable(Variable v, VariableAccess ac) {
  (
    //在switch语句或者if语句中被使用
    ac.getEnclosingStmt() instanceof SwitchStmt
    or
    ac.getEnclosingStmt() instanceof IfStmt and
    (
      //在if语句中使用时，保证左边是状态变量，右边是常量
      ac.getParent().(EQExpr).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(EQExpr).getRightOperand() instanceof Literal and
      not ac.getParent().(EQExpr).getRightOperand().getValue() = "0"
      or
      ac.getParent().(NEExpr).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(NEExpr).getRightOperand() instanceof Literal and
      not ac.getParent().(NEExpr).getRightOperand().getValue() = "0"
    )
  )
}

//查找指针类型的状态变量
predicate isPtrStateVariable(Variable v, VariableAccess ac) {
  v.getUnderlyingType() instanceof PointerType and
  not v.getUnspecifiedType() instanceof FunctionPointerType and
  (
    //在if语句中被使用，保证与NULL比较
    ac.getEnclosingStmt() instanceof IfStmt and
    (
      ac.getParent().(EQExpr).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(EQExpr).getRightOperand() instanceof Literal and
      ac.getParent().(EQExpr).getRightOperand().getValue() = "0"
      or
      ac.getParent().(NEExpr).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(NEExpr).getRightOperand() instanceof Literal and
      ac.getParent().(NEExpr).getRightOperand().getValue() = "0"
    )
  )
}

//判断状态变量是否在其他函数中被赋值
predicate isAssignInOtherFunc(Variable v, VariableAccess ac, AssignExpr ae) {
  ae.getLValue().(VariableAccess).getTarget() = v and
  ae.getEnclosingFunction() != ac.getEnclosingFunction()
}

//判断变量是否被定义于标准库中，过滤该情况
predicate isDefineInStd(Variable v) {
  v.getDefinitionLocation().getFile().getAbsolutePath().regexpMatch("/usr/.*")
}

//判断变量是否是在源文件中被定义的
predicate isDefineInSrc(Variable v) {
  v.getDefinitionLocation().getFile().fromSource()
}

//定位bitmap类型的状态变量
predicate isBitmapStateVariable(Variable v, VariableAccess ac) {
  (
    ac.getEnclosingStmt() instanceof IfStmt and
    (
      //状态变量通过位运算被使用
      ac.getParent().(BinaryBitwiseOperation).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(BinaryBitwiseOperation).getRightOperand() instanceof Literal
    )
  )
}

//判断状态变量是否在其他函数中被赋值
predicate isBitOpAssignInOtherFunc(Variable v, VariableAccess ac, AssignBitwiseOperation ae) {
  ae.getLValue().(VariableAccess).getTarget() = v and
  ae.getEnclosingFunction() != ac.getEnclosingFunction()
}

//查找通过函数指针影响控制流的状态变量
predicate isIndirectStateVariable(Variable v, VariableAccess ac) {
  not v.getUnspecifiedType() instanceof FunctionPointerType and
  (
    //由状态变量决定函数指针的值
    exists(VariableAccess fac, DataFlow::Node source, DataFlow::Node sink |
      fac.getTarget().getUnspecifiedType() instanceof FunctionPointerType and
      fac.getTarget() = sink.asVariable() and
      ac.getTarget() = source.asVariable() and
      TaintTracking::localTaint(source, sink)
    )
    or
    //由状态变量从数组中决定函数指针的值
    exists(VariableAccess fac, ArrayExpr ae, DataFlow::Node source, DataFlow::Node sink |
      fac.getTarget().getUnspecifiedType() instanceof FunctionPointerType and
      ac.getParent*() = ae.getArrayOffset() and
      source.asExpr() = ae and
      sink.asExpr() = fac and
      DataFlow::localFlow(source, sink)
    )
    or
    //由状态变量决定结构体（一般为状态机规则，包含了下一个状态、行为函数指针），结构体中包含函数指针
    exists(FieldAccess pac, ArrayExpr ae, DataFlow::Node source, DataFlow::Node sink |
      pac.getTarget().getUnspecifiedType() instanceof FunctionPointerType and
      ac.getParent*() = ae.getArrayOffset() and
      source.asExpr() = ae and
      sink.asExpr() = pac.getQualifier() and
      DataFlow::localFlow(source, sink)
    )
  )
}

Variable getRealVariable(Variable v) {
  exists(Function f, VariableAccess va, FunctionCall fc, Variable rv, int i |
    fc.getTarget() = f and
    f.getParameter(i).(Variable) = v and
    fc.getArgument(i) = va and
    va.getTarget() = rv and
    (
      rv instanceof MemberVariable
      or
      rv instanceof GlobalVariable
    ) and
    not rv.getUnderlyingType() instanceof Class and
    result = rv
  )
}

predicate isStateVariable(Variable v, VariableAccess ac) {
  ac.getTarget() = v and
  (
    v instanceof MemberVariable
    or
    v instanceof GlobalVariable
  ) and
  not v.getUnderlyingType() instanceof Class and
  (
    isConstStateVariable(v, ac) and
    exists(AssignExpr ae | isAssignInOtherFunc(v, ac, ae))
    or
    isBitmapStateVariable(v, ac) and
    exists(AssignBitwiseOperation ae | isBitOpAssignInOtherFunc(v, ac, ae))
    or
    isIndirectStateVariable(v, ac) and
    exists(AssignExpr ae | isAssignInOtherFunc(v, ac, ae))
  ) and
  not isDefineInStd(v) and
  isDefineInSrc(v)
}

//注意容易出现假阳性的情况，如：strdup函数可能存在全局变量作为参数，但参数在多数时候不能作为状态变量, v被状态变量赋值的参数变量
predicate isParameterStateVariable(Variable rv, VariableAccess ac) {
  exists(Variable v |
    ac.getTarget() = v and
    v instanceof Parameter and
    (
      isConstStateVariable(v, ac) and
      exists(AssignExpr ae |
        rv = getRealVariable(v) and
        isAssignInOtherFunc(rv, ac, ae) and
        not isDefineInStd(rv) and isDefineInSrc(rv)
      )
      or
      isBitmapStateVariable(v, ac) and
      exists(AssignBitwiseOperation ae |
        rv = getRealVariable(v) and
        isBitOpAssignInOtherFunc(rv, ac, ae) and
        not isDefineInStd(rv) and isDefineInSrc(rv)
      )
      or
      isIndirectStateVariable(v, ac) and
      exists(AssignExpr ae |
        rv = getRealVariable(v) and
        isAssignInOtherFunc(rv, ac, ae) and
        not isDefineInStd(rv) and isDefineInSrc(rv)
      )
    )
  )
}

predicate isStateVariablePtr(Variable v, VariableAccess ac) {
  ac.getTarget() = v and
  (
    v instanceof MemberVariable
    or
    v instanceof GlobalVariable
  ) and
  isPtrStateVariable(v, ac) and
  exists(AssignExpr ae | isAssignInOtherFunc(v, ac, ae)) and
  not isDefineInStd(v) and isDefineInSrc(v)
}

predicate isParameterStateVariablePtr(Variable rv, VariableAccess ac) {
  exists(Variable v |
    ac.getTarget() = v and
    v instanceof Parameter and
    isPtrStateVariable(v, ac) and
    exists(AssignExpr ae |
      rv = getRealVariable(v) and
      isAssignInOtherFunc(rv, ac, ae) and
      not isDefineInStd(rv) and isDefineInSrc(rv)
    )
  )
}

predicate stateVariableAccess(StateVariable v, VariableAccess ac) {
  ac.getTarget() = v and
  ac.getEnclosingElement().(Assignment).getLValue() = ac
}

predicate stateVariableCompare(StateVariable v, VariableAccess ac) {
  ac.getTarget() = v and
  (
    ac.getEnclosingStmt() instanceof IfStmt
    or
    ac.getEnclosingStmt() instanceof SwitchStmt
  )
}

class StateVariable instanceof Variable {
  StateVariable() {
    exists(VariableAccess ac |
      isStateVariable(this, ac)
      or
      isParameterStateVariable(this, ac)
    )
  }

  string toString() { result = super.toString() }
}

class StateVariableCheck instanceof VariableAccess {
  StateVariable v;

  StateVariableCheck() {
      stateVariableCompare(v, this)
  }

  string toString() { result = super.toString() }

  StateVariable getStateV() { result = v }

  string getStateVName() { result = v.(Variable).getQualifiedName() }
}

class StateVariableCheckConst instanceof VariableAccess {
  StateVariable v;

  StateVariableCheckConst() {
    this.getTarget() = v and
    (
      //在switch语句或者if语句中被使用
      this.getEnclosingStmt() instanceof SwitchStmt
      or
      this.getEnclosingStmt() instanceof IfStmt and
      (
        //在if语句中使用时，保证左边是状态变量，右边是常量
        this.getParent().(EQExpr).getRightOperand().isConstant()
        or
        this.getParent().(NEExpr).getRightOperand().isConstant()
      )
    )
  }

  string toString() { result = super.toString() }

  StateVariable getStateV() { result = v }

  string getStateVName() { result = v.(Variable).getQualifiedName() }
}

class StateVariableAssign instanceof VariableAccess {
  StateVariable v;
  StateVariableAssign() {  stateVariableAccess(v, this) }

  string toString() { result = super.toString() }

  StateVariable getStateV() { result = v }

  string getStateVName() { result = v.(Variable).getQualifiedName() }
}
