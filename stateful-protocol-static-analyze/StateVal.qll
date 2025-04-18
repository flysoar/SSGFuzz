import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking

predicate isConstStateVariable(Variable v, VariableAccess ac) {
  (
    ac.getEnclosingStmt() instanceof SwitchStmt
    or
    ac.getEnclosingStmt() instanceof IfStmt and
    (
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

predicate isPtrStateVariable(Variable v, VariableAccess ac) {
  v.getUnderlyingType() instanceof PointerType and
  not v.getUnspecifiedType() instanceof FunctionPointerType and
  (
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

predicate isAssignInOtherFunc(Variable v, VariableAccess ac, AssignExpr ae) {
  ae.getLValue().(VariableAccess).getTarget() = v and
  ae.getEnclosingFunction() != ac.getEnclosingFunction()
}

predicate isDefineInStd(Variable v) {
  v.getDefinitionLocation().getFile().getAbsolutePath().regexpMatch("/usr/.*")
}

predicate isDefineInSrc(Variable v) {
  v.getDefinitionLocation().getFile().fromSource()
}

predicate isBitmapStateVariable(Variable v, VariableAccess ac) {
  (
    ac.getEnclosingStmt() instanceof IfStmt and
    (
      ac.getParent().(BinaryBitwiseOperation).getRightOperand() instanceof EnumConstantAccess
      or
      ac.getParent().(BinaryBitwiseOperation).getRightOperand() instanceof Literal
    )
  )
}

predicate isBitOpAssignInOtherFunc(Variable v, VariableAccess ac, AssignBitwiseOperation ae) {
  ae.getLValue().(VariableAccess).getTarget() = v and
  ae.getEnclosingFunction() != ac.getEnclosingFunction()
}

predicate isIndirectStateVariable(Variable v, VariableAccess ac) {
  not v.getUnspecifiedType() instanceof FunctionPointerType and
  (
    exists(VariableAccess fac, DataFlow::Node source, DataFlow::Node sink |
      fac.getTarget().getUnspecifiedType() instanceof FunctionPointerType and
      fac.getTarget() = sink.asVariable() and
      ac.getTarget() = source.asVariable() and
      TaintTracking::localTaint(source, sink)
    )
    or
    exists(VariableAccess fac, ArrayExpr ae, DataFlow::Node source, DataFlow::Node sink |
      fac.getTarget().getUnspecifiedType() instanceof FunctionPointerType and
      ac.getParent*() = ae.getArrayOffset() and
      source.asExpr() = ae and
      sink.asExpr() = fac and
      DataFlow::localFlow(source, sink)
    )
    or
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
      this.getEnclosingStmt() instanceof SwitchStmt
      or
      this.getEnclosingStmt() instanceof IfStmt and
      (
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
