import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.controlflow.DefinitionsAndUses
import StateVal

predicate functionContain(VariableAccess sc, Function f) {
  sc.getEnclosingFunction() = f
  or
  exists(FunctionCall call |
    call.getEnclosingFunction() = f and
    functionContain(sc, call.getTarget())
  )
}

//判定if的true分支中是否存在对状态变量的赋值，以及调用的函数中是否存在对状态变量的赋值
predicate ifTrueExistStateAssign(
  VariableAccess ac, VariableAccess sc, Expr scope, Expr target, Stmt stmt
) {
  ac.getEnclosingStmt() instanceof IfStmt and
  stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
  (
    stmt = sc.getEnclosingStmt().getParent*()
    or
    exists(FunctionCall call |
      stmt = call.getEnclosingStmt().getParent*() and
      functionContain(sc, call.getTarget())
    )
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand() and
  target = sc.getEnclosingElement().(Assignment).getRValue()
}



//判定if的false分支中是否存在对状态变量的赋值，以及调用的函数中是否存在对状态变量的赋值
predicate ifFalseExistStateAssign(
  VariableAccess ac, VariableAccess sc, Expr scope, Expr target, Stmt stmt
) {
  ac.getEnclosingStmt() instanceof IfStmt and
  stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
  (
    stmt = sc.getEnclosingStmt().getParent*()
    or
    exists(FunctionCall call |
      stmt = call.getEnclosingStmt().getParent*() and
      functionContain(sc, call.getTarget())
    )
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand() and
  target = sc.getEnclosingElement().(Assignment).getRValue()
}

//判定switch中是否存在对状态变量的赋值，以及调用的函数中是否存在对状态变量的赋值
predicate switchExistStateAssign(
  VariableAccess ac, VariableAccess sc, Expr scope, Expr target, Stmt stmt
) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    (
      stmt = case.getAStmt() and
      (
        stmt = sc.getEnclosingStmt().getParent*()
        or
        exists(FunctionCall call |
          stmt = call.getEnclosingStmt().getParent*() and
          functionContain(sc, call.getTarget())
        )
      )
    ) and
    not case.isDefault() and
    scope = case.getExpr() and
    target = sc.getEnclosingElement().(Assignment).getRValue()
  )
}

//提取出所有的子表达式
predicate getAllChildExpr(Expr e, Expr c) {
  if not e instanceof Operation then c = e else getAllChildExpr(e.(Operation).getAnOperand(), c)
}

//将表达式转换为全局变量、成员变量和确定值
Expr getExtractExpr(Stmt stmt, Expr e) {
  (
    //达成目标
    e.(VariableAccess).getTarget() instanceof MemberVariable
    or
    e.(VariableAccess).getTarget() instanceof GlobalVariable
    or
    e.isConstant()
    or
    not e instanceof VariableAccess and
    not e instanceof Operation
  ) and
  result = e
  or
  //当变量为本地变量时
  e.(VariableAccess).getTarget() instanceof SemanticStackVariable and
  exists(SemanticStackVariable localv, Expr def, Expr defv |
    localv = e.(VariableAccess).getTarget() and
    definitionUsePair(localv, def, e) and
    getAllChildExpr(def, defv) and
    result = getExtractExpr(stmt, defv)
  )
  or
  //当变量为参数时
  e.(VariableAccess).getTarget() instanceof Parameter and
  //如果参数位于判定条件所在函数，则达成目标，不进行处理
  not e.getEnclosingFunction() = stmt.getEnclosingFunction() and
  exists(FunctionCall call, int i, Expr def, Expr defv, Variable pv, Function cf |
    cf = e.getEnclosingFunction() and
    call = getPathFunctionCall(stmt, cf) and
    pv = e.(VariableAccess).getTarget() and
    pv = cf.getParameter(i) and
    def = call.getArgument(i) and
    getAllChildExpr(def, defv) and
    result = getExtractExpr(stmt, defv)
  )
  or
  e.(VariableAccess).getTarget() instanceof Parameter and
  //如果参数位于判定条件所在函数，则达成目标，不进行处理
  exists(Function f |
    f = e.getEnclosingFunction() and
    f = stmt.getEnclosingFunction()
  ) and
  result = e
  or
  //其他情况，对表达式先进行分解，再进行处理
  e instanceof Operation and
  exists(Expr c |
    getAllChildExpr(e, c) and
    result = getExtractExpr(stmt, c)
  )
}

//逐渐查找从判定到赋值的路径上的call调用
FunctionCall getContainCall(Function contain_func, Function f) {
  exists(FunctionCall call |
    call.getEnclosingFunction() = contain_func and
    if f = call.getTarget() then result = call else result = getContainCall(call.getTarget(), f)
  )
}

//获取从判定到赋值路径上的对应函数的call调用
FunctionCall getPathFunctionCall(Stmt stmt, Function f) {
  exists(FunctionCall call |
    stmt = call.getEnclosingStmt().getParent*() and
    if f = call.getTarget() then result = call else result = getContainCall(call.getTarget(), f)
  )
}

//可以识别出来模板的情况，但是这种情况目前不知道有什么用处
//example: InterData = new DiMonoCopyTemplate<Sint32>(image->InterData, fstart, fcount, fsize);
Expr getTTAllChildExpr(Expr e) {
  exists(Expr c, Operation o |
    e = o.getParent*() and
    c = o.getAnOperand() and
    result = getTTAllChildExpr(c)
  )
  or
  exists(Expr c, FunctionCall f |
    e = f.getParent*() and
    c = f.getAnArgument() and
    result = getTTAllChildExpr(c)
  )
  or
  result = e
}

//fixme: 无法处理循环递归的情况
language[monotonicAggregates]
string getExtractDetials(Stmt stmt, Expr e) {
  e.isConstant() and
  result =
    "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Constant\"," + "\"Value\":\"" + e.getValue() +
      "\"" + "}"
  or
  not e.isConstant() and
  (
    (
      //达成目标
      e.(VariableAccess).getTarget() instanceof MemberVariable and
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Member\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(MemberVariable).getQualifiedName() + "\"," + "\"Type\":\""
          + e.(VariableAccess).getTarget().(MemberVariable).getUnspecifiedType().toString() + "\"" +
          "}"
      or
      e.(VariableAccess).getTarget() instanceof GlobalVariable and
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Global\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(GlobalVariable).getQualifiedName() + "\"," + "\"Type\":\""
          + e.(VariableAccess).getTarget().(GlobalVariable).getUnspecifiedType().toString() + "\"" +
          "}"
    )
    or
    //当变量为本地变量时
    e.(VariableAccess).getTarget() instanceof LocalVariable and
    if not exists(Expr def | definitionUsePair(e.(VariableAccess).getTarget(), def, e))
    then
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Local\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(LocalVariable).getName() + "\"," + "\"Type\":\"" +
          e.(VariableAccess).getTarget().(LocalVariable).getUnspecifiedType().toString() + "\"" +
          "}"
    else
      result =
      "{" + "\"Class\": \"Split\"," +"\"Value\":" + "[" +
          concat(Expr def |
            definitionUsePair(e.(VariableAccess).getTarget(), def, e)
          |
            getExtractDetials(stmt, def), ","
          ) + "]}" // result = e.toString()
    or
    //当变量为参数时
    e.(VariableAccess).getTarget() instanceof Parameter and
    //如果参数位于判定条件所在函数，则达成目标，不进行处理
    if
      exists(Function f |
        f = e.getEnclosingFunction() and
        f = stmt.getEnclosingFunction()
      )
    then
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Parameter\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(Parameter).getName() + "\"," + "\"Type\":\"" +
          e.(VariableAccess).getTarget().(Parameter).getUnspecifiedType().toString() + "\"" + "}"
    else
      result =
      "{" + "\"Class\": \"CallSplit\"," +"\"Value\":" + "[" +
          concat(Expr def |
            exists(FunctionCall call, int i, Variable pv, Function cf |
              cf = e.getEnclosingFunction() and
              call = getPathFunctionCall(stmt, cf) and
              pv = e.(VariableAccess).getTarget() and
              pv = cf.getParameter(i) and
              def = call.getArgument(i)
            )
          |
            getExtractDetials(stmt, def), ","
          ) + "]} " // result = e.toString()
    or
    //其他情况，对表达式先进行分解，再进行处理
    e instanceof Operation and
    result =
      "{" + "\"Class\": \"Op\"," + "\"Operator\":\"" + e.(Operation).getOperator() + "\"," +
        "\"Value\":" + "[" +
        concat(Expr c | c = e.(Operation).getAnOperand() | getConditionExtractDetials(c), ",") +
        "]}"
    or
    e instanceof FunctionCall and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"FunctionCall\"," + "\"Value\":\"" + e.toString()
        + "\"}"
    or
    not e instanceof Operation and
    not e instanceof VariableAccess and
    not e instanceof FunctionCall and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Unknown\"," + "\"Value\":\"" + e.toString() +
        "\"}"
  )
}

language[monotonicAggregates]
string getConditionExtractDetials(Expr e) {
  e.isConstant() and
  result =
    "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Constant\"," + "\"Value\":\"" + e.getValue() +
      "\"" + "}"
  or
  not e.isConstant() and
  (
    (
      //达成目标
      e.(VariableAccess).getTarget() instanceof MemberVariable and
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Member\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(MemberVariable).getQualifiedName() + "\"," + "\"Type\":\""
          + e.(VariableAccess).getTarget().(MemberVariable).getUnspecifiedType().toString() + "\"" +
          "}"
      or
      e.(VariableAccess).getTarget() instanceof GlobalVariable and
      result =
        "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Global\"," + "\"Value\":\"" +
          e.(VariableAccess).getTarget().(GlobalVariable).getQualifiedName() + "\"," + "\"Type\":\""
          + e.(VariableAccess).getTarget().(GlobalVariable).getUnspecifiedType().toString() + "\"" +
          "}"
    )
    or
    //当变量为本地变量时
    e.(VariableAccess).getTarget() instanceof LocalVariable and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Local\"," + "\"Value\":\"" +
        e.(VariableAccess).getTarget().(LocalVariable).getName() + "\"," + "\"Type\":\"" +
        e.(VariableAccess).getTarget().(LocalVariable).getUnspecifiedType().toString() + "\"" + "}"
    or
    //当变量为参数时
    e.(VariableAccess).getTarget() instanceof Parameter and
    //如果参数位于判定条件所在函数，则达成目标，不进行处理
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Parameter\"," + "\"Value\":\"" +
        e.(VariableAccess).getTarget().(Parameter).getName() + "\"," + "\"Type\":\"" +
        e.(VariableAccess).getTarget().(Parameter).getUnspecifiedType().toString() + "\"" + "}"
    or
    //其他情况，对表达式先进行分解，再进行处理
    e instanceof Operation and
    result =
      "{" + "\"Class\": \"Op\"," + "\"Operator\":\"" + e.(Operation).getOperator() + "\"," +
        "\"Value\":" + "[" +
        concat(Expr c | c = e.(Operation).getAnOperand() | getConditionExtractDetials(c), " , ") +
        "]}"
    or
    e instanceof FunctionCall and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"FunctionCall\"," + "\"Value\":\"" + e.toString()
        + "\"}"
    or
    not e instanceof Operation and
    not e instanceof VariableAccess and
    not e instanceof FunctionCall and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Unknown\"," + "\"Value\":\"" + e.toString() +
        "\"}"
  )
}
