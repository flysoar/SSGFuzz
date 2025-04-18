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


predicate getAllChildExpr(Expr e, Expr c) {
  if not e instanceof Operation then c = e else getAllChildExpr(e.(Operation).getAnOperand(), c)
}


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
  e.(VariableAccess).getTarget() instanceof SemanticStackVariable and
  exists(SemanticStackVariable localv, Expr def, Expr defv |
    localv = e.(VariableAccess).getTarget() and
    definitionUsePair(localv, def, e) and
    getAllChildExpr(def, defv) and
    result = getExtractExpr(stmt, defv)
  )
  or
  e.(VariableAccess).getTarget() instanceof Parameter and
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
  exists(Function f |
    f = e.getEnclosingFunction() and
    f = stmt.getEnclosingFunction()
  ) and
  result = e
  or
  e instanceof Operation and
  exists(Expr c |
    getAllChildExpr(e, c) and
    result = getExtractExpr(stmt, c)
  )
}

FunctionCall getContainCall(Function contain_func, Function f) {
  exists(FunctionCall call |
    call.getEnclosingFunction() = contain_func and
    if f = call.getTarget() then result = call else result = getContainCall(call.getTarget(), f)
  )
}

FunctionCall getPathFunctionCall(Stmt stmt, Function f) {
  exists(FunctionCall call |
    stmt = call.getEnclosingStmt().getParent*() and
    if f = call.getTarget() then result = call else result = getContainCall(call.getTarget(), f)
  )
}


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
    e.(VariableAccess).getTarget() instanceof Parameter and
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
    e.(VariableAccess).getTarget() instanceof LocalVariable and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Local\"," + "\"Value\":\"" +
        e.(VariableAccess).getTarget().(LocalVariable).getName() + "\"," + "\"Type\":\"" +
        e.(VariableAccess).getTarget().(LocalVariable).getUnspecifiedType().toString() + "\"" + "}"
    or
    e.(VariableAccess).getTarget() instanceof Parameter and
    result =
      "{" + "\"Class\": \"Val\"," + "\"SubClass\":\"Parameter\"," + "\"Value\":\"" +
        e.(VariableAccess).getTarget().(Parameter).getName() + "\"," + "\"Type\":\"" +
        e.(VariableAccess).getTarget().(Parameter).getUnspecifiedType().toString() + "\"" + "}"
    or
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
