/**
 * @name State Variable Metrics Global Variables Access
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-gc
 */

import cpp
import StateVal

class GlobalAccess instanceof VariableAccess {
  GlobalAccess() {
    (
      this.getTarget() instanceof GlobalVariable
      or
      this.getTarget() instanceof MemberVariable
    ) and
    not this.isConstant() and
    this.getTarget().getDefinition().fromSource()
  }

  string toString() { result = super.toString() }

  string getName() { result = super.getTarget().getQualifiedName() }
}


string stmtGlobalAccessCount(Stmt stmt) {
  result =
    concat(GlobalAccess ga |
      ga.(VariableAccess).getEnclosingStmt().getParent*() = stmt
    |
      ga.getName(), " , "
    )
}


string functionGlobalAccessCount(Function f) {
  result =
    concat(GlobalAccess ga | ga.(VariableAccess).getEnclosingFunction() = f | ga.getName(), " , ")
}


string stmtDoGolobalAccessCount(Stmt stmt) {
  result =
    stmtGlobalAccessCount(stmt) + " , " +
      concat(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionCountainGlobalAccessCount(f), " , "
      )
}


language[monotonicAggregates]
string functionCountainGlobalAccessCount(Function f) {
  if exists(int c | c = f.getMetrics().getNumberOfLinesOfCode())
  then
    result =
      functionGlobalAccessCount(f) + " , " +
        concat(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionCountainGlobalAccessCount(subf), " , "
        )
  else result = ""
}


string ifTrueGlobalAccessCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoGolobalAccessCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


string ifFalseGlobalAccessCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoGolobalAccessCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


string switchGlobalAccessCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = concat(Stmt stmt | stmt = case.getAStmt() | stmtDoGolobalAccessCount(stmt), " , ") and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


from StateVariableCheckConst ac, string gac, Expr scope, string condition
where
(
    gac = ifTrueGlobalAccessCount(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "!="
    else condition = "=="
)
or
(
    gac = ifFalseGlobalAccessCount(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "=="
    else condition = "!="
)
or
(
    gac = switchGlobalAccessCount(ac, scope) and
    condition = "=="
)

select ac.(VariableAccess), "{" + "\"StateVName\":" + "\"" + ac.(VariableAccess).getTarget().getQualifiedName() + "\"" + "," + "\"Condition\":" + "\"" + condition + "\"" + "," + "\"Value\":" + "\"" + scope.getValue() + "\"," + "\"GlobalAccess\":" + "\"" + gac + "\"" +"}"