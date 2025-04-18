/**
 * @name State Variable Metrics Global Variables Assignment
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-ga
 */

import cpp
import StateVal

class GlobalAssign instanceof VariableAccess {
  GlobalAssign() {
    (
      this.getTarget() instanceof GlobalVariable
      or
      this.getTarget() instanceof MemberVariable
    ) and
    not this.isConstant() and
    this.getTarget().getDefinition().fromSource() and
    exists(AssignExpr ae |
      this.getEnclosingElement() = ae and
      ae.getLValue() = this
    )
  }

  string toString() { result = super.toString() }

  string getName() { result = super.getTarget().getQualifiedName() }
}


string stmtGlobalAssignCount(Stmt stmt) {
  result =
    concat(GlobalAssign ga |
      ga.(VariableAccess).getEnclosingStmt().getParent*() = stmt
    |
      ga.getName(), " , "
    )
}


string functionGlobalAssignCount(Function f) {
  result =
    concat(GlobalAssign ga | ga.(VariableAccess).getEnclosingFunction() = f | ga.getName(), " , ")
}


string stmtDoGolobalAssignCount(Stmt stmt) {
  result =
    stmtGlobalAssignCount(stmt) + " , " +
      //sum( FunctionCall call | call.getEnclosingStmt().getParent*() = stmt  and call.getTarget().fromSource() | functionContainCoL(call.getTarget()) )
      concat(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionCountainGlobalAssignCount(f), " , "
      )
}


language[monotonicAggregates]
string functionCountainGlobalAssignCount(Function f) {
  if exists(int c | c = f.getMetrics().getNumberOfLinesOfCode())
  then
    result =
      functionGlobalAssignCount(f) + " , " +
        concat(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionCountainGlobalAssignCount(subf), " , "
        )
  else result = ""
}


string ifTrueGlobalAssignCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoGolobalAssignCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


string ifFalseGlobalAssignCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoGolobalAssignCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


string switchGlobalAssignCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = concat(Stmt stmt | stmt = case.getAStmt() | stmtDoGolobalAssignCount(stmt), " , ") and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


from StateVariableCheckConst ac, string gac, Expr scope, string condition
where
(
    gac = ifTrueGlobalAssignCount(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "!="
    else condition = "=="
)
or
(
    gac = ifFalseGlobalAssignCount(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "=="
    else condition = "!="
)
or
(
    gac = switchGlobalAssignCount(ac, scope) and
    condition = "=="
)

select ac.(VariableAccess), "{" + "\"StateVName\":" + "\"" + ac.(VariableAccess).getTarget().getQualifiedName() + "\"" + "," + "\"Condition\":" + "\"" + condition + "\"" + "," + "\"Value\":" + "\"" + scope.getValue() + "\"," + "\"GlobalAssign\":" + "\"" + gac + "\"" +"}"