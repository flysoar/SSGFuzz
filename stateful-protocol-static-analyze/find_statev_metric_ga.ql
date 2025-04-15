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

//统计一个stmt中全局变量赋值
string stmtGlobalAssignCount(Stmt stmt) {
  result =
    concat(GlobalAssign ga |
      ga.(VariableAccess).getEnclosingStmt().getParent*() = stmt
    |
      ga.getName(), " , "
    )
}

//统计一个函数中全局变量赋值
string functionGlobalAssignCount(Function f) {
  result =
    concat(GlobalAssign ga | ga.(VariableAccess).getEnclosingFunction() = f | ga.getName(), " , ")
}

//统计stmt以及其调用的函数中全局变量赋值
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

//统计函数以及其调用的函数中全局变量赋值
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

//获取IF中True分支的全局变量赋值
string ifTrueGlobalAssignCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoGolobalAssignCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}

//获取IF中False分支的全局变量赋值
string ifFalseGlobalAssignCount(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoGolobalAssignCount(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}

//获取Switch中的全局变量赋值
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