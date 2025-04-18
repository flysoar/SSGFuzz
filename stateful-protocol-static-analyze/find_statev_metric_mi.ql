/**
 * @name State Variable Metrics MI
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-col
 */

import cpp
import StateVal

language[monotonicAggregates]
int functionContainCoL(Function f) {
  if exists(int c | c = f.getMetrics().getNumberOfLinesOfCode())
  then
    result =
      f.getMetrics().getNumberOfLinesOfCode() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainCoL(subf)
        )
  else result = 0
}

language[monotonicAggregates]
int functionContainCC(Function f) {
  if exists(int c | c = f.getMetrics().getCyclomaticComplexity())
  then
    result =
      f.getMetrics().getCyclomaticComplexity() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainCC(subf)
        )
  else result = 0
}

language[monotonicAggregates]
int functionContainN1(Function f) {
  if exists(int c | c = f.getMetrics().getHalsteadN1())
  then
    result =
      f.getMetrics().getHalsteadN1() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainN1(subf)
        )
  else result = 0
}


language[monotonicAggregates]
int functionContainN2(Function f) {
  if exists(int c | c = f.getMetrics().getHalsteadN2())
  then
    result =
      f.getMetrics().getHalsteadN2() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainN2(subf)
        )
  else result = 0
}



language[monotonicAggregates]
int functionContainN1D(Function f) {
  if exists(int c | c = f.getMetrics().getHalsteadN1Distinct())
  then
    result =
      f.getMetrics().getHalsteadN1() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainN1D(subf)
        )
  else result = 0
}


language[monotonicAggregates]
int functionContainN2D(Function f) {
  if exists(int c | c = f.getMetrics().getHalsteadN2Distinct())
  then
    result =
      f.getMetrics().getHalsteadN1() +
        sum(Function subf |
          exists(FunctionCall call |
            call.getEnclosingFunction() = f and
            call.getTarget() = subf
          ) and
          subf.fromSource() and
          not subf = f
        |
          functionContainN2D(subf)
        )
  else result = 0
}



int stmtDoCol(Stmt stmt) {
  result =
    stmtCoL(stmt) +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainCoL(f)
      )
}


int stmtDoCC(Stmt stmt) {
  result = 0 +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainCC(f)
      )
}


int stmtDoN1(Stmt stmt) {
  result = 0 +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainN1(f)
      )
}


int stmtDoN2(Stmt stmt) {
  result = 0 +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainN2(f)
      )
}


int stmtDoN1D(Stmt stmt) {
  result = 0 +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainN1D(f)
      )
}



int stmtDoN2D(Stmt stmt) {
  result = 0 +
      sum(Function f |
        exists(FunctionCall call |
          call.getEnclosingStmt().getParent*() = stmt and
          call.getTarget() = f
        ) and
        f.fromSource()
      |
        functionContainN2D(f)
      )
}

language[monotonicAggregates]
int stmtCoL(Stmt stmt) {
  result = 1 + sum(Stmt substmt | substmt = stmt.getAChild() | stmtCoL(substmt))
}


int ifTrueCoL(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoCol(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifTrueCC(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoCC(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifTrueN1(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoN1(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifTrueN2(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoN2(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifTrueN1D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoN1D(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifTrueN2D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
    result = stmtDoN2D(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseCoL(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoCol(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseCC(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoCC(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseN1(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoN1(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseN2(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoN2(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseN1D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoN1D(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int ifFalseN2D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof IfStmt and
  exists(Stmt stmt |
    stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
    result = stmtDoN2D(stmt)
  ) and
  scope = ac.getEnclosingElement().(ComparisonOperation).getRightOperand()
}


int switchCoL(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoCol(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


int switchCC(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoCC(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


int switchN1(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoN1(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


int switchN2(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoN2(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


int switchN1D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoN1D(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


int switchN2D(VariableAccess ac, Expr scope) {
  ac.getEnclosingStmt() instanceof SwitchStmt and
  exists(SwitchCase case |
    case = ac.getEnclosingStmt().(SwitchStmt).getASwitchCase() and
    result = sum(Stmt stmt | stmt = case.getAStmt() | stmtDoN2D(stmt)) and
    not case.isDefault() and
    scope = case.getExpr()
  )
}


from StateVariableCheckConst ac, int line, int cycc, int n1, int n2, int n1d, int n2d, Expr scope, string condition
where
(
    line = ifTrueCoL(ac, scope) and
    cycc = ifTrueCC(ac, scope) and
    n1 = ifTrueN1(ac, scope) and
    n2 = ifTrueN2(ac, scope) and
    n1d = ifTrueN1D(ac, scope) and
    n2d = ifTrueN2D(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "!="
    else condition = "=="
)
or
(
    line = ifFalseCoL(ac, scope) and
    cycc = ifFalseCC(ac, scope) and
    n1 = ifFalseN1(ac, scope) and
    n2 = ifFalseN2(ac, scope) and
    n1d = ifFalseN1D(ac, scope) and
    n2d = ifFalseN2D(ac, scope) and
    if ac.(VariableAccess).getParent().(Operation).getOperator() = "!="
    then condition = "=="
    else condition = "!="
)
or
(
    line = switchCoL(ac, scope) and
    cycc = switchCC(ac, scope) and
    n1 = switchN1(ac, scope) and
    n2 = switchN2(ac, scope) and
    n1d = switchN1D(ac, scope) and
    n2d = switchN2D(ac, scope) and
    condition = "=="
)

select ac.(VariableAccess), "{" + "\"StateVName\":" + "\"" + ac.(VariableAccess).getTarget().getQualifiedName() + "\"" + "," + "\"Condition\":" + "\"" + condition + "\"" + "," + "\"Value\":" + "\"" + scope.getValue() + "\"," + "\"CoL\":" + line + "," + "\"CC\":" + cycc + "," + "\"N1\":" + n1 + "," + "\"N2\":" + n2 + "," + "\"N1D\":" + n1d + "," + "\"N2D\":" + n2d + "}"