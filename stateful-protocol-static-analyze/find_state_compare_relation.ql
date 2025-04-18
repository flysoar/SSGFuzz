/**
 * @name State Variable Compare Relationship
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-compare-relation
 */

/*
 * find the compare pair like if(statev1 == VAL!)
 *                                if(statev2 == VAL2)
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.controlflow.DefinitionsAndUses
import StateVal
import StateValRelation

class StateVariableCheckConstEqual instanceof StateVariableCheckConst {
  StateVariableCheckConstEqual() {
    this.(VariableAccess).getEnclosingStmt() instanceof SwitchStmt
    or
    this.(VariableAccess).getEnclosingStmt() instanceof IfStmt and
    this.(VariableAccess).getParent().(EQExpr).getRightOperand().isConstant()
  }

  string toString() { result = super.toString() }

  string getValue() {
    this.(VariableAccess).getEnclosingStmt() instanceof SwitchStmt and
    result = "switch"
    or
    this.(VariableAccess).getEnclosingStmt() instanceof IfStmt and
    result = this.(VariableAccess).getParent().(EQExpr).getRightOperand().getValue().toString()
  }
}

predicate functionContain(VariableAccess sc, Function f) {
  sc.getEnclosingFunction() = f
  or
  exists(FunctionCall call |
    call.getEnclosingFunction() = f and
    functionContain(sc, call.getTarget())
  )
}

predicate ifTrueExistStateCompare(VariableAccess ac, VariableAccess sc, Stmt stmt) {
  ac.getEnclosingStmt() instanceof IfStmt and
  stmt = ac.getEnclosingStmt().(IfStmt).getThen() and
  (
    stmt = sc.getEnclosingStmt().getParent*()
    or
    exists(FunctionCall call |
      stmt = call.getEnclosingStmt().getParent*() and
      functionContain(sc, call.getTarget())
    )
  )
}


predicate ifFalseExistStateCompare(VariableAccess ac, VariableAccess sc, Stmt stmt) {
  ac.getEnclosingStmt() instanceof IfStmt and
  stmt = ac.getEnclosingStmt().(IfStmt).getElse() and
  (
    stmt = sc.getEnclosingStmt().getParent*()
    or
    exists(FunctionCall call |
      stmt = call.getEnclosingStmt().getParent*() and
      functionContain(sc, call.getTarget())
    )
  )
}


predicate switchExistStateCompare(VariableAccess ac, VariableAccess sc, Expr scope, Stmt stmt) {
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
    scope = case.getExpr()
  )
}

from StateVariableCheckConst sc1, StateVariableCheckConstEqual sc2, Expr target
where 
(
    sc1.(VariableAccess).getParent() instanceof EQExpr and
    ifTrueExistStateCompare(sc1.(VariableAccess), sc2.(VariableAccess), _) and
    target = sc1.(VariableAccess).getParent().(EQExpr).getRightOperand()
)
or
(
    sc1.(VariableAccess).getParent() instanceof NEExpr and
    ifFalseExistStateCompare(sc1.(VariableAccess), sc2.(VariableAccess), _) and
    target = sc1.(VariableAccess).getParent().(NEExpr).getRightOperand()
)
or
(
    switchExistStateCompare(sc1.(VariableAccess), sc2.(VariableAccess), target, _)
)
select sc1.(VariableAccess), sc1.(VariableAccess).getTarget().getQualifiedName() + "," + sc2.(VariableAccess).getTarget().getQualifiedName() + "," + target.getValue() + "," + sc2.getValue()