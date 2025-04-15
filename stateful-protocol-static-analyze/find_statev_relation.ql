/**
 * @name State Variable Relationship
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-relation
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.controlflow.DefinitionsAndUses
import StateVal
import StateValRelation

class StateConditionPair instanceof Expr {
  StateVariableCheck ac;
  StateVariableAssign sc;
  Expr scope;
  Stmt stmt;
  string range_str;

  StateConditionPair() {
    ifTrueExistStateAssign(ac, sc, scope, this, stmt) and
    exists(string op |
      (
        if ac.(VariableAccess).getEnclosingStmt().(IfStmt).getControllingExpr() instanceof Operation
        then op = ac.(VariableAccess).getParent().(Operation).getOperator()
        else op = "None"
      ) and
      range_str = "{\"Type\":\"if-true\",\"Op\":\"" + op + "\"}"
    )
    or
    ifFalseExistStateAssign(ac, sc, scope, this, stmt) and
    exists(string op |
      (
        if ac.(VariableAccess).getEnclosingStmt().(IfStmt).getControllingExpr() instanceof Operation
        then op = ac.(VariableAccess).getParent().(Operation).getOperator()
        else op = "None"
      ) and
      range_str = "{\"Type\":\"if-true\",\"Op\":\"" + op + "\"}"
    )
    or
    switchExistStateAssign(ac, sc, scope, this, stmt) and
    range_str = "{\"Type\":\"switch\",\"Op\":\"" + "None" + "\"}"
  }

  string toString() { result = super.toString() }

  Expr getScope() { result = scope }

  Expr getTarget() { result = this }

  string getRangeStr() { result = range_str }

  StateVariableCheck getStateV() { result = ac }

  StateVariableAssign getAssignV() { result = sc }

  Stmt getStmt() { result = stmt }

  string getExtractDetials() {
    result = "{" + "\"Class\":\"Top\"," +
      "\"Range\":" + range_str + "," +
      "\"StateVName\":\"" + ac.getStateVName() + "\"," +
      "\"AssignVName\":\"" + sc.getStateVName() + "\"," +
      "\"Condition\":" + getConditionExtractDetials(scope) + "," +
      "\"Extract\":" + getExtractDetials(stmt, this) + "}"
  }
}


/*
   from
    StateVariableCheck ac, StateVariableAssign sc, Expr scope, Expr target, string range_str,
    Stmt stmt, string ex_str
   where
    (
      ifTrueExistStateAssign(ac, sc, scope, target, stmt) and
      range_str = "if true "
      or
      ifFalseExistStateAssign(ac, sc, scope, target, stmt) and
      range_str = "if false "
      or
      switchExistStateAssign(ac, sc, scope, target, stmt) and
      range_str = "switch "
    )
    and
    ex_str = getExtractDetials(stmt, target)
   select  target, scope, ac, sc, range_str, ex_str
 */

from StateConditionPair target, string ex
where ex = target.getExtractDetials()
//va = getAllChildExpr(target.getTarget())
select target.(Expr), ex