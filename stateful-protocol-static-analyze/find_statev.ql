/**
 * @name State Variable
 * @kind problem
 * @problem.severity Critical
 * @id cpp/example/find-statev
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking
import StateVal



from Variable v, VariableAccess ac, VariableAccess sc

where 
(
    isStateVariable(v, ac)
    or
    isParameterStateVariable(v, ac)
) and
stateVariableAccess(v, sc)

//select v, ac, sc

select v, v.(Variable).getQualifiedName()

//select v, "State"  ,sc.getEnclosingElement(),  sc.getLocation().getFile().getAbsolutePath() + " File. " + sc.getEnclosingElement().getLocation().getEndLine() + " Line. " + sc.getEnclosingElement().getLocation().getEndColumn() + " Column." 

//select v,   sc.getLocation().getFile().getAbsolutePath() + " File. " + sc.getEnclosingElement().getLocation().getStartLine() + " Line. " + sc.getEnclosingElement().getLocation().getStartColumn() + " Column. " + sc.getEnclosingElement().getLocation().getEndLine() + " Line. " + sc.getEnclosingElement().getLocation().getEndColumn() + " Column. "