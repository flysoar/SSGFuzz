/**
 * @name State Variable
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking
import StateVal



from StateVariable v, VariableAccess sc

where 
stateVariableAccess(v, sc)

select sc, "{ \"StateName\": \"" + v.(Variable).getQualifiedName() + "\", \"FileName\": \"" + sc.getLocation().getFile().getAbsolutePath() + "\", \"StartLine\": " + sc.getEnclosingElement().getLocation().getStartLine() + ", \"StartColumn\": " + sc.getEnclosingElement().getLocation().getStartColumn() + ", \"EndLine\": " + sc.getEnclosingElement().getLocation().getEndLine() + ", \"EndColumn\": " + sc.getEnclosingElement().getLocation().getEndColumn() + ", \"VariableString\":\"" + sc.getTarget().toString() + "\" }"

//select sc, "{ \"StateName\": \"" + v.(Variable).getQualifiedName() + "\", \"FileName\": \"" + sc.getLocation().getFile().getAbsolutePath() + "\", \"StartLine\": " + sc.getEnclosingElement().getLocation().getStartLine() + ", \"StartColumn\": " + sc.getEnclosingElement().getLocation().getStartColumn() + ", \"EndLine\": " + sc.getEnclosingElement().getLocation().getEndLine() + ", \"EndColumn\": " + sc.getEnclosingElement().getLocation().getEndColumn() + " }"