/**
 * @name State Variable Keyword
 * @kind problem
 * @problem.severity recommendation
 * @id cpp/example/find-statev-keyword
 */

import cpp
import StateVal

predicate statevEnmu(StateVariable v, Enum ed) {
    //v.(Variable).getUnderlyingType() = ed 
    //or
    exists( VariableAccess sc |   
        sc.getTarget() = v and
        (
            (
                sc.(VariableAccess).getParent().(EQExpr).getRightOperand() instanceof EnumConstantAccess and
                ed = sc.(VariableAccess).getParent().(EQExpr).getRightOperand().(EnumConstantAccess).getUnderlyingType()
            )
            or
            (
                exists(SwitchCase case |
                    case = sc.(VariableAccess).getEnclosingStmt().(SwitchStmt).getASwitchCase() and
                    case.getExpr().(EnumConstantAccess).getUnderlyingType() = ed
                )
            )
        )
    )
}


// example static ksr_hdr_map_t _ksr_hdr_map[] = {
//	{ str_init("a"), HDR_ACCEPTCONTACT_T, HDR_ACCEPTCONTACT_F },
string enumConstantStringArray(EnumConstant ec) {
    exists(	AggregateLiteral aexpr, StringLiteral sl |  
        aexpr = ec.getAnAccess().getEnclosingElement() and
        sl.getEnclosingElement*() = aexpr and
        result = ec.getValue() + "," + sl.getValue()
    )
    or
    result = ec.getValue() + ","
}


predicate enumConstantStringArrayDebug(Enum ed, EnumConstantAccess eca, string str) {
    ed = eca.getUnderlyingType() and
    exists(	AggregateLiteral aexpr |  
        aexpr = eca.getEnclosingElement*().(AggregateLiteral) and
        exists( StringLiteral sl | 
            sl.getEnclosingElement*() = aexpr and
            sl.getValue() = str
        )
    )
}

class StateVariableKeypair extends StateVariable {
    
    string info;
    StateVariableKeypair() {
        exists( Enum ed, EnumConstant ec  | 
            statevEnmu(this, ed) and
            ec = ed.getAnEnumConstant() and
            info = this.(Variable).getQualifiedName().toString() + "," + ec.getValue() + "," + enumConstantStringArray(ec)
        )
    }

    string getResult() { result = info }
}



//from  StringLiteral sl, AggregateLiteral al
//where
//sl.getEnclosingElement*() = al 
//select al, "State variable should be initialized with"


from StateVariable v, Enum ed, string str
where
statevEnmu(v, ed) and
exists(EnumConstant ec |  
    ec.getDeclaringEnum() = ed and
    str = enumConstantStringArray(ec)
)
select v.(Variable), ed, str

/*
from StateVariable v, Enum ed
where
statevEnmu(v, ed)
select v.(Variable), ed, "aaa"
*/

//from StateVariableKeypair v
//select v, v.getResult()
