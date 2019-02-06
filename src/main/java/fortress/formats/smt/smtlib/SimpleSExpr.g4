grammar SimpleSExpr;

s_exprs : s_expr+ ;

s_expr : ID                    # atom
       | '(' s_expr* ')'       # list
       ;
       
ID : [_a-zA-Z][_a-zA-Z0-9]* ;

WS : [ \t\r\n] -> skip;
COMMENT : ';'   ~('\r' | '\n')*  ('\r'? '\n')? -> skip;
