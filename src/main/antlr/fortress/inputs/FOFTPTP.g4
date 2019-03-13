grammar FOFTPTP;

spec : fof_annotated+ ;

fof_annotated : 'fof' '(' ID ',' ID ',' fof_formula ')' '.' ;

fof_formula : '~' fof_formula                            # not
            | '!' '[' ID (',' ID)* ']' ':' fof_formula   # forall
            | '?' '[' ID (',' ID)* ']' ':' fof_formula   # exists
            | fof_formula '&' fof_formula                # and
            | fof_formula '|' fof_formula                # or
            | fof_formula '=>' fof_formula               # imp
            | fof_formula '<=>' fof_formula              # iff
            | term '=' term                              # eq
            | term '!=' term                             # neq
            | ID                                         # prop
            | ID '(' term (',' term)* ')'                # pred
            | '(' fof_formula ')'                        # paren
            ;

term : ID                          # conVar
     | ID '(' term (',' term)* ')' # apply
     ;

ID : [_a-zA-Z][_a-zA-Z0-9]* ;

WS : [ \t\r\n] -> skip;
COMMENT : '%'   ~('\r' | '\n')*  ('\r'? '\n')? -> skip;
            