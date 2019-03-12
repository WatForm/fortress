grammar SmtLibSubset;

commands : command+ ;

command : '(' 'declare-const' ID ID ')'             # declareconst
        | '(' 'declare-fun' ID '(' ID* ')' ID ')'   # declarefun
        | '(' 'declare-sort' ID ')'                 # declaresort
	    | '(' 'assert' term ')'                     # assertion
        | '(' 'check-sat' ')'                       # checksat
        | '(' 'exit' ')'                            # exit
        ;

term : 'true'                                       # true
     | 'false'                                      # false
     | '(' 'and' term term term* ')'                # and
     | '(' 'or' term term term* ')'                 # or
     | '(' 'distinct' term+ ')'                     # distinct
     | '(' '=' term term ')'                        # eq
     | '(' '=>' term term ')'                       # imp
     | '(' 'not' term ')'                           # not
     | '(' 'forall' '(' binding+ ')' term ')'       # forall  
     | '(' 'exists' '(' binding+ ')' term ')'       # exists
     | '(' ID term+ ')'                             # application
     | ID                                           # var
     ;

binding : '(' ID ID ')';
       
ID : [?_a-zA-Z][_a-zA-Z0-9]* ;

WS : [ \t\r\n] -> skip;
COMMENT : ';'   ~('\r' | '\n')*  ('\r'? '\n')? -> skip;
SETINFO : '(set-info' ~( ')' )* ( ')' ) -> skip;
SETLOGIC: '(set-logic' ~( ')' )* ( ')' ) -> skip; 
