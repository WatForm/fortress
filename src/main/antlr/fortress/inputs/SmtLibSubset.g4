grammar SmtLibSubset;

// Parser rules

commands : command+ ;

command : '(' 'declare-const' ID ID ')'             # declare_const
        | '(' 'declare-fun' ID '(' ID* ')' ID ')'   # declare_fun
        | '(' 'declare-sort' ID ')'                 # declare_sort
	    | '(' 'assert' term ')'                     # assert
        | '(' 'check-sat' ')'                       # check_sat
        | '(' 'set-info' attribute ')'              # set_info
        | '(' 'set-logic' ID ')'                    # set_logic
        | '(' 'get-model' ')'                       # get_model
        | '(' 'exit' ')'                            # exit
        ;

attribute : ':' ID ID                              # attribute_id
          | ':' ID QUOTE                           # attribute_quote
          | ':' ID STRING                          # attribute_string
          ;

term : 'true'                                       # true
     | 'false'                                      # false
     | '(' 'and' term term term* ')'                # and
     | '(' 'or' term term term* ')'                 # or
     | '(' 'distinct' term+ ')'                     # distinct
     | '(' '=' term term+ ')'                       # eq
     | '(' '=>' term term+ ')'                      # imp
     | '(' 'not' term ')'                           # not
     | '(' ID term+ ')'                             # application
     | '(' 'forall' '(' binding+ ')' term ')'       # forall  
     | '(' 'exists' '(' binding+ ')' term ')'       # exists
     | '(' '!' term term_attribute+ ')'             # term_with_attributes
     | ID                                           # var
     ;

binding : '(' ID ID ')' ;

term_attribute: ':named' ID                          #namedAttribute
              | ':pattern'  '(' term+ ')'            #patternAttribute
              ;

// Lexer rules

ID: (LETTER | DIGIT | SPECIAL)+ ;
QUOTE: '|' (PRINTABLE_NOT_PIPE_BS | WS)* '|' ;
STRING: '"' (PRINTABLE_NOT_QUOTE | WS)* '"' ;

LETTER: [A-Za-z] ;
DIGIT: [0-9] ;
SPECIAL: [~!@$%^&*] | '_' | [-+=<>.?/] ;

PRINTABLE_NOT_QUOTE: [\u0021] | [\u0023-\u007E] ; // ASCII 33 to 226
PRINTABLE_NOT_PIPE_BS:  [\u0021-\u005B] | [\u005D-\u007B] | [\u007D-\u007E] ;

WS : [ \t\r\n] -> skip;
COMMENT : ';'   ~('\r' | '\n')*  ('\r'? '\n')? -> skip;
