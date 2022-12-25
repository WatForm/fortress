grammar SmtLibSubset;

// Parser rules

commands : command+ ;

command : '(' 'declare-const' ID sort ')'                           # declare_const
        | '(' 'declare-fun' ID '(' sort* ')' sort ')'               # declare_fun
        | '(' 'declare-sort' ID '0' ')'                             # declare_sort
	    | '(' 'assert' term ')'                                     # assert
        | '(' 'check-sat' ')'                                       # check_sat
        | '(' 'set-info' attribute ')'                              # set_info
        | '(' 'set-logic' ID ')'                                    # set_logic
        | '(' 'get-model' ')'                                       # get_model
        | '(' 'exit' ')'                                            # exit
        | '(' 'define-fun' ID '(' sorted_var* ')' sort term ')'     # define_fun
        | term                                                      # constraint
        ;

//function_def : ID '(' sorted_var* ')' sort term ;

sorted_var : '(' ID sort  ')' ;

sort : ID                                             # sort_name
     | '(' '_' 'BitVec' NUMBER ')'                    # bv_sort
     ;

attribute : ':' ID ID                                 # attribute_id
       // | ':' ID QUOTE                              # attribute_quote
          | ':' ID STRING                             # attribute_string
          | ':' ID DEC_DIGIT						  # attribute_dec_digit
          ;

term : 'true'                                         # true
     | 'false'                                        # false
     | '(' 'ite' term term term ')'                   # ite
     | '(' 'let' '(' letbinding+ ')' term ')'         # let
     | '(' 'and' term term term* ')'                  # and
     | '(' 'or' term term term* ')'                   # or
     | '(' 'distinct' term+ ')'                       # distinct
     | '(' '=' term term+ ')'                         # eq
     | '(' '=>' term term+ ')'                        # imp
     | '(' 'not' term ')'                             # not
     | '(' ID term+ ')'                               # application
     | '(' 'forall' '(' binding+ ')' term ')'         # forall
     | '(' 'exists' '(' binding+ ')' term ')'         # exists
     | '(' '!' term term_attribute+ ')'               # term_with_attributes
     | ID                                             # var
     // Expanded to support closures
     | '(' 'closure' ID term term term* ')'           # closure
     | '(' 'reflexive-closure' ID term term term* ')' # reflexive_closure   

// Integers
     | NUMBER                                         # int_literal
     | ZERO                                           # int_zero
     | '(' '-' term ')'                               # neg
     | '(' '-' term term+ ')'                         # sub
     | '(' '+' term term+ ')'                         # plus
     | '(' '*' term term+ ')'                         # mult
     | '(' 'div' term term+ ')'                       # div
     | '(' 'mod' term term ')'                        # mod
     | '(' 'abs' term ')'                             # abs
     | '(' '<=' term term+ ')'                        # le
     | '(' '<' term term+ ')'                         # lt
     | '(' '>=' term term+ ')'                        # ge
     | '(' '>' term term+ ')'                         # gt

// Bit vectors
     | BIN_NUMBER                                     # bin_literal
     | HEX_NUMBER                                     # hex_literal
     | '(' 'concat' term term term ')'                # bvconcat
     | '(' 'bvnot' term ')'                           # bvnot
     | '(' 'bvneg' term ')'                           # bvneg
     | '(' 'bvand' term term ')'                      # bvand
     | '(' 'bvor' term term ')'                       # bvor
     | '(' 'bvadd' term term ')'                      # bvadd
     | '(' 'bvmul' term term ')'                      # bvmul
     | '(' 'bvudiv' term term ')'                     # bvudiv
     | '(' 'bvurem' term term ')'                     # bvurem
     | '(' 'bvshl' term term ')'                      # bvshl
     | '(' 'bvshr' term term ')'                      # bvshr
     ;

letbinding: '(' ID term ')' ;

binding : '(' ID sort ')' ;

term_attribute: ':named' ID                           # namedAttribute
              | ':pattern'  '(' term+ ')'             # patternAttribute
              ;

// Lexer rules

// abc == |abc| as an identifier!! Treat it as such.
ID: SIMPLE | QUOTE;
// Simple Symbols must contain at least one letter, to distinguish from numerals
SIMPLE: (LETTER | SPECIAL) (LETTER | DIGIT | SPECIAL)* ;
QUOTE: '|' (PRINTABLE_NOT_PIPE_BS | WS)* '|' ;
STRING: '"' (PRINTABLE_NOT_QUOTE | WS)* '"' ;
NUMBER: POS_NUMBER | '-' POS_NUMBER ;
BIN_NUMBER: '#b' BIN_DIGIT+ ;
HEX_NUMBER: '#x' HEX_DIGIT+ ;

POS_NUMBER: NON_ZERO DIGIT* ;

ZERO: '0';

LETTER: [A-Za-z] ;
NON_ZERO: [1-9] ;
DIGIT: [0-9] ;
DEC_DIGIT: DIGIT+ '.' DIGIT+ ;
BIN_DIGIT: [01] ;
HEX_DIGIT: [0-9a-fA-F] ;
SPECIAL: [~!@$%^&*] | '_' | [-+=<>.?/] ;

PRINTABLE_NOT_QUOTE: [\u0021] | [\u0023-\u007E] ; // ASCII 33 to 226
PRINTABLE_NOT_PIPE_BS:  [\u0021-\u005B] | [\u005D-\u007B] | [\u007D-\u007E] ;

WS : [ \t\r\n] -> skip;
COMMENT : ';'   ~('\r' | '\n')*  ('\r'? '\n')? -> skip;
