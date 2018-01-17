package fortress.theory;


%%

%class Lexer

%byaccj

%{
  private Parser yyparser;

  public Lexer(java.io.Reader r, Parser yyparser) {
    this(r);
    this.yyparser = yyparser;
  }
%}

INT = [0-9]+
ID  = [_a-zA-Z][_a-zA-Z0-9]*
IMP = "=>"
IFF = "<=>"
NEQ = "!="

%%

/* operators */
"{" |
"}" |
"=" |
"!" |
"&" |
"|" |
"+" | 
"-" | 
"*" | 
"/" | 
"^" | 
"(" | 
")" |
"[" |
"]" |
":" | 
"," |
"."  { return (int) yycharat(0); }

{INT}  { yyparser.yylval = new ParserVal((Object) yytext());
         return Parser.INT; }
{ID} { yyparser.yylval = new ParserVal((Object) yytext());
        return Parser.ID;}

{IMP} { yyparser.yylval = new ParserVal((Object) yytext());
        return Parser.IMP;}

{IFF} { yyparser.yylval = new ParserVal((Object) yytext());
        return Parser.IFF;}
{NEQ} { yyparser.yylval = new ParserVal((Object) yytext());
        return Parser.NEQ;}

/* whitespace */
[ \r\n\t]+ { }

/* error fallback */
[^]    { System.err.println("Error: unexpected character '"+yytext()+"'"); return -1; }