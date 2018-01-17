//### This file created by BYACC 1.8(/Java extension  1.15)
//### Java capabilities added 7 Jan 97, Bob Jamison
//### Updated : 27 Nov 97  -- Bob Jamison, Joe Nieten
//###           01 Jan 98  -- Bob Jamison -- fixed generic semantic constructor
//###           01 Jun 99  -- Bob Jamison -- added Runnable support
//###           06 Aug 00  -- Bob Jamison -- made state variables class-global
//###           03 Jan 01  -- Bob Jamison -- improved flags, tracing
//###           16 May 01  -- Bob Jamison -- added custom stack sizing
//###           04 Mar 02  -- Yuval Oren  -- improved java performance, added options
//###           14 Mar 02  -- Tomas Hurka -- -d support, static initializer workaround
//### Please send bug reports to tom@hukatronic.cz
//### static char yysccsid[] = "@(#)yaccpar	1.8 (Berkeley) 01/20/90";






//#line 2 "term.y"
    package fortress.theory;

    import fortress.fol.pterm.PTerm;
    import fortress.fol.pterm.PVar;
    import fortress.fol.pterm.Com;
    import fortress.fol.FOL;
    import fortress.fol.Arith;

    import fortress.lambda.Term;
    import fortress.lambda.Var;
    import fortress.lambda.App;
    import fortress.lambda.Abs;
    import fortress.lambda.Type;

    import fortress.util.Pair;

    import java.util.ArrayList;
    import java.util.Arrays;
    import java.util.List;
    import java.util.Map;
    import java.util.HashMap;
    import java.util.Optional;
//#line 40 "Parser.java"




public class Parser
{

boolean yydebug;        //do I want debug output?
int yynerrs;            //number of errors so far
int yyerrflag;          //was there an error?
int yychar;             //the current working character

//########## MESSAGES ##########
//###############################################################
// method: debug
//###############################################################
void debug(String msg)
{
  if (yydebug)
    System.out.println(msg);
}

//########## STATE STACK ##########
final static int YYSTACKSIZE = 500;  //maximum stack size
int statestk[] = new int[YYSTACKSIZE]; //state stack
int stateptr;
int stateptrmax;                     //highest index of stackptr
int statemax;                        //state when highest index reached
//###############################################################
// methods: state stack push,pop,drop,peek
//###############################################################
final void state_push(int state)
{
  try {
		stateptr++;
		statestk[stateptr]=state;
	 }
	 catch (ArrayIndexOutOfBoundsException e) {
     int oldsize = statestk.length;
     int newsize = oldsize * 2;
     int[] newstack = new int[newsize];
     System.arraycopy(statestk,0,newstack,0,oldsize);
     statestk = newstack;
     statestk[stateptr]=state;
  }
}
final int state_pop()
{
  return statestk[stateptr--];
}
final void state_drop(int cnt)
{
  stateptr -= cnt; 
}
final int state_peek(int relative)
{
  return statestk[stateptr-relative];
}
//###############################################################
// method: init_stacks : allocate and prepare stacks
//###############################################################
final boolean init_stacks()
{
  stateptr = -1;
  val_init();
  return true;
}
//###############################################################
// method: dump_stacks : show n levels of the stacks
//###############################################################
void dump_stacks(int count)
{
int i;
  System.out.println("=index==state====value=     s:"+stateptr+"  v:"+valptr);
  for (i=0;i<count;i++)
    System.out.println(" "+i+"    "+statestk[i]+"      "+valstk[i]);
  System.out.println("======================");
}


//########## SEMANTIC VALUES ##########
//public class ParserVal is defined in ParserVal.java


String   yytext;//user variable to return contextual strings
ParserVal yyval; //used to return semantic vals from action routines
ParserVal yylval;//the 'lval' (result) I got from yylex()
ParserVal valstk[];
int valptr;
//###############################################################
// methods: value stack push,pop,drop,peek.
//###############################################################
void val_init()
{
  valstk=new ParserVal[YYSTACKSIZE];
  yyval=new ParserVal();
  yylval=new ParserVal();
  valptr=-1;
}
void val_push(ParserVal val)
{
  if (valptr>=YYSTACKSIZE)
    return;
  valstk[++valptr]=val;
}
ParserVal val_pop()
{
  if (valptr<0)
    return new ParserVal();
  return valstk[valptr--];
}
void val_drop(int cnt)
{
int ptr;
  ptr=valptr-cnt;
  if (ptr<0)
    return;
  valptr = ptr;
}
ParserVal val_peek(int relative)
{
int ptr;
  ptr=valptr-relative;
  if (ptr<0)
    return new ParserVal();
  return valstk[ptr];
}
final ParserVal dup_yyval(ParserVal val)
{
  ParserVal dup = new ParserVal();
  dup.ival = val.ival;
  dup.dval = val.dval;
  dup.sval = val.sval;
  dup.obj = val.obj;
  return dup;
}
//#### end semantic value section ####
public final static short NL=257;
public final static short INT=258;
public final static short ID=259;
public final static short IMP=260;
public final static short IFF=261;
public final static short NEQ=262;
public final static short NEG=263;
public final static short YYERRCODE=256;
final static short yylhs[] = {                           -1,
    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,
    0,    0,    0,    0,    0,    0,    0,    4,    5,    5,
    3,    3,    6,    6,    1,    1,    2,    2,
};
final static short yylen[] = {                            2,
    1,    1,    2,    1,    3,    3,    3,    3,    2,    3,
    3,    3,    3,    3,    3,    2,    3,    3,    1,    3,
    2,    4,    0,    2,    1,    4,    1,    3,
};
final static short yydefred[] = {                         0,
    1,    0,    0,    0,    0,    0,    0,    4,    3,    0,
   16,    0,    0,    0,    0,    0,    0,    0,    0,    0,
    0,    0,    0,    0,   17,    0,   21,   19,    0,    0,
   18,    0,    0,    0,    0,    0,    0,    0,    0,   15,
   14,    0,   24,    0,    0,    0,   20,   22,   27,    0,
   26,    0,   28,
};
final static short yydgoto[] = {                          7,
   43,   50,   14,    8,   31,   27,
};
final static short yysindex[] = {                       -31,
    0,  -91,  -31,  -31,  -31,  -31,  141,    0,    0,  -37,
    0,  -26,  113,  -16,  -31,  -31,  -31,  -31,  -31,  -31,
  -31,  -31,  -31,  -31,    0, -256,    0,    0,  -31,  -31,
    0,  152,  152,   60,  -20,  -37,  -11,   69,   69,    0,
    0,  -87,    0,  121,  113, -256,    0,    0,    0,   -7,
    0, -256,    0,
};
final static short yyrindex[] = {                         0,
    0,    1,    0,    0,    0,    0,    0,    0,    0,   68,
    0,    0,    7,    0,    0,    0,    0,    0,    0,    0,
    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,
    0,   92,  165,   29,   74,   83,   38,   11,   20,    0,
    0,   47,    0,    0,    7,    0,    0,    0,    0,    0,
    0,    0,    0,
};
final static short yygindex[] = {                       289,
  -39,    0,    0,   24,    0,  -12,
};
final static int YYTABLESIZE=414;
static short yytable[];
static { yytable();}
static void yytable(){
yytable = new short[]{                          6,
    2,    3,   42,   46,   23,   22,   49,   21,    5,   24,
   13,   19,   53,    4,   25,   23,   22,   19,   21,   12,
   24,   23,   22,   20,   21,    9,   24,   30,   10,   29,
   23,   22,   48,   21,   20,   24,   52,   11,    2,    0,
   20,    2,    2,    2,    2,    2,    2,    2,   13,    0,
   23,   13,   23,   13,   13,   13,   13,   12,    2,    6,
   12,    2,   12,   12,   12,   12,   10,    9,   13,   10,
    0,   13,   10,    7,   10,   11,   28,   12,   11,    0,
   12,   11,    8,   11,    0,   51,   10,    0,    0,   10,
   25,    6,   25,    2,    0,   11,    0,   18,   11,   23,
    0,   23,   22,   13,   21,    9,   24,    0,    9,    0,
   23,    9,   12,    9,    7,   24,    0,    7,    0,    7,
    8,   10,    0,    8,    2,    9,    8,    0,    8,    0,
   11,    7,    6,    0,   13,    6,    0,    6,    0,   25,
    8,    0,    0,   12,    0,    0,    0,    0,    0,    6,
   19,    0,   10,    0,   23,   22,    0,   21,   19,   24,
    9,   11,   23,   22,    5,   21,    7,   24,    0,    0,
   26,    0,    0,   20,    0,    8,    0,    0,   19,    0,
    0,   20,   23,   22,    6,   21,    0,   24,    0,   19,
    0,    9,    0,   23,   22,    0,   21,    7,   24,    0,
    0,   20,    0,    0,    0,    5,    8,    0,    5,    0,
    5,    0,   20,   47,    0,    0,    0,    0,    0,    0,
    0,    0,    5,    0,   17,    0,    1,    2,    0,    0,
    0,    0,    0,   15,   16,   17,   18,    0,    0,    0,
    0,   17,    0,    0,   18,    0,    0,    0,    0,    0,
   17,    0,    0,    0,    0,    0,    0,    5,    0,    0,
    2,    2,    2,    0,   18,    0,    0,    0,    0,    0,
   13,   13,   13,    0,    0,   18,    0,    0,    0,   12,
   12,   12,    0,    0,    0,    0,    0,    0,   10,   10,
   10,   10,   11,   12,   13,    0,    0,   11,   11,    0,
    0,    0,    0,   32,   33,   34,   35,   36,   37,   38,
   39,   40,   41,    0,    0,    0,    0,   44,   45,    0,
    0,    0,    0,    0,    0,    0,    0,    9,    9,    0,
    0,    0,    0,    7,    7,    0,    0,    0,    0,    0,
    0,    0,    8,    8,    0,    0,    0,    0,    0,    0,
    0,    0,    6,    0,    0,    0,    0,    0,    0,    0,
    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,
    0,    0,   15,   16,   17,    0,    0,    0,    0,    0,
   15,   16,   17,    0,    0,    0,    0,    0,    0,    0,
    0,    0,    0,    0,    0,    0,    0,    0,    0,    0,
   15,   16,   17,    0,    0,    0,    0,    0,    0,    0,
    0,   15,    0,   17,
};
}
static short yycheck[];
static { yycheck(); }
static void yycheck() {
yycheck = new short[] {                         91,
    0,   33,  259,   91,   42,   43,   46,   45,   40,   47,
    0,   38,   52,   45,   41,   42,   43,   38,   45,    0,
   47,   42,   43,   61,   45,    2,   47,   44,    0,   46,
   42,   43,   45,   45,   61,   47,   44,    0,   38,   -1,
   61,   41,   42,   43,   44,   45,   46,   47,   38,   -1,
   44,   41,   46,   43,   44,   45,   46,   38,   58,   91,
   41,   61,   43,   44,   45,   46,   38,    0,   58,   41,
   -1,   61,   44,    0,   46,   38,   93,   58,   41,   -1,
   61,   44,    0,   46,   -1,   93,   58,   -1,   -1,   61,
   44,    0,   46,   93,   -1,   58,   -1,  124,   61,   93,
   -1,   42,   43,   93,   45,   38,   47,   -1,   41,   -1,
   42,   44,   93,   46,   41,   47,   -1,   44,   -1,   46,
   38,   93,   -1,   41,  124,   58,   44,   -1,   46,   -1,
   93,   58,   41,   -1,  124,   44,   -1,   46,   -1,   93,
   58,   -1,   -1,  124,   -1,   -1,   -1,   -1,   -1,   58,
   38,   -1,  124,   -1,   42,   43,   -1,   45,   38,   47,
   93,  124,   42,   43,    0,   45,   93,   47,   -1,   -1,
   58,   -1,   -1,   61,   -1,   93,   -1,   -1,   38,   -1,
   -1,   61,   42,   43,   93,   45,   -1,   47,   -1,   38,
   -1,  124,   -1,   42,   43,   -1,   45,  124,   47,   -1,
   -1,   61,   -1,   -1,   -1,   41,  124,   -1,   44,   -1,
   46,   -1,   61,   93,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,   58,   -1,  262,   -1,  258,  259,   -1,   -1,
   -1,   -1,   -1,  260,  261,  262,  124,   -1,   -1,   -1,
   -1,  262,   -1,   -1,  124,   -1,   -1,   -1,   -1,   -1,
  262,   -1,   -1,   -1,   -1,   -1,   -1,   93,   -1,   -1,
  260,  261,  262,   -1,  124,   -1,   -1,   -1,   -1,   -1,
  260,  261,  262,   -1,   -1,  124,   -1,   -1,   -1,  260,
  261,  262,   -1,   -1,   -1,   -1,   -1,   -1,  260,  261,
  262,    3,    4,    5,    6,   -1,   -1,  260,  261,   -1,
   -1,   -1,   -1,   15,   16,   17,   18,   19,   20,   21,
   22,   23,   24,   -1,   -1,   -1,   -1,   29,   30,   -1,
   -1,   -1,   -1,   -1,   -1,   -1,   -1,  260,  261,   -1,
   -1,   -1,   -1,  260,  261,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,  260,  261,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,  261,   -1,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,  260,  261,  262,   -1,   -1,   -1,   -1,   -1,
  260,  261,  262,   -1,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,   -1,
  260,  261,  262,   -1,   -1,   -1,   -1,   -1,   -1,   -1,
   -1,  260,   -1,  262,
};
}
final static short YYFINAL=7;
final static short YYMAXTOKEN=263;
final static String yyname[] = {
"end-of-file",null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,"'!'",null,null,null,null,"'&'",null,"'('","')'","'*'","'+'",
"','","'-'","'.'","'/'",null,null,null,null,null,null,null,null,null,null,"':'",
null,null,"'='",null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,"'['",null,"']'",null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,"'|'",null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,
null,null,null,null,null,null,null,null,null,"NL","INT","ID","IMP","IFF","NEQ",
"NEG",
};
final static String yyrule[] = {
"$accept : term",
"term : INT",
"term : ID",
"term : ID abs_or_term_seq",
"term : abs_or_term_seq",
"term : term IFF term",
"term : term IMP term",
"term : term '|' term",
"term : term '&' term",
"term : '!' term",
"term : term NEQ term",
"term : term '=' term",
"term : term '+' term",
"term : term '-' term",
"term : term '/' term",
"term : term '*' term",
"term : '-' term",
"term : '(' term ')'",
"abs_or_term_seq : '[' term_seq app_rest",
"app_rest : ']'",
"app_rest : '.' term ']'",
"term_seq : term term_seq_rest",
"term_seq : term_seq ',' term term_seq_rest",
"term_seq_rest :",
"term_seq_rest : ':' type",
"type : ID",
"type : ID '[' type_seq ']'",
"type_seq : type",
"type_seq : type_seq ',' type",
};

//#line 173 "term.y"

  private Theory theory;
  private Lexer lexer;
  private Map<String, Var> vars;


  private int yylex () {
    int yyl_return = -1;
    try {
      yylval = new ParserVal(0);
      yyl_return = lexer.yylex();
    }
    catch (java.io.IOException e) {
      System.err.println("Error :"+e);
    }
    return yyl_return;
  }


  public void yyerror (String error) {
    System.err.println ("Error: " + error);
  }


  public Parser(Theory theory, String s) {
        vars = new HashMap<>();
        lexer = new Lexer(new java.io.StringReader(s), this);
        this.theory = theory;
  }

  public static Term termOfString(Theory t, String s){
        Parser p  = new Parser(t, s);
        p.yyparse();
        return (Term) p.yyval.obj;
  }
//#line 344 "Parser.java"
//###############################################################
// method: yylexdebug : check lexer state
//###############################################################
void yylexdebug(int state,int ch)
{
String s=null;
  if (ch < 0) ch=0;
  if (ch <= YYMAXTOKEN) //check index bounds
     s = yyname[ch];    //now get it
  if (s==null)
    s = "illegal-symbol";
  debug("state "+state+", reading "+ch+" ("+s+")");
}





//The following are now global, to aid in error reporting
int yyn;       //next next thing to do
int yym;       //
int yystate;   //current parsing state from state table
String yys;    //current token string


//###############################################################
// method: yyparse : parse input and execute indicated items
//###############################################################
int yyparse()
{
boolean doaction;
  init_stacks();
  yynerrs = 0;
  yyerrflag = 0;
  yychar = -1;          //impossible char forces a read
  yystate=0;            //initial state
  state_push(yystate);  //save it
  val_push(yylval);     //save empty value
  while (true) //until parsing is done, either correctly, or w/error
    {
    doaction=true;
    if (yydebug) debug("loop"); 
    //#### NEXT ACTION (from reduction table)
    for (yyn=yydefred[yystate];yyn==0;yyn=yydefred[yystate])
      {
      if (yydebug) debug("yyn:"+yyn+"  state:"+yystate+"  yychar:"+yychar);
      if (yychar < 0)      //we want a char?
        {
        yychar = yylex();  //get next token
        if (yydebug) debug(" next yychar:"+yychar);
        //#### ERROR CHECK ####
        if (yychar < 0)    //it it didn't work/error
          {
          yychar = 0;      //change it to default string (no -1!)
          if (yydebug)
            yylexdebug(yystate,yychar);
          }
        }//yychar<0
      yyn = yysindex[yystate];  //get amount to shift by (shift index)
      if ((yyn != 0) && (yyn += yychar) >= 0 &&
          yyn <= YYTABLESIZE && yycheck[yyn] == yychar)
        {
        if (yydebug)
          debug("state "+yystate+", shifting to state "+yytable[yyn]);
        //#### NEXT STATE ####
        yystate = yytable[yyn];//we are in a new state
        state_push(yystate);   //save it
        val_push(yylval);      //push our lval as the input for next rule
        yychar = -1;           //since we have 'eaten' a token, say we need another
        if (yyerrflag > 0)     //have we recovered an error?
           --yyerrflag;        //give ourselves credit
        doaction=false;        //but don't process yet
        break;   //quit the yyn=0 loop
        }

    yyn = yyrindex[yystate];  //reduce
    if ((yyn !=0 ) && (yyn += yychar) >= 0 &&
            yyn <= YYTABLESIZE && yycheck[yyn] == yychar)
      {   //we reduced!
      if (yydebug) debug("reduce");
      yyn = yytable[yyn];
      doaction=true; //get ready to execute
      break;         //drop down to actions
      }
    else //ERROR RECOVERY
      {
      if (yyerrflag==0)
        {
        yyerror("syntax error");
        yynerrs++;
        }
      if (yyerrflag < 3) //low error count?
        {
        yyerrflag = 3;
        while (true)   //do until break
          {
          if (stateptr<0)   //check for under & overflow here
            {
            yyerror("stack underflow. aborting...");  //note lower case 's'
            return 1;
            }
          yyn = yysindex[state_peek(0)];
          if ((yyn != 0) && (yyn += YYERRCODE) >= 0 &&
                    yyn <= YYTABLESIZE && yycheck[yyn] == YYERRCODE)
            {
            if (yydebug)
              debug("state "+state_peek(0)+", error recovery shifting to state "+yytable[yyn]+" ");
            yystate = yytable[yyn];
            state_push(yystate);
            val_push(yylval);
            doaction=false;
            break;
            }
          else
            {
            if (yydebug)
              debug("error recovery discarding state "+state_peek(0)+" ");
            if (stateptr<0)   //check for under & overflow here
              {
              yyerror("Stack underflow. aborting...");  //capital 'S'
              return 1;
              }
            state_pop();
            val_pop();
            }
          }
        }
      else            //discard this token
        {
        if (yychar == 0)
          return 1; //yyabort
        if (yydebug)
          {
          yys = null;
          if (yychar <= YYMAXTOKEN) yys = yyname[yychar];
          if (yys == null) yys = "illegal-symbol";
          debug("state "+yystate+", error recovery discards token "+yychar+" ("+yys+")");
          }
        yychar = -1;  //read another
        }
      }//end error recovery
    }//yyn=0 loop
    if (!doaction)   //any reason not to proceed?
      continue;      //skip action
    yym = yylen[yyn];          //get count of terminals on rhs
    if (yydebug)
      debug("state "+yystate+", reducing "+yym+" by rule "+yyn+" ("+yyrule[yyn]+")");
    if (yym>0)                 //if count of rhs not 'nil'
      yyval = val_peek(yym-1); //get current semantic value
    yyval = dup_yyval(yyval); //duplicate yyval if ParserVal is used as semantic value
    switch(yyn)
      {
//########## USER-SUPPLIED ACTIONS ##########
case 1:
//#line 56 "term.y"
{yyval.obj = Arith.numeral(Integer.parseInt((String) val_peek(0).obj));}
break;
case 2:
//#line 57 "term.y"
{
        Optional<Term> temp =theory.getTermByName((String) val_peek(0).obj);
        if (temp.isPresent())
            yyval.obj = temp.get();
        else yyval.obj = vars.getOrDefault((String) val_peek(0).obj, new Var((String) val_peek(0).obj, Type._c));
    }
break;
case 3:
//#line 63 "term.y"
{
        Term tt;
        Optional<Term> temp =theory.getTermByName((String) val_peek(1).obj);
        if (temp.isPresent())
            tt = temp.get();
        else tt = vars.getOrDefault((String) val_peek(1).obj, new Var((String) val_peek(1).obj, Type.BOOL));
        if (!tt.equals(FOL.forall) && !tt.equals(FOL.exists)){
            yyval.obj = App.mkApp(tt, (List<Term>) val_peek(0).obj);
        } else {
            Pair<List<Var>, Term> p = ((Term) val_peek(0).obj).brkAbs();
            if (tt.equals(FOL.forall))
                yyval.obj = FOL.mkForall(p.left, p.right);
            else
                yyval.obj = FOL.mkExists(p.left, p.right);
        }
    }
break;
case 4:
//#line 79 "term.y"
{yyval.obj = val_peek(0).obj;}
break;
case 5:
//#line 80 "term.y"
{yyval.obj = FOL.mkIff((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 6:
//#line 81 "term.y"
{yyval.obj = FOL.mkImp((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 7:
//#line 82 "term.y"
{yyval.obj = FOL.mkOr((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 8:
//#line 83 "term.y"
{yyval.obj = FOL.mkAnd((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 9:
//#line 84 "term.y"
{yyval.obj = FOL.mkNot((Term) val_peek(0).obj);}
break;
case 10:
//#line 85 "term.y"
{yyval.obj = FOL.mkNot(FOL.mkEq((Term) val_peek(2).obj, (Term) val_peek(0).obj));}
break;
case 11:
//#line 86 "term.y"
{yyval.obj = FOL.mkEq((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 12:
//#line 87 "term.y"
{yyval.obj = Arith.mkAdd((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 13:
//#line 88 "term.y"
{yyval.obj = Arith.mkSub((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 14:
//#line 89 "term.y"
{yyval.obj = Arith.mkDiv((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 15:
//#line 90 "term.y"
{yyval.obj = Arith.mkMul((Term) val_peek(2).obj, (Term) val_peek(0).obj);}
break;
case 16:
//#line 91 "term.y"
{yyval.obj = Arith.mkMul(Arith.numeral(-1), (Term) val_peek(0).obj);}
break;
case 17:
//#line 92 "term.y"
{yyval.obj = val_peek(1).obj;}
break;
case 18:
//#line 95 "term.y"
{
                   if (val_peek(0).obj == null){
                       yyval.obj = val_peek(1).obj;
                   } else {
                       List<Var> temp = new ArrayList<>();
                       for(Term t: (List<Term>) val_peek(1).obj)
                           temp.add((Var) t);
                       yyval.obj = Abs.mkAbs((List<Var>) temp, (Term) val_peek(0).obj);
                   }
               }
break;
case 19:
//#line 107 "term.y"
{yyval.obj = null;}
break;
case 20:
//#line 108 "term.y"
{yyval.obj = val_peek(1).obj;}
break;
case 21:
//#line 110 "term.y"
{
            List<Term> result = new ArrayList<>();
            if (val_peek(0).obj == null){
                result.add((Term) val_peek(1).obj);
                yyval.obj = result;
            } else {
                String name = ((Var) val_peek(1).obj).getName();
                Var v = new Var(name, (PTerm) val_peek(0).obj);
                vars.put(name, v);
                result.add(v);
                yyval.obj = result;
            }
        }
break;
case 22:
//#line 123 "term.y"
{
            List<Term> result = (List<Term>) val_peek(3).obj;
            if (val_peek(0).obj == null){
                result.add((Term) val_peek(1).obj);
                yyval.obj = result;
            }
            else{
                String name;
                Var v;
                List<Term> temp = new ArrayList<>();
                for(Term t: result){
                    if (!t.getType().equals(Type._c)){
                        temp.add(t);
                        continue;
                    }
                    name = ((Var) t).getName();
                    v = new Var(name, (PTerm) val_peek(0).obj);
                    vars.put(name, v);
                    temp.add(v);
                }
                name = ((Var) val_peek(1).obj).getName();
                v = new Var(name, (PTerm) val_peek(0).obj);
                vars.put(name, v);
                temp.add(v);
                yyval.obj = temp;
            }
        }
break;
case 23:
//#line 152 "term.y"
{yyval.obj = null;}
break;
case 24:
//#line 153 "term.y"
{yyval.obj = val_peek(0).obj;}
break;
case 25:
//#line 156 "term.y"
{String name = (String) val_peek(0).obj;
           if (name.charAt(0) == '_')
               yyval.obj = new PVar(name);
           else
               yyval.obj = new Com(name, Arrays.asList());}
break;
case 26:
//#line 161 "term.y"
{yyval.obj = new Com((String) val_peek(3).obj, (List<PTerm>) val_peek(1).obj);}
break;
case 27:
//#line 164 "term.y"
{List<PTerm> result = new ArrayList<>();
                result.add((PTerm) val_peek(0).obj);
                yyval.obj = result;}
break;
case 28:
//#line 167 "term.y"
{List<PTerm> result = (List<PTerm>) val_peek(2).obj;
                             result.add((PTerm) val_peek(0).obj);
                             yyval.obj = result;}
break;
//#line 680 "Parser.java"
//########## END OF USER-SUPPLIED ACTIONS ##########
    }//switch
    //#### Now let's reduce... ####
    if (yydebug) debug("reduce");
    state_drop(yym);             //we just reduced yylen states
    yystate = state_peek(0);     //get new state
    val_drop(yym);               //corresponding value drop
    yym = yylhs[yyn];            //select next TERMINAL(on lhs)
    if (yystate == 0 && yym == 0)//done? 'rest' state and at first TERMINAL
      {
      if (yydebug) debug("After reduction, shifting from state 0 to state "+YYFINAL+"");
      yystate = YYFINAL;         //explicitly say we're done
      state_push(YYFINAL);       //and save it
      val_push(yyval);           //also save the semantic value of parsing
      if (yychar < 0)            //we want another character?
        {
        yychar = yylex();        //get next character
        if (yychar<0) yychar=0;  //clean, if necessary
        if (yydebug)
          yylexdebug(yystate,yychar);
        }
      if (yychar == 0)          //Good exit (if lex returns 0 ;-)
         break;                 //quit the loop--all DONE
      }//if yystate
    else                        //else not done yet
      {                         //get next state and push, for next yydefred[]
      yyn = yygindex[yym];      //find out where to go
      if ((yyn != 0) && (yyn += yystate) >= 0 &&
            yyn <= YYTABLESIZE && yycheck[yyn] == yystate)
        yystate = yytable[yyn]; //get new state
      else
        yystate = yydgoto[yym]; //else go to new defred
      if (yydebug) debug("after reduction, shifting from state "+state_peek(0)+" to state "+yystate+"");
      state_push(yystate);     //going again, so push state & val...
      val_push(yyval);         //for next action
      }
    }//main loop
  return 0;//yyaccept!!
}
//## end of method parse() ######################################



//## run() --- for Thread #######################################
/**
 * A default run method, used for operating this parser
 * object in the background.  It is intended for extending Thread
 * or implementing Runnable.  Turn off with -Jnorun .
 */
public void run()
{
  yyparse();
}
//## end of method run() ########################################



//## Constructors ###############################################
/**
 * Default constructor.  Turn off with -Jnoconstruct .

 */
public Parser()
{
  //nothing to do
}


/**
 * Create a parser, setting the debug to true or false.
 * @param debugMe true for debugging, false for no debug.
 */
public Parser(boolean debugMe)
{
  yydebug=debugMe;
}
//###############################################################



}
//################### END OF CLASS ##############################
