%{
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

    import util.Pair;

    import java.util.ArrayList;
    import java.util.Arrays;
    import java.util.List;
    import java.util.Map;
    import java.util.HashMap;
    import java.util.Optional;
%}
      
%token NL
%token <obj> INT
%token <obj> ID
%token <obj> IMP
%token <obj> IFF
%token <obj> NEQ

%start term
%type <obj> term
%type <obj> type
%type <obj> type_seq
%type <obj> term_seq
%type <obj> abs_or_term_seq
%type <obj> app_rest
%type <obj> term_seq_rest

%nonassoc IFF
%right IMP
%left '|'
%left '&'
%left '!'
%left '='
%left NEQ
%left '-' '+'
%left '*' '/'
%left NEG

   
%%

term: INT {$$ = Arith.numeral(Integer.parseInt((String) $1));}
    | ID {
        Optional<Term> temp =theory.getTermByName((String) $1);
        if (temp.isPresent())
            $$ = temp.get();
        else $$ = vars.getOrDefault((String) $1, new Var((String) $1, Type._c));
    }
    | ID abs_or_term_seq {
        Term tt;
        Optional<Term> temp =theory.getTermByName((String) $1);
        if (temp.isPresent())
            tt = temp.get();
        else tt = vars.getOrDefault((String) $1, new Var((String) $1, Type.BOOL));
        if (!tt.equals(FOL.forall) && !tt.equals(FOL.exists)){
            $$ = App.mkApp(tt, (List<Term>) $2);
        } else {
            Pair<List<Var>, Term> p = ((Term) $2).brkAbs();
            if (tt.equals(FOL.forall))
                $$ = FOL.mkForall(p.left, p.right);
            else
                $$ = FOL.mkExists(p.left, p.right);
        }
    }
    | abs_or_term_seq {$$ = $1;}
    | term IFF term {$$ = FOL.mkIff((Term) $1, (Term) $3);}
    | term IMP term {$$ = FOL.mkImp((Term) $1, (Term) $3);}
    | term '|' term {$$ = FOL.mkOr((Term) $1, (Term) $3);}
    | term '&' term {$$ = FOL.mkAnd((Term) $1, (Term) $3);}
    |      '!' term {$$ = FOL.mkNot((Term) $2);}
    | term NEQ term {$$ = FOL.mkNot(FOL.mkEq((Term) $1, (Term) $3));}
    | term '=' term {$$ = FOL.mkEq((Term) $1, (Term) $3);}
    | term '+' term {$$ = Arith.mkAdd((Term) $1, (Term) $3);}
    | term '-' term {$$ = Arith.mkSub((Term) $1, (Term) $3);}
    | term '/' term {$$ = Arith.mkDiv((Term) $1, (Term) $3);}
    | term '*' term {$$ = Arith.mkMul((Term) $1, (Term) $3);}
    |      '-' term %prec NEG {$$ = Arith.mkMul(Arith.numeral(-1), (Term) $2);}
    | '(' term ')'  {$$ = $2;}
    ;

abs_or_term_seq: '[' term_seq app_rest {
                   if ($3 == null){
                       $$ = $2;
                   } else {
                       List<Var> temp = new ArrayList<>();
                       for(Term t: (List<Term>) $2)
                           temp.add((Var) t);
                       $$ = Abs.mkAbs((List<Var>) temp, (Term) $3);
                   }
               }
               ;

app_rest: ']' {$$ = null;}
        | '.' term ']' {$$ = $2;}

term_seq: term term_seq_rest {
            List<Term> result = new ArrayList<>();
            if ($2 == null){
                result.add((Term) $1);
                $$ = result;
            } else {
                String name = ((Var) $1).getName();
                Var v = new Var(name, (PTerm) $2);
                vars.put(name, v);
                result.add(v);
                $$ = result;
            }
        }
        | term_seq ',' term term_seq_rest {
            List<Term> result = (List<Term>) $1;
            if ($4 == null){
                result.add((Term) $3);
                $$ = result;
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
                    v = new Var(name, (PTerm) $4);
                    vars.put(name, v);
                    temp.add(v);
                }
                name = ((Var) $3).getName();
                v = new Var(name, (PTerm) $4);
                vars.put(name, v);
                temp.add(v);
                $$ = temp;
            }
        }
        ;

term_seq_rest: {$$ = null;}
             | ':' type {$$ = $2;}
             ;

type : ID {String name = (String) $1;
           if (name.charAt(0) == '_')
               $$ = new PVar(name);
           else
               $$ = new Com(name, Arrays.asList());}
     | ID '[' type_seq ']' {$$ = new Com((String) $1, (List<PTerm>) $3);}
     ;

type_seq: type {List<PTerm> result = new ArrayList<>();
                result.add((PTerm) $1);
                $$ = result;}
        | type_seq ',' type {List<PTerm> result = (List<PTerm>) $1;
                             result.add((PTerm) $3);
                             $$ = result;}
        ;

%%

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
