%{
    module S = Syntax.Make(D)
    module I = Interval.Make(D)

    let equal r e1 e2 =
      let x = S.fresh_name "gen" in
      let y = S.fresh_name "gen" in
      let d = S.Binary (S.Minus, e1, e2) in
	S.Let (y, r,
	    S.Let (x, d,
		  S.And [S.Less (S.Unary (S.Opposite, S.Var y), S.Var x); S.Less (S.Var x, S.Var y)]))

    let apart e1 e2 =
      let x = S.fresh_name "gen" in
      let y = S.fresh_name "gen" in
	S.Let (x, e1,
	    S.Let (y, e2,
		  S.Or [S.Less (S.Var x, S.Var y); S.Less (S.Var y, S.Var x)]))
%}

%parameter <D : Dyadic.DYADIC>

%token TSIGMA TREAL
%token TARROW
%token <Syntax.Make(D).name> VAR
%token <D.t> DYADIC
%token <int> NATURAL
%token <int> PROJECT
%token INFINITY
%token TRUE FALSE
%token AND OR
%token ANDB ORB LTB NEGB
%token JOIN RESTRICT
%token FORALL EXISTS INTEGRAL
%token LET IN
%token CUT LEFT RIGHT
%token TBOOL MKBOOL
%token ISTRUE ISFALSE
%token FUN DARROW
%token PLUS MINUS TIMES QUOTIENT INVERSE POWER
%token EQUAL LESS GREATER UNEQUAL
%token COLON COMMA SEMISEMI
%token LPAREN RPAREN
%token LBRACK RBRACK LBRACE RBRACE
%token USE QUIT TRACE PRECISION HNF HELP PLOT
%token <string> STRING
%token EOF

%start <Syntax.Make(D).toplevel_cmd list> file
%start <Syntax.Make(D).toplevel_cmd> commandline

%right TARROW
%nonassoc EQUAL LESS GREATER UNEQUAL LTB
%left PLUS MINUS
%left TIMES QUOTIENT
%left ANDB ORB

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require ;; at the
   end of the file. *)
file:
  | lst = file_topdef
    { lst }
  | t = expr EOF
     { [(S.Expr (t, false))] }
  | t = expr SEMISEMI lst = file
     { (S.Expr (t, false)) :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = file
     { dir :: lst }

file_topdef:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = file
     { def :: lst }
  | def = topdef lst = file_topdef
     { def :: lst }

commandline:
  | t = expr SEMISEMI
    { S.Expr (t, false) }
  | def = topdef SEMISEMI
    { def }
  | dir = topdirective SEMISEMI
    { dir }

(* Things that can be defined at toplevel. *)
topdef:
  | LET x = VAR EQUAL e = expr       { S.Definition (x, e, None) }
  | LET x = VAR t = ty_sig EQUAL e = expr { S.Definition(x, e, Some t) }
  | LET x = VAR args = arglist EQUAL e = expr
    { S.Definition (x, List.fold_right (fun (x, t) e' -> S.Lambda (x, t, e')) args e, None)}
  | LET x = VAR args = arglist t = ty_sig EQUAL e = expr
    { S.Definition (x, List.fold_right (fun (x, t) e' -> S.Lambda (x, t, e')) args e,
      Some (List.fold_right (fun (x, targ) t' -> S.Ty_Arrow (targ, t')) args t)) }

ty_sig:
  | COLON t = ty
    { t }

arglist:
  | LPAREN x = VAR COLON t = ty RPAREN args = arglist
    { (x, t) :: args }
  |
    { [] }

(* Toplevel directives. *)
topdirective:
  | USE s = STRING
    { S.Use s }
  | TRACE e = expr
    { S.Expr (e, true) }
  | PRECISION n = numconst
    { S.Precision n }
  | HNF e = expr
    { S.Hnf e }
  | HELP
    { S.Help }
  | PLOT n = NATURAL e = expr
    { S.Plot (n, e) }
  | QUIT
    { S.Quit }

(* Main syntax tree. *)
expr:
  | e = join_expr
    { e }
  | CUT x = VAR COLON s = segment LEFT e1 = expr RIGHT e2 = expr
    { S.Cut (x, s, e1, e2) }
  | CUT x = VAR LEFT e1 = expr RIGHT e2 = expr
    { S.Cut (x, I.bottom, e1, e2) }
  | EXISTS x = VAR COLON s = segment COMMA e = expr
    { S.Exists (x, s, e) }
  | FORALL x = VAR COLON s = segment COMMA e = expr
    { S.Forall (x, s, e) }
  | INTEGRAL x = VAR COLON s = segment COMMA e = expr
    { S.Integral (x, s, e) }
  | LET x = VAR EQUAL e1 = expr IN e2 = expr
    { S.Let (x, e1, e2) }
  | FUN x = VAR COLON t = ty DARROW e = expr
    { S.Lambda (x, t, e) }

simple_expr:
  | x = VAR
    { S.Var x }
  | n = NATURAL
    { S.Dyadic (D.of_int ~round:D.down n) }
  | q = DYADIC
    { S.Dyadic q }
  | TRUE
    { S.True }
  | FALSE
    { S.False }
  | MKBOOL e1 = simple_expr; e2 = simple_expr
    { S.MkBool (e1, e2) }
  | ISTRUE e = simple_expr
    { S.IsTrue e }
  | ISFALSE e = simple_expr
    { S.IsFalse e }
  | e = simple_expr p = PROJECT
    { S.Proj (e, p) }
  | LPAREN e = expr RPAREN
    { e }
  | LPAREN es = expr_list RPAREN
    { S.Tuple es }

apply_expr:
  | e1 = apply_expr e2 = simple_expr
    { S.App (e1, e2) }
  | e = simple_expr
    { e }

pow_expr:
  | e = apply_expr
    { e }
  | e = pow_expr POWER n = NATURAL
    { S.Power (e, n) }

unary_expr:
  | e = pow_expr
    { e }
  | MINUS e = pow_expr
    { S.Unary (S.Opposite, e) }
  | INVERSE e = pow_expr
    { S.Unary (S.Inverse, e) }
  | NEGB e = pow_expr
    { S.App (S.Var (S.Ident "negb"), e) }

bin_expr:
  | e = unary_expr
    { e }
  | e1 = bin_expr PLUS e2 = bin_expr
    { S.Binary (S.Plus, e1, e2) }
  | e1 = bin_expr MINUS e2 = bin_expr
    { S.Binary (S.Minus, e1, e2) }
  | e1 = bin_expr TIMES e2 = bin_expr
    { S.Binary (S.Times, e1, e2) }
  | e1 = bin_expr QUOTIENT e2 = bin_expr
    { S.Binary (S.Quotient, e1, e2) }

bbin_expr:
  | e = bin_expr
    { e }
  | e1 = bbin_expr EQUAL LBRACE r = expr RBRACE EQUAL e2 = bbin_expr
    { equal r e1 e2 }
  | e1 = bbin_expr UNEQUAL e2 = bbin_expr
    { apart e1 e2 }
  | e1 = bbin_expr LESS e2 = bbin_expr
    { S.Less (e1, e2) }
  | e1 = bbin_expr LTB e2 = bbin_expr
    { S.App (S.App (S.Var (S.Ident "lt"), e1), e2) }
  | e1 = bbin_expr GREATER e2 = bbin_expr
    { S.Less (e2, e1) }

andb_expr:
  | e = bbin_expr
    { e }
  | e1 = andb_expr ANDB e2 = andb_expr
    { S.App (S.App (S.Var (S.Ident "andb"), e1), e2) }

orb_expr:
  | e = andb_expr
    { e }
  | e1 = orb_expr ORB e2 = orb_expr
    { S.App (S.App (S.Var (S.Ident "orb"), e1), e2) }

and_expr:
  | e = orb_expr
    { e }
  | e1 = orb_expr AND e2 = and_expr_list
    { S.And (e1 :: e2) }

and_expr_list:
  | e = orb_expr
    { [e] }
  | e = orb_expr AND es = and_expr_list
    { e :: es }

or_expr:
  | e = and_expr
    { e }
  | e = and_expr OR es = or_expr_list
    { S.Or (e :: es) }

or_expr_list:
  | e = and_expr
    { [e] }
  | e = and_expr OR es = or_expr_list
    { e :: es }

restrict_expr:
  | e = or_expr
    { e }
  | e1 = or_expr RESTRICT e2 = or_expr
    { S.Restrict (e1, e2) }

join_expr:
  | e = restrict_expr
    { e }
  | e = restrict_expr JOIN es = join_expr_list
    { S.Join (e :: es) }

join_expr_list:
  | e = restrict_expr
    { [e] }
  | e = restrict_expr JOIN es = join_expr_list
    { e :: es }

expr_list:
  | e1 = expr COMMA e2 = expr
    { [e1; e2] }
  | e = expr COMMA es = expr_list
    { e :: es }

ty_simple:
  | TSIGMA
    { S.Ty_Sigma }
  | TREAL
    { S.Ty_Real }
  | TBOOL
    { S.Ty_Bool }
  | LPAREN t = ty RPAREN
    { t }

ty_prod:
  | t = ty_simple
    { t }
  | t = ty_simple TIMES ts = ty_prod_list
    { S.Ty_Tuple (t :: ts) }

ty_prod_list:
  | t = ty_simple
    { [t] }
  | t = ty_simple TIMES ts = ty_prod_list
    { t :: ts }

ty:
  | t1 = ty TARROW t2 = ty
    { S.Ty_Arrow (t1, t2) }
  | t = ty_prod
    { t }

segment:
  | TREAL
    { I.bottom }
  | q1 = left_endpoint COMMA q2 = right_endpoint
    { I.make q1 q2 }

left_endpoint:
  | LPAREN MINUS INFINITY
    { D.negative_infinity }
  | LBRACK q = numconst
    { q }

right_endpoint:
  | INFINITY RPAREN
    { D.positive_infinity }
  | PLUS INFINITY RPAREN
    { D.positive_infinity }
  | q = numconst RBRACK
    { q }

numconst:
  | n = NATURAL
    { D.of_int ~round:D.down n }
  | q = DYADIC
    { q }
