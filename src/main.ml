
(** The main program, wrapped as a functor depending on an implementation of dyadics. *)

module Make = functor (D : Dyadic.DYADIC) ->
struct
  module TC = Typecheck.Make(D)
  module E = Eval.Make(D)
  module P = Parser.Make(D)
  module L = Lexer.Make(D)

  let usage = "Usage: marshall [option] ... [file] ..."
  let interactive_shell = ref true
  let prelude = ref true
  let wrapper = ref (Some ["rlwrap"; "ledit"])

let help_text = "Toplevel commands:
#help ;;           print this help
#precision d ;;    set output precision to dyadic constant d
#quit ;;           exit Marshall
#use \"<file>\" ;; evaluate <file>.
#trace <expr> ;;   trace the evaluation of an expression
#hnf <expr> ;;     compute the head-normal form of an expression" ;;

  (** We look for prelude.asd _first_ next to the executable and _then_ in the relevant
      install directory. This makes it easier to experiment with prelude.asd because eff
      will work straight from the build directory. We are probably creating a security hole,
      but we'll deal with that when eff actually gets used by more than a dozen people. *)
  let prelude_file =
    ref (if Sys.file_exists "prelude.asd"
         then Filename.concat (Filename.dirname Sys.argv.(0)) "prelude.asd"
         else Filename.concat Version.marshalldir "prelude.asd")

  (** A list of files to be loaded and run. *)
  let files = ref []

  let add_file interactive filename = (files := (filename, interactive) :: !files)

  (* Command-line options *)
  let options = Arg.align [
    ("--prelude",
     Arg.String (fun str -> prelude_file := str),
     " Specify the prelude.asd file");
    ("--no-prelude",
     Arg.Clear prelude,
     " Do not load prelude.asd");
    ("--wrapper",
     Arg.String (fun str -> wrapper := Some [str]),
     "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
    ("--no-wrapper",
     Arg.Unit (fun () -> wrapper := None),
     " Do not use a command-line wrapper");
    ("-v",
     Arg.Unit (fun () ->
       print_endline ("Marshall " ^ Version.version ^ "(" ^ Sys.os_type ^ ")") ;
       exit 0),
     " Print version information and exit");
    ("-n",
     Arg.Clear interactive_shell,
     " Do not run the interactive toplevel");
    ("-l",
     Arg.String (fun str -> add_file false str),
     "<file> Load <file> into the initial environment");
  ] ;;

  (* Treat anonymous arguments as files to be run. *)
  let anonymous str =
    add_file true str ;
    interactive_shell := false ;;

  (* Parser wrapper *)
  let parse parser lex =
    try
      parser L.token lex
    with
      | P.Error ->
          Error.syntax ~pos:(L.position_of_lex lex) ""
      | Failure f ->
          Error.syntax ~pos:(L.position_of_lex lex) "unrecognised symbol. (%s)" f

  let initial_ctxenv = ([], [], [])

  let color_bool x =
  	match x with
	  | None -> 128
    | Some true -> 0
    | Some false -> 255
    ;;


  (* e must have type bool *)
  let rec to_bool_option e =
    match e with
    | E.S.Tuple (E.S.True :: _) -> Some true
    | E.S.Tuple (_ :: E.S.True :: []) -> Some false
    | E.S.Join (e :: es) -> (match to_bool_option e with
       | Some b -> Some b
       | None -> to_bool_option (E.S.Join es))
    | _ -> None
  ;;

  let to_dyadic e =
    match e with
    | E.S.Interval i -> D.average (E.I.lower i) (E.I.upper i)
    | E.S.Dyadic d -> d
    | _ -> Message.runtime_error "Didn't return real number answer"
    ;;

  let one_half = D.average D.zero D.one;;

  let rec dyadic_to_int' max d =
    if max <= 0 then 0 else
    if D.leq d D.zero
      then 0
      else if D.leq D.one d
        then max - 1
        else let max' = max / 2 in
          if D.lt d one_half
            then dyadic_to_int' max' (D.double ~round:D.up d)
            else max' + dyadic_to_int' max' (D.double ~round:D.up (D.sub ~round:D.up d one_half))


  (* should only be called when `e` has type `bool` *)
  let eval_bool env e =
	let v, _ = E.eval_bounded 10 env e in
    color_bool (to_bool_option v);;

  let eval_real env e =
   dyadic_to_int' 256 (match E.eval false false env e with
    | E.S.Interval i -> let a = E.I.lower i in let b = E.I.upper i in
       if D.is_infinity a || D.is_infinity b
         then b
         else D.average a b
    | E.S.Dyadic d -> d
    | _ -> Message.runtime_error "Didn't return real number answer"
   );;
  (* let v = E.eval false false env e in
    dyadic_to_int' 256 (to_dyadic v);; *)

  let plot_shape filename pixels tenv ctx env e =
    let mypixels = D.of_int ~round:D.down pixels in
    let evaluate = match TC.type_of tenv ctx e with
      | E.S.Ty_Arrow (_, _, E.S.Ty_Real) -> eval_real
      | E.S.Ty_Arrow (_, _, _) -> eval_bool
      | _ -> Message.runtime_error "Must be function type with return type real or bool"
    in
    Grapher.plot filename (-pixels) (-pixels) (pixels - 1) (pixels - 1) (fun i j ->
      let x : D.t = D.div ~prec:10 ~round:D.down (D.of_int ~round:D.down i) mypixels in
      let y : D.t = D.div ~prec:10 ~round:D.down (D.of_int ~round:D.down j) mypixels in
      evaluate env (E.S.App (e, E.S.Tuple [E.S.Dyadic x; E.S.Dyadic y])));
    ;;

  (** [exec_cmd interactive (ctx,env) c] executes toplevel command [c] in global
      environment [env] and typing context [ctx]. It prints the result on
      standard output and return the new environment. *)
  let rec exec_cmd interactive (ctx,env,tenv) = function
    | E.S.Expr (e, trace) ->
	(try
	   let ty = TC.type_of tenv ctx e in
	   let v = E.eval true trace env (E.hnf env e) in
	     print_endline ("- : " ^ E.S.string_of_type ty ^ " |= " ^ E.S.string_of_expr v) ;
	     (ctx, env, tenv)
	 with error -> (Message.report error; (ctx, env, tenv)))
    | E.S.Definition (x, e, ot) ->
	(try
	   let type_of_e = TC.type_of tenv ctx e in
     let ty = match ot with
       | None -> type_of_e
       | Some ty' -> TC.check_same tenv ty' type_of_e; ty' in
	   let v = E.hnf env e in
	     print_endline
	       (E.S.string_of_name x ^ " : " ^ E.S.string_of_type ty (*^ " = " ^ E.S.string_of_expr v*)) ;
	     ((x,type_of_e)::ctx, E.Env.extend x v env, tenv)
	 with error -> (Message.report error; (ctx, env, tenv)))
    | E.S.Precision q ->
	E.target_precision := q ;
	print_endline ("Target precision set to " ^ D.to_string q) ;
	(ctx, env, tenv)
    | E.S.TypeDefinition (x, t) ->
        (ctx, env, (x, TC.resolve tenv t) :: tenv)
    | E.S.Hnf e ->
	let v = E.hnf ~free:true env e in
	  print_endline (E.S.string_of_expr v) ;
	  (ctx, env, tenv)
    | E.S.Help -> print_endline help_text ; (ctx, env, tenv)
    | E.S.Quit -> raise End_of_file
    | E.S.Plot (filename, pixels, e) -> (try plot_shape filename pixels tenv ctx env (E.hnf env e)
      with error -> Message.report error);
      (ctx, env, tenv)
    | E.S.Use fn -> use_file (ctx, env, tenv) (fn, interactive)

  (** [exec_cmds interactive (ctx,env) cmds] executes the list of commands [cmds] in
      context [ctx] and environment [env], and returns the new
      environment. *)
  and exec_cmds interactive ce cmds =
    List.fold_left (exec_cmd interactive) ce cmds

  and use_file env (filename, interactive) =
    let cmds = L.read_file (parse P.file) filename in
      let cwd = Unix.getcwd () in
      Unix.chdir (Filename.dirname filename);
      let env' = List.fold_left (exec_cmd interactive) env cmds in
      Unix.chdir cwd;
      env'


  (* Interactive toplevel *)
  let toplevel ctxenv =
    let eof = match Sys.os_type with
      | "Unix" | "Cygwin" -> "Ctrl-D"
      | "Win32" -> "Ctrl-Z"
      | _ -> "EOF"
    in
      print_endline ("Marshall " ^ Version.version);
      print_endline ("[Type " ^ eof ^ " to exit or #help;; for help.]");
      try
        let ctxenv = ref ctxenv in
          while true do
            try
              let cmd = L.read_toplevel (parse P.commandline) () in
                ctxenv := exec_cmd true !ctxenv cmd
            with
              | Error.Error err -> Print.error err
              | Sys.Break -> prerr_endline "Interrupted."
          done
      with End_of_file -> ()

  (** Main program *)
  let main =
    Sys.catch_break true ;
    (* Parse the arguments. *)
    Arg.parse options anonymous usage ;
    (* Attemp to wrap yourself with a line-editing wrapper. *)
    if !interactive_shell then
      begin match !wrapper with
        | None -> ()
        | Some lst ->
            let n = Array.length Sys.argv + 2 in
            let args = Array.make n "" in
              Array.blit Sys.argv 0 args 1 (n - 2) ;
              args.(n - 1) <- "--no-wrapper" ;
              List.iter
                (fun wrapper ->
                   try
                     args.(0) <- wrapper ;
                     Unix.execvp wrapper args
                   with Unix.Unix_error _ -> ())
                lst
      end ;
    (* Files were listed in the wrong order, so we reverse them *)
    files := List.rev !files;
    (* Load the pervasives. *)
    if !prelude then add_file false !prelude_file ;
    try
      (* Run and load all the specified files. *)
      let ctxenv = List.fold_left use_file initial_ctxenv !files in
        if !interactive_shell then toplevel ctxenv
    with
        Error.Error err -> Print.error err; exit 1
end
