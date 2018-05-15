open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env cfg prg =
    match prg with
    | [] -> cfg
    | instr::p_tail ->
      let (cstack, stack, config) = cfg in
      let (st, i, o) = config in
      match instr with
      | BINOP oper ->
        let (x::y::s_tail) = stack in
        eval env (cstack,  (Value.of_int (Expr.binop oper (Value.to_int y) (Value.to_int x))) :: s_tail, config) p_tail
      | CONST c -> eval env (cstack, (Value.of_int c)::stack, config) p_tail
      | STRING s -> eval env (cstack, (Value.of_string s)::stack, config) p_tail
      | LD x -> eval env (cstack, (State.eval st x)::stack, config) p_tail
      | ST x -> 
        let (s::s_tail) = stack in
        eval env (cstack, s_tail, ((State.update x s st), i, o)) p_tail
      | STA (x, n) -> let v::ind, stack' = split (n + 1) stack in eval env (cstack, stack', (Language.Stmt.update st x v ind, i, o)) p_tail
      | LABEL _ -> eval env cfg p_tail
      | SEXP (s, vals) -> let exprs, rest = split vals stack in eval env (cstack, (Value.sexp s (List.rev exprs)) :: rest, config) p_tail
      | JMP label -> eval env cfg (env#labeled label)
      | CJMP (cond, label)  -> 
        let (s::s_tail) = stack in
        let x = match cond with
        | "nz" -> Value.to_int s <> 0
        | "z" -> Value.to_int s = 0 
        in eval env (cstack, s_tail, config) (if (x) then (env#labeled label) else p_tail)
      | CALL (f, n, p) -> if env#is_label f then eval env ((p_tail, st)::cstack, stack, config) (env#labeled f) else eval env (env#builtin cfg f n p) p_tail
      | BEGIN (_, args, xs) ->
        let new_st = State.enter st (args @ xs) in
        let args', stack' = split (List.length args) stack in
        let st' = List.fold_left2 (fun ast p v -> State.update p v ast) new_st args (List.rev args')
        in eval env (cstack, stack', (st', i, o)) p_tail
      | DROP -> eval env (cstack, List.tl stack, config) p_tail
      | DUP -> eval env (cstack, List.hd stack :: stack, config) p_tail
      | SWAP -> let x::y::s_tail = stack in eval env (cstack, y::x::s_tail, config) p_tail
      | TAG s -> let x::s_tail = stack in 
        let res = if s = Value.tag_of x then 1 else 0
        in eval env (cstack, (Value.of_int res)::s_tail, config) p_tail
      | ENTER xs ->
        let vals, stack' = split (List.length xs) stack in
        let st' = List.fold_left2 (fun s x v -> State.bind v x s) State.undefined vals xs in
          eval env (cstack, stack', (State.push st st' xs, i, o)) p_tail
      | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) p_tail
      | END | RET _ ->
        match cstack with
        | (prog, s)::cstack' ->
          eval env (cstack', stack, (State.leave st s, i, o)) prog
        | [] -> cfg  


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
    and pattern p lfalse =
    (let rec comp patt =
      (match patt with
        Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [DROP]
      | Stmt.Pattern.Sexp (tag, ps) -> 
        let res, _ = (List.fold_left (fun (acc, pos) patt -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp patt)), pos + 1) ([], 0) ps) in
        [DUP; TAG tag; CJMP ("z", lfalse)] @ res) in 
        comp p)
  and bindings p =
    let rec bind cp = 
      (match cp with
        Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [SWAP]
      | Stmt.Pattern.Sexp (_, xs) -> 
        let res, _ = List.fold_left (fun (acc, pos) curp -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)) ([], 0) xs in res @ [DROP]) in
    bind p @ [ENTER (Stmt.Pattern.vars p)]
  and expr e =
    match e with
    | Expr.Const c -> [CONST c]
    | Expr.Var x -> [LD x]
    | Expr.String s -> [STRING s]
    | Expr.Sexp (s, exprs) -> let args = List.fold_left (fun acc index -> acc @ (expr index)) [] exprs in args @ [SEXP (s, List.length exprs)]
    | Expr.Array arr -> List.flatten (List.map expr arr) @ [CALL (".array", List.length arr, false)]
    | Expr.Elem (arr, i) -> expr arr @ expr i @ [CALL (".elem", 2, false)]
    | Expr.Length t -> expr t @ [CALL (".length", 1, false)]
    | Expr.Binop (op, left_expr, right_expr) -> expr left_expr @ expr right_expr @ [BINOP op]
    | Expr.Call (proc, args) -> call (label proc) args false in
  let rec compile_stmt l env stmt =
    match stmt with
    | Stmt.Assign (x, [], e) -> env, false, expr e @ [ST x]
    | Stmt.Assign (x, is, e) -> let indexes = List.fold_left (fun acc index -> acc @ (expr index)) [] is in 
      env, false, (List.rev indexes @ expr e @ [STA (x, List.length is)])
    | Stmt.Seq (left_st, right_st) ->
      let env, _, left = compile_stmt l env left_st in
      let env, _, right = compile_stmt l env right_st in
      env, false, left @ right
    | Stmt.Skip -> env, false, []
    | Stmt.If (e, s1, s2) ->
      let else_label, env = env#get_label in
      let end_label, env = env#get_label in
      let env, _, current_case = compile_stmt l env s1 in
      let env, _, last_case = compile_stmt l env s2 in
      env, false, (expr e) @ [CJMP ("z", else_label)] @ current_case @ [JMP end_label] @ [LABEL else_label] @ last_case @ [LABEL end_label]
    | Stmt.While (e, s) ->
      let end_label, env = env#get_label in
      let loop_label, env = env#get_label in
      let env, _, body = compile_stmt l env s in
      env, false, [JMP end_label] @ [LABEL loop_label] @ body @ [LABEL end_label] @ expr e @ [CJMP ("nz", loop_label)]
    | Stmt.Repeat (e, s) ->
      let loop_label, env = env#get_label in
      let env, _, body = compile_stmt l env s in
      env, false, [LABEL loop_label] @ body @ expr e @ [CJMP ("z", loop_label)]
    | Stmt.Return e -> (
      match e with
      | None -> env, false, [RET false]
      | Some e -> env, false, expr e @ [RET true]
    )
    | Stmt.Call (name, args) -> 
      env, false, List.concat (List.map expr args) @ [CALL ("L" ^ name, List.length args, true)]
    | Stmt.Case (e, patterns) ->
      let rec comp_pat ps env lbl isFirst lend = 
      (match ps with
        [] -> env, []
        | (p, act)::tl -> 
          let env, _, body = compile_stmt l env act in 
          let lfalse, env = env#get_label
          and start = if isFirst then [] else [LABEL lbl] in
          let env, code = comp_pat tl env lfalse false lend in
          env, start @ (pattern p lfalse) @ bindings p @ body @ [LEAVE; JMP lend] @ code) in
      let lend, env = env#get_label in
      let env, code = comp_pat patterns env "" true lend in
      env, false, (expr e) @ code @ [LABEL lend]
    | Stmt.Leave -> env, false, [LEAVE] in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

