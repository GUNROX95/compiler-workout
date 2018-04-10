open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  

let rec eval env conf pr = 
  match pr with
  | insn::pr' -> (
    match conf, insn with
    | (cstack, y::x::stack, conf'), BINOP op -> 
      let v = Expr.to_func op x y in
      eval env (cstack, v::stack, conf') pr'
    | (cstack, stack, conf'), CONST n ->
      eval env (cstack, n::stack, conf') pr'
    | (cstack, stack, (st, z::i, o)), READ ->
      eval env (cstack, z::stack, (st, i, o)) pr'
    | (cstack, z::stack, (st, i, o)), WRITE ->
      eval env (cstack, stack, (st, i, o @ [z])) pr'
    | (cstack, stack, (st, i, o)), LD x ->
      let v = State.eval st x in
      eval env (cstack, v::stack, (st, i, o)) pr'
    | (cstack, z::stack, (st, i, o)), ST x ->
      let st' =	State.update x z st in
      eval env (cstack, stack, (st', i, o)) pr'
    | conf, LABEL label -> 
      eval env conf pr'
    | conf, JMP label ->
      eval env conf (env#labeled label)
    | (cstack, z::stack, conf'), CJMP (suffix, label) -> (
      match suffix with
      | "z" -> 
        if z == 0 then eval env (cstack, stack, conf') (env#labeled label)
        else eval env (cstack, stack, conf') pr'
      | "nz" -> 
        if z <> 0 then eval env (cstack, stack, conf') (env#labeled label)
        else eval env (cstack, stack, conf') pr'
      | _ -> failwith("Undefined suffix!!!")
    )
    | (cstack, stack, (st, i, o)), CALL name ->
      eval env ((pr', st)::cstack, stack,(st, i, o)) (env#labeled name)
    | (cstack, stack, (st, i, o)), BEGIN (args, locals) ->
      let rec assoc st args stack = 
        match args, stack with
        | arg::args', z::stack' -> 
          let st', _stack = assoc st args' stack' in
          (State.update arg z st', _stack)
        | [], stack' -> (st, stack') in
      let st', stack' = assoc (State.enter st (args @ locals)) args stack in
      eval env (cstack, stack',(st',i, o)) pr'
    | (cstack, stack, (st, i, o)), END -> (
      match cstack with
      | (_pr, st')::cstack' -> 
        eval env (cstack', stack, (State.leave st st', i, o)) _pr
      | [] -> conf
    )
  )
  | [] -> conf

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let env = object
  val count_label = 0
  method generate = "LABEL_" ^ string_of_int count_label, {< count_label = count_label + 1 >}
end

let rec expr e = 
  match e with
  | Expr.Const n -> [CONST n]
  | Expr.Var x -> [LD x]
  | Expr.Binop (op, l, r) ->
    expr l @ expr r @ [BINOP op]
  | Expr.Call (name, args) ->
    List.concat (List.map expr (List.rev args)) @ [CALL name]

let rec compile' stmt env = 
  match stmt with
  | Stmt.Assign (x, e) -> expr e @ [ST x], env
  | Stmt.Read x -> [READ; ST x], env
  | Stmt.Write e -> expr e @ [WRITE], env
  | Stmt.Seq (l, r) -> 
    let left, env = compile' l env in
    let right, env = compile' r env in
    left @ right, env
  | Stmt.Skip -> [], env
  | Stmt.If (e, _then, _else) ->
    let label_else, env = env#generate in 
    let label_fi, env = env#generate in
    let _then', env = compile' _then env in
    let _else', env = compile' _else env in
    expr e @ [CJMP ("z", label_else)] @ _then' @ [JMP label_fi; LABEL label_else] @ _else' @ [LABEL label_fi], env
  | Stmt.While (e, _while) ->
    let label_check, env = env#generate in
    let label_loop, env = env#generate in
    let body, env = compile' _while env in
    [JMP label_check; LABEL label_loop] @ body @ [LABEL label_check] @ expr e @ [CJMP ("nz", label_loop)], env
  | Stmt.Repeat (e, _rep) ->
    let label_loop, env = env#generate in
    let body, env = compile' _rep env in
    [LABEL label_loop] @ body @ expr e @ [CJMP ("z", label_loop)], env
  | Stmt.Call (name, args) ->
    List.concat (List.map expr (List.rev args)) @ [CALL name], env
  | Stmt.Return e ->
    match e with
    | None -> [END], env
    | Some ex -> expr ex @ [END], env

let compile (defs, stmt) = 
  let prog, env = compile' stmt env in
  let rec compile_defs env defs =
    match defs with
    | (name, (args, locals, body))::defs' ->
      let body_defs, env = compile_defs env defs' in
      let compile_body, env = compile' body env in 
      [LABEL name; BEGIN (args, locals)] @ compile_body @ [END] @ body_defs, env
    | [] -> [], env  in
  let cdefs, _  = compile_defs env defs in 
  prog @ [END] @ cdefs
