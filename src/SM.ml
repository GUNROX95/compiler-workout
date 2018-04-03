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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  match insn with
  | BINOP op -> let y::x::stack' = stack in eval env (Expr.to_func op x y :: stack', c) prg'
  | READ     -> let z::i'        = i     in eval env (z::stack, (st, i', o)) prg'
  | WRITE    -> let z::stack'    = stack in eval env (stack', (st, i, o @ [z])) prg'
  | CONST i  -> eval env (i::stack, c) prg'
  | LD x     -> eval env (st x :: stack, c) prg'
  | ST x     -> let z::stack'    = stack in eval env (stack', (Expr.update x z st, i, o)) prg'
  | LABEL _ -> eval env (stack, c) prg'
  | JMP label -> eval env (stack, c) (env#labeled label)
  | CJMP (cond, label)  -> 
    let z::stack' = stack in 
    let x = match cond with
    | "nz" -> z <> 0
    | "z" -> z = 0 in
    eval env (stack', c) (if (x) then (env#labeled label) else prg')

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let env = object 
  val mutable id = 0
  method next_lbl = 
    id <- (id + 1);
    "L" ^ string_of_int id
end

let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
  | Stmt.Skip -> []
  | Stmt.If (e, s1, s2) ->
    let else_lbl = env#next_lbl in
    let end_lbl = env#next_lbl in
    let curr = compile s1 in
    let last = compile s2 in
    (expr e @ [CJMP ("z", else_lbl)] @ curr @ [JMP end_lbl] @ [LABEL else_lbl] @ last @ [LABEL end_lbl])
  | Stmt.While (e, s) ->
    let end_lbl = env#next_lbl in
    let loop_lbl = env#next_lbl in
    let body = compile s in
    ([JMP end_lbl] @ [LABEL loop_lbl] @ body @ [LABEL end_lbl] @ expr e @ [CJMP ("nz", loop_lbl)])
  | Stmt.Repeat (e, s) ->
    let loop_lbl = env#next_lbl in
    let body = compile s in
    ([LABEL loop_lbl] @ body @ expr e @ [CJMP ("z", loop_lbl)])

