open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval cfg prg =
  match prg with
  | [] -> cfg
  | instr::prg_t ->
    let (stack, config) = cfg in
    let (state, i, o) = config in
    match instr with
    | BINOP oper ->
      let (x::y::stack_t) = stack in
      let expr = Expr.Binop (oper, Expr.Const y, Expr.Const x) in
      let value = Expr.eval state expr in
      eval (value::stack_t, config) prg_t
    | CONST c -> eval (c::stack, config) prg_t
    | READ -> 
      let (f::i_t) = i in 
      eval (f::stack, (state, i_t, o)) prg_t
    | WRITE -> 
      let (s::stack_t) = stack in 
      eval (stack_t, (state, i, o @ [s])) prg_t
    | LD x -> eval (state x :: stack, config) prg_t
    | ST x -> 
      let (s::stack_t) = stack in
      eval (stack_t, ((Expr.update x s state), i, o)) prg_t

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

let rec comp_expr expr = 
  match expr with
  | Expr.Const c -> [CONST c]
  | Expr.Var x -> [LD x]
  | Expr.Binop (oper, l, r) -> comp_expr l @ comp_expr r @ [BINOP oper]

(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile st =
  match st with
  | Stmt.Assign (x, e) -> (comp_expr e) @ [ST x]
  | Stmt.Read x -> [READ] @ [ST x]
  | Stmt.Write e -> (comp_expr e) @ [WRITE]
  | Stmt.Seq (l, r) -> (compile l) @ (compile r)
