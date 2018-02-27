open GT       
       
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
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
(*let eval _ = failwith "Not yet implemented"*)
let rec eval conf prog =
  match prog with
  | [] -> conf
  | instr :: tail ->
    let (stack, config) = conf in
    let (st, i, o) = config in
    match instr with
    | CONST c -> 
			eval (c :: stack, config) tail
    | READ -> 
			let (inp :: t) = i in 
			eval (inp :: stack, config) tail
    | WRITE ->
      let (s :: t) = stack in 
			eval (t, (st, i, o @ [s])) tail
    | ST v -> 
			let (s :: t) = stack in
      let st_up = Syntax.Expr.update v s st in
      eval (t, (st_up, i, o)) tail
    | LD var -> 
			let v = st var in
      eval (v :: stack, config) tail
    | BINOP oper -> 
			let (ls :: rs :: t) = stack in
      let v = Syntax.Expr.binop oper rs ls in
      eval (v :: t, config) tail


let rec comp_ex ex =
  match ex with
  | Syntax.Expr.Const c -> [CONST c]
  | Syntax.Expr.Var v -> [LD v]
  | Syntax.Expr.Binop (oper, left, right) -> (comp_ex left) @ (comp_ex right) @ [BINOP oper]

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

(*let compile _ = failwith "Not yet implemented"*)
let rec compile st =
  match st with
  | Syntax.Stmt.Assign (v, expr) -> (comp_ex expr) @ [ST v]
  | Syntax.Stmt.Read v -> [READ; ST v]
  | Syntax.Stmt.Write expr -> (comp_ex expr) @ [WRITE]
  | Syntax.Stmt.Seq (l, r) -> (compile l) @ (compile r)
