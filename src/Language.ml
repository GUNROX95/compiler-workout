(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    let fail x = failwith (Printf.sprintf "%s undefined" x)

    (* Empty state *)
    let empty = { g = fail; l = fail; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let update' f y = if x = y then v else f y in 
      if List.mem x s.scope then { s with l = update' s.l } else { s with g = update' s.g }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = fail; scope = xs }

    (* Drops a scope *)
    let leave st st' = { st with g = st'.g }

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
        !(Ostap.Util.expr 
          (fun x -> x)
	  (Array.map (fun (a, s) -> a, 
            List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
          ) 
          [|                
	    `Lefta, ["!!"];
	    `Lefta, ["&&"];
	    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
	    `Lefta, ["+" ; "-"];
	    `Lefta, ["*" ; "/"; "%"];
           |] 
	  )
         primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as conf) stmt =
      match stmt with
      | Read    x       -> (match i with z::i' -> (State.update x z st, i', o) | _ -> failwith "Unexpected end of input")
      | Write   e       -> (st, i, o @ [Expr.eval st e])
      | Assign (x, e)   -> (State.update x (Expr.eval st e) st, i, o)
      | Seq    (s1, s2) -> eval env (eval env conf s1) s2
      | Skip -> conf
      | If (e, s1, s2) -> if Expr.eval st e != 0 then eval env conf s1 else eval env conf s2
      | While  (e, s) -> if Expr.eval st e != 0 then eval env (eval env conf s) stmt else conf
      | Repeat (e, s) -> 
        let (st', i', o') as conf' = eval env conf s in
        if Expr.eval st' e == 0 then eval env conf' stmt else conf'
      | Call (f, e)  ->
        let args, locals, body = env#definition f in
        let rec zip = function
        | x::xs, y::ys -> (x, y) :: zip (xs, ys)
        | [], []       -> [] in
        let assign_arg st1 (x, e) = State.update x (Expr.eval st e) st1 in
        let withArgs = List.fold_left assign_arg (State.enter st @@ args @ locals) @@ zip (args, e) in
        let st', i, o = eval env (withArgs, i, o) body in
        State.leave st st', i, o
                               
    (* Statement parser *)
    ostap (
      parse:
        s:stmt -";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        "read" "(" x:IDENT ")"          {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | "if" e:!(Expr.parse) "then" s:parse "fi" {If (e, s, Skip)}
      | "if" e:!(Expr.parse) "then" s1:parse s2:else_or_elif "fi" {If (e, s1, s2)}
      | "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)}
      | "for" cond:parse "," e:!(Expr.parse) "," s1:parse "do" s2:parse "od" {Seq (cond, While (e, Seq(s2, s1)))}
      | "repeat" s:parse "until" e:!(Expr.parse) {Repeat (e, s)}
      | "skip" {Skip}
      | x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}; 
      else_or_elif: 
        "else" s:parse {s}
      | "elif" e:!(Expr.parse) "then" s1:parse s2:else_or_elif {If (e, s1, s2)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg_: IDENT;
      parse:
        "fun" fun_name:IDENT "(" args: !(Util.list0 arg_) ")"
        locals: (%"local" !(Util.list arg_))?
        "{" body: !(Stmt.parse) "}" { (fun_name, (args, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = 
  let module DefMap = Map.Make (String) in
  let defMap = List.fold_left (fun f ((name, _) as definitions) -> DefMap.add name definitions f) DefMap.empty defs in
  let env = (object method definition name = snd (DefMap.find name defMap) end) in
  let _, _, o = Stmt.eval env (State.empty, i, []) body in
  o
                                   
(* Top-level parser *)
let parse = 
  ostap (
    defs:!(Definition.parse) * body:!(Stmt.parse) {
      (defs, body) 
    }
  )
