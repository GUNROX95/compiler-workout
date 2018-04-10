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

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
    
    let rec eval env ((st, i, o, r) as conf) expr =      
      match expr with
      | Const n -> (st, i, o, Some n)
      | Var   x -> 
        let v = State.eval st x in
        (st, i, o, Some v) 
      | Binop (op, x, y) -> 
        let (st', i', o', Some left) as conf' = eval env conf x in
        let (st', i', o', Some right) = eval env conf' y in
        let ret_val = to_func op left right in
        (st', i', o', Some ret_val)
      | Call (name, args) -> 
        let rec eval_Args env conf args =
          match args with
          | e::args' ->
            let (st', i', o', Some eval_arg) as conf' = eval env conf e in
            let eval_args, conf' = eval_Args env conf' args' in 
            eval_arg::eval_args, conf'
          |[] -> [], conf  
        in
        let eval_args', conf' = eval_Args env conf args in
        env#definition env name eval_args' conf'
         
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
        x:IDENT "(" args:!(Util.list0)[parse] ")" {Call (x, args)}
      | var:IDENT   {Var var}
      | n:DECIMAL {Const n}
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let rec eval env conf k stmt = 
      let rhombus stmt k = 
        if k = Skip then stmt
        else Seq (stmt, k)
      in
      match conf, stmt with
      | (st, i, o, r), Assign (x, e) ->
        let (st', i', o', Some v) = Expr.eval env conf e in
        eval env (State.update x v st', i', o', r) Skip k
      | (st, z::i, o, r), Read x ->
        eval env (State.update x z st, i, o, r) Skip k
      | (st, i, o, r), Write e ->
        let (st', i', o', Some v) = Expr.eval env conf e in
        eval env (st', i', o' @ [v], r) Skip k
      | conf, Seq (l, r) -> 
        eval env conf (rhombus r k) l
      | conf, Skip ->
        if k = Skip then conf
        else eval env conf Skip k
      | (st, i, o, r), If (e, _then, _else) ->
        let (st', i', o', Some v) as conf' = Expr.eval env conf e in
        let ans _val = if _val == 0 then _else else _then in
        eval env conf' k (ans v)
      | conf, While (e, _while) ->
        let (st', i', o', Some v) as conf' = Expr.eval env conf e in
        if v == 0 then eval env conf' Skip k
        else eval env conf'(rhombus stmt k) _while
      | conf, Repeat (e, _rep) ->
        eval env conf (rhombus (While (Expr.Binop ("==",e, Expr.Const 0), _rep)) k) _rep
      | (st, i, o, r), Call (name, args) ->
        let rec eval_Args env conf args =
          match args with
          | e::args' ->
            let (st', i', o', Some eval_arg) as conf' = Expr.eval env conf e in
            let eval_args, conf' = eval_Args env conf' args' in 
            eval_arg::eval_args, conf'
          |[] -> [], conf  
        in
        let eval_args', conf' = eval_Args env conf args in
        let c' = env#definition env name eval_args' conf' in
        eval env c' Skip k
      | (st, i, o, r), Return e -> 
        (match e with
         | None -> (st, i, o, None)
         | Some ex -> Expr.eval env conf ex
        )
      | _, _ -> failwith("Undefined language statement!!!")
         
    (* Statement parser *)
    ostap (
      parse:
        s:stmt -";" ss:parse {Seq (s, ss)}
      | stmt;
      stmt:
        %"read" "(" x:IDENT ")"          {Read x}
      | %"write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | %"if" e:!(Expr.parse) %"then" s:parse %"fi" {If (e, s, Skip)}
      | %"if" e:!(Expr.parse) %"then" s1:parse s2:else_or_elif %"fi" {If (e, s1, s2)}
      | %"while" e:!(Expr.parse) %"do" s:parse %"od" {While (e, s)}
      | %"for" cond:parse "," e:!(Expr.parse) "," s1:parse %"do" s2:parse %"od" {Seq (cond, While (e, Seq(s2, s1)))}
      | %"repeat" s:parse %"until" e:!(Expr.parse) {Repeat (e, s)}
      | %"skip" {Skip}
      | x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)}
      | %"return" e:!(Expr.parse)? {Return e};
      else_or_elif: 
        %"else" s:parse {s}
      | %"elif" e:!(Expr.parse) %"then" s1:parse s2:else_or_elif {If (e, s1, s2)}
      | "" {Skip}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
