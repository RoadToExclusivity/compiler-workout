(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
	*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

	let is_local s = fun x -> List.exists (fun z -> (x = z)) s.scope

	(* Empty state *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
		let upd' s' = fun y -> if x = y then v else s' y in
		if is_local s x then { g = s.g; l = upd' s.l; scope = s.scope} else { g = upd' s.g; l = s.l; scope = s.scope }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if is_local s x then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = { g = st.g; l = empty; scope = xs }

    (* Drops a scope *)
    let leave st st' = { g = st.g; l = st'.l ; scope = st'.scope }

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
    
	let rec eval st expr =
		let calc binop x y = 
		   (let val_to_bool x = x <> 0
			and logic_calc logic_op x y = if logic_op x y then 1 else 0 in
			match binop with
			| "+" -> x + y
			| "-" -> x - y
			| "*" -> x * y
			| "/" -> x / y
			| "%" -> x mod y
			| "<" -> logic_calc (<) x y
			| ">" -> logic_calc (>) x y
			| "<=" -> logic_calc (<=) x y
			| ">=" -> logic_calc (>=) x y
			| "==" -> logic_calc (=) x y
			| "!=" -> logic_calc (<>) x y
			| "&&" -> logic_calc (&&) (val_to_bool x) (val_to_bool y)
			| "!!" -> logic_calc (||) (val_to_bool x) (val_to_bool y)
			| _ -> failwith "No such binary operator") in
		match expr with
		| Const value -> value
		| Var x -> State.eval st x
		| Binop (binop, x, y) -> calc binop (eval st x) (eval st y);;   

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse: expr;
	  expr: 
		!(Ostap.Util.expr
			(fun x -> x)
			(Array.map (fun (pr, ops) -> pr, List.map (fun op -> ostap(- $(op)), (fun x y -> Binop (op, x, y))) ops)
			[|
				`Lefta, ["!!"]; 
				`Lefta, ["&&"]; 
				`Nona, ["<="; ">="; "<"; ">"; "=="; "!="];
				`Lefta, ["+"; "-"]; 
				`Lefta, ["*"; "/"; "%"]; 
			|])
			atom
		);
		
	  atom: num:DECIMAL {Const num} | x:IDENT {Var x} | -"(" expr -")"
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
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
		| Read x -> 
			(match i with 
			| num :: tail -> ((State.update x num st), tail, o)
			| _ -> failwith "Error in input stream")
		| Write expr -> (st, i, o @ [(Expr.eval st expr)])
		| Assign (x, expr) -> ((State.update x (Expr.eval st expr) st), i, o)
		| Seq (stmt_left, stmt_right) -> 
			let c_left = eval env conf stmt_left in
			eval env c_left stmt_right
		| Skip -> conf
		| If (cond, t, f) ->
			let true_cond = (Expr.eval st cond) <> 0 in
			eval env conf (if true_cond then t else f)
		| While (cond, stmt) -> eval env conf (If (cond, Seq (stmt, While (cond, stmt)), Skip))
		| Repeat (stmt, cond) -> eval env conf (Seq (stmt, If (cond, Skip, Repeat (stmt, cond))))
		| Call (proc, vals) -> 
			let (params, local, stmt') = env#definition proc in
			let new_scope = State.enter st local in
			let st' = List.fold_left2 (fun acc p v -> State.update p (Expr.eval st v) acc) new_scope params vals in
			let (proc_st, i', o') = eval env (st', i, o) stmt' in
			let old_scope = State.leave proc_st st in (old_scope, i', o');;
                                
    (* Statement parser *)
    ostap (
      parse: full_stmt;
	  full_stmt: <s::xs> :!(Ostap.Util.listBy)[ostap (";")][stmt] {List.fold_left (fun acc y -> Seq (acc, y)) s xs};
	  stmt: 
		  %"read" "(" x:IDENT ")" {Read x}
		| %"write" "(" e:!(Expr.parse) ")" {Write e}
		| x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}
		| %"skip" {Skip}
		| cond:!(if_cond) {cond}
		| %"while" cond:!(Expr.parse) %"do" st:!(parse) %"od" {While (cond, st)}
		| %"repeat" st:!(parse) %"until" cond:!(Expr.parse) {Repeat (st, cond)}
		| %"for" init:!(stmt) "," cond:!(Expr.parse) "," step:!(stmt) %"do" st:!(parse) %"od" {Seq(init, While (cond, Seq(st, step)))}
		| x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][Expr.parse]? ")" {Call (x, match params with Some s -> s | None -> [])};
	  if_cond:
		  %"if" cond:!(Expr.parse) %"then" st:!(parse) el:!(else_block)? %"fi" {If (cond, st, match el with Some s -> s | None -> Skip)};
	  else_block:
		  %"elif" cond:!(Expr.parse) %"then" st:!(parse) next:!(else_block)? {If (cond, st, match next with Some s -> s | None -> Skip)}
		| %"else" st:!(parse) {st}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: def;
	  def: %"fun" nm:IDENT "(" args:!(Ostap.Util.listBy)[ostap (",")][ostap (IDENT)]? ")" lc:!(locals)? "{" stmt:!(Stmt.parse) "}" 
							{ nm, ((match args with Some s -> s | None -> []), (match lc with Some s -> s | None -> []), stmt) };
	  locals: %"local" vars:!(Ostap.Util.listBy)[ostap (",")][ostap (IDENT)] {vars}
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
	let rec find_proc p = function
	| [] -> failwith "Unknown procedure"
	| (h, ret) :: xs when h = p -> ret
	| _ :: xs -> find_proc p xs in
	let _, _, o = Stmt.eval (object method definition proc = find_proc proc defs end) ({ g = State.empty; l = State.empty; scope = [] }, i, []) body in o
                                   
(* Top-level parser *)
let parse =	ostap ( defs:!(Definition.parse)* body:!(Stmt.parse) { defs, body } )
