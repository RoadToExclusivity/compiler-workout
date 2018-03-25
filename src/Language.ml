(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                    
	let calc binop x y = 
		let val_to_bool x = x <> 0
		and logic_calc logic_op x y = if logic_op x y then 1 else 0 in
		match binop with
		  "+" -> x + y
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
		| _ -> failwith "No such binary operator";;
	
	let rec eval st expr =
		match expr with
		  Const value -> value
		| Var x -> st x
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
    (* loop with a post-condition       *) | Repeat of Expr.t * t with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((s, i, o) : config) stmt =
		match stmt with
		| Read x -> 
			(match i with 
			| num :: tail -> ((Expr.update x num s), tail, o)
			| _ -> failwith "Error in input stream")
		| Write expr -> (s, i, o @ [(Expr.eval s expr)])
		| Assign (x, expr) -> ((Expr.update x (Expr.eval s expr) s), i, o)
		| Seq (stmt_left, stmt_right) -> 
			let c_left = eval (s, i, o) stmt_left in
			eval c_left stmt_right
		| Skip -> (s, i, o)
		| If (cond, t, f) ->
			let true_cond = (Expr.eval s cond) <> 0 in
			eval (s, i, o) (if true_cond then t else f)
		| While (cond, st) -> eval (s, i, o) (If (cond, Seq (st, While (cond, st)), Skip))
		| Repeat (cond, st) -> eval (s, i, o) (Seq (st, If (cond, Skip, Repeat (cond, st))));;
                               
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
		| %"repeat" st:!(parse) %"until" cond:!(Expr.parse) {Repeat (cond, st)}
		| %"for" init:!(stmt) "," cond:!(Expr.parse) "," step:!(stmt) %"do" st:!(parse) %"od" {Seq(init, While (cond, Seq(st, step)))};
	  if_cond:
		  %"if" cond:!(Expr.parse) %"then" st:!(parse) el:!(else_block)? %"fi" {If (cond, st, match el with Some s -> s | None -> Skip)};
	  else_block:
		  %"elif" cond:!(Expr.parse) %"then" st:!(parse) next:!(else_block)? {If (cond, st, match next with Some s -> s | None -> Skip)}
		| %"else" st:!(parse) {st}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
