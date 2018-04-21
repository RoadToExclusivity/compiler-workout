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

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)
	let calc binop x y = 
		let val_to_bool x = x <> 0
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
			| _ -> failwith "No such binary operator";;
			
    let rec eval env ((st, i, o, r) as conf) expr =
		match expr with
			| Const value -> (st, i, o, Some value)
			| Var x -> (st, i, o, Some (State.eval st x))
			| Binop (binop, x, y) -> 
				let (st', i', o', Some cx) = eval env conf x in
				let (st'', i'', o'', Some cy) = eval env (st', i', o', Some cx) y in
				(st'', i'', o'', Some (calc binop cx cy))
			| Call (proc, args) -> 
				let (c'', params) = List.fold_left (fun (c', vals) p -> let (st', i', o', Some r') = eval env c' p in ((st', i', o', Some r'), [r'] @ vals)) (conf, []) args in
				env#definition env proc (List.rev params) c'';;	
         
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
	  atom: fun_call | num:DECIMAL {Const num} | x:IDENT {Var x} | -"(" expr -")";
	  fun_call: x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][parse]? ")" {Call (x, match params with Some s -> s | None -> [])}
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) k stmt = 
		let merge stmt1 stmt2 = 
			(match stmt2 with
			| Skip -> stmt1
			| _ -> Seq(stmt1, stmt2)) in
		match stmt with
		| Read x -> 
			(match i with 
			| num :: tail -> eval env ((State.update x num st), tail, o, r) Skip k
			| _ -> failwith "Error in input stream")
		| Write expr -> 
			let (st', i', o', Some v) = Expr.eval env conf expr in
			eval env (st', i', o' @ [v], r) Skip k
		| Assign (x, expr) -> 
			let (st', i', o', Some v) = Expr.eval env conf expr in
			eval env ((State.update x v st'), i', o', r) Skip k
		| Seq (stmt_left, stmt_right) -> 
			eval env conf (merge stmt_right k) stmt_left
		| Skip -> 
			(match k with
			| Skip -> conf
			| _ -> eval env conf Skip k)
		| If (cond, t, f) ->
			let (st', i', o', Some v) = Expr.eval env conf cond in
			eval env conf k (if v <> 0 then t else f)
		| While (cond, stmt) -> eval env conf k (If (cond, Seq (stmt, While (cond, stmt)), Skip))
		| Repeat (stmt, cond) -> eval env conf k (Seq (stmt, If (cond, Skip, Repeat (stmt, cond))))
		| Return expr -> 
			(match expr with
			| None -> conf
			| Some e -> Expr.eval env conf e)
		| Call (proc, args) -> eval env (Expr.eval env conf (Expr.Call (proc, args))) Skip k;;
         
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
		| x:IDENT "(" params:!(Ostap.Util.listBy)[ostap (",")][Expr.parse]? ")" {Call (x, match params with Some s -> s | None -> [])}
		| %"return" expr:!(Expr.parse)? {Return expr};
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
