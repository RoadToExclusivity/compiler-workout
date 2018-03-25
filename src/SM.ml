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
let rec eval env (st, (s, i, o)) prog =
	match prog with
	  [] -> (st, (s, i, o))
	| inst :: tail -> 
	  let cfg, next = 
		  match inst with 
		  | BINOP binop -> 
				(match st with 
					  y :: x :: st_end -> ((Language.Expr.calc binop x y) :: st_end, (s, i ,o)), tail
					| _ -> failwith "Not enough arguments for binary operation")
		  | CONST n -> (n :: st, (s, i, o)), tail
		  | READ -> let num = List.hd i in (num :: st, (s, List.tl i, o)), tail
		  | WRITE -> let num = List.hd st in (List.tl st, (s, i, o @ [num])), tail
		  | LD x -> ((s x) :: st, (s, i, o)), tail
		  | ST x -> let num = List.hd st in (List.tl st, (Language.Expr.update x num s, i, o)), tail
		  | LABEL l -> (st, (s, i, o)), tail
		  | JMP l -> (st, (s, i, o)), (env#labeled l)
		  | CJMP (op, l) ->
				let cmp = List.hd st in
				let ret = if op = "z" && cmp = 0 || op == "nz" && cmp != 0 then (env#labeled l) else tail in
				(List.tl st, (s, i, o)), ret in
	  eval env cfg next

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

let compile (stmt : Language.Stmt.t) =
	let label_creator =
		object
			val cur_val = 0
			method get = "label_" ^ string_of_int cur_val, {< cur_val = cur_val + 1 >}
		end in
	let rec compile_expr (expr : Language.Expr.t) = 
		match expr with
		| Expr.Const n -> [CONST n]
		| Expr.Var x -> [LD x]
		| Expr.Binop (binop, x, y) -> compile_expr x @ compile_expr y @ [BINOP binop] in
	let rec compile_label lbl stmt = 
		match stmt with
		  Stmt.Read x -> lbl, [READ; ST x]
		| Stmt.Write expr -> lbl, (compile_expr expr) @ [WRITE]
		| Stmt.Assign (x, expr) -> lbl, (compile_expr expr) @ [ST x]
		| Stmt.Seq (stmt_left, stmt_right) ->
			let lbl, left = compile_label lbl stmt_left in
			let lbl, right = compile_label lbl stmt_right in
			lbl, left @ right
		| Stmt.Skip -> lbl, []
		| Stmt.If (cond, t, f) ->
			let flbl, lbl = lbl#get in
			let endlbl, lbl = lbl#get in
			let lbl, ift = compile_label lbl t in
			let lbl, iff = compile_label lbl f in
			let instr = 
				match f with
				| Skip -> [LABEL flbl]
				| _ -> [JMP endlbl; LABEL flbl] @ iff @ [LABEL endlbl] in
			lbl, (compile_expr cond) @ [CJMP ("z", flbl)] @ ift @ instr
		| Stmt.While (cond, st) ->
			let initlbl, lbl = lbl#get in
			let endlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [LABEL initlbl] @ (compile_expr cond) @ [CJMP ("z", endlbl)] @ body @ [JMP initlbl; LABEL endlbl]
		| Stmt.Repeat (cond, st) ->
			let initlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [LABEL initlbl] @ body @ (compile_expr cond) @ [CJMP ("z", initlbl)]
	in
	let _, code = compile_label label_creator stmt
	in code