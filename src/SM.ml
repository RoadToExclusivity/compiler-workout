open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg =
	match prg with
	| [] -> conf
	| inst :: tail -> 
	  let cfg, next = 
		 (match inst with 
		  | BINOP binop -> 
				(match stack with 
					  y :: x :: st_end -> (cstack, Value.of_int (Expr.calc binop (Value.to_int x) (Value.to_int y)) :: st_end, c), tail
					| _ -> failwith "Not enough arguments for binary operation")
		  | CONST n -> (cstack, (Value.of_int n) :: stack, c), tail
		  | STRING s -> (cstack, (Value.of_string s) :: stack, c), tail
		  | LD x -> (cstack, (State.eval st x) :: stack, c), tail
		  | ST x -> let num = List.hd stack in (cstack, List.tl stack, (State.update x num st, i, o)), tail
		  | STA (x, count) -> let taken, rest = split (count + 1) stack in
								let value::indexes = List.rev taken in
							(cstack, rest, (Stmt.update st x value (List.rev indexes), i, o)), tail
		  | LABEL _ -> conf, tail
		  | JMP l -> conf, (env#labeled l)
		  | CJMP (op, l) ->
				let cmp = Value.to_int (List.hd stack) in
				let ret = if (op = "z" && cmp = 0) || (op = "nz" && cmp <> 0) then (env#labeled l) else tail in
				(cstack, List.tl stack, c), ret
		  | BEGIN (_, params, locals) ->
				let new_st = State.enter st (params @ locals) in
				let st', stack' = List.fold_left (fun (a_st, v :: a_stack) p -> State.update p v a_st, a_stack) (new_st, stack) params in
				(cstack, stack', (st', i, o)), tail
		  | END | RET _ -> 
			   (match cstack with
				| [] -> conf, []
				| (prg', st') :: rest -> 
					let new_st = State.leave st st' in
					(rest, stack, (new_st, i, o)), prg')
		  | CALL (proc, argCount, isFunc) -> if env#is_label proc then ((tail, st) :: cstack, stack, c), (env#labeled proc) 
											 else (env#builtin conf proc argCount (not isFunc)), tail) in
	  eval env cfg next;;

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) =
	let label_creator =
		object
			val cur_val = 0
			method name x = "L" ^ x
			method get = "L" ^ string_of_int cur_val, {< cur_val = cur_val + 1 >}
		end in
	let rec compile_expr lbl (expr : Language.Expr.t) = 
		(match expr with
		| Expr.Const n -> [CONST n]
		| Expr.Array a -> let args = List.fold_left (fun acc index -> acc @ (compile_expr lbl index)) [] a in args @ [CALL ("$array", List.length args, true)]
		| Expr.String s -> [STRING s]
		| Expr.Var x -> [LD x]
		| Expr.Binop (binop, x, y) -> compile_expr lbl x @ compile_expr lbl y @ [BINOP binop]
		| Expr.Elem (v, e) -> compile_expr lbl v @ compile_expr lbl e @ [CALL ("$elem", 2, true)]
		| Expr.Length l -> compile_expr lbl l @ [CALL ("$length", 1, true)]
		| Expr.Call (proc, params) -> 
			let compiled_params = List.fold_right (fun expr lst -> lst @ (compile_expr lbl expr)) params [] in
			(compiled_params @ [CALL ((lbl#name proc), List.length params, true)])) in
	let rec compile_label lbl stmt = 
	   (match stmt with
		  Stmt.Assign (x, args, expr) -> 
			(match args with
			  [] -> lbl, compile_expr lbl expr @ [ST x]
			| args -> let indexes = List.fold_right (fun index acc -> (compile_expr lbl index) @ acc) args [] in 
			lbl, ((compile_expr lbl expr) @ (List.rev indexes) @ [STA (x, List.length args)]))
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
			lbl, (compile_expr lbl cond) @ [CJMP ("z", flbl)] @ ift @ instr
		| Stmt.While (cond, st) ->
			let initlbl, lbl = lbl#get in
			let endlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [JMP endlbl; LABEL initlbl] @ body @ [LABEL endlbl] @ (compile_expr lbl cond) @ [CJMP ("nz", initlbl)]
		| Stmt.Repeat (st, cond) ->
			let initlbl, lbl = lbl#get in
			let lbl, body = compile_label lbl st in
			lbl, [LABEL initlbl] @ body @ (compile_expr lbl cond) @ [CJMP ("z", initlbl)]
		| Stmt.Return expr -> 
			let ret, isFunc =
			(match expr with
			| None -> [], false
			| Some e -> (compile_expr lbl e), true) in
			lbl, ret @ [RET isFunc]
		| Stmt.Call (proc, params) -> 
			let compiled_params = List.fold_right (fun expr lst -> lst @ (compile_expr lbl expr)) params [] in
			lbl, (compiled_params @ [CALL ((lbl#name proc), List.length params, false)])) in
	let rec compile_def lbl procs =
		match procs with
		| [] -> lbl, []
		| (proc, (args, locals, body)) :: ps -> 
			let lbl, compiled_body = compile_label lbl body in
			let lbl, rest = compile_def lbl ps in
			lbl, [LABEL (lbl#name proc); BEGIN (proc, args, locals)] @ compiled_body @ [END] @ rest in 
	let lbl, procs = compile_def label_creator defs in
	let _, code = compile_label lbl p
	in code @ [END] @ procs;;
