(*Temporarily in it's own file to allow for rapid reloading without having to destroy and rebuild the types built in addon.ml*)
(*Will be merged into the same file later on*)


(*OUTDATED FUNCTIONS FOR OLD TYPE - FOR REFERENCE ONLY

(*Function to take an operator constant and turn it into a combation of that constant and EXPR_OPER*)
let makeExprOper crec =
	let c = fst crec in
	let t = snd crec in
	let s = mk_const("EXPR_OPER",[t,`:A`]) in
	let SCNDCNST = mk_mconst(c,t) in
	mk_comb(s,SCNDCNST);;

(*Function to take any other constant and wrap it up with ATOMIC_CONS*)
let makeAtomicCons cons t =
	let s = mk_const("ATOMIC_CONS",[t,`:A`]) in
	mk_comb(s,cons);;

(*Function that checks whether a constant should be assigned to EXPR_OPER or ATOMIC_CONS*)
let isOperator op = match op with
	"+" | "-" | "*" | "/" | "/\\" | "\\/" | "!" | "?" | "~" | "=" | "<=>" -> true
	| _ -> false;;

(*Function that applies isOperator to a received constant instead of just a string*)
let isOperatorCons cons = match cons with
	Const(a,b) -> isOperator a
	| _ -> false;;

(*Receives two expressions and turns them into an expression combination*)
let mkExprComb a b = 
	(*Run both sides through the converter so that we are definitely dealing with expressions on both sides*)
	let conva = converter a in
	let convb = converter b in
	(*Creates the expr_comb operator, then links it to the converted a expression, then generates the comma and links that to the combined expression*)
	let ecmb = mk_const("EXPR_COMB",[type_of a,`:A`]) in
	let lhook = mk_comb(ecmb,conva) in
	let com = mk_const(",",[type_of lhook,`:A`;type_of convb,`:B`]) in
	let lhook = mk_comb(com,lhook) in
	(*Joins the constructed comma operator with the converted right side of the expresion*)
	mk_comb(lhook,convb);;

(*Main conversion function to recursively take apart an expression and piece it back together as a syntax*)
let converter x = match x with
	| Const("T",_) -> makeAtomicCons x (`:bool`) (*Handle boolean constants*)
	| Const("F",_) -> makeAtomicCons x (`:bool`)
	| Const(a,b) -> if isOperator a then makeExprOper (a,b) else x 
	(*These next patterns find numeric constants*)
	| Comb(Const("NUMERAL",_),_) -> makeAtomicCons x `:num`
	| Comb(Const("real_of_num",_),_) -> makeAtomicCons x `:real`
	| Comb(Comb(Const("DECIMAL",_),_),_) -> makeAtomicCons x `:real`
	(*Identify combinations and split them recursively*)
	| Comb(a,b) -> mkExprComb a b
	| _ -> x;;

*)

(*This function takes an exploded string, searches for the "->" indicating a function type, and returns the parts before and after the function. *)
let rec splitForFunction x before = match x with
	| "-" :: ">" :: rest -> before,(implode rest)
	| [] -> before,""
	| a :: rest -> splitForFunction rest (before ^ a);;

(*This function converts a string into the custom defined 'type' type. I have tried to find a way to match types directly, but all attempts have proven unsuccesful. OCaml rejects the use of, for example, `:bool`
as it is not a constructor, along with attempts to create a type on the spot such as with mk_type("bool",[]).*)
let rec getType x = match x with
	| "bool" -> mk_const("Bool",[`:type`,`:A`])
	| "Placeholder For Ind" -> mk_const("Ind",[`:type`,`:A`]) (*This is most likely an inductive type, not entirely sure how to check for these as of yet so the placeholder pattern remains*)
	(*This last case will handle making function and Tyvar types. splitForFunction is called to determine if this is a function type or not, if not, we create a Tyvar with the appropriate string*)
	| customType -> let a,b = (splitForFunction (explode x) "") in if b = "" then (mk_comb(mk_const("Tyvar",[`:(char)list`,`:string`]),(mk_string customType)))
	(*This else means that there WAS a succesful split, so a type of Fun is created*)
	  else mk_comb(mk_comb(mk_const("Fun",[]),(getType a)),(getType b));;