(*Temporarily in it's own file to allow for rapid reloading without having to destroy and rebuild the types built in addon.ml*)
(*Will be merged into addon.ml later on*)

(*This function takes an exploded string, searches for the "->" indicating a function type, and returns the parts before and after the function. *)
let rec splitForFunction x before = match x with
	| "-" :: ">" :: rest -> before,(implode rest)
	| [] -> before,""
	| a :: rest -> splitForFunction rest (before ^ a);;

(*This function converts a string into the custom defined 'type' type. I have tried to find a way to match types directly, but all attempts have proven unsuccesful. OCaml rejects the use of, for example, `:bool`
as it is not a constructor, along with attempts to create a type on the spot such as with mk_type("bool",[]).*)
let rec getType x = match x with
	| "bool" -> mk_const("Bool",[])
	| "num" -> mk_const("NaturalInd",[])
	| "real" -> mk_const("RealInd",[])
	| "int" -> mk_const("IntegerInd",[])
	(*This last case will handle making function and Tyvar types. splitForFunction is called to determine if this is a function type or not, if not, we create a Tyvar with the appropriate string*)
	| customType -> let a,b = (splitForFunction (explode x) "") in if b = "" then (mk_comb(mk_const("Tyvar",[`:(char)list`,`:string`]),(mk_string customType)))
	(*This else means that there WAS a succesful split, so a type of Fun is created*)
	  else mk_comb(mk_comb(mk_const("Fun",[]),(getType a)),(getType b));;

(*A conversion function to convert a HOL term into a quoted expression*)
let rec convert x = match x with
	| Var(a,b) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string a),(getType (string_of_type b)))
	| Abs(Var(v,t),b) -> mk_comb(mk_comb(mk_comb(mk_const("Abs",[]),(mk_string v)),(getType (string_of_type t))),convert b)
	(*Abs should not have anything other than a variable in it's first position *)
	| Abs(a,b) -> failwith "Malformed abstraction in provided term"
	(*These combinatory cases handle operators*)
	| Const("=",tEq) ->  mk_comb(mk_const("Equal",[]),getType (string_of_type tEq))
	(*A most likely temporary conversion that turns numbers into variables - possibly add a type for constant terms to avoid doing this?*)
	| Comb(Const("NUMERAL",ty),_) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string (string_of_term x)),(getType (string_of_type ty)))
	| Comb(Const("real_of_num",ty),_) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string (string_of_term x)),(getType (string_of_type ty)))
	| Comb(Const("DECIMAL",ty),_) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string (string_of_term x)),(getType (string_of_type ty)))
	| Const("T",ty) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string (string_of_term x)),(getType (string_of_type ty)))
	| Const("F",ty) -> mk_comb(mk_comb(mk_const("Var",[]),mk_string (string_of_term x)),(getType (string_of_type ty)))
	(*General combinatory case to handle combining expressions*)
	| Comb(a,b) -> mk_comb(mk_comb(mk_const("Comb",[]),convert a),convert b)
	(*Catch-all pattern for when conversion has failed, should not happen under regular use once this function is completed*)
	| _ -> failwith ("Could not convert term " ^ (string_of_term x));;
