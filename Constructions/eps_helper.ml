(*Temporarily in it's own file to allow for rapid reloading without having to destroy and rebuild the types built in epsilon.ml*)
(*Will be merged into epsilon.ml later on*)

(*Definition of abstraction*)
(*This cannot be nammed because abs is already reserved by absolute value, so this is now e_abs for epsilon_abs*)
let e_abs = define `e_abs e1 e2 = Abs e1 e2`;;

(*Definition of application*)
let app = define `app e1 e2 = App e1 e2`;;

(*Definition of quo for epsilon types*)
let quo = define `quo eps = Quote eps`;;

(*Comparison to see if two types are equal*)
let eqTypes = define `eqTypes t1 t2 = (decomposeType t1 = decomposeType t2)`;;

(*Todo: Implement a function to check constants for validity*)

(*Proof that application works for basic expressions*)
prove(`app (QuoVar "x" Bool) (QuoVar "y" Bool) = App (QuoVar "x" Bool) (QuoVar "y" Bool)`,
	REWRITE_TAC[app]
);;

(*Testing it for bigger expressions*)
prove(`app (app (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool) = App (App (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool)`,
	REWRITE_TAC[app]
);;

(*Proof that abstraction works for basic expressions*)
prove(`e_abs (QuoVar "x" Bool) (QuoVar "y" Bool) = Abs (QuoVar "x" Bool) (QuoVar "y" Bool)`,
	REWRITE_TAC[e_abs]
);;

(*Testing it for bigger expressions, along with proving that x is free in the expression on it's own but is no longer free after applying e_abs*)
prove(`(e_abs (QuoVar "x" Bool) (App (App (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool)) = 
	   Abs (QuoVar "x" Bool) (App (App (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool))) /\ 
	   (~(isFreeIn (QuoVar "x" Bool) (e_abs (QuoVar "x" Bool) (app (app (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool))))) /\
	   (isFreeIn (QuoVar "x" Bool) (App (App (QuoVar "x" Bool) (QuoConst "/\\" (Fun (Fun Bool Bool) Bool))) (QuoConst "F" Bool)))`,
	REWRITE_TAC[e_abs] THEN
	REWRITE_TAC[isFreeIn]
);;

(*Proof that quoting works as intended*)
prove(`quo (App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoConst "3" NaturalInd)) = 
	Quote (App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoConst "3" NaturalInd))`,
	REWRITE_TAC[quo]
);;

(*Proof that quotes can be quoted*)
prove(`quo (quo (App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoConst "3" NaturalInd))) = 
	Quote (Quote (App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoConst "3" NaturalInd)))`,
	REWRITE_TAC[quo]
);;


(*Proves that eqTypes returns true when the two types are equal*)
prove(`eqTypes Bool Bool`,REWRITE_TAC[eqTypes]);;

(*Proves that eqTypes returns false when the two types are not equal*)
prove(`eqTypes Bool Ind <=> F`,
	REWRITE_TAC[eqTypes] THEN
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "Ind"`)]
);;

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
(*MOST LIKELY BROKEN DUE TO TYPE CHANGES, TO BE FIXED LATER)


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
*)