(*Temporarily in it's own file to allow for rapid reloading without having to destroy and rebuild the types built in epsilon.ml*)
(*Will be merged into epsilon.ml later on*)

(*Mathematical function that can be used to inspect terms inside epsilon*)
(*Discard values are never actually used, but the type checker doesn't know this so they are kept numbered to separate them*)
let ep_type = define 
`(ep_type (QuoVar Discard1 Discard2) = "QuoVar") /\
 (ep_type (QuoConst Discard3 Discard4) = "QuoConst") /\
 (ep_type (Abs Discard5 Discard6) = "Abs") /\
 (ep_type (App Discard7 Discard8) = "App") /\
 (ep_type (Quote Discard9 Discard10) = "Quote")`;;

let decomposeType = define
`decomposeType Bool = "Bool" /\
 decomposeType Ind = "Ind" /\
 decomposeType NaturalInd = "NaturalInt" /\
 decomposeType IntegerInd = "IntegerInd" /\
 decomposeType RealInd = "RealInd" /\
 decomposeType (Fun T1 T2) = APPEND (APPEND (APPEND (APPEND "(Fun " (decomposeType T1)) "->") (decomposeType T2)) ")" /\ 
 decomposeType (Tyvar name) = name`;;


(*This proof is to check that the recursive definition of decomposeType is working*)
prove(`decomposeType (Fun (Fun Bool Ind) (Fun Ind Ind)) = "(Fun (Fun Bool->Ind)->(Fun Ind->Ind))"`,
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[APPEND]
)

(*This function returns true if the given expression f appears free anywhere in e*)
(*Regarding abstractions: I assume that the structure of an abstraction will contain the variable to
bind on the left and expression on the right, therefore for a variable to be free in an abstraction it
must appear in the right while not appearing free in the left*)
let isFreeIn = define
`(isFreeIn n1 (QuoVar n2 Discard1) = (n1 = n2)) /\
 (isFreeIn n3 (QuoConst n4 Discard2) = (n3 = n4)) /\ 
 (isFreeIn n5 (App n6 n7) = ((isFreeIn n5 n6) \/ (isFreeIn n5 n7))) /\
 (isFreeIn n8 (Abs n9 n10) = (~(isFreeIn n8 n9) /\ (isFreeIn n8 n10))) /\
 (isFreeIn n11 (Quote n12 Discard3) = (isFreeIn n11 n12))`;;

(*Mathematical function to inspect a member of epsilon's subtype*)
(*Will call decomposeType to turn a type into a string for easy comparisons*)
let ep_subtype = define
`(ep_subtype (QuoVar Discard1 T1) = (decomposeType T1)) /\
 (ep_subtype (QuoConst Discard2 T2) = (decomposeType T2)) /\
 (ep_subtype (Quote Discard3 T3) = (decomposeType T3))`;;

(*Mathematical definition of what constitutes a variable*)
let isVar = define `isVar e = ((ep_type e) = "QuoVar")`;;

(*A simple proof that variables are variables*)
prove(`isVar (QuoVar "ProveMe" Bool) = T`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_type]
);;

(*A simple proof that another type of epsilon is NOT a variable*)
prove(`isVar (QuoConst "DontProveMe" Bool) = F`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*Mathematical definition of what constitutes a constant*)
let isConst = define `isConst e = ((ep_type e) = "QuoConst")`;;

(*A simple proof that constants are constants*)
prove(`isConst (QuoConst "ProveMe" Bool) = T`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_type]
);;

(*A simple proof that another type of epsilon is NOT a constant*)
prove(`isConst (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Mathematical definition of what constitutes an abstraction*)
let isAbs = define `isAbs e = ((ep_type e) = "Abs")`;;

(*Simple proof that an abstraction is recognized as an abstraction*)
prove(`isAbs (Abs (QuoVar "Prove" Bool) (QuoConst "Me" Bool)) = T`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_type]
);;

(*Simple proof that non-abstractions are not abstractions*)
prove(`isAbs (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Abs"`)]
);;

(*Mathematical definition of what constitutes an application*)
let isApp = define `isApp e = ((ep_type e) = "App")`;;

(*Simple proof that an application is recognized as an application*)
prove(`isApp (App (QuoVar "Prove" Bool) (QuoConst "Me" Bool)) = T`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_type]
);;

(*Simple proof that non-applications are not applications*)
prove(`isApp (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "App"`)]
);;

(*Mathematical definition of what constitutes an expression*)
let isExpr = define `isExpr e = ((ep_type e) = "Quote")`;;

(*Simple proof that a quote is recognized as an expression*)
prove(`isExpr (Quote (QuoVar "Prove" Bool) Bool) = T`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[ep_type]
);;

(*Simple proof that non-expressions are not expressions*)
prove(`isExpr (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Quote"`)]
);;

(*Mathematical definition for isVarType *)
let isVarType = define `isVarType e t = ((isVar e) /\ ((decomposeType t) = (ep_subtype e)))`;;

(*Start by proving that isVarType is false when something is not a var*)
prove(`isVarType (QuoConst "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*Now prove that isVarType with the wrong variable type is false*)
prove(`isVarType (QuoVar "Wrong" Ind) Bool <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[decomposeType;ep_subtype] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "Ind"`)]
);;

(*Now proves that isVarType with the right variable type is true*)
prove(`isVarType (QuoVar "Right" Ind) Ind`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[decomposeType;ep_subtype;isVar] THEN
	REWRITE_TAC[ep_type]
)

(*Mathematical definition for isConstType*)
let isConstType = define `isConstType e t = ((isConst e) /\ ((decomposeType t) = (ep_subtype e)))`;;

(*Test for failure when not a constant*)
prove(`isConstType (QuoVar "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Test for failure when the constant is of the wrong type*)
prove(`isConstType (QuoConst "Wrong" Bool) Ind <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[decomposeType;ep_subtype] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Ind" = "Bool"`)]
);;

(*Proves that the right types result in true*)
prove(`isConstType (QuoConst "Right" (Fun Bool Ind)) (Fun Bool Ind)`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst;decomposeType;ep_subtype] THEN
	REWRITE_TAC[ep_type]
);;

(*Mathematical definition of isExprType*)
let isExprType = define `isExprType e t = ((isExpr e) /\ ((decomposeType t) = (ep_subtype e)))`;;

(*Test for failure when e is not an expression*)
prove(`isExprType (QuoVar "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Quote"`)]
);;

(*Test for failure when e is an expression of the wrong type*)
prove(`isExprType (Quote (QuoConst "Wrong" Ind) Ind) Bool <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[decomposeType; ep_subtype] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "Ind"`)]
);;

(*Test for success when the types agree and e is an expression*)
prove(`isExprType (Quote (QuoVar "Right" Ind) Ind) Ind`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[decomposeType; ep_subtype;ep_type]
)

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