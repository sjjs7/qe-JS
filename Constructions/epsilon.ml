(*** Type Definitions ***)

(*Defines type and term as is defined in John Harisson's paper
TyBar -> String representing a type variable
TyCons -> String representing a constructed type, followed by a type and a list of types.*) 
let lt, rt = define_type "type = 
				    TyVar string
			 	  | TyCons string ((type)list)";;    

(*
QuoVar -> Variable named after the string represented by the type (could this also be used to represent a constant?)
QuoConst -> A constant with the given type
App -> Function application
Abs -> Marks the first epsilon as a bound variable inside the other epsilon
Quote -> Representation of an expression as a type of epsilon
*)

let lth, rth = define_type "epsilon = 
					   QuoVar string type 
				  	 | QuoConst string type
				     | Abs epsilon epsilon
				     | App epsilon epsilon
				     | Quote epsilon";;

(*Distinctness operator can do what strings were implemented to do: Prove that different types of terms and types are unequal*)
let typeDistinct = distinctness "type";;
let epsilonDistinct = distinctness "epsilon";; 
(*These two theorems say that for any elements of type or epsilon to be equal, their arguments must be equal*)
let typeInjective = injectivity "type";;
let epsilonInjective = injectivity "epsilon";;

(*** Function Definitions ***)
(*Mathematical function that can be used to inspect terms inside epsilon*)
(*This needs to be kept until I can find a way to make this function return just the raw function - type checker currently disallows it*)
let ep_constructor = define 
`(ep_constructor (QuoVar str ty) = "QuoVar") /\
 (ep_constructor (QuoConst str ty) = "QuoConst") /\
 (ep_constructor (Abs eps eps2) = "Abs") /\
 (ep_constructor (App eps eps2) = "App") /\
 (ep_constructor (Quote eps) = "Quote")`;;

 (*This function returns true if the given expression f appears free anywhere in e*)
(*Regarding abstractions: I assume that the structure of an abstraction will contain the variable to
bind on the left and expression on the right, therefore for a variable to be free in an abstraction it
must appear in the right while not appearing free in the left.*)
let isFreeIn = define
`(isFreeIn (QuoVar n1 t1) (QuoVar n2 t2) = (n1 = n2 /\ t1 = t2)) /\
 (isFreeIn qv (QuoConst str ty) = F) /\ 
 (isFreeIn qv (App eps eps2) = ((isFreeIn qv eps) \/ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Abs eps eps2) = (~(isFreeIn qv eps) /\ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Quote eps) = F)`;; 

 (*Mathematical function to inspect a member of epsilon's type*)
let ep_type = define
`(ep_type (QuoVar str ty) = (ty)) /\
 (ep_type (QuoConst str ty) = (ty)) /\
 (ep_type (Quote eps) = (TyCons "epsilon" []))`;;

(*This function takes a Fun type and takes off the first part of it - for use in calculating types of Abs/App*)
let stripFunc = define `stripFunc (TyCons "fun" [T1;T2]) = T2`

(*This function takes a function type and returns the first part of it*)
let headFunc = define `headFunc (TyCons "fun" [T1;T2]) = T1`;;

(*This function handles calculating the type of App and Abs expressions, necessary to handle function applications*)
(*Assuming that function will always be on left*)
let combinatoryType = define
`combinatoryType (App e1 e2) = (stripFunc (combinatoryType e1)) /\
combinatoryType (QuoConst str ty) = ty /\
combinatoryType (Abs (QuoVar str ty) e2) = (TyCons "fun" [ty;(combinatoryType e2)]) /\
combinatoryType (QuoVar str ty) = ty /\
combinatoryType (Quote e) = combinatoryType e`;;

(*Mathematical definition of what constitutes a variable*)
let isVar = define `isVar e = ((ep_constructor e) = "QuoVar")`;;

(*Mathematical definition of what constitutes a constant*)
let isConst = define `isConst e = ((ep_constructor e) = "QuoConst")`;;

(*Mathematical definition of what constitutes an abstraction*)
let isAbs = define `isAbs e = ((ep_constructor e) = "Abs")`;;

(*Mathematical definition of what constitutes an application*)
let isApp = define `isApp e = ((ep_constructor e) = "App")`;;

(*Checks if a given type is a function using a much cleaner method*)
let isFunction = define `isFunction ty = (?a0. ty = (TyCons "fun" a0))`;; 

(*Checks that the constant name is valid*)
let isValidConstName = define `
	isValidConstName name = EX (\x. x = name) ["isValidConstNameDev"; "eqTypes"; "quo"; "app"; "e_abs"; "isProperSubexpressionOf"; "isPartOf"; "isExprType"; "isConstType"; "isVarType"; "isExpr"; "typeMismatch"; "isValidConstName"; "isFunction"; "isApp"; "isAbs"; "isConst"; "isVar"; "combinatoryType"; "headFunc"; "stripFunc"; "ep_type"; "isFreeIn"; "ep_constructor"; "Quote"; "App"; "Abs"; "QuoConst"; "QuoVar"; "_dest_epsilon"; "_mk_epsilon"; "TyCons"; "TyBase"; "TyVar"; "_dest_type"; "_mk_type"; "superadmissible"; "tailadmissible"; "admissible"; "CASEWISE"; "PCROSS"; "vector"; "dest_auto_define_finite_type_4"; "mk_auto_define_finite_type_4"; "dest_auto_define_finite_type_3"; "mk_auto_define_finite_type_3"; "dest_auto_define_finite_type_2"; "mk_auto_define_finite_type_2"; "dest_finite_prod"; "mk_finite_prod"; "dest_finite_diff"; "mk_finite_diff"; "sndcart"; "fstcart"; "pastecart"; "dest_finite_sum"; "mk_finite_sum"; "lambda"; "$"; "dest_cart"; "mk_cart"; "dest_finite_image"; "finite_index"; "dimindex"; "polynomial_function"; "sum"; "nsum"; "iterate"; "support"; "monoidal"; "neutral"; ".."; "has_sup"; "has_inf"; "inf"; "sup"; "COUNTABLE"; ">_c"; ">=_c"; "=_c"; "<_c"; "<=_c"; "ARBITRARY"; "INTERSECTION_OF"; "UNION_OF"; "pairwise"; "list_of_set"; "set_of_list"; "cartesian_product"; "EXTENSIONAL"; "ARB"; "CROSS"; "HAS_SIZE"; "CARD"; "ITSET"; "FINREC"; "REST"; "CHOICE"; "BIJ"; "SURJ"; "INJ"; "IMAGE"; "INFINITE"; "FINITE"; "SING"; "DISJOINT"; "PSUBSET"; "SUBSET"; "DELETE"; "DIFF"; "INTERS"; "INTER"; "UNIONS"; "UNION"; "UNIV"; "INSERT"; "EMPTY"; "SETSPEC"; "GSPEC"; "IN"; "num_gcd"; "num_coprime"; "num_mod"; "num_divides"; "num_of_int"; "int_gcd"; "int_coprime"; "int_mod"; "int_divides"; "real_mod"; "=="; "rem"; "div"; "int_pow"; "int_min"; "int_max"; "int_sgn"; "int_abs"; "int_mul"; "int_sub"; "int_add"; "int_neg"; "int_of_num"; "int_gt"; "int_ge"; "int_lt"; "int_le"; "real_of_int"; "int_of_real"; "integer"; "DECIMAL"; "sqrt"; "real_sgn"; "real_min"; "real_max"; "real_div"; "real_pow"; "real_abs"; "real_gt"; "real_ge"; "real_lt"; "real_sub"; "real_inv"; "real_le"; "real_mul"; "real_add"; "real_neg"; "real_of_num"; "dest_real"; "mk_real"; "treal_eq"; "treal_inv"; "treal_le"; "treal_mul"; "treal_add"; "treal_neg"; "treal_of_num"; "hreal_inv"; "hreal_le"; "hreal_mul"; "hreal_add"; "hreal_of_num"; "dest_hreal"; "mk_hreal"; "nadd_inv"; "nadd_rinv"; "nadd_mul"; "nadd_add"; "nadd_le"; "nadd_of_num"; "nadd_eq"; "dest_nadd"; "mk_nadd"; "is_nadd"; "dist"; "ASCII"; "_19631"; "_dest_char"; "_mk_char"; "list_of_seq"; "PAIRWISE"; "ZIP"; "ITLIST2"; "ASSOC"; "FILTER"; "EL"; "MAP2"; "ALL2"; "MEM"; "ITLIST"; "EX"; "ALL"; "NULL"; "REPLICATE"; "BUTLAST"; "LAST"; "MAP"; "LENGTH"; "REVERSE"; "APPEND"; "TL"; "HD"; "ISO"; "CONS"; "NIL"; "_dest_list"; "_mk_list"; "SOME"; "NONE"; "_dest_option"; "_mk_option"; "OUTR"; "OUTL"; "INR"; "INL"; "_dest_sum"; "_mk_sum"; "FNIL"; "FCONS"; "CONSTR"; "BOTTOM"; "_dest_rec"; "_mk_rec"; "ZRECSPACE"; "ZBOT"; "ZCONSTR"; "INJP"; "INJF"; "INJA"; "INJN"; "NUMRIGHT"; "NUMLEFT"; "NUMSUM"; "NUMSND"; "NUMFST"; "NUMPAIR"; "MEASURE"; "WF"; "minimal"; "MOD"; "DIV"; "FACT"; "-"; "ODD"; "EVEN"; "MIN"; "MAX"; ">"; ">="; "<"; "<="; "EXP"; "*"; "+"; "PRE"; "BIT1"; "BIT0"; "NUMERAL"; "SUC"; "_0"; "dest_num"; "mk_num"; "NUM_REP"; "IND_0"; "IND_SUC"; "ONTO"; "ONE_ONE"; "PASSOC"; "UNCURRY"; "CURRY"; "SND"; "FST"; ","; "REP_prod"; "ABS_prod"; "mk_pair"; "_FUNCTION"; "_MATCH"; "_GUARDED_PATTERN"; "_UNGUARDED_PATTERN"; "_SEQPATTERN"; "GEQ"; "GABS"; "LET_END"; "LET"; "one"; "one_REP"; "one_ABS"; "I"; "o"; "COND"; "@"; "_FALSITY_"; "?!"; "~"; "F"; "\\/"; "?"; "!"; "==>"; "/\\"; "T"; "="]
`;;

(*Checks that a type is a valid type*)
let isValidType = define `
	(isValidType (TyVar str) = T) /\
	(isValidType (TyCons str []) = (EX (\x. x = str) ["epsilon";"type";"4";"3";"2";"int";"real";"hreal";"nadd";"char";"num";"ind";"1";"bool"])) /\
	(isValidType (TyCons str [a]) = ((isValidType a) /\ (EX (\x. x = str) ["finite_image";"list";"option";"recspace"]))) /\
	(isValidType (TyCons str [(a:type);(b:type)]) = ((isValidType a) /\ (isValidType b) /\ (EX (\x. x = str) ["finite_prod";"finite_diff";"finite_sum";"cart";"sum";"prod";"fun"])))
`;;

(*This function will take a variable term, and another term of type epsilon, and return whether or not the types mismatch. If the term is not found, false is returned.
i.e. true means that two variables of the same name but different types exist inside these terms*)
(*Todo: Prove some things with this function to test it for correctness*)
let typeMismatch = define `
(typeMismatch (QuoVar name ty) (QuoVar name2 ty2) = (name = name2 /\ ~(ty = ty2))) /\
(typeMismatch (QuoVar name ty) (QuoConst name2 ty2) = F) /\ 
(typeMismatch (QuoVar name ty) (App e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Abs e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Quote e) = (typeMismatch (QuoVar name ty) e))`;;

(*The below is temporary testing code while I try to get isValidType to recurse properly*)
let rc = prove_general_recursive_function_exists `?rc.
(rc [] = 0) /\
(rc (CONS (TyVar str) t) = 1 + (rc t)) /\
(rc (CONS (TyCons str l) t) = 1 + (rc l) + (rc t)) 
`;;

let test = define `
	(lrt (a:type) (TyVar str) = F) /\
	(lrt (a:type) (TyCons str []) = F) /\
	(lrt (a:type) (TyCons str [b]) = (a=b)) /\
	(lrt (a:type) (TyCons str [b;c]) = (a = b \/ a = c))
`;;

let SUM = new_recursive_definition list_RECURSION
  `(SUM [] = 0) /\
   (SUM (CONS h t) = h + SUM t)`;;

let getList = define `
	(getList (TyCons str lt)) = (lt)
`;;

let flattenlist = define `
	(flattenlist (TyCons str lt) = 1 + (SUM (MAP flattenlist lt))) /\
	(flattenlist (TyVar str) = 1)
`;;


let flatten = prove_general_recursive_function_exists `?flatten.
	(flatten [] = 0) /\
	(flatten [(TyCons str l)] = 1 + (flatten l)) /\
	(flatten [(TyVar str)] = 1) /\
	(flatten [(TyCons str l);(TyVar str2)] = 2 + (flatten l)) /\
	(flatten [(TyVar str);(TyCons str2 l)] = 2 + (flatten l)) /\
	(flatten [(TyVar str);(TyVar str2)] = 2) /\
	(flatten [(TyCons str l);(TyCons str2 l2)] = 2 + (flatten l) + (flatten l2))
`;;

let so0 = prove_general_recursive_function_exists `?so0.
	(so0 (TyVar str) = 1) /\
	(so0 (TyCons str l) = (SUM (MAP so0 l)) + 1)
`;;

let so1 = define `
	(so1 (a:type) (TyVar str) = F) /\
	(so1 (a:type) (TyCons str l) = (EX (\x. x = a) l))
`;;


let isValidType = prove_general_recursive_function_exists `?isValidType.
	(isValidType (TyVar str) = T) /\
	(isValidType (TyCons str []) = (EX (\x. x = str) ["epsilon";"type";"4";"3";"2";"int";"real";"hreal";"nadd";"char";"num";"ind";"1";"bool"])) /\
	(isValidType (TyCons str [a]) = ((isValidType a) /\ (EX (\x. x = str) ["finite_image";"list";"option";"recspace"]))) /\
	(isValidType (TyCons str [(a:type);(b:type)]) = ((isValidType a) /\ (isValidType b) /\ (EX (\x. x = str) ["finite_prod";"finite_diff";"finite_sum";"cart";"sum";"prod";"fun"])))
`;;

let listUnordered = prove_general_recursive_function_exists `?luo.
	luo [] = F /\
	luo [a] = F /\
	luo [b;c] = ((luo [c]) \/ (luo [b]))
`;;

(*End of testing code*)

(*
(*Mathematical definition of what constitutes a correct expression*)
(*Todo: Enforce a check to see that constants are valid*)
Variable -> Always a valid expression
Constant -> Always a valid expression (except for when name is invalid?)
App -> Valid when left side is constant of type function and right side's type matches that function OR left side is app and right side's type aligns 
Abs -> Valid when variable types match (variable doesn't need to be in function, but if it is, the types must match)
Quote -> Valid if the quoted expression is valid
*)

let isExpr = define 
`
	(isExpr (QuoVar str ty) = T) /\
	(isExpr (QuoConst str ty) = isValidConstName str) /\
	(isExpr (App e1 e2) = (((isConst e1) \/ (isApp e1)) /\ (((headFunc (combinatoryType e1))) = (((combinatoryType e2)))) /\ (isFunction (combinatoryType e1)) /\ (isExpr e2)))  /\
	(isExpr (Abs e1 e2) = ((isVar e1) /\ ~(typeMismatch e1 e2) /\ (isExpr e2))) /\ 
	(isExpr (Quote e) = (isExpr e))
`;;

(*Mathematical definition for isVarType *)
let isVarType = define `isVarType e t = ((isVar e) /\ (t = (ep_type e)))`;;

(*Mathematical definition for isConstType*)
let isConstType = define `isConstType e t = ((isConst e) /\ (t = (ep_type e)))`;;

(*Mathematical definition of isExprType*)
let isExprType = define `isExprType e t = ((isExpr e) /\ (t = (combinatoryType e)))`;;

(*This is a sub part of the "is proper subexpression of" definition - it checks if the given first term appears anywhere inside the second *)
let isPartOf = define `
isPartOf (exp:epsilon) (QuoVar str ty) = (exp = (QuoVar str ty)) /\
isPartOf (exp:epsilon) (QuoConst str ty) = (exp = (QuoConst str ty)) /\
isPartOf (exp:epsilon) (App exp1 exp2) = ((isPartOf exp exp1) \/ (isPartOf exp exp2) \/ (exp = (App exp1 exp2))) /\
isPartOf (exp:epsilon) (Abs exp1 exp2) = ((isPartOf exp exp1) \/ (isPartOf exp exp2) \/ (exp = (Abs exp1 exp2))) /\
isPartOf (exp:epsilon) (Quote exp1) = ((isPartOf exp exp1) \/ (exp = (Quote exp1))) 
`;;

(*This defines the check to see if something is a proper subexpression of another expression*)
let isProperSubexpressionOf = define `isProperSubexpressionOf (exp1:epsilon) (exp2:epsilon) = ((isExpr exp1) /\ (isPartOf exp1 exp2))`;;

(*Definition of abstraction*)
(*This cannot be nammed because abs is already reserved by absolute value, so this is now e_abs for epsilon_abs*)
let e_abs = define `e_abs e1 e2 = Abs e1 e2`;;

(*Definition of application*)
let app = define `app e1 e2 = App e1 e2`;;

(*Definition of quo for epsilon types*)
let quo = define `quo eps = Quote eps`;;

(*Comparison to see if two types are equal*)
let eqTypes = define `eqTypes t1 t2 = (t1 = t2)`;;

(*** PROOFS FOR TESTING ***)
(*Proof that a variable not inside an expression is not free in that expression*)
prove(`isFreeIn (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable is free if the entire expression is just that variable*)
prove(`isFreeIn (QuoVar "x" (TyCons "Bool" [])) (QuoVar "x" (TyCons "Bool" []))`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable cannot be free inside a constant even if the names match*)
prove(`isFreeIn (QuoVar "x" (TyCons "Bool" [])) (QuoConst "x" (TyCons "Bool" [])) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable inside an application can be free*)
prove(`isFreeIn (QuoVar "x" (TyCons "RealInd" [])) (App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" [])))`,
	REWRITE_TAC[isFreeIn]
);;

(*Prove that a mistyped variable in an otherwise free context is not free
(Mathematically a mistyped variable makes no sense, this is just meant to test that typing is enforced)*)
prove(`isFreeIn (QuoVar "x" (TyCons "Bool" [])) (App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" []))) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "RealInd"`]
);;

(*Proof that a variable inside an abstraction can be free if it is not bound*)
prove(`isFreeIn (QuoVar "x" (TyCons "RealInd" [])) (Abs (QuoVar "y" (TyCons "RealInd" [])) ((App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" [])))))`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable inside an abstraction is not free if it is bound*)
prove(`isFreeIn (QuoVar "x" (TyCons "RealInd" [])) (Abs (QuoVar "x" (TyCons "RealInd" [])) ((App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" []))))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;

(*The next two proofs show that wrapping the previous two expressions inside a quotation makes them false*)
prove(`isFreeIn (QuoVar "x" (TyCons "RealInd" [])) (Quote (Abs (QuoVar "y" (TyCons "RealInd" [])) ((App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" [])))))) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

prove(`isFreeIn (QuoVar "x" (TyCons "RealInd" [])) (Quote (Abs (QuoVar "x" (TyCons "RealInd" [])) ((App (App (QuoVar "x" (TyCons "RealInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "RealInd" [];TyCons "fun" [TyCons "RealInd" [];TyCons "RealInd" []]]))) (QuoVar "y" (TyCons "RealInd" [])))))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;


(*A simple proof that variables are variables*)
prove(`isVar (QuoVar "ProveMe" (TyCons "Bool" [])) = T`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a variable*)
prove(`isVar (QuoConst "DontProveMe" (TyCons "Bool" [])) = F`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*A simple proof that constants are constants*)
prove(`isConst (QuoConst "ProveMe" (TyCons "Bool" [])) = T`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a constant*)
prove(`isConst (QuoVar "DontProveMe" (TyCons "Bool" [])) = F`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Simple proof that an abstraction is recognized as an abstraction*)
prove(`isAbs (Abs (QuoVar "Prove" (TyCons "Bool" [])) (QuoConst "Me" (TyCons "Bool" []))) = T`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-abstractions are not abstractions*)
prove(`isAbs (QuoVar "DontProveMe" (TyCons "Bool" [])) = F`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Abs"`)]
);;

(*Simple proof that an application is recognized as an application*)
prove(`isApp (App (QuoVar "Prove" (TyCons "Bool" [])) (QuoConst "Me" (TyCons "Bool" []))) = T`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-applications are not applications*)
prove(`isApp (QuoVar "DontProveMe" (TyCons "Bool" [])) = F`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "App"`)]
);;


(*Start by proving that isVarType is false when something is not a var*)
prove(`isVarType (QuoConst "Wrong" (TyVar "A")) (TyVar "A") <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*Now prove that isVarType with the wrong variable type is false*)
prove(`isVarType (QuoVar "Wrong" (TyVar "A")) (TyCons "Bool" []) <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[typeDistinct]
);;

(*Now proves that isVarType with the right variable type is true*)
prove(`isVarType (QuoVar "Right" (TyVar "A")) (TyVar "A")`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[ep_type;isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Test for failure when not a constant*)
prove(`isConstType (QuoVar "Wrong" (TyVar "A")) (TyVar "A") <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Test for failure when the constant is of the wrong type*)
prove(`isConstType (QuoConst "Wrong" (TyCons "Bool" [])) (TyVar "A") <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[typeDistinct]
);;

(*Proves that the right types result in true*)
prove(`isConstType (QuoConst "Right" (TyCons "fun" [TyCons "Bool" [];TyVar "A"])) (TyCons "fun" [TyCons "Bool" [];TyVar "A"])`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst;ep_type] THEN
	REWRITE_TAC[ep_constructor]
);;

(*The following proofs will test combinatoryType*)

(*(+) 3 is of type (TyCons "NaturalInd" [])->(TyCons "NaturalInd" [])*)
prove(`combinatoryType(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) = TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(* 2 + 3 is of type (TyCons "NaturalInd" []) *)
prove(`combinatoryType(App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoConst "3" (TyCons "NaturalInd" []))) = (TyCons "NaturalInd" [])`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in (+) x gets a type of (TyCons "NaturalInd" [])->(TyCons "NaturalInd" [])->(TyCons "NaturalInd" [])*)
prove(`combinatoryType (Abs (QuoVar "x" (TyCons "NaturalInd" [])) (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoVar "x" (TyCons "NaturalInd" [])))) = TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]]`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in 2 + x should make it (TyCons "NaturalInd" []) -> (TyCons "NaturalInd" [])*)
prove(`combinatoryType (Abs (QuoVar "x" (TyCons "NaturalInd" [])) (App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" [])))) =  TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*The below are all tests for isExpr - it is a very important function so it will be extensively tested*)

(*Prove that a variable is an expression*)
prove(`isExpr (QuoVar "x" (TyCons "Bool" []))`,
	REWRITE_TAC[isExpr]
);;

(*Prove that a constant is an expression*)
prove(`isExpr (QuoConst "T" (TyCons "Bool" []))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX]
);;

(*Prove that a simple function application is an expression*)
prove(`isExpr (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" [])))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

(*Prove that recursed function applications are an expression*)
prove(`isExpr (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" [])))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "NaturalInd" []]` THEN
	REFL_TAC
);;

(*Prove that a malformed application is not an expression*)
prove(`isExpr(App (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" []))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "App"`)] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "QuoConst"`)]
);;


(*Prove that a function application whose initial types match is an expression (i.e. this takes a number -> (TyCons "Bool" []) -> number so it should work when giving it a single number)*)
prove(`isExpr (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" [])))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

(*Proving that the above should no longer work when giving it a second number*)
prove(`isExpr (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" []))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "NaturalInd"`]
);;

(*Proving that function application does not work out of order*)
prove(`isExpr (App  (QuoConst "3" (TyCons "NaturalInd" [])) (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]]))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"NaturalInd" = "fun"`]
);;

(*A function application to an invalid expresion is also an invalid expression*)
prove(`isExpr (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (App (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "fun"`]
);;

(*An abstraction where the first expression is not a variable is invalid*)
prove(`isExpr (Abs (QuoConst "3" (TyCons "NaturalInd" [])) (QuoVar "x" (TyCons "NaturalInd" []))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoConst" = "QuoVar"`)]
);;

(*An abstraction where the abstracted variable makes no appearence in the second term is valid*)
prove(`isExpr (Abs (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstracted variable appears and is the same type is valid*)
prove(`isExpr (Abs (QuoVar "x" (TyCons "Bool" [])) (QuoVar "x" (TyCons "Bool" [])))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstraced variable appears but is a different type is invalid*)
prove(`isExpr (Abs (QuoVar "x" (TyCons "Bool" [])) (QuoVar "x" (TyCons "NaturalInd" []))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "NaturalInd"`]
);;

(*Abstracting over an application is invalid in the case of a type mismatch*)
prove(`isExpr (Abs (QuoVar "x" (TyCons "Bool" [])) (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" [])))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "NaturalInd"`]
);;

(*Abstracting over an application is valid when the types do match*)
prove(`isExpr (Abs (QuoVar "x" (TyCons "NaturalInd" [])) (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" []))))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "NaturalInd" []]` THEN
	REFL_TAC
);;

(*The following will test isExprType*)
prove(`isExprType (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []])`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	EXISTS_TAC `[TyCons "NaturalInd" []; TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

(*This tests that isExprType fails when the given expression is not an expression*)
prove(`isExprType (App (QuoConst "2" (TyCons "NaturalInd" [])) (QuoConst "3" (TyCons "NaturalInd" []))) (TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"NaturalInd" = "fun"`]
);;

(*This tests that isExprType fails when the types do not match*)
prove(`isExprType (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (TyCons "Bool" []) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "fun"`]
);;

(*This tests that isProperSubexpression returns false when the given subexpression is not a subexpression*)
prove(`isProperSubexpressionOf (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[epsilonInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"x" = "y"`]
);;

(*This tests that isProperSubexpression returns false when the given subexpression is not an expression*)
prove(`isProperSubexpressionOf (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "y" (TyCons "Bool" []))) (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "y" (TyCons "Bool" []))) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "fun"`]
);;


(*This tests that isProperSubexpression returns true even if the expresion on the right is improper*)
prove(`isProperSubexpressionOf (QuoVar "x" (TyCons "Bool" [])) (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "y" (TyCons "Bool" [])))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf]
);;

(*Tests that isProperSubExpression works for large terms*)
prove(`isProperSubexpressionOf (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" [])))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[headFunc] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

(*Final tests for this type - making sure that quote does not interfere with previous proofs*)
prove(`isExpr (Quote (Abs (QuoVar "x" (TyCons "NaturalInd" [])) (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" [])))))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "NaturalInd" []]` THEN
	REFL_TAC
);;

prove(`isExpr (Quote (Abs (QuoVar "x" (TyCons "Bool" [])) (App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "3" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" []))))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "NaturalInd"`]
);;

prove(`isExprType (Quote ((App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))))) (TyCons "fun" [TyCons "Bool" []; TyCons "NaturalInd" []])`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

prove(`isExprType (Quote(App (QuoConst "2" (TyCons "NaturalInd" [])) (QuoConst "3" (TyCons "NaturalInd" [])))) (TyCons "fun" [TyCons "Bool" []; TyCons "NaturalInd" []]) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"NaturalInd" = "fun"`]
);;

prove(`isExprType (Quote (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "Bool" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" [])))) (TyCons "Bool" []) <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[typeInjective] THEN
	REWRITE_TAC[STRING_EQ_CONV `"Bool" = "fun"`]
);;

prove(`isProperSubexpressionOf (QuoVar "x" (TyCons "Bool" [])) (Quote (QuoVar "y" (TyCons "Bool" []))) <=> F`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[epsilonInjective] THEN
	REWRITE_TAC[epsilonDistinct] THEN
	REWRITE_TAC[STRING_EQ_CONV `"x" = "y"`]
);;

prove(`isProperSubexpressionOf (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (Quote(App(App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "NUMERAL" (TyCons "NaturalInd" []))) (QuoVar "x" (TyCons "NaturalInd" []))))`,
	REWRITE_TAC[isProperSubexpressionOf] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isPartOf] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isValidConstName] THEN
	REWRITE_TAC[EX] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[headFunc] THEN
	EXISTS_TAC `[TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]]` THEN
	REFL_TAC
);;

(*Got to this point before the meeting, debug below proofs*)

(*Proof that application works for basic expressions*)
prove(`app (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])) = App (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" []))`,
	REWRITE_TAC[app]
);;

(*Testing it for bigger expressions*)
prove(`app (app (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" [])) = App (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" []))`,
	REWRITE_TAC[app]
);;

(*Proof that abstraction works for basic expressions*)
prove(`e_abs (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" [])) = Abs (QuoVar "x" (TyCons "Bool" [])) (QuoVar "y" (TyCons "Bool" []))`,
	REWRITE_TAC[e_abs]
);;

(*Testing it for bigger expressions, along with proving that x is free in the expression on it's own but is no longer free after applying e_abs*)
prove(`(e_abs (QuoVar "x" (TyCons "Bool" [])) (App (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" []))) = 
	   Abs (QuoVar "x" (TyCons "Bool" [])) (App (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" [])))) /\ 
	   (~(isFreeIn (QuoVar "x" (TyCons "Bool" [])) (e_abs (QuoVar "x" (TyCons "Bool" [])) (app (app (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" [])))))) /\
	   (isFreeIn (QuoVar "x" (TyCons "Bool" [])) (App (App (QuoVar "x" (TyCons "Bool" [])) (QuoConst "/\\" (TyCons "fun" [TyCons "fun" [TyCons "Bool" [];TyCons "Bool" []];TyCons "Bool" []]))) (QuoConst "F" (TyCons "Bool" []))))`,
	REWRITE_TAC[e_abs] THEN
	REWRITE_TAC[isFreeIn]
);;

(*Proof that quoting works as intended*)
prove(`quo (App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoConst "3" (TyCons "NaturalInd" []))) = 
	Quote (App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoConst "3" (TyCons "NaturalInd" [])))`,
	REWRITE_TAC[quo]
);;

(*Proof that quotes can be quoted*)
prove(`quo (quo (App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoConst "3" (TyCons "NaturalInd" [])))) = 
	Quote (Quote (App (App (QuoConst "+" (TyCons "fun" [TyCons "NaturalInd" [];TyCons "fun" [TyCons "NaturalInd" [];TyCons "NaturalInd" []]])) (QuoConst "2" (TyCons "NaturalInd" []))) (QuoConst "3" (TyCons "NaturalInd" []))))`,
	REWRITE_TAC[quo]
);;


(*Proves that eqTypes returns true when the two types are equal*)
prove(`eqTypes (TyCons "Bool" []) (TyCons "Bool" [])`,REWRITE_TAC[eqTypes]);;

(*Proves that eqTypes returns false when the two types are not equal*)
prove(`eqTypes (TyCons "Bool" []) (TyVar "A") <=> F`,
	REWRITE_TAC[eqTypes] THEN
	REWRITE_TAC[typeDistinct]
);;

(*Future code goes here, for now load eps_helper.ml for unfinished developments*)