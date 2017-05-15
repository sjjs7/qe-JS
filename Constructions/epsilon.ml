(*** Type Definitions ***)

(*Defines type and term as is defined in John Harisson's paper
Tyvar -> String representing a type
Bool -> Boolean type
RealInd -> A real individual
NaturalInd -> An individual belonging to the natural numbers
IntegerInd -> An individual belonging to the integers
(These have been separated to avoid losing information when converting a number to an individual - 3 could be a real, integer, or natural number with no way of discerning this outside of keeping track of the original type)
Ind -> Generic type for individuals that do not fit into other categories
Fun -> Function going from type to type*)
define_type "type = 
				    Tyvar string
			      | Bool
			      | RealInd
			      | IntegerInd
			      | NaturalInd
			      | Ind
			      | Fun type type";;    

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


(*** Function Definitions ***)
(*Mathematical function that can be used to inspect terms inside epsilon*)
(*Discard values are never actually used, but the type checker doesn't know this so they are kept numbered to separate them*)
let ep_constructor = define 
`(ep_constructor (QuoVar str ty) = "QuoVar") /\
 (ep_constructor (QuoConst str ty) = "QuoConst") /\
 (ep_constructor (Abs eps eps2) = "Abs") /\
 (ep_constructor (App eps eps2) = "App") /\
 (ep_constructor (Quote eps) = "Quote")`;;

let decomposeType = define
`decomposeType Bool = "Bool" /\
 decomposeType Ind = "Ind" /\
 decomposeType NaturalInd = "NaturalInd" /\
 decomposeType IntegerInd = "IntegerInd" /\
 decomposeType RealInd = "RealInd" /\
 decomposeType (Fun T1 T2) = APPEND (APPEND (APPEND (APPEND "(Fun " (decomposeType T1)) "->") (decomposeType T2)) ")" /\ 
 decomposeType (Tyvar name) = name`;;

 (*This function returns true if the given expression f appears free anywhere in e*)
(*Regarding abstractions: I assume that the structure of an abstraction will contain the variable to
bind on the left and expression on the right, therefore for a variable to be free in an abstraction it
must appear in the right while not appearing free in the left.*)
let isFreeIn = define
`(isFreeIn (QuoVar n1 t1) (QuoVar n2 t2) = (n1 = n2 /\ (decomposeType t1) = (decomposeType t2))) /\
 (isFreeIn qv (QuoConst str ty) = F) /\ 
 (isFreeIn qv (App eps eps2) = ((isFreeIn qv eps) \/ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Abs eps eps2) = (~(isFreeIn qv eps) /\ (isFreeIn qv eps2))) /\
 (isFreeIn qv (Quote eps) = F)`;; 

 (*Mathematical function to inspect a member of epsilon's subtype*)
(*Will return the raw type - need to now call decomposeType manually to convert to string*)
let ep_type = define
`(ep_type (QuoVar str ty) = (ty)) /\
 (ep_type (QuoConst str ty) = (ty)) /\
 (ep_type (Quote eps) = (Tyvar "epsilon"))`;;

(*This function takes a Fun type and takes off the first part of it - for use in calculating types of Abs/App*)
let stripFunc = define `stripFunc (Fun T1 T2) = T2`

(*This function takes a function type and returns the first part of it*)
let headFunc = define `headFunc (Fun T1 T2) = T1`;;

(*This function handles calculating the type of App and Abs expressions, necessary to handle function applications*)
(*Assuming that function will always be on left*)
let combinatoryType = define
`combinatoryType (App e1 e2) = (stripFunc (combinatoryType e1)) /\
combinatoryType (QuoConst str ty) = ty /\
combinatoryType (Abs (QuoVar str ty) e2) = (Fun (ty) (combinatoryType e2)) /\
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

(*Checks if a given type is a function - hopefully I can replace this with a cleaner method later, but this seems like the only way right now*)
let isFunction = define `
	(isFunction (Fun T1 T2) = T) /\
	(isFunction (Bool) = F) /\
	(isFunction (Ind) = F) /\
	(isFunction (NaturalInd) = F) /\ 
	(isFunction (IntegerInd) = F) /\
	(isFunction (RealInd) = F) /\
	(isFunction (Tyvar name) = F)`;; 

(*Placeholder to check for a valid constant name*)
let isValidConstName = define`
	isValidConstName (str:string) = T
`;;

(*This function will take a variable term, and another term of type epsilon, and return whether or not the types mismatch. If the term is not found, false is returned.
i.e. true means that two variables of the same name but different types exist inside these terms*)
(*Todo: Prove some things with this function to test it for correctness*)
let typeMismatch = define `
(typeMismatch (QuoVar name ty) (QuoVar name2 ty2) = (name = name2 /\ ~((decomposeType ty) = (decomposeType ty2)))) /\
(typeMismatch (QuoVar name ty) (QuoConst name2 ty2) = F) /\
(typeMismatch (QuoVar name ty) (App e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Abs e1 e2) = ((typeMismatch (QuoVar name ty) e1) \/ (typeMismatch (QuoVar name ty) e2))) /\
(typeMismatch (QuoVar name ty) (Quote e) = (typeMismatch (QuoVar name ty) e))`;;

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
	(isExpr (App e1 e2) = (((isConst e1) \/ (isApp e1)) /\ ((decomposeType (headFunc (combinatoryType e1))) = ((decomposeType (ep_type e2)))) /\ (isFunction (combinatoryType e1)) /\ (isExpr e2))) /\
	(isExpr (Abs e1 e2) = ((isVar e1) /\ ~(typeMismatch e1 e2) /\ (isExpr e2))) /\ 
	(isExpr (Quote e) = (isExpr e))
`;;

(*Mathematical definition for isVarType *)
let isVarType = define `isVarType e t = ((isVar e) /\ ((decomposeType t) = decomposeType (ep_type e)))`;;

(*Mathematical definition for isConstType*)
let isConstType = define `isConstType e t = ((isConst e) /\ ((decomposeType t) = decomposeType (ep_type e)))`;;

(*Mathematical definition of isExprType*)
let isExprType = define `isExprType e t = ((isExpr e) /\ ((decomposeType t) = decomposeType (ep_type e)))`;;

(*** PROOFS FOR TESTING ***)
(*This proof is to check that the recursive definition of decomposeType is working*)
prove(`decomposeType (Fun (Fun Bool Ind) (Fun Ind Ind)) = "(Fun (Fun Bool->Ind)->(Fun Ind->Ind))"`,
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[APPEND]
);;

(*Proof that a variable not inside an expression is not free in that expression*)
prove(`isFreeIn (QuoVar "x" Bool) (QuoVar "y" Bool) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable is free if the entire expression is just that variable*)
prove(`isFreeIn (QuoVar "x" Bool) (QuoVar "x" Bool)`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable cannot be free inside a constant even if the names match*)
prove(`isFreeIn (QuoVar "x" Bool) (QuoConst "x" Bool) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

(*Proof that a variable inside an application can be free*)
prove(`isFreeIn (QuoVar "x" RealInd) (App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd))`,
	REWRITE_TAC[isFreeIn]
);;

(*Prove that a mistyped variable in an otherwise free context is not free
(Mathematically a mistyped variable makes no sense, this is just meant to test that typing is enforced)*)
prove(`isFreeIn (QuoVar "x" Bool) (App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd)) <=> F`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "RealInd"`)]
);;

(*Proof that a variable inside an abstraction can be free if it is not bound*)
prove(`isFreeIn (QuoVar "x" RealInd) (Abs (QuoVar "y" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd))))`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

(*Proof that a variable inside an abstraction is not free if it is bound*)
prove(`isFreeIn (QuoVar "x" RealInd) (Abs (QuoVar "x" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd)))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;

(*The next two proofs show that wrapping the previous two expressions inside a quotation makes them false*)
prove(`isFreeIn (QuoVar "x" RealInd) (Quote (Abs (QuoVar "y" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd))))) <=> F`,
	REWRITE_TAC[isFreeIn]
);;

prove(`isFreeIn (QuoVar "x" RealInd) (Quote (Abs (QuoVar "x" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd))))) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;


(*A simple proof that variables are variables*)
prove(`isVar (QuoVar "ProveMe" Bool) = T`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a variable*)
prove(`isVar (QuoConst "DontProveMe" Bool) = F`,
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*A simple proof that constants are constants*)
prove(`isConst (QuoConst "ProveMe" Bool) = T`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor]
);;

(*A simple proof that another type of epsilon is NOT a constant*)
prove(`isConst (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Simple proof that an abstraction is recognized as an abstraction*)
prove(`isAbs (Abs (QuoVar "Prove" Bool) (QuoConst "Me" Bool)) = T`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-abstractions are not abstractions*)
prove(`isAbs (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isAbs] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Abs"`)]
);;

(*Simple proof that an application is recognized as an application*)
prove(`isApp (App (QuoVar "Prove" Bool) (QuoConst "Me" Bool)) = T`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Simple proof that non-applications are not applications*)
prove(`isApp (QuoVar "DontProveMe" Bool) = F`,
	REWRITE_TAC[isApp] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "App"`)]
);;


(*Start by proving that isVarType is false when something is not a var*)
prove(`isVarType (QuoConst "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoConst" = "QuoVar"`)]
);;

(*Now prove that isVarType with the wrong variable type is false*)
prove(`isVarType (QuoVar "Wrong" Ind) Bool <=> F`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[decomposeType;ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "Ind"`)]
);;

(*Now proves that isVarType with the right variable type is true*)
prove(`isVarType (QuoVar "Right" Ind) Ind`,
	REWRITE_TAC[isVarType] THEN
	REWRITE_TAC[decomposeType;ep_type;isVar] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Test for failure when not a constant*)
prove(`isConstType (QuoVar "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "QuoConst"`)]
);;

(*Test for failure when the constant is of the wrong type*)
prove(`isConstType (QuoConst "Wrong" Bool) Ind <=> F`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[decomposeType;ep_type] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Ind" = "Bool"`)]
);;

(*Proves that the right types result in true*)
prove(`isConstType (QuoConst "Right" (Fun Bool Ind)) (Fun Bool Ind)`,
	REWRITE_TAC[isConstType] THEN
	REWRITE_TAC[isConst;decomposeType;ep_type] THEN
	REWRITE_TAC[ep_constructor]
);;

(*Test for failure when e is not an expression
prove(`isExprType (QuoVar "Wrong" Ind) Ind <=> F`,
	REWRITE_TAC[isExprType] THEN
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"QuoVar" = "Quote"`)]
);;
*)

(*The following proofs will test combinatoryType*)

(*(+) 3 is of type NaturalInd->NaturalInd*)
prove(`combinatoryType(App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "3" NaturalInd)) = (Fun NaturalInd NaturalInd)`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(* 2 + 3 is of type NaturalInd *)
prove(`combinatoryType(App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoConst "3" NaturalInd)) = NaturalInd`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in (+) x gets a type of NaturalInd->NaturalInd->NaturalInd*)
prove(`combinatoryType (Abs (QuoVar "x" NaturalInd) (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoVar "x" NaturalInd))) = Fun NaturalInd (Fun NaturalInd NaturalInd)`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*Binding x in 2 + x should make it NaturalInd -> NaturalInd*)
prove(`combinatoryType (Abs (QuoVar "x" NaturalInd) (App (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "2" NaturalInd)) (QuoVar "x" NaturalInd))) = Fun NaturalInd NaturalInd`,
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc]
);;

(*The below are all tests for isExpr - it is a very important function so it will be extensively tested*)

(*Prove that a variable is an expression*)
prove(`isExpr (QuoVar "x" Bool)`,
	REWRITE_TAC[isExpr]
);;

(*Prove that a constant is an expression*)
prove(`isExpr (QuoConst "3" NaturalInd)`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isValidConstName]
);;

(*Prove that a simple function application is an expression*)
prove(`isExpr (App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "3" NaturalInd))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName]
);;

(*Prove that recursed function applications are an expression*)
prove(`isExpr (App(App (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd))) (QuoConst "3" NaturalInd)) (QuoVar "x" NaturalInd))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName]
);;

(*Prove that a malformed application is not an expression*)
prove(`isExpr(App (QuoVar "x" Bool) (QuoVar "y" Bool)) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "App"`)] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoVar" = "QuoConst"`)]
);;


(*Prove that a function application whose initial types match is an expression (i.e. this takes a number -> bool -> number so it should work when giving it a single number)*)
prove(`isExpr (App (QuoConst "+" (Fun NaturalInd (Fun Bool NaturalInd))) (QuoConst "3" NaturalInd))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[isValidConstName];
);;

(*Proving that the above should no longer work when giving it a second number*)
prove(`isExpr (App(App (QuoConst "+" (Fun NaturalInd (Fun Bool NaturalInd))) (QuoConst "3" NaturalInd)) (QuoVar "x" NaturalInd)) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;isApp;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[stripFunc] THEN
	REWRITE_TAC[isFunction] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "NaturalInd"`)]
);;

(*Proving that function application does not work out of order*)
prove(`isExpr (App  (QuoConst "3" NaturalInd) (QuoConst "+" (Fun NaturalInd (Fun NaturalInd NaturalInd)))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isConst;ep_constructor] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[headFunc] THEN
	REWRITE_TAC[ep_type] THEN
	REWRITE_TAC[isFunction]
);;

(*A function application to an invalid expresion is also an invalid expression*)
prove(`isExpr (App (QuoConst "+" (Fun NaturalInd (Fun Bool NaturalInd))) (App (QuoVar "x" Bool) (QuoVar "y" Bool))) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[combinatoryType] THEN
	REWRITE_TAC[isFunction]
);;

(*An abstraction where the first expression is not a variable is invalid*)
prove(`isExpr (Abs (QuoConst "3" NaturalInd) (QuoVar "x" NaturalInd)) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar] THEN
	REWRITE_TAC[ep_constructor] THEN
	REWRITE_TAC[STRING_EQ_CONV(`"QuoConst" = "QuoVar"`)]
);;

(*An abstraction where the abstracted variable makes no appearence in the second term is valid*)
prove(`isExpr (Abs (QuoVar "x" Bool) (QuoVar "y" Bool))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstracted variable appears and is the same type is valid*)
prove(`isExpr (Abs (QuoVar "x" Bool) (QuoVar "x" Bool))`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch]
);;

(*An abstraction where the abstraced variable appears but is a different type is invalid*)
prove(`isExpr (Abs (QuoVar "x" Bool) (QuoVar "x" NaturalInd)) <=> F`,
	REWRITE_TAC[isExpr] THEN
	REWRITE_TAC[isVar;ep_constructor] THEN
	REWRITE_TAC[typeMismatch] THEN
	REWRITE_TAC[decomposeType] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"Bool" = "NaturalInd"`)]
);;

(*Future code goes here, for now load eps_helper.ml for unfinished developments*)