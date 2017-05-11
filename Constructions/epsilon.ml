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

define_type "epsilon = 
					   QuoVar string type 
				  	 | QuoConst string type
				     | Abs epsilon epsilon
				     | App epsilon epsilon
				     | Quote epsilon type";;


(*** Function Definitions ***)
(*Mathematical function that can be used to inspect terms inside epsilon*)
(*Discard values are never actually used, but the type checker doesn't know this so they are kept numbered to separate them*)
let ep_type = define 
`(ep_type (QuoVar str ty) = "QuoVar") /\
 (ep_type (QuoConst str ty) = "QuoConst") /\
 (ep_type (Abs eps eps2) = "Abs") /\
 (ep_type (App eps eps2) = "App") /\
 (ep_type (Quote eps ty) = "Quote")`;;

let decomposeType = define
`decomposeType Bool = "Bool" /\
 decomposeType Ind = "Ind" /\
 decomposeType NaturalInd = "NaturalInt" /\
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
 (isFreeIn qv (Quote eps ty) = (isFreeIn qv eps))`;;

 (*Mathematical function to inspect a member of epsilon's subtype*)
(*Will call decomposeType to turn a type into a string for easy comparisons*)
let ep_subtype = define
`(ep_subtype (QuoVar str ty) = (decomposeType ty)) /\
 (ep_subtype (QuoConst str ty) = (decomposeType ty)) /\
 (ep_subtype (Quote eps ty) = (decomposeType ty))`;;

(*Mathematical definition of what constitutes a variable*)
let isVar = define `isVar e = ((ep_type e) = "QuoVar")`;;

(*Mathematical definition of what constitutes a constant*)
let isConst = define `isConst e = ((ep_type e) = "QuoConst")`;;

(*Mathematical definition of what constitutes an abstraction*)
let isAbs = define `isAbs e = ((ep_type e) = "Abs")`;;

(*Mathematical definition of what constitutes an application*)
let isApp = define `isApp e = ((ep_type e) = "App")`;;

(*Mathematical definition of what constitutes an expression*)
let isExpr = define `isExpr e = ((ep_type e) = "Quote")`;;

(*Mathematical definition for isVarType *)
let isVarType = define `isVarType e t = ((isVar e) /\ ((decomposeType t) = (ep_subtype e)))`;;

(*Mathematical definition for isConstType*)
let isConstType = define `isConstType e t = ((isConst e) /\ ((decomposeType t) = (ep_subtype e)))`;;

(*Mathematical definition of isExprType*)
let isExprType = define `isExprType e t = ((isExpr e) /\ ((decomposeType t) = (ep_subtype e)))`;;

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

(*The next two proofs show that wrapping the previous two expressions inside a quotation does not change whether or not the variables are free*)
prove(`isFreeIn (QuoVar "x" RealInd) (Quote (Abs (QuoVar "y" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd)))) RealInd)`,
	REWRITE_TAC[isFreeIn] THEN
	REWRITE_TAC[(STRING_EQ_CONV `"x" = "y"`)]
);;

prove(`isFreeIn (QuoVar "x" RealInd) (Quote (Abs (QuoVar "x" RealInd) ((App (App (QuoVar "x" RealInd) (QuoConst "+" (Fun (Fun RealInd RealInd) RealInd))) (QuoVar "y" RealInd)))) RealInd) <=> F`,
	REWRITE_TAC[isFreeIn] 
);;


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
);;

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
);;



(*Future code goes here, for now load eps_helper.ml for unfinished developments*)