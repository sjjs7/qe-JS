(* Law of excluded middle (LEM) *)

let lem = prove(`!x:epsilon. isExprType x (TyBase "bool") ==> ((eval x to bool) \/ ~(eval x to bool))`,
GEN_TAC THEN
DISCH_TAC THEN
ASM_REWRITE_TAC[EXCLUDED_MIDDLE]
);;

INST [`x:epsilon`,`x:epsilon`] lem;;

INST [`y:epsilon`,`x:epsilon`] (GEN lem);;

(*Proving what this means to be:*)
let startingPoint = SPEC `y:epsilon` lem;;
let appThm = BETA_CONV `(\x. x) y`;;
let rawBETA = BETA_REDUCE_EVAL `x:epsilon` `y:epsilon` `x:epsilon` `:bool`;;
let rawBETA_term = concl rawBETA;;
let rawBETA_equiv = ONCE_DEPTH_CONV BETA_CONV rawBETA_term;;
let desired_rawBETA = EQ_MP rawBETA_equiv rawBETA;;
let varFree = CONJUNCT1 isFreeIn;;

INST [`QuoConst "T" (TyBase "bool")`,`x:epsilon`] lem;;

	let constTrue_LEM = prove(`(eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool))`,
	REWRITE_TAC[GSYM (MP (EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`)) (MESON[CONJ ((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`) ((REWRITE_CONV[isFreeIn]) `~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`)] `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool") /\ ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`))] THEN
	REWRITE_TAC[MP (SPEC `QuoConst "T" (TyBase "bool")` lem) (MESON[((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`)] `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`)]
	);;

INST [`QuoConst "F" (TyBase "bool")`,`x:epsilon`] lem;;

	let constFalse_LEM = prove(`(eval (QuoConst "F" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "F" (TyBase "bool")) to (bool))`,
	REWRITE_TAC[GSYM (MP (EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "F" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "F" (TyBase "bool"))` `x:epsilon` `:bool`)) (MESON[CONJ ((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`) ((REWRITE_CONV[isFreeIn]) `~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "F" (TyBase "bool"))`)] `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool") /\ ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "F" (TyBase "bool"))`))] THEN
	REWRITE_TAC[MP (SPEC `QuoConst "F" (TyBase "bool")` lem) (MESON[((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`)] `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`)]
	);;

INST [`Q_ (0 = 0) _Q`,`x:epsilon`] lem;;

	(EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `Q_ (0 = 0) _Q` `x:epsilon` `:epsilon`))) (BETA_REDUCE_EVAL `x:epsilon` `Q_ (0 = 0) _Q` `x:epsilon` `:epsilon`))




