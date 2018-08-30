(* Law of excluded middle (LEM) *)

let lem = prove(`!x:epsilon. isExprType x (TyBase "bool") ==> ((eval x to bool) \/ ~(eval x to bool))`,
GEN_TAC THEN
DISCH_TAC THEN
ASM_REWRITE_TAC[EXCLUDED_MIDDLE]
);;

INST [`x:epsilon`,`x:epsilon`] lem;;

INST [`y:epsilon`,`x:epsilon`] lem;;

(*Proving what this means to be:*)
let startingPoint = SPEC `y:epsilon` lem;;
let appThm = BETA_CONV `(\x. x) y`;;
let rawBETA = BETA_REDUCE_EVAL `x:epsilon` `y:epsilon` `x:epsilon` `:bool`;;
let rawBETA_term = concl rawBETA;;
let rawBETA_equiv = ONCE_DEPTH_CONV BETA_CONV rawBETA_term;;
let desired_rawBETA = EQ_MP rawBETA_equiv rawBETA;;
let varFree = CONJUNCT1 isFreeIn;;

INST [`QuoConst "T" (TyBase "bool")`,`x:epsilon`] lem;;

	(* Proof of: (eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool)) *)

	let constLEM_with_assumption = SPEC `QuoConst "T" (TyBase "bool")` lem;;
	(*desired_rawBETA is the statement that is needed to properly instantiate LEM with the QuoConst*)
	let desired_rawBETA = EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`);;
	(*Now what needs to be proven are the two antecedents of desired_rawBETA*)


	(*FIRST ANTECEDENT: isExprType isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")*)
	let inst_isExpr = prove(`isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`,
		REWRITE_TAC[isExprType] THEN
		REWRITE_TAC[isExpr] THEN
		REWRITE_TAC[isValidConstName] THEN
		REWRITE_TAC[isValidType] THEN
		REWRITE_TAC[EX] THEN
		REWRITE_TAC[combinatoryType] (*INST [`"T"`,`str:string`;`(TyBase "bool")`,`ty:type`] (CONJUNCT1 (CONJUNCT2 combinatoryType));;*)
	);;
	(*SECOND ANTECEDENT: ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))*)
	let notIsFree = prove(`~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`,REWRITE_TAC[isFreeIn]);;

	(*Now we can easily prove the relationship between the abstracted version of the eval and the eval with QuoConst inside*)

	let eval_abs_equivalence = prove(`((\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool")) <=> (eval (QuoConst "T" (TyBase "bool")) to (bool)))`,
		ASSUME_TAC (CONJ inst_isExpr notIsFree) THEN
		UNDISCH_TAC (concl (CONJ inst_isExpr notIsFree)) THEN
		REWRITE_TAC[desired_rawBETA]);;

	(*Now, lets prove the abstracted version of LEM with QuoConst, no assumptions:*)
	let abs_constLEM = prove(`(\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool")) \/ ~(\x. (eval (x) to (bool))) (QuoConst "T" (TyBase "bool"))`,
	ASSUME_TAC inst_isExpr THEN
	UNDISCH_TAC (concl inst_isExpr) THEN
	REWRITE_TAC[constLEM_with_assumption]	
	);;

	(*And finally, the theorem we've all been waiting for:*)

	let trueLEM = prove(`(eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool))`,
	REWRITE_TAC[GSYM eval_abs_equivalence] THEN
	REWRITE_TAC[abs_constLEM]
	);;

	let true_LEM = prove(`(eval (QuoConst "T" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "T" (TyBase "bool")) to (bool))`,
	REWRITE_TAC[GSYM (MP (EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "T" (TyBase "bool"))` `x:epsilon` `:bool`)) (MESON[CONJ ((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`) ((REWRITE_CONV[isFreeIn]) `~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`)] `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool") /\ ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))`))] THEN
	REWRITE_TAC [(MP (SPEC `QuoConst "T" (TyBase "bool")` lem) (MESON[((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`)] `isExprType (QuoConst "T" (TyBase "bool")) (TyBase "bool")`))]
	);;

INST [`QuoConst "F" (TyBase "bool")`,`x:epsilon`] lem;;

	let false_LEM = prove(`(eval (QuoConst "F" (TyBase "bool")) to (bool)) \/ ~(eval (QuoConst "F" (TyBase "bool")) to (bool))`,
	REWRITE_TAC[GSYM (MP (EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "F" (TyBase "bool"))` `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` `(QuoConst "F" (TyBase "bool"))` `x:epsilon` `:bool`)) (MESON[CONJ ((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`) ((REWRITE_CONV[isFreeIn]) `~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "F" (TyBase "bool"))`)] `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool") /\ ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "F" (TyBase "bool"))`))] THEN
	REWRITE_TAC [(MP (SPEC `QuoConst "F" (TyBase "bool")` lem) (MESON[((REWRITE_CONV[isExprType;isExpr;isValidConstName;isValidType;EX;combinatoryType]) `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`)] `isExprType (QuoConst "F" (TyBase "bool")) (TyBase "bool")`))]
	);;

INST [`Q_ (0 = 0) _Q`,`x:epsilon`] lem;;

	
	(*The proof structure used previously requires a construction not a term, therefore we will do the proof with the right hand side of this equivalence, and them make the substitution at the end.*)
	let quote_construct_equiv = TERM_TO_CONSTRUCTION `Q_ (0 = 0) _Q`;;
	let construction_form = rhs (concl quote_construct_equiv);;

	let quoteLEM_with_assumption = SPEC construction_form lem;;
	(*desired_rawBETA is the statement that is needed to properly instantiate LEM with the QuoConst*)
	let desired_rawBETA_quote = EQ_MP (ONCE_DEPTH_CONV BETA_CONV (concl (BETA_REDUCE_EVAL `x:epsilon` construction_form `x:epsilon` `:bool`))) (BETA_REDUCE_EVAL `x:epsilon` construction_form `x:epsilon` `:bool`);;
	(*Now what needs to be proven are the two antecedents of desired_rawBETA*)


	(*FIRST ANTECEDENT: isExprType isExprType construction_form*)
	let inst_isExpr_quote = prove(`isExprType (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (TyBase "bool")`,
		REWRITE_TAC[isExprType] THEN
		REWRITE_TAC[isExpr] THEN
		REWRITE_TAC[combinatoryType] THEN
		REWRITE_TAC[stripFunc] THEN
		REWRITE_TAC[headFunc] THEN
		REWRITE_TAC[isFunction;isAbs;isApp;isConst] THEN
		REWRITE_TAC[isValidType;isValidConstName] THEN
		REWRITE_TAC[EX;ep_constructor] THEN
		REPEAT CONJ_TAC THENL [
			EXISTS_TAC `TyBase "num"` THEN EXISTS_TAC `TyBase "bool"` THEN REFL_TAC;
			EXISTS_TAC `TyBase "num"` THEN EXISTS_TAC `TyBase "num"` THEN REFL_TAC; 
			EXISTS_TAC `TyBase "num"` THEN EXISTS_TAC `TyBiCons "fun" (TyBase "num") (TyBase "bool")` THEN REFL_TAC;
			EXISTS_TAC `TyBase "num"` THEN EXISTS_TAC `TyBase "num"` THEN REFL_TAC
			]
	);;

	(*SECOND ANTECEDENT: ~isFreeIn (QuoVar "x" (TyBase "epsilon")) (QuoConst "T" (TyBase "bool"))*)
	let notIsFree_quote = prove(`~isFreeIn (QuoVar "x" (TyBase "epsilon")) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))))`,
		REWRITE_TAC[isFreeIn]);;

	(*Now we can easily prove the relationship between the abstracted version of the eval and the eval with QuoConst inside*)

	let eval_abs_equivalence_quote = prove(`((\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) <=> (eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool)))`,
		ASSUME_TAC (CONJ inst_isExpr_quote notIsFree_quote) THEN
		UNDISCH_TAC (concl (CONJ inst_isExpr_quote notIsFree_quote)) THEN
		REWRITE_TAC[desired_rawBETA_quote]
	);;

	(*Now, lets prove the abstracted version of LEM with QuoConst, no assumptions:*)
	let abs_quoteLEM = prove(`(\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))))  \/ ~(\x. (eval (x) to (bool))) (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) `,
	ASSUME_TAC inst_isExpr_quote THEN
	UNDISCH_TAC (concl inst_isExpr_quote) THEN
	REWRITE_TAC[quoteLEM_with_assumption]	
	);;

	(*And finally, the theorem we've all been waiting for:*)

	let quoteLEM = prove(`(eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool)) \/ ~(eval (App (App (QuoConst "=" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "bool")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) (App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num")))) to (bool))`,
	REWRITE_TAC[GSYM eval_abs_equivalence_quote] THEN
	REWRITE_TAC[abs_quoteLEM]
	);;

	let quoteLEM2 = prove (`(eval (Q_ (0 = 0) _Q) to (bool)) \/ ~ (eval (Q_ (0 = 0) _Q) to (bool))`,
		REWRITE_TAC[quote_construct_equiv] THEN
		REWRITE_TAC[quoteLEM]
	);;





