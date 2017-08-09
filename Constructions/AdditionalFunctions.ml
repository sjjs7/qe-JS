(*Testing a few proofs to make sure this definition works*)

(*Trivial proof that x is effecitve in x + 3*)
prove(effectiveIn `x:num` `x + 3`,
	EXISTS_TAC `x + 1` THEN
	BETA_TAC THEN
	ARITH_TAC
);;

(*Trivial proof that x is not effective in x = x*)
prove(mk_neg (effectiveIn `x:bool` `x <=> x`),
	REWRITE_TAC[REFL `x`]
);; 

(*Helper lemmas for proving disquotation*)
let appsplitexpr = prove(`isExpr (App a0 a1) ==> isExpr a0 /\ isExpr a1`,
	MESON_TAC[isExpr]
);;

(*Attempting to define size of recursion to prove recursion is wellfounded*)
(*Fails to define because recursion is not proven to be well founded*)
let sizeOfQuo = define `
(sizeOfQuo (QuoConst s t) = 1) /\
(sizeOfQuo (QuoVar s t) = 1) /\ 
(sizeOfQuo (QuoAbs a b) = sizeOfQuo a + sizeOfQuo b + 1) /\
(sizeOfQuo (QuoComb a b) = sizeOfQuo a + sizeOfQuo b + 1) /\
(sizeOfQuo (Quo a) = sizeOfQuo a + 1)
`;;

(*Definition of peano for inductive proof*)

let isPeano = define `
(isPeano (QuoConst "!" (TyBiCons "fun" (TyBiCons "fun" ty (TyBase "bool")) (TyBase "bool"))) = T) /\
(isPeano (QuoConst "?" (TyBiCons "fun" (TyBiCons "fun" ty (TyBase "bool")) (TyBase "bool"))) = T) /\
(isPeano (QuoConst "/\\" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "\\/" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "==>" (TyBiCons "fun" (TyBase "bool") (TyBiCons "fun" (TyBase "bool") (TyBase "bool")))) = T) /\
(isPeano (QuoConst "=" (TyBiCons "fun" ty (TyBiCons "fun" ty (TyBase "bool")))) = T) /\
(isPeano (QuoConst "<=>" (TyBiCons "fun" ty (TyBiCons "fun" ty (TyBase "bool")))) = T) /\
(isPeano (QuoConst "~" (TyBiCons "fun" (TyBase "bool") (TyBase "bool"))) = T) /\
(isPeano (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) = T) /\
(isPeano (QuoConst "*" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) = T) /\
//HOL does not do greedy pattern matching, need to detect numbers like this
(isPeano (QuoComb a b) = 
	//Check is this is a number
	if a = (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) then
	  //Check that b is 1
	  (b = (QuoComb (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num"))) (QuoConst "_0" (TyBase "num"))) 
	  	//or 0
	  	\/ b = (QuoConst "_0" (TyBase "num")))
	else
	//This is not a number, check that the function and it's argument are Peano arithemtic
	(isPeano a /\ isPeano b))
`;;