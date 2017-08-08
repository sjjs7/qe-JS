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

(*Attempt at proving the law of disquotation*)
(*Commented out as OCaml code for now, will convert to proof script when done*)
(*

(*Begin by defining law of disquotation as a function, I'm not sure that this is necessary but it does aid in matching up the attempted goal with the way HOL defines structural induction, so I believe this is the best way to go about beginning
the proof*)
let disq = define `disq x = ((eval (quo x) to epsilon) = x)`;;


(*Set up the proof in the goalstack*)
g(`!x. disq x`);;

(*Perform induction over the structure of epsilon*)
e(MATCH_MP_TAC lth THEN ASM_REWRITE_TAC[disq]);;

(*Before the case split, use beta evals to fill in all instances of x with their respective case for the rest of the proof*)
e(BETA_TAC);;

(*Induction does not naturally do a case split, so it will be done manually here*)
e(REPEAT CONJ_TAC);;

(*Axiomatically prove disquotation is true for QuoVar and QuoConst*)
e(REWRITE_TAC[VAR_DISQUO `eval quo (QuoVar a0 a1) to epsilon`]);;
e(REWRITE_TAC[CONST_DISQUO `eval quo (QuoConst a0 a1) to epsilon`]);;

(*Prove disquotation is true in the case of App*)
e(REWRITE_TAC[SYM app]);;
e(REWRITE_TAC[appQuo]);;
e(MP_TAC (APP_SPLIT `quo a0` `quo a1`));;

*)