(*Similair to the tests for epsilon, this will prove a few theoremms to verify that _Q_ and Q_ _Q work as intended, along with a few tests with OCaml functions to ensure the Quote term is working correctly*)

(*Firstly a proof to test that _Q_ puts quotations around expressions properly*)
prove (`(_Q_ (x:num) = Q_ (x:num) _Q) /\ (_Q_ (3) = Q_ 3 _Q) /\
_Q_ (T \/ F = T) = Q_ (T \/ F = T) _Q`,
(REPEAT QUOTE_TAC) THEN 
REWRITE_TAC[ALL]
);;

(*This tests that quotations are correctly converted to epsilon terms*)
prove(`Q_ (x + 3) _Q = (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoVar "x" (TyBase "num")))
	(App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (QuoConst "_0" (TyBase "num"))))))`,
TERM_TO_CONSTRUCTION_TAC THEN
REFL_TAC
);;

(*This tests that the result of QUOTE can be fed into TERM_TO_CONSTRUCTION to fully transition from the _Q_ operator to an epsilon term*)
prove(`_Q_ (x + 3) = (App (App (QuoConst "+" (TyBiCons "fun" (TyBase "num") (TyBiCons "fun" (TyBase "num") (TyBase "num")))) (QuoVar "x" (TyBase "num")))
	(App (QuoConst "NUMERAL" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (App (QuoConst "BIT1" (TyBiCons "fun" (TyBase "num") (TyBase "num")))
   (QuoConst "_0" (TyBase "num"))))))`,
QUOTE_TAC THEN
TERM_TO_CONSTRUCTION_TAC THEN
REFL_TAC
);;

(*These tests ensure that OCaml functions behave correctly when dealing with quotations*)

(*Substitution into a quotation should not be possible*)
assert ((concl (SUBS [ASSUME `x = 2`] (QUOTE `_Q_ (x + 3)`))) = `_Q_ (x + 3) = Q_ x + 3 _Q`);;

(*Also testing substitutions into TERM_TO_CONSTRUCTION*)
assert ((concl (SUBS [ASSUME `x = 2`] (TERM_TO_CONSTRUCTION  `Q_ x + 3 _Q`))) = concl (TERM_TO_CONSTRUCTION `Q_ x + 3 _Q`));;

(*Instantiation should also not do anything to a quotation*)
assert ((concl (INST [`2`,`x:num`] (QUOTE `_Q_ (x + 3)`))) = `_Q_ (x + 3) = Q_ x + 3 _Q`);;
assert ((concl (INST [`2`,`x:num`] (TERM_TO_CONSTRUCTION  `Q_ x + 3 _Q`))) = concl (TERM_TO_CONSTRUCTION `Q_ x + 3 _Q`));;

(*The above theorems were for substituting into proven theorems, these ones will test the respective operations on terms*)
(*Epsilon terms will not appear here as they have no variables that it is possible to substitute into
*)
assert (subst [`2`,`x:num`] (`_Q_ (x + 3)`) = `_Q_ (x + 3)`);;
assert (subst [`2`,`x:num`] (`Q_ x + 3 _Q`) = `Q_ x + 3 _Q`);;

(*It is possible to instantiate into type variables, this also should not be allowed to happen in quoted terms*)

assert (inst [`:num`,`:A`] (`_Q_ (x:A)`) = `_Q_ (x:A)`);;
assert (inst [`:num`,`:A`] (`Q_ (x:A) _Q`) = `Q_ (x:A) _Q`);;

(*Tests that hole terms can be created*)
`Q_ H_ Q_ x + 3 _Q _H _Q`;;

(*Tests that hole terms not of type epsilon cannot be created*)
try `Q_ H_ x + 3 _H _Q` with Failure _ -> `HOLE_EPSILON_TEST_SUCCESS:unit`;;

(*Tests that holes can be created and combined with non-hole terms*)
`Q_ H_ Q_ x + 3 _Q _H + 2 _Q`;

(*Tests that mistypes are still not allowed*)
try `Q_ H_ Q_ x + 3 _Q _H /\ T _Q` with Failure _ -> `HOLE_MISTYPE_TEST_SUCCESS:unit`;;