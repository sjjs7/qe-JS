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

(*For testing, defines a function that takes an integer and recursively adds quotations until n is 0*)
let testFun = define `
    (testFun 0 = Q_ 0 _Q) /\
    (testFun (n + 1) = (Q_ H_ testFun(n) _H _Q))
`;;

let testFun2 = define `
    (testFun2 0 = Q_ 0 _Q) /\
    (testFun2 (n + 1) = (Q_ 2 + H_ testFun2(n) _H _Q))`;;

(*This tests that unquote tactics work even on long winded recursive functions*)
prove(`testFun 10 = Q_ 0 _Q`,
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 10 = testFun(9 + 1)`] `testFun 10`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 9 = testFun(8 + 1)`] `testFun 9`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 8 = testFun(7 + 1)`] `testFun 8`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 7 = testFun(6 + 1)`] `testFun 7`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 6 = testFun(5 + 1)`] `testFun 6`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 5 = testFun(4 + 1)`] `testFun 5`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 4 = testFun(3 + 1)`] `testFun 4`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 3 = testFun(2 + 1)`] `testFun 3`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 2 = testFun(1 + 1)`] `testFun 2`] THEN
    REWRITE_TAC[testFun] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun 1 = testFun(0 + 1)`] `testFun 1`] THEN
    REWRITE_TAC[testFun] THEN
    REPEAT UNQUOTE_TAC THEN
    REFL_TAC
);;

prove(`testFun2 10 = Q_ 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 0 _Q`,
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 10 = testFun2(9 + 1)`] `testFun2 10`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 9 = testFun2(8 + 1)`] `testFun2 9`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 8 = testFun2(7 + 1)`] `testFun2 8`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 7 = testFun2(6 + 1)`] `testFun2 7`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 6 = testFun2(5 + 1)`] `testFun2 6`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 5 = testFun2(4 + 1)`] `testFun2 5`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 4 = testFun2(3 + 1)`] `testFun2 4`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 3 = testFun2(2 + 1)`] `testFun2 3`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 2 = testFun2(1 + 1)`] `testFun2 2`] THEN
    REWRITE_TAC[testFun2] THEN
    REWRITE_TAC[REWRITE_CONV[ARITH_RULE `testFun2 1 = testFun2(0 + 1)`] `testFun2 1`] THEN
    REWRITE_TAC[testFun2] THEN
    REPEAT UNQUOTE_TAC THEN
    REFL_TAC
);;