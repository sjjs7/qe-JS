(* Law of excluded middle (LEM) *)

let lem = prove(`!x:epsilon. isExprType x (TyBase "bool") ==> ((eval x to bool) \/ ~(eval x to bool))`,
GEN_TAC THEN
DISCH_TAC THEN
ASM_REWRITE_TAC[EXCLUDED_MIDDLE]
);;

INST [`x:epsilon`,`x:epsilon`] lem;;

INST [`y:epsilon`,`x:epsilon`] lem;;

INST [`QuoConst "T" (TyBase "bool")`,`x:epsilon`] lem;;

INST [`QuoConst "F" (TyBase "bool")`,`x:epsilon`] lem;;

INST [`Q_ (0 = 0) _Q`,`x:epsilon`] lem;;




