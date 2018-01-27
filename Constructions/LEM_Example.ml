let test = prove(`isExprType (x:epsilon) (TyBase "bool") ==> ((eval x to bool) \/ ~(eval x to bool))`,
DISCH_TAC THEN
ASM_REWRITE_TAC[EXCLUDED_MIDDLE]
);;
INST [`QuoConst "T" (TyBase "bool")`,`x:epsilon`] test;;
