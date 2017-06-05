(*Two tactics to make use of quotation easier inside proofs*)
let (QUOTE_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[QUOTE_CONV gl] (asm,gl);;
let (TERM_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[TERM_TO_CONSTRUCTION_CONV gl] (asm,gl);;