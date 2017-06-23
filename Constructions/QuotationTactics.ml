let (QUOTE_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[QUOTE_CONV gl] (asm,gl);;
let (TERM_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[TERM_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (UNQUOTE_TAC: tactic) = fun (asm,gl) -> PURE_REWRITE_TAC[UNQUOTE_CONV gl] (asm,gl);;  
(*These tactics do the same as their original counterparts, but make use of the assumptions in the goal stack*)
let (ASM_QUOTE_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[QUOTE_CONV gl] (asm,gl);;
let (ASM_TERM_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[TERM_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (ASM_UNQUOTE_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[UNQUOTE_CONV gl] (asm,gl);; 