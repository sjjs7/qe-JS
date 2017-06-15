(*Like HOLE_THM_CONV_FIND, but tries to find the theorem on it's own*)  
(*Functionally almost the same as HOLE_THM_CONV_FIND, but attempts to generate the appropriate based on the function definition*)

let HOLE_DEF_CONV_FIND trm dList = 
	let rec HOLE_DEF_CONV_FIND_INTERNAL trm dList orig =
		let thm = PURE_REWRITE_CONV dList trm in 
		let tlhs,trhs = dest_eq (concl thm) in
		(*If theorem is not a reflexive theorem (default return for failure in REWRITE_CONV) return result of HOLE_THM_CONV_FIND*)
		if not (isQuoteSame tlhs trhs) then
		HOLE_THM_CONV_FIND orig thm
		else
		match trm with
		| Quote(e,t,h) -> HOLE_DEF_CONV_FIND_INTERNAL e dList orig
		| Comb(l,r) | Abs(l,r) -> (try HOLE_DEF_CONV_FIND_INTERNAL l dList orig with Failure _ -> HOLE_DEF_CONV_FIND_INTERNAL r dList orig)
		| Var(_,_) -> failwith "HOLE_DEF_CONV_FIND"
		| Const("HOLE",ty) -> HOLE_DEF_CONV_FIND_INTERNAL (match_hole ty !hole_lookup) dList orig
		| Const(_,_) -> failwith "HOLE_DEF_CONV_FIND"
	in
	HOLE_DEF_CONV_FIND_INTERNAL trm dList trm;;


(*Two tactics to make use of quotation easier inside proofs*)
let (QUOTE_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[QUOTE_CONV gl] (asm,gl);;
let (TERM_TO_CONSTRUCTION_TAC: tactic) = fun (asm,gl) -> PURE_ASM_REWRITE_TAC[TERM_TO_CONSTRUCTION_CONV gl] (asm,gl);;  
let (HOLE_THM_TAC) = fun tm (asm, gl) -> PURE_ASM_REWRITE_TAC[HOLE_THM_CONV_FIND gl tm] (asm,gl);;
let (HOLE_DEF_TAC) = fun tm (asm, gl) -> PURE_ASM_REWRITE_TAC[HOLE_DEF_CONV_FIND gl tm] (asm,gl);; 