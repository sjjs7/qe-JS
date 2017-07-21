  (*Constructs an effectiveIn expression for the given variable in the given term*)
  let effectiveIn var tm = 
  	(*This function checks that the variable name  does not exist in the term - if it does, it adds ' until a valid name is found*)
  	let rec unusedVarName var tm root = let dName = fst (dest_var var) in
  		match tm with
  		| Var(a,b) -> if a = dName then (unusedVarName (mk_var ((dName ^ "'"),type_of var)) root root) else dName
  		| Const(_,_) -> dName
  		| Comb(a,b) -> let aN = (unusedVarName var a root) and bN = (unusedVarName var b root) in if aN <> dName then aN else if bN <> dName then bN else dName
  		| Abs(a,b) -> let aN = (unusedVarName var a root) and bN = (unusedVarName var b root) in if aN <> dName then aN else if bN <> dName then bN else dName
  		| Quote(e,ty) -> unusedVarName var e root
  		| Hole(e,ty) -> unusedVarName var e root
  		| Eval(e,ty) -> unusedVarName var e root
  	in
  	(*Creates a y variable that will not clash with anything inside the term*)
    if not (is_var var) then failwith "effectiveIn: First argument must be a variable" else
    let vN,vT = dest_var var in 
    let y = mk_var(unusedVarName `y:A` tm tm,vT) in
    (*Now assembles the term using HOL's constructors*)
    let subTerm = mk_comb(mk_abs(var,tm),y) in
    let eqTerm = mk_eq(subTerm,tm) in
    (*At this point, have (\x. B)y = B, want to negate this*)
    let neqTerm = mk_comb(mk_const("~",[]),eqTerm) in
    let toExst = mk_abs(y,neqTerm) in
    mk_comb(mk_const("?",[type_of y,`:A`]),toExst);;

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

(*Attempt at proving the law of disquotation*)
(*Commented out as OCaml code for now, will convert to proof script when done*)
(*

Setting up proof

g(`(eval (quo x:epsilon) to epsilon) = x:epsilon`);;
 e(STRUCT_CASES_TAC (SPEC `x:epsilon` (cases "epsilon"))) ;;
 e(ASM_EVAL_LAMBDA_TAC);;
 e(MP_TAC (BETA_REVAL `x:epsilon` `QuoVar a0 a1` `quo x`));;
 e(PURE_REWRITE_TAC[isExprType]);;
 e(PURE_REWRITE_TAC[isExpr]);;
 e(PURE_REWRITE_TAC[headFunc]);;
 e(PURE_REWRITE_TAC[combinatoryType]);;
 e(PURE_REWRITE_TAC[isValidType]);;
 e(PURE_REWRITE_TAC[isApp]);;
 e(PURE_REWRITE_TAC[isFreeIn]);;
 e(PURE_REWRITE_TAC[stripFunc]);;
 e(PURE_REWRITE_TAC[headFunc]);;
 e(PURE_REWRITE_TAC[isValidType]);;
 e(PURE_REWRITE_TAC[ep_constructor]);;
 e(PURE_REWRITE_TAC[isConst]);;
 e(PURE_REWRITE_TAC[isFunction]);;
 e(PURE_REWRITE_TAC[EX]);;
 e(REWRITE_TAC[]);;
*)

