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

  let abs_split var tm ty = 
  if not (is_var var) then failwith "ABS_SPLIT: Not a variable" else
  if not (fst (dest_type (type_of tm)) = "epsilon") then failwith "ABS_SPLIT: Term must be of type epsilon" else
  (*Create the antecedent*)
  let aced = mk_comb(mk_comb(mk_const("/\\",[]),mk_comb(mk_comb(mk_const("isExprType",[]),tm),(matchType ty))),mk_comb(mk_comb(mk_const("isFreeIn",[]),mk_quote(var)),mk_quote(tm))) in
  (*Create the consequent*)
  let consq = mk_eq(mk_eval(mk_comb(mk_comb(mk_const("e_abs",[]),mk_quote(var)),tm),mk_type ("fun",[(type_of var);ty])),mk_abs(var,mk_eval(tm,ty))) in
  (*Merge the two with an implication*)
  mk_comb(mk_comb(mk_const("==>",[]),aced),consq);;


(*Introduces axioms about eval into HOL*)

let app_split = new_axiom `((isExprType At (TyBiCons "fun" (TyVar "A") (TyVar "B"))) /\ (isExprType Bt (TyVar "A"))) ==> ((eval (app At Bt) to B) = ((eval At to A->B) (eval Bt to A)))`;;
let quotable = new_axiom `(isExprType e (TyBase "epsilon")) ==> ((eval (quo e) to epsilon) = e)`;; 

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