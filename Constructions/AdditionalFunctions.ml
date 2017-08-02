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