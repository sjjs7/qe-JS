(*Helper functions to make vital functions more readable*)
let makeGenericComb constName firstArg secondArg = mk_comb(mk_comb(mk_const(constName,[]),firstArg),secondArg);;
let makeQuoVarComb a b = makeGenericComb "QuoVar" (mk_string a) b;;
let makeQuoConstComb a b = makeGenericComb "QuoConst" (mk_string a) b;;
let makeAppComb a b = makeGenericComb "App" a b;;
let makeAbsComb a b = makeGenericComb "Abs" a b;;
let makeTyVarComb a = mk_comb(mk_const("TyVar",[]),mk_var((string_of_type a),mk_type("list",[`:char`])));;
let makeTyConsComb a b = makeGenericComb "TyCons" (mk_string a) (mk_list (b,`:type`));;
let makeTyBaseComb a  = makeTyConsComb a [];;
let makeFunComb a = makeTyConsComb "Fun" a;;


(*Converts HOL's types into the types defined inside the 'type' type*)
let rec matchTypes hType = 
	(*This function will be used to recursively create function types*)
	let makeFun hType = 
		let a,b = dest_fun_ty hType in 
		makeFunComb [(matchTypes a);(matchTypes b)]
	in

	(*This funtion handles creation of lists*)

	let makeList hType = 
		let a,b = dest_type hType in
		makeTyConsComb a (List.map matchTypes b)
	in

	(*Cannot call dest_type on a variable type, so this must be checked and explicitly handled before getting to the main pattern matcher*)
	if (is_vartype hType) then makeTyVarComb hType else
	let a = fst (dest_type hType) in
	match a with
	| "num" | "real" | "int" | "bool" | "char" -> makeTyBaseComb(a)
	| "list" -> makeList hType
	| "fun" -> makeFun hType
	| _ -> failwith "This is not a valid type";;

(*Function to actually handle conversion*)
let rec quoteRecursion = function
	| Var (vName, vType) -> makeQuoVarComb vName (matchTypes vType)
	| Const (cName, cType) -> makeQuoConstComb cName (matchTypes cType)
	| Comb(E1,E2) -> makeAppComb (quoteRecursion E1) (quoteRecursion E2)
	| Abs(E1, E2) -> makeAbsComb (quoteRecursion E1) (quoteRecursion E2);;

(*Function to take an expression, and convert it into a type of epsilon wrapped inside of a Quote*)
let quote exp = mk_comb(mk_const("Quote",[]),(quoteRecursion exp));;