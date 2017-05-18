(*Converts HOL's types into the types defined inside the 'type' type*)
let rec matchTypes hType = 
	(*This function will be used to recursively create function types*)
	let makeFun hType = 
		let a,b = dest_fun_ty hType in 
		mk_comb(mk_comb(mk_const("Fun",[]),(matchTypes a)),(matchTypes b))
	in

	(*Cannot call dest_type on a variable type, so this must be checked and explicitly handled before getting to the main pattern matcher*)
	if (is_vartype hType) then
	mk_comb(mk_const("Tyvar",[]),mk_var((string_of_type hType),mk_type("list",[`:char`])))
	else

	match fst (dest_type hType) with
	| "num" -> mk_const("NaturalInd",[])
	| "real" -> mk_const("RealInd",[])
	| "int" -> mk_const("IntegerInd",[])
	| "bool" -> mk_const("Bool",[])
	| "fun" -> makeFun hType
	| _ -> failwith "This is not a valid type";;

(*Function to actually handle conversion*)
let rec quoteRecursion = function
	| Var (vName, vType) -> mk_comb(mk_comb(mk_const("QuoVar",[]),mk_string(vName)),(matchTypes vType))
	| Const (cName, cType) -> mk_comb(mk_comb(mk_const("QuoConst",[]),mk_string(cName)),(matchTypes cType))
	| Comb(E1,E2) -> mk_comb(mk_comb(mk_const("App",[]),(quoteRecursion E1)), (quoteRecursion E2))
	| Abs(E1, E2) -> mk_comb(mk_comb(mk_const("Abs",[]),(quoteRecursion E1)), (quoteRecursion E2));;

(*Function to take an expression, and convert it into a type of epsilon wrapped inside of a Quote*)
let quote exp = mk_comb(mk_const("Quote",[]),(quoteRecursion exp));;