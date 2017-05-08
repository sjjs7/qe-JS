(* Legacy type:S
let lth,rth = define_type "syntax = ATOMIC_VAR A | ATOMIC_CONS A | EXPR_OPER A | EXPR_BIND syntax,syntax | EXPR_COMB syntax,syntax";;
*)

(*Defines type and term as is defined in John Harisson's paper
Tyvar -> String representing a type
Bool -> Boolean type
Ind -> ???
Fun -> Function going from type to type*)
define_type "type = Tyvar string
			      | Bool
			      | Ind
			      | Fun type type";;    

(*
Var -> Variable named after the string represented by the type (could this also be used to represent a constant?)
Equal -> ???
Select -> ???
Comb -> Combines two terms
Abs -> Takes a string of a selected type along with another term, used to "mark" bound variables like the native Abs type
*)

define_type "term = Var string type 
				  | Equal type
				  | Select type
				  | Comb term term
				  | Abs string type term";;

(*Future code goes here, for now load q.ml for development of conversion*)