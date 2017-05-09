(*Defines type and term as is defined in John Harisson's paper
Tyvar -> String representing a type
Bool -> Boolean type
RealInd -> A real individual
NaturalInd -> An individual belonging to the natural numbers
IntegerInd -> An individual belonging to the integers
(These have been separated to avoid losing information when converting a number to an individual - 3 could be a real, integer, or natural number with no way of discerning this outside of keeping track of the original type)
Ind -> Generic type for individuals that do not fit into other categories
Fun -> Function going from type to type*)
define_type "type = Tyvar string
			      | Bool
			      | RealInd
			      | IntegerInd
			      | NaturalInd
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

