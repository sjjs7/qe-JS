(*Defines type and term as is defined in John Harisson's paper
Tyvar -> String representing a type
Bool -> Boolean type
RealInd -> A real individual
NaturalInd -> An individual belonging to the natural numbers
IntegerInd -> An individual belonging to the integers
(These have been separated to avoid losing information when converting a number to an individual - 3 could be a real, integer, or natural number with no way of discerning this outside of keeping track of the original type)
Ind -> Generic type for individuals that do not fit into other categories
Fun -> Function going from type to type*)
define_type "type = 
				    Tyvar string
			      | Bool
			      | RealInd
			      | IntegerInd
			      | NaturalInd
			      | Ind
			      | Fun type type";;    

(*
QuoVar -> Variable named after the string represented by the type (could this also be used to represent a constant?)
QuoConst -> A constant with the given type
App -> Function application
Abs -> Marks the first epsilon as a bound variable inside the other epsilon
Quote -> Representation of an expression as a type of epsilon
*)

define_type "epsilon = 
					   QuoVar string type 
				  	 | QuoConst string type
				     | Abs epsilon epsilon
				     | App epsilon epsilon
				     | Quote epsilon type";;

(*Future code goes here, for now load q.ml for development of conversion*)

