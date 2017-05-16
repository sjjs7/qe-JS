(*Todo: Implement "raw quotation" - directly convert HOL's data structure to a type of Epsilon using OCaml's faculties*)

(*Simple conversion functions to take HOL types and convert them to the type of type*)

(*Converts functions by taking an exploded strings, think about returning these in a linked list for easier conversion to an HOL function?*)
let rec breakFunction before remaining = match remaining with
	| "-" :: ">" :: rest -> before, (breakFunction "" rest)
	| [] -> before, 
	| a :: rest -> splitForFunction (before ^ a) rest;;