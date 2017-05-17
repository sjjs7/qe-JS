(*Temporarily in it's own file to allow for rapid reloading without having to destroy and rebuild the types built in epsilon.ml*)
(*Will be merged into epsilon.ml later on*)

(*Todo: Implement a function to check constants for validity*)

(*Temporarily named Dev so as not to break the proofs currently using isValidConstName - this will replace isValidConstName when finished*)
let isValidConstNameDev = define `
	isValidConstNameDev name = ((name = "NUMERAL") \/ (name = "BIT1") \/ (name = "BIT0") \/ (name = "_0") \/ (name = "CONS") \/ (name = "ASCII") \/ (name = "NIL") \/ 
	(name="real_of_num") \/ (name = "real_neg") \/ (name = "DECIMAL") \/ (name = "int_of_num") \/ (name = "int_neg") \/ (name = "+") \/ (name = "*") \/ (name = "/") \/
	(name="-") \/ (name = "/\\") \/ (name = "\\/") \/ (name = "!") \/ (name = "?") \/ (name = "?!")
)
`
