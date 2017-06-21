(*Need to prove some basic theorems on holes for them to work properly with define*)

(*First, prove that if x = y, then f x = f y*)
let intrFun = prove(`! (x) (y). x = y ==> ((f x):epsilon) = f y`,
	(REPEAT STRIP_TAC) THEN
	(ASM_REWRITE_TAC[])
);;

(*For debugging purposes, adding the print_typed_var function from the reference manual*)
let print_typed_var fmt tm = 
  let s,ty = dest_var tm in
    pp_print_string fmt ("("^s^":"^string_of_type ty^")") in
    install_user_printer("print_typed_var",print_typed_var);;


(*Now prove the actual theorem that is causing problems: `!x y. x = y ==> Q_ (H_ (f (x:A)):epsilon _H) _Q = Q_ (H_ (f (y:A)) _H) _Q`*) 