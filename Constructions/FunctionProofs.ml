(*Need to prove some basic theorems on holes for them to work properly with define*)

(*First, prove that if x = y, then f x = f y*)
let intrFun = prove(`! (x) (y). x = y ==> ((f x):epsilon) = f y`,
	(REPEAT STRIP_TAC) THEN
	(ASM_REWRITE_TAC[])
);;

(*Now prove the actual theorem that is causing problems: `!x y. x = y ==> Q_ (H_ (f (x:A)):epsilon _H) _Q = Q_ (H_ (f (y:A)) _H) _Q`*) 