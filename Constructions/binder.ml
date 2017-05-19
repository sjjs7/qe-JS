(*Prefix to quote inside HOL's logic, name is temporary*)
parse_as_prefix "_Q_";;

let QUOTE_BOOLS = define`
(_Q_ (T:bool)) = (QuoConst "T" Bool) /\
(_Q_ (F:bool)) = (QuoConst "F" Bool)
`;;

let QUOTE_EPS = define`
(_Q_ (eps:epsilon)) = (Quote (eps:epsilon))
`;;

let QUOTE_NUMS = define`
(_Q_ (n:num)) = (App (QuoConst "NUMERAL" (Fun NaturalInd NaturalInd)) (_Q_ (NUMERAL n)))
`;;

let quotenet = itlist(enter [])
[`(_Q_ (T:bool))`,QUOTE_BOOLS;
`(_Q_ (T:bool))`,QUOTE_BOOLS;
`(_Q_ (e:epsilon))`,QUOTE_EPS;
`(_Q_ (n:num))`, QUOTE_NUMS;]
empty_net;;

(*Currently meant to be a test run, should just give a TEST var every time. Currently not working*)
let QUOTE_DEF tm = FIRST_CONV (lookup tm arithnet) tm;;
