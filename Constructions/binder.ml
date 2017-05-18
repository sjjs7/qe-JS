(*Binder to quote inside HOL's logic, name is temporary*)
parse_as_binder "_Q_"

(*Currently meant to be a test run, should just give a TEST var every time. Currently not working*)
let QUOTE_DEF = new_basic_definition
 `(_Q_) = \P:A->epsilon. P = \x. (QuoVar "TEST" Bool)`;;