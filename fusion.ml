(* ========================================================================= *)
(* Complete HOL kernel of types, terms and theorems.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "lib.ml";;

module type Hol_kernel =
  sig
      type hol_type = private
        Tyvar of string
      | Tyapp of string *  hol_type list

      type term = private
        Var of string * hol_type
      | Const of string * hol_type
      | Comb of term * term
      | Abs of term * term
      | Quote of term * hol_type
      | Hole of term * hol_type
      | Eval of term * hol_type

      type thm

      val types: unit -> (string * int)list
      val get_type_arity : string -> int
      val new_type : (string * int) -> unit
      val mk_type: (string * hol_type list) -> hol_type
      val mk_vartype : string -> hol_type
      val dest_type : hol_type -> (string * hol_type list)
      val dest_vartype : hol_type -> string
      val is_type : hol_type -> bool
      val is_vartype : hol_type -> bool
      val tyvars : hol_type -> hol_type list
      val type_subst : (hol_type * hol_type)list -> hol_type -> hol_type
      val bool_ty : hol_type
      val aty : hol_type

      val constants : unit -> (string * hol_type) list
      val get_const_type : string -> hol_type
      val new_constant : string * hol_type -> unit
      val type_of : term -> hol_type
      val fun_type_of : term -> hol_type
      val alphaorder : term -> term -> int
      val is_var : term -> bool
      val is_const : term -> bool
      val is_abs : term -> bool
      val is_comb : term -> bool
      val is_quote : term -> bool
      val is_hole : term -> bool
      val is_eval : term -> bool
      val mk_var : string * hol_type -> term
      val mk_const : string * (hol_type * hol_type) list -> term
      val mk_abs : term * term -> term
      val mk_comb : term * term -> term
      val mk_quote : term -> term
      val mk_hole : term -> term
      val mk_eval : term * hol_type -> term
      val dest_var : term -> string * hol_type
      val dest_const : term -> string * hol_type
      val dest_comb : term -> term * term
      val dest_abs : term -> term * term
      val dest_quote: term -> term
      val dest_hole : term -> term * hol_type
      val dest_eval : term -> term * hol_type
      val frees : term -> term list
      val freesl : term list -> term list
      val freesin : term list -> term -> bool
      val vfree_in : term -> term -> bool
      val type_vars_in_term : term -> hol_type list
      val variant : term list -> term -> term
      val vsubst : (term * term) list -> term -> term
      val qsubst : (term * term) list -> term -> term
      val inst : (hol_type * hol_type) list -> term -> term
      val rand: term -> term
      val rator: term -> term
      val dest_eq: term -> term * term

      val isQuoteSame: term -> term -> bool
      val QSUB_CONV : (term->thm) -> term -> ((term->thm) -> term -> thm) -> thm
      val QBETA_CONV : term -> (term -> thm) -> thm

      val dest_thm : thm -> term list * term
      val hyp : thm -> term list
      val concl : thm -> term
      val orda: (term * term) list -> term -> term -> int
      val REFL : term -> thm
      val TERM_TO_CONSTRUCTION : term -> thm
      val TERM_TO_CONSTRUCTION_CONV : term -> thm
      val CONSTRUCTION_TO_TERM : term -> thm
      val TRANS : thm -> thm -> thm
      val MK_COMB : thm * thm -> thm
      val ABS : term -> thm -> thm
      val BETA : term -> thm
      val ASSUME : term -> thm
      val EQ_MP : thm -> thm -> thm
      val DEDUCT_ANTISYM_RULE : thm -> thm -> thm
      val INST_TYPE : (hol_type * hol_type) list -> thm -> thm
      val INST : (term * term) list -> thm -> thm
      val axioms : unit -> thm list
      val new_axiom : term -> thm
      val definitions : unit -> thm list
      val new_basic_definition : term -> thm
      val new_basic_type_definition :
              string -> string * string -> thm -> thm * thm
      val getTyv : unit -> int
      val UNQUOTE : term -> thm
      val UNQUOTE_CONV : term -> thm
      val EVAL_QUOTE : term -> thm
      val EVAL_QUOTE_CONV : term -> thm
      val matchType : hol_type -> term
      val INTERNAL_TTC : term -> thm
      val INTERNAL_TTC_CONV : term -> thm
      (*Debugging functions temporarily revealed for tracing go here*)
      val constructionToTerm : term -> term
      val qcheck_type_of : term -> hol_type
      val VAR_DISQUO : term -> thm
      val CONST_DISQUO : term -> thm
      val LAW_OF_QUO : term -> thm
      val QUOTABLE : term -> thm
      val ABS_SPLIT : term -> term -> thm
      val APP_SPLIT : term -> term -> thm
      val BETA_EVAL : term -> term -> thm
      val BETA_REVAL : term -> term -> term -> thm
      val NOT_FREE_OR_EFFECTIVE : term -> term -> thm
      val NEITHER_EFFECTIVE : term -> term -> term -> term -> thm
      val EVAL_VSUB : thm -> term -> thm
      val EVAL_GOAL_VSUB : term list * term -> thm 
      val is_eval_free : term -> bool
      val stackAbs : (term * term) list -> term -> term
      val effectiveIn : term -> term -> term
      val addThm : thm -> unit
      val is_proven_thm : term -> bool
end;;

(* ------------------------------------------------------------------------- *)
(* This is the implementation of those primitives.                           *)
(* ------------------------------------------------------------------------- *)

module Hol : Hol_kernel = struct

  type hol_type = Tyvar of string
                | Tyapp of string *  hol_type list

  type term = Var of string * hol_type
            | Const of string * hol_type
            | Comb of term * term
            | Abs of term * term
            | Quote of term * hol_type
            | Hole of term * hol_type
            | Eval of term * hol_type

  type thm = Sequent of (term list * term)

(* ------------------------------------------------------------------------- *)
(* List of current type constants with their arities.                        *)
(*                                                                           *)
(* Initially we just have the boolean type and the function space            *)
(* constructor. Later on we add as primitive the type of individuals.        *)
(* All other new types result from definitional extension.                   *)
(* ------------------------------------------------------------------------- *)

  let the_type_constants = ref ["bool",0; "fun",2]

(* ------------------------------------------------------------------------- *)
(* Return all the defined types.                                             *)
(* ------------------------------------------------------------------------- *)

  let types() = !the_type_constants

(* ------------------------------------------------------------------------- *)
(* Lookup function for type constants. Returns arity if it succeeds.         *)
(* ------------------------------------------------------------------------- *)

  let get_type_arity s = assoc s (!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new type.                                                       *)
(* ------------------------------------------------------------------------- *)

  let new_type(name,arity) =
    if can get_type_arity name then
      failwith ("new_type: type "^name^" has already been declared")
    else the_type_constants := (name,arity)::(!the_type_constants)

(* ------------------------------------------------------------------------- *)
(* Basic type constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

  let mk_type(tyop,args) =
    let arity = try get_type_arity tyop with Failure _ ->
      failwith ("mk_type: type "^tyop^" has not been defined") in
    if arity = length args then
      Tyapp(tyop,args)
    else failwith ("mk_type: wrong number of arguments to "^tyop)

  let mk_vartype v = Tyvar(v)

(* ------------------------------------------------------------------------- *)
(* Basic type destructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let dest_type =
    function
        (Tyapp (s,ty)) -> s,ty
      | (Tyvar _) -> failwith "dest_type: type variable not a constructor"

  let dest_vartype =
    function
        (Tyapp(_,_)) -> failwith "dest_vartype: type constructor not a variable"
      | (Tyvar s) -> s

(* ------------------------------------------------------------------------- *)
(* Basic type discriminators.                                                *)
(* ------------------------------------------------------------------------- *)

  let is_type = can dest_type

  let is_vartype = can dest_vartype

(* ------------------------------------------------------------------------- *)
(* Return the type variables in a type and in a list of types.               *)
(* ------------------------------------------------------------------------- *)

  let rec tyvars =
      function
          (Tyapp(_,args)) -> itlist (union o tyvars) args []
        | (Tyvar v as tv) -> [tv]

(* ------------------------------------------------------------------------- *)
(* Substitute types for type variables.                                      *)
(*                                                                           *)
(* NB: non-variables in subst list are just ignored (a check would be        *)
(* repeated many times), as are repetitions (first possibility is taken).    *)
(* ------------------------------------------------------------------------- *)

(*Todo: Remove the  prefix to restore normal operations*)

let rec type_subst i ty =
    match ty with
      Tyapp(tycon,args) ->
          let args' = qmap (type_subst i) args in
          if args' == args then ty else Tyapp(tycon,args')
      | _ -> rev_assocd ty i ty


  let bool_ty = Tyapp("bool",[])

  let aty = Tyvar "A"

(* ------------------------------------------------------------------------- *)
(* List of term constants and their types.                                   *)
(*                                                                           *)
(* We begin with just equality (over all types). Later, the Hilbert choice   *)
(* operator is added. All other new constants are defined.                   *)
(* ------------------------------------------------------------------------- *)


  let the_term_constants =
     ref ["=",Tyapp("fun",[aty;Tyapp("fun",[aty;bool_ty])]);"TTC",Tyapp("fun",[aty;Tyapp("epsilon",[])])]

  (*Check if two quotes are equal for use in match_type*)
  let rec isQuoteSame tm tm2 = match tm,tm2 with
    | Quote(e1,t),Quote(e2,t2) -> isQuoteSame e1 e2
    | Comb(l,r),Comb(l2,r2) -> isQuoteSame l l2 && isQuoteSame r r2
    | Const(a,b),Const(c,d) | Var(a,b),Var(c,d)  -> a = c && b = d
    | Abs(a,b),Abs(c,d) -> a = c && b = d
    | Hole(a,b),Hole(c,d) -> a = c && b = d
    | _ -> false

  (*Need to move the faculties for generating variable types from preterm to here for quote conversion to work*)
  let tyv_num = ref 0;;

  let getTyv unit = let () = tyv_num := (!tyv_num + 1) in !tyv_num;;

  let proven_thms = ref [];;

  let is_proven_thm tm = exists (fun thm -> tm = (snd ((fun a -> match a with Sequent(b,c) -> (b,c) | _ -> fail()) thm))) (!proven_thms)

  let addThm tm = match tm with Sequent(asl,c) -> if (forall (fun a -> is_proven_thm a) asl) then proven_thms := tm :: !proven_thms else failwith "Unproven assumptions in theorem" | _ -> failwith "Not a theorem";;

(* ------------------------------------------------------------------------- *)
(* Return all the defined constants with generic types.                      *)
(* ------------------------------------------------------------------------- *)

  let constants() = !the_term_constants

(* ------------------------------------------------------------------------- *)
(* Gets type of constant if it succeeds.                                     *)
(* ------------------------------------------------------------------------- *)

  let get_const_type s = assoc s (!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Declare a new constant.                                                   *)
(* ------------------------------------------------------------------------- *)

  let new_constant(name,ty) =
    if can get_const_type name then
      failwith ("new_constant: constant "^name^" has already been declared")
    else the_term_constants := (name,ty)::(!the_term_constants)

(* ------------------------------------------------------------------------- *)
(* Finds the type of a term (assumes it is well-typed).                      *)
(* ------------------------------------------------------------------------- *)

  (*This is used when checking quote types match the term types as holes should always be of type epsilon - type_of returns the type of the thing inside the quote so that they can be used more easily
  in the parser*)
  let rec qcheck_type_of tm = match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match qcheck_type_of s with Tyapp("fun",[dty;rty]) -> rty | Tyapp("epsilon",[]) -> Tyapp("epsilon",[]))
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;qcheck_type_of t])
    | Quote(e,_) -> Tyapp("epsilon",[])
    | Hole(e,ty) -> ty
    | Eval(e,ty) -> ty
    | _ -> failwith "TYPE_OF: Invalid term. You should not see this error under normal use, if you do, the parser has allowed an ill formed term to be created."

  let rec type_of tm =
    match tm with
      Var(_,ty) -> ty
    | Const(_,ty) -> ty
    | Comb(s,_) -> (match type_of s with Tyapp("fun",[dty;rty]) -> rty| Tyapp("epsilon",[]) -> Tyapp("epsilon",[]))
    | Abs(Var(_,ty),t) -> Tyapp("fun",[ty;type_of t])
    | Quote(e,_) -> Tyapp("epsilon",[])
    | Hole(e,ty) -> ty
    | Eval(e,ty) -> ty
    | _ -> failwith "TYPE_OF: Invalid term. You should not see this error under normal use, if you do, the parser has allowed an ill formed term to be created."

  (*Internal function to grab the type of an applied function*)
  let fun_type_of tm = 
    let rec ftype_of trm = match trm with
    | Comb(l,_) -> ftype_of l
    | Const(n,t) | Var(n,t) when not (is_vartype t) && fst (dest_type t) = "fun" -> t  
    | _ -> failwith "Not a function"

  in

  match tm with
    | Comb(l,r) when type_of tm = Tyapp("epsilon",[]) -> ftype_of l 
    | _ -> failwith "Incomplete or mistyped function" 

    (*Checks if a term is eval-free*)
    let rec is_eval_free tm = match tm with
    | Var(_,_) -> true
    | Const(_,_) -> true
    | Comb(a,b) -> is_eval_free a && is_eval_free b
    | Abs(a,b) -> is_eval_free a && is_eval_free b
    | Quote(e,ty) -> is_eval_free e
    | Hole(e,ty) -> is_eval_free e
    | Eval(e,ty) -> false

(* ------------------------------------------------------------------------- *)
(* Primitive discriminators.                                                 *)
(* ------------------------------------------------------------------------- *)

  let is_var = function (Var(_,_)) -> true | _ -> false

  let is_const = function (Const(_,_)) -> true | _ -> false

  let is_abs = function (Abs(_,_)) -> true | _ -> false

  let is_comb = function (Comb(_,_)) -> true | _ -> false

  let is_quote = function (Quote(_,_)) -> true | _ -> false

  let dest_quote =
    function (Quote(e,ty)) when qcheck_type_of e = ty -> e | _ -> failwith "dest_quote: not a quotation or type mismatch"

  let is_hole = function (Hole(_,_)) -> true | _ -> false

  let is_eval = function (Eval(_,_)) -> true | _ -> false

  let dest_hole = 
    function (Hole(e,ty)) -> e,ty | _ -> failwith "dest_hole: not a hole"

(* ------------------------------------------------------------------------- *)
(* Primitive constructors.                                                   *)
(* ------------------------------------------------------------------------- *)

  let mk_var(v,ty) = Var(v,ty)

  let mk_const(name,theta) =
    let uty = try get_const_type name with Failure _ ->
      failwith "mk_const: not a constant name" in
    Const(name,type_subst theta uty)

  let mk_abs(bvar,bod) =
    match bvar with
      Var(_,_) -> Abs(bvar,bod)
    | _ -> failwith "mk_abs: not a variable"


  (*Local functions to simplify the logic in mk_comb*)
  let holequotecheck ty a = if is_hole a && is_quote (fst (dest_hole a)) then Pervasives.compare ty (type_of (dest_quote (fst (dest_hole a)))) = 0 else false


  (*This allows any function of type A -> epsilon - therefore it is possible for ill formed terms to be constructed. The alternative - checking through all definitions to find what a function will return and 
  verifying it's type - would be too inefficient to be feasible*)

  let holefunctioncheck a = try
  if is_hole a then let ty3 = fun_type_of (fst (dest_hole a)) in if is_vartype ty3 then false else
    if (fst (dest_type ty3)) = "fun" && (hd (tl (snd(dest_type ty3)))) = Tyapp("epsilon",[]) then true else false 
  else false 
  with Failure _ -> false

  let mk_comb(f,a) =
    match type_of f with
      Tyapp("fun",[ty;ty2]) when Pervasives.compare ty (type_of a) = 0 || holequotecheck ty a || holefunctioncheck a
        -> Comb(f,a)
    | _ -> failwith "mk_comb: types do not agree"

  let mk_quote t = if is_eval_free t then Quote(t,qcheck_type_of t) else failwith "Can only quote eval-free terms"

  let mk_hole t = if type_of t = Tyapp("epsilon",[]) then Hole(t,type_of t) else failwith "Not an epsilon term"

  let mk_eval (e,ty) = Eval(e,ty)

(* ------------------------------------------------------------------------- *)
(* Primitive destructors.                                                    *)
(* ------------------------------------------------------------------------- *)

  let dest_var =
    function (Var(s,ty)) -> s,ty | _ -> failwith "dest_var: not a variable"

  let dest_const =
    function (Const(s,ty)) -> s,ty | _ -> failwith "dest_const: not a constant"

  let dest_comb =
    function (Comb(f,x)) -> f,x | _ -> failwith "dest_comb: not a combination"

  let dest_abs =
    function (Abs(v,b)) -> v,b | _ -> failwith "dest_abs: not an abstraction"

  let dest_eval = 
    function (Eval(e,ty)) -> e,ty | _ -> failwith "dest_eval: not an eval"

(* ------------------------------------------------------------------------- *)
(* Finds the variables free in a term (list of terms).                       *)
(* ------------------------------------------------------------------------- *)

  let rec frees tm =
    let rec qfrees tm = match tm with
      | Hole(e,ty) -> frees e
      | Comb(l,r) -> union (qfrees l) (qfrees r)
      | Quote(e,ty) -> qfrees e
      | _ -> []
    
    in

    match tm with
      Var(_,_) -> [tm]
    | Const(_,_) -> []
    | Abs(bv,bod) -> subtract (frees bod) [bv]
    | Comb(s,t) -> union (frees s) (frees t)
    | Quote(e,ty) -> qfrees e
    | Hole(e,ty) -> frees e
    | Eval(e,ty) -> frees e

  let freesl tml = itlist (union o frees) tml []

(* ------------------------------------------------------------------------- *)
(* Whether all free variables in a term appear in a list.                    *)
(* ------------------------------------------------------------------------- *)

  let rec freesin acc tm =
    let rec qfreesin acc tm = match tm with
      | Hole(e,ty) -> freesin acc e
      | Comb(l,r) -> qfreesin acc l && qfreesin acc r
      | Quote(e,ty) -> qfreesin acc e
      | _ -> true

    in

    match tm with
      Var(_,_) -> mem tm acc
    | Const(_,_) -> true
    | Abs(bv,bod) -> freesin (bv::acc) bod
    | Comb(s,t) -> freesin acc s && freesin acc t
    | Quote(e,_) -> qfreesin acc e
    | Hole(e,_) -> freesin acc e
    | Eval(e,_) -> freesin acc e

(* ------------------------------------------------------------------------- *)
(* Whether a variable (or constant in fact) is free in a term.               *)
(* ------------------------------------------------------------------------- *)

  let rec vfree_in v tm =
    let rec qvfree_in v tm = match tm with
      | Hole(e,ty) -> vfree_in v e
      | Comb(l,r) -> qvfree_in v l || qvfree_in v r
      | Quote(e,ty) -> qvfree_in v e
      | _ -> false

    in

    match tm with
      Abs(bv,bod) -> v <> bv && vfree_in v bod
    | Comb(s,t) -> vfree_in v s || vfree_in v t
    | Quote(e,_) -> qvfree_in v e
    | Hole(e,ty) -> qvfree_in v e
    | Eval(e,ty) -> vfree_in v e
    | _ -> Pervasives.compare tm v = 0

(* ------------------------------------------------------------------------- *)
(* Finds the type variables (free) in a term.                                *)
(* ------------------------------------------------------------------------- *)

  let rec type_vars_in_term tm =
    let rec qtype_vars_in_term tm = match tm with
      | Hole(e,_) -> type_vars_in_term e
      | Quote(e,_) -> qtype_vars_in_term e
      | Comb(l,r) -> union (qtype_vars_in_term l) (qtype_vars_in_term r)
      | _ -> tyvars (Tyapp ("epsilon",[]))

    in

    match tm with
      Var(_,ty)        -> tyvars ty
    | Const(_,ty)      -> tyvars ty
    | Comb(s,t)        -> union (type_vars_in_term s) (type_vars_in_term t)
    | Abs(Var(_,ty),t) -> union (tyvars ty) (type_vars_in_term t)
    | Quote(_,_)       -> tyvars (Tyapp ("epsilon",[]))
    | Hole(e,_)        -> type_vars_in_term e
    | Eval(e,ty)        -> union (type_vars_in_term e) (tyvars ty)
    | _                -> failwith "TYPE_VARS_IN_TERM: Invalid type."

(* ------------------------------------------------------------------------- *)
(* For name-carrying syntax, we need this early.                             *)
(* ------------------------------------------------------------------------- *)

  let rec variant avoid v =
    if not(exists (vfree_in v) avoid) then v else
    match v with
      Var(s,ty) -> variant avoid (Var(s^"'",ty))
    | _ -> failwith "variant: not a variable"

(* ------------------------------------------------------------------------- *)
(* Substitution primitive (substitution for variables only!)                 *)
(* ------------------------------------------------------------------------- *)

  (*Checks is a term is free in terms of another term*)
 
  (*Handles variable substitution for evaluations*)
    (* | (a,b) :: rest when a = b -> mkNewEval rest tm *)
  let rec mkNewEval sL tm =
    let rec VarInTerm vr trm = 
        let rec Q_VarInTerm vr trm = match trm with
          | Hole(t,ty) -> VarInTerm vr trm
          | Quote(t,ty) -> Q_VarInTerm vr trm
          | Comb(a,b) -> (Q_VarInTerm vr trm) || (Q_VarInTerm vr trm)
          | _ -> false
        in
      match trm with
      | Var (_,_) -> (dest_var vr) = (dest_var trm)
      | Const (_,_) -> false
      | Comb (a,b) -> (VarInTerm vr a) || (VarInTerm vr b)
      | Abs (a,b) -> not ((dest_var vr) = (dest_var a)) && VarInTerm vr b
      | Quote (e,ty) -> Q_VarInTerm vr e
      | Hole (e,ty) -> Q_VarInTerm vr e
      | Eval(e,ty) -> VarInTerm vr e
      in
    match sL with
    | (a,b) :: rest when a = b -> mkNewEval rest tm
    | (a,b) :: rest when not (VarInTerm b tm) -> mkNewEval rest tm
    | (a,b) :: rest -> Comb(Abs(b,(mkNewEval rest tm)),a)
    | [] -> tm 
  (*Removes all abstractions*) 
  let rec int_no_abs tm = match tm with
  | Abs(a,b) -> int_no_abs b
  | _ -> tm


  let rec makeAbsSubst sl tm = 
    let com = dest_comb tm in
    let a = snd com in
    let abs = dest_abs (fst com) in
    let var = fst abs in
    let e = fst (dest_eval (snd abs)) in
    match sl with
    | (a,b) :: rest when a = b -> makeAbsSubst rest tm
    | (a,b) :: rest ->  if (vfree_in var (Comb(Abs(var,e),a))) then Comb(Abs(b,(makeAbsSubst rest tm)),a) else (makeAbsSubst rest (Eval(Comb(Abs(var,e),a),type_of ((Comb(Abs(var,e),a))))))
    | [] -> tm

    (*Constructs an effectiveIn expression for the given variable in the given term*)
  let effectiveIn var tm = 
    (*This function checks that the variable name  does not exist in the term - if it does, it adds ' until a valid name is found*)
    let rec unusedVarName var tm root = let dName = fst (dest_var var) in
      match tm with
      | Var(a,b) -> if a = dName then (unusedVarName (mk_var ((dName ^ "'"),type_of var)) root root) else dName
      | Const(_,_) -> dName
      | Comb(a,b) -> let aN = (unusedVarName var a root) and bN = (unusedVarName var b root) in if aN <> dName then aN else if bN <> dName then bN else dName
      | Abs(a,b) -> let aN = (unusedVarName var a root) and bN = (unusedVarName var b root) in if aN <> dName then aN else if bN <> dName then bN else dName
      | Quote(e,ty) -> unusedVarName var e root
      | Hole(e,ty) -> unusedVarName var e root
      | Eval(e,ty) -> unusedVarName var e root
    in
    (*Creates a y variable that will not clash with anything inside the term*)
    if not (is_var var) then failwith "effectiveIn: First argument must be a variable" else
    let vN,vT = dest_var var in 
    let y = mk_var(unusedVarName (Var("y",Tyvar "A")) tm tm,vT) in
    (*Now assembles the term using HOL's constructors*)
    let subTerm = mk_comb(mk_abs(var,tm),y) in
    let eqTerm = mk_comb(mk_comb(Const("=",(Tyapp ("fun",[(type_of subTerm);(Tyapp ("fun",[(type_of subTerm);Tyapp ("bool",[])]))]))),subTerm),tm) in
    (*At this point, have (\x. B)y = B, want to negate this*)
    let neqTerm = mk_comb(mk_const("~",[]),eqTerm) in
    let toExst = mk_abs(y,neqTerm) in
    mk_comb(mk_const("?",[type_of y,Tyvar "A"]),toExst);;


  let rec stackAbs l tm = match l with
  | (a,b) :: rest when List.length l > 1 -> Comb(Abs(b,(stackAbs rest tm)),a)
  | [(a,b)] -> Comb(Abs(b,tm),a)
  | _ -> failwith "Bad substitution list"

      (*Function to handle substitutions in holes in quotations*)
  let rec qsubst ilist tm =

    let rec vsubst ilist tm =
      match tm with
      | Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Quote(e,ty) -> let newquo = qsubst ilist e in Quote(newquo,qcheck_type_of newquo)
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
     | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                  if ilist' = [] then tm else
                  let s' = vsubst ilist' s in
                  if s' == s then tm else
                  (* There are no variable captures. *)
                  if forall (fun (t,x) ->
                    (*Todo: Fix this to properly use is_effective_in*)
                  ((is_eval_free t && (not (vfree_in v t))) ||
                  is_proven_thm (mk_comb((Const("~",(Tyapp ("fun",[(Tyapp ("bool",[]));(Tyapp ("bool",[]))])))),(effectiveIn v t))) ||
                  (is_eval_free s && (not (vfree_in x s))) ||
                  is_proven_thm (mk_comb((Const("~",(Tyapp ("fun",[(Tyapp ("bool",[]));(Tyapp ("bool",[]))])))),(effectiveIn x s))))) ilist'
                  then Abs(v,s') else
                  (* There is an unresolvable subsitution. *)
                  if not (is_eval_free s) ||
                     exists (fun (t,x) -> not (is_eval_free t)) ilist'
                  then failwith "Possible variable capture in eval detected"
                  (* All substitutions are resolvable. *)
                  else let v' = variant [s'] v in
                       Abs(v',vsubst ((v',v)::ilist') s) in
    match tm with
    | Quote(e,ty) -> let newquo = qsubst ilist e in Quote(newquo,qcheck_type_of newquo)
    | Comb(s,t) -> let s' = qsubst ilist s and t' = qsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
    | Hole(e,ty) -> Hole(vsubst ilist e,ty)
    | _ -> tm 

  let vsubst =

    let rec vsubst ilist tm =
      match tm with
      | Var(_,_) -> rev_assocd tm ilist tm
      | Const(_,_) -> tm
      | Quote(e,ty) -> let newquo = qsubst ilist e in Quote(newquo,qcheck_type_of newquo)
      | Eval(e,ty) -> mkNewEval ilist tm
      | Comb(s,t) -> let s' = vsubst ilist s and t' = vsubst ilist t in
                     if s' == s && t' == t then tm else Comb(s',t')
     | Abs(v,s) -> let ilist' = filter (fun (t,x) -> x <> v) ilist in
                  if ilist' = [] then tm else
                  let s' = vsubst ilist' s in
                  if s' == s then tm else
                  (* There are no variable captures. *)
                  if forall (fun (t,x) ->
                    (*Todo: Fix this to properly use is_effective_in*)
                  ((is_eval_free t && (not (vfree_in v t))) ||
                  is_proven_thm (mk_comb((Const("~",(Tyapp ("fun",[(Tyapp ("bool",[]));(Tyapp ("bool",[]))])))),(effectiveIn v t))) ||
                  (is_eval_free s && (not (vfree_in x s))) ||
                  is_proven_thm (mk_comb((Const("~",(Tyapp ("fun",[(Tyapp ("bool",[]));(Tyapp ("bool",[]))])))),(effectiveIn x s))))) ilist'
                  then Abs(v,s') else
                  (* There is an unresolvable subsitution. *)
                  if not (is_eval_free s) ||
                     exists (fun (t,x) -> not (is_eval_free t)) ilist'
                  then failwith "Possible variable capture in eval detected"
                  (* All substitutions are resolvable. *)
                  else let v' = variant [s'] v in
                       Abs(v',vsubst ((v',v)::ilist') s) in
    fun theta ->
      if theta = [] then (fun tm -> tm) else
      if forall (function (t,Var(_,y)) -> Pervasives.compare (type_of t) y = 0
                        | _ -> false) theta
      then vsubst theta else failwith "vsubst: Bad substitution list"

(* ------------------------------------------------------------------------- *)
(* Type instantiation primitive.                                             *)
(* ------------------------------------------------------------------------- *)

  exception Clash of term

  let rec qinst =

   let rec oinst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Quote(e,_)    -> let newquo = (qinst tyin e) in Quote(newquo,(type_of newquo)) 
      | Comb(f,x)   -> let f' = oinst env tyin f and x' = oinst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> let y' = oinst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = oinst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (oinst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       oinst env tyin (Abs(z,vsubst[z,y] t)) in

    let rec qinst env tyin tm =
       match tm with
        | Comb(l,r) -> Comb(qinst env tyin l, qinst env tyin r)
        | Hole(e,ty) -> Hole(oinst env tyin e,ty)
        | Quote(e,ty) -> Quote(qinst env tyin e,ty)
        | _ -> tm
    in

    fun tyin -> if tyin = [] then fun tm -> tm else qinst [] tyin



  let inst =

    let rec inst env tyin tm =
      match tm with
        Var(n,ty)   -> let ty' = type_subst tyin ty in
                       let tm' = if ty' == ty then tm else Var(n,ty') in
                       if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                       then tm'
                       else raise (Clash tm')
      | Const(c,ty) -> let ty' = type_subst tyin ty in
                       if ty' == ty then tm else Const(c,ty')
      | Quote(e,_)-> let newquo = (qinst tyin e) in Quote(newquo,(qcheck_type_of newquo))
      | Comb(f,x)   -> let f' = inst env tyin f and x' = inst env tyin x in
                       if f' == f && x' == x then tm else Comb(f',x')
      | Abs(y,t)    -> (let y' = inst [] tyin y in
                       let env' = (y,y')::env in
                       try let t' = inst env' tyin t in
                           if y' == y && t' == t then tm else Abs(y',t')
                       with (Clash(w') as ex) ->
                       if w' <> y' then raise ex else
                       let ifrees = map (inst [] tyin) (frees t) in
                       let y'' = variant ifrees y' in
                       let z = Var(fst(dest_var y''),snd(dest_var y)) in
                       inst env tyin (Abs(z,vsubst[z,y] t))) 
      | Hole(e,ty) -> Hole(inst env tyin e,ty)
      | Eval(e,ty) -> Eval(inst env tyin e,ty)

      in

    fun tyin -> if tyin = [] then fun tm -> tm else inst [] tyin

(* ------------------------------------------------------------------------- *)
(* A few bits of general derived syntax.                                     *)
(* ------------------------------------------------------------------------- *)

  let rator tm =
    match tm with
      Comb(l,r) -> l
    | _ -> failwith "rator: Not a combination"

  let rand tm =
    match tm with
      Comb(l,r) -> r
    | _ -> failwith "rand: Not a combination"

(* ------------------------------------------------------------------------- *)
(* Syntax operations for equations.                                          *)
(* ------------------------------------------------------------------------- *)

  let safe_mk_eq l r =
    let ty = type_of l in
    Comb(Comb(Const("=",Tyapp("fun",[ty;Tyapp("fun",[ty;bool_ty])])),l),r)

  let dest_eq tm =
    match tm with
      Comb(Comb(Const("=",_),l),r) -> l,r
    | _ -> failwith "dest_eq"

(* ------------------------------------------------------------------------- *)
(* Useful to have term union modulo alpha-conversion for assumption lists.   *)
(* ------------------------------------------------------------------------- *)



  let rec ordav env x1 x2 =
    match env with
      [] -> Pervasives.compare x1 x2
    | (t1,t2)::oenv -> if Pervasives.compare x1 t1 = 0
                       then if Pervasives.compare x2 t2 = 0
                            then 0 else -1
                       else if Pervasives.compare x2 t2 = 0 then 1
                       else ordav oenv x1 x2

  let rec orda env tm1 tm2 =
    if tm1 == tm2 && forall (fun (x,y) -> x = y) env then 0 else
    match (tm1,tm2) with
      Var(x1,ty1),Var(x2,ty2) -> ordav env tm1 tm2
    | Const(x1,ty1),Const(x2,ty2) -> Pervasives.compare tm1 tm2
    | Comb(s1,t1),Comb(s2,t2) ->
          let c = orda env s1 s2 in if c <> 0 then c else orda env t1 t2
    | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          let c = Pervasives.compare ty1 ty2 in
          if c <> 0 then c else orda ((x1,x2)::env) t1 t2
    | Quote(e1,_),Quote(e2,_) -> orda env e1 e2
    | Hole(e1,_),Hole(e2,_) -> orda env e1 e2
    | Eval(e1,t1),Eval(e2,t2) when t1 = t2 -> orda env e1 e2 
    | Const(_,_),_ -> -1
    | _,Const(_,_) -> 1
    | Var(_,_),_ -> -1
    | _,Var(_,_) -> 1
    | Comb(_,_),_ -> -1
    | _,Comb(_,_) -> 1
    | Quote(_,_),_ -> -1
    | _,Quote(_,_) -> 1  
    | Hole(_,_),_ -> -1
    | _,Hole(_,_) -> 1
    | Eval(_,_),_ -> -1
    | _,Eval(_,_) -> 1

  let alphaorder = orda []

  let rec term_union l1 l2 =
    match (l1,l2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                         if c = 0 then h1::(term_union t1 t2)
                         else if c < 0 then h1::(term_union t1 l2)
                         else h2::(term_union l1 t2)

  let rec term_remove t l =
    match l with
      s::ss -> let c = alphaorder t s in
               if c > 0 then
                 let ss' = term_remove t ss in
                 if ss' == ss then l else s::ss'
               else if c = 0 then ss else l
    | [] -> l

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if h' == h && t' == t then l else term_union [h'] t'
    | [] -> l

(* ------------------------------------------------------------------------- *)
(* Basic theorem destructors.                                                *)
(* ------------------------------------------------------------------------- *)

  let dest_thm (Sequent(asl,c)) = (asl,c)

  let hyp (Sequent(asl,c)) = asl

  let concl (Sequent(asl,c)) = c

(* ------------------------------------------------------------------------- *)
(* Basic equality properties; TRANS is derivable but included for efficiency *)
(* ------------------------------------------------------------------------- *)

  let REFL tm =
    Sequent([],safe_mk_eq tm tm)

  let TRANS (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    match (c1,c2) with
      Comb((Comb(Const("=",_),_) as eql),m1),Comb(Comb(Const("=",_),m2),r)
        when alphaorder m1 m2 = 0 -> Sequent(term_union asl1 asl2,Comb(eql,r))
    | _ -> failwith "TRANS"

(* ------------------------------------------------------------------------- *)
(* Congruence properties of equality.                                        *)
(* ------------------------------------------------------------------------- *)

  let MK_COMB(Sequent(asl1,c1),Sequent(asl2,c2)) =
     match (c1,c2) with
       Comb(Comb(Const("=",_),l1),r1),Comb(Comb(Const("=",_),l2),r2) ->
        (match type_of r1 with
           Tyapp("fun",[ty;_]) when Pervasives.compare ty (type_of r2) = 0
             -> Sequent(term_union asl1 asl2,
                        safe_mk_eq (Comb(l1,l2)) (Comb(r1,r2)))
         | _ -> failwith "MK_COMB: types do not agree")
     | _ -> failwith "MK_COMB: not both equations"

  let ABS v (Sequent(asl,c)) =
    match (v,c) with
      Var(_,_),Comb(Comb(Const("=",_),l),r) when not(exists (vfree_in v) asl)
         -> Sequent(asl,safe_mk_eq (Abs(v,l)) (Abs(v,r)))
    | _ -> failwith "ABS";;

(* ------------------------------------------------------------------------- *)
(* Trivial case of lambda calculus beta-conversion.                          *)
(* ------------------------------------------------------------------------- *)

  let rec BETA tm =
    (*
    Newvar - what to replace oldvar with
    Oldvar - bound variable to replace
    Tm - term to perform replacement in
    shouldEvalFree - Whether or not the term is supposed to be eval-free. Causes exceptions to be thrown if an Eval is encountered in an eval-free term.
    *)
    let rec betarep newvar oldvar tm shouldEvalFree = match tm with
      | Comb(a,b) -> Comb(betarep newvar oldvar a shouldEvalFree, betarep newvar oldvar b shouldEvalFree)
      | Abs(a,b) -> Abs(betarep newvar oldvar a shouldEvalFree, betarep newvar oldvar b shouldEvalFree)
      | Var(a,b) -> if (dest_var tm) = (dest_var oldvar) then newvar else tm
      | Quote(a,b) -> Quote(a,b)
      | Hole(a,b) -> Hole(betarep newvar oldvar a shouldEvalFree,b)
      | Eval(a,b) -> if shouldEvalFree then failwith "BETA: Unexpected eval in what should be an eval free term" else Comb(Abs(oldvar,tm),newvar)
      | Const(a,b) -> Const(a,b)
    in(*

    if not (is_eval_free tm) then (
        (
        let rec VarInTerm vr trm = 
        let rec Q_VarInTerm vr trm = match trm with
          | Hole(t,ty) -> VarInTerm vr trm
          | Quote(t,ty) -> Q_VarInTerm vr trm
          | Comb(a,b) -> (Q_VarInTerm vr trm) || (Q_VarInTerm vr trm)
          | _ -> false
        in
      match trm with
      | Var (_,_) -> (dest_var vr) = (dest_var trm)
      | Const (_,_) -> false
      | Comb (a,b) -> (VarInTerm vr a) || (VarInTerm vr b)
      | Abs (a,b) -> not ((dest_var vr) = (dest_var a)) && VarInTerm vr b
      | Quote (e,ty) -> Q_VarInTerm vr e
      | Hole (e,ty) -> Q_VarInTerm vr e
      | Eval(e,ty) -> VarInTerm vr e
      in
        match tm with
        (*
        (*Instance of B11.1, can cancel out the beta conversion automatically across the entire term*)
        | Comb(Abs(a,b),c) when a = c -> Sequent([], safe_mk_eq tm b)
        (*There's no evals in the term substitution actually takes place in, so it can proceed as normal*)
        | Comb(Abs(a,b),c) when (is_eval_free b) && (is_eval_free a) -> Sequent([], safe_mk_eq tm (betarep c a b true))
        (*There is an eval in b but b itself is not JUST an eval - need to bring the eval into the term*)
        | Comb(Abs(a,b),c) when not (is_eval b) -> Sequent([], safe_mk_eq tm (betarep c a b false))
        (*A simplifcation of B11.2 - if the variable to beta reduce does not appear anywhere inside the term, it is clearly not free in the term, giving us eval (\x. y) z, but, as previously established,
         x does not appear in y, so we are able to remove the entire reduction. *)
        | Comb(Abs(a,b),c) when not (VarInTerm a b) -> Sequent([], safe_mk_eq tm b)
        (*Everything else*)
      *)
        | _ -> failwith "BETA: Not eval free"
        )
    ) else
  *)
  let rec VarInTerm vr trm = 
        let rec Q_VarInTerm vr trm = match trm with
          | Hole(t,ty) -> VarInTerm vr t
          | Quote(t,ty) -> Q_VarInTerm vr t
          | Comb(a,b) -> (Q_VarInTerm vr a) || (Q_VarInTerm vr b)
          | _ -> false
        in
      match trm with
      | Var (_,_) -> (dest_var vr) = (dest_var trm)
      | Const (_,_) -> false
      | Comb (a,b) -> (VarInTerm vr a) || (VarInTerm vr b)
      | Abs (a,b) -> not ((dest_var vr) = (dest_var a)) && VarInTerm vr b
      | Quote (e,ty) -> Q_VarInTerm vr e
      | Hole (e,ty) -> Q_VarInTerm vr e
      | Eval(e,ty) -> VarInTerm vr e
      in
    match tm with
    |  Comb(Abs(v,Eval(e,ty)),b) when not (vfree_in v (Comb(Abs(v,e),b))) -> Sequent([],safe_mk_eq tm (Eval(Comb(Abs(v,e),b),ty)))
    |  Comb(Abs(v,bod),arg) when Pervasives.compare arg v = 0
        -> Sequent([],safe_mk_eq tm bod)
    |  Comb(Abs(v,bod),arg) when not (VarInTerm v bod) -> Sequent([],safe_mk_eq tm bod)
    | _ -> failwith "BETA: not a trivial beta-redex"

(* ------------------------------------------------------------------------- *)
(* Rules connected with deduction.                                           *)
(* ------------------------------------------------------------------------- *)

  let ASSUME tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then Sequent([tm],tm)
    else failwith "ASSUME: not a proposition"

  let EQ_MP (Sequent(asl1,eq)) (Sequent(asl2,c)) =
    match eq with
      Comb(Comb(Const("=",_),l),r) when alphaorder l c = 0
        -> Sequent(term_union asl1 asl2,r)
    | _ -> failwith "EQ_MP"

  let DEDUCT_ANTISYM_RULE (Sequent(asl1,c1)) (Sequent(asl2,c2)) =
    let asl1' = term_remove c2 asl1 and asl2' = term_remove c1 asl2 in
    Sequent(term_union asl1' asl2',safe_mk_eq c1 c2)

(* ------------------------------------------------------------------------- *)
(* Type and term instantiation.                                              *)
(* ------------------------------------------------------------------------- *)

  let INST_TYPE theta (Sequent(asl,c)) =
    let inst_fn = inst theta in
    Sequent(term_image inst_fn asl,inst_fn c)

  let INST theta (Sequent(asl,c)) =
    let inst_fun = vsubst theta in
    Sequent(term_image inst_fun asl,inst_fun c)


  let rec varInAsl asl = match asl with
  | a :: rest -> (is_var (fst (dest_eq (a)))) || (varInAsl rest)
  | [] -> false 

  (*Causing CONV_TAC error?*)
  let rec makeVarToSub asl tm = match asl with
  | a :: rest -> let l,r = dest_eq a in
  if is_var l then
  makeVarToSub rest (Comb(Abs(l,tm),r))
  else makeVarToSub rest tm
  | [] -> tm

  (*Conversion functions to handle hole rewrites on a lower level*)
  let rec QSUB_CONV (conv:term->thm) tm nConv = match tm with
    | Comb(l,r) -> let ls = (try QSUB_CONV conv l nConv with Failure _ -> REFL l) in
                   let rs = (try QSUB_CONV conv r nConv with Failure _ -> REFL r) in
                   let lasl,cl = dest_thm ls in
                   let rasl,cr = dest_thm rs in
                   let clls,clrs = dest_eq cl in
                   let crls,crrs = dest_eq cr in
                   if clls = clrs && crls = crrs then failwith "QSUB_CONV" else 
                   let convedComb = Comb(clrs,crrs) in
                   Sequent ((lasl @ rasl),safe_mk_eq tm convedComb)
    | Quote(e,ty) -> let newThm = (QSUB_CONV conv e nConv) in 
                     let asl,c = dest_thm newThm in
                     let ls,rs = dest_eq c in
                     Sequent (asl,safe_mk_eq (mk_quote ls) (mk_quote rs))
    | Hole(e,ty) -> let newThm = (nConv conv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    Sequent (asl,safe_mk_eq (mk_hole ls) (mk_hole rs))
    (*This should not cause any issues on the assumption that a quote will never contain an eval inside it*)
    | Eval(e,ty) -> if not (varInAsl (fst (dest_thm (conv e)))) then
                    let newThm = (nConv conv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    (*The middle evaluates to nothing, check if the term itself can be switched out*)
                    if ls = rs then
                    let newThm = (nConv conv tm) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in 
                    Sequent (asl,safe_mk_eq ls rs)
                    else
                    Sequent (asl,safe_mk_eq (mk_eval (ls,ty)) (mk_eval (rs,ty)))
                    else
                    (*What to do when there is a variable substitution*)
                    let asl, c = dest_thm (nConv conv e) in
                    let ls,rs = dest_eq c in
                    Sequent (asl, safe_mk_eq (mk_eval (ls,type_of ls)) (mk_eval (rs,type_of rs)))
    | _ -> failwith "QSUB_CONV"

  (*Conversion function to handle hole rewrites on a lower level*)
  let rec QBETA_CONV tm nConv = match tm with
    | Comb(l,r) -> let ls = (try QBETA_CONV l nConv with Failure _ -> REFL l) in
                   let rs = (try QBETA_CONV r nConv with Failure _ -> REFL r) in
                   let lasl,cl = dest_thm ls in
                   let rasl,cr = dest_thm ls in
                   let clls,clrs = dest_eq cl in
                   let crls,crrs = dest_eq cr in
                   if clls = clrs && crls = crrs then failwith "QBETA_CONV" else 
                   let convedComb = Comb(snd(dest_eq(concl ls)),snd(dest_eq(concl rs))) in
                   Sequent ((lasl @ rasl),safe_mk_eq tm convedComb)
    | Quote(e,ty) -> let newThm = (QBETA_CONV e nConv) in 
                     let asl,c = dest_thm newThm in
                     let ls,rs = dest_eq c in
                     Sequent (asl,safe_mk_eq (mk_quote ls) (mk_quote rs))
    | Hole(e,ty) -> let newThm = (nConv e) in
                    let asl,c = dest_thm newThm in
                    let ls,rs = dest_eq c in
                    Sequent (asl,safe_mk_eq (mk_hole ls) (mk_hole rs))
    | _ -> failwith "QBETA_CONV"



(* ------------------------------------------------------------------------- *)
(* Quotation handling.                                                       *)
(* ------------------------------------------------------------------------- *)

(*First a bunch of definitions normally defined later during HOL's startup process must be defined*)
(*The purpose of all these is to implement an early version of mk_string so that epsilon's type types may be constructed*)
  let makeConstructedType name list = (Tyapp (name,list));;
  let makeBasicType name = makeConstructedType name [];;
  let makeFalse = Const("F",(makeBasicType "bool"));;
  let makeTrue = Const("T",(makeBasicType "bool"));;
  (*This makes a function called ASCII of type bool->bool->bool->bool->bool->bool->bool->bool->char*)
  let makeAscii = Const("ASCII",(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [(makeBasicType "bool");(makeConstructedType "fun" [
(makeBasicType "bool");(makeBasicType "char")])])])])
])])])]));;
  (*This makes a function called CONS of type char -> (list)char -> list(char)*)
  let makeCONS = Const("CONS",makeConstructedType "fun" [makeBasicType "char"; makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeConstructedType "list" [makeBasicType "char"]]]);;
  
  let numToBool = function
    | 1 -> makeTrue
    | 0 -> makeFalse
    | _ -> failwith "Cannot convert this number to a boolean value"

(*Converts a char value to a combination of T's and F's representing the binary form of it's ASCII value (HOL stores it this way)*)

  let rec charToHOL c depth = if depth < 8 then Comb((charToHOL (c / 2) (depth + 1)),(numToBool (c mod 2)))
  else Comb(makeAscii,(numToBool (c mod 2)));;

(*Takes an exploded string and turns it into a HOL string*)
  let rec tmp_mk_string = function
    | [] -> Const("NIL",makeConstructedType "list" [makeBasicType "char"])
    | a :: rest -> Comb(Comb(makeCONS,(charToHOL (Char.code (a.[0])) 1)),(tmp_mk_string rest));;

(*Takes a list of eight 1s and 0s and reads it as a binary number to return a decimal number*)
 let binToDec l p = 
  let rec innerConv l p = 
    match l with
    | [] -> 0
    | a :: rest -> (int_of_float ((float_of_int a) *. (2. ** (float_of_int p)))) + (innerConv rest (p - 1))
  in
 if List.length l = 8 then innerConv l p else failwith "Cannot convert non 8-bit number";;

(*Reads a character back as HOL input*)
  let translateChar = function
    | Comb(Comb(Comb(Comb(Comb(Comb(Comb(Comb(Const("ASCII",_),b1),b2),b3),b4),b5),b6),b7),b8) -> String.make 1 (Char.chr (binToDec (List.map (fun a -> let b = fst (dest_const a) in if b = "T" then 1 else 0) [b1;b2;b3;b4;b5;b6;b7;b8]) 7))
    | _ -> failwith "Not an HOL character";;

(*Takes a string in HOL's list format and turns it back into an Ocaml string*)
  let rec readStringList = function
    | Comb(Comb(Const("CONS",_),str),next) -> translateChar str :: (readStringList next)
    | Const("NIL",_) -> []
    | _ -> failwith "Not a valid string";;

  (*Need a temporary implementation of mk_string and related functions*)

  (*Helper functions to make vital functions more readable*)
  let makeHolFunction a b = Tyapp("fun",[a;b]);;
  let makeHolType a b = Tyapp(a,b)
  let makeGenericComb constName ty firstArg secondArg = Comb(Comb(Const(constName,ty),firstArg),secondArg);;
  let makeQuoVarComb a b = makeGenericComb "QuoVar" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "epsilon" [])) ) (tmp_mk_string (explode a)) b;;
  let makeQuoConstComb a b = makeGenericComb "QuoConst" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "epsilon" [])) ) (tmp_mk_string (explode a)) b;;
  let makeAppComb a b = makeGenericComb "App" (makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))) a b;;
  let makeAbsComb a b = makeGenericComb "Abs" (makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))) a b;;
  let makeTyVarComb a = Comb(Const("TyVar",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyBaseComb a  = Comb(Const("TyBase",makeConstructedType "fun" [makeConstructedType "list" [makeBasicType "char"];makeBasicType "type"]),(tmp_mk_string (explode a)));;
  let makeTyMonoConsComb a b = makeGenericComb "TyMonoCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolType "type" []))) (tmp_mk_string (explode a)) b;;
  let makeTyBiConsComb a b c= Comb((makeGenericComb "TyBiCons" (makeHolFunction (makeHolType "list" [makeHolType "char" []]) (makeHolFunction (makeHolType "type" []) (makeHolFunction (makeHolType "type" []) (makeHolType "type" [])))) (tmp_mk_string (explode a)) b),c);;
  let makeFunComb a b = makeTyBiConsComb "fun" a b;;
  let makeQuoComb a = Comb(Const("Quo",(makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))),a);;

  let rec matchType ty = 
      if (is_vartype ty) then makeTyVarComb (dest_vartype ty) else
        let a,b = (dest_type ty) in
        match length b with
          | 0 -> makeTyBaseComb a
          | 1 -> makeTyMonoConsComb a (matchType (hd b))
          | 2 -> makeTyBiConsComb a (matchType (hd b)) (matchType (hd (tl b)))
          | _ -> failwith "This is not a valid type";;

  let rec revTypeMatch = function
      |  Comb(Const("TyVar",_),tName) -> Tyapp ((implode (readStringList tName)),[])
      |  Comb(Const("TyBase",_),tName) -> Tyapp((implode (readStringList tName)),[])
      |  Comb(Comb(Const("TyMonoCons",_),tName),sType) -> Tyapp ((implode (readStringList tName)),[revTypeMatch sType])
      |  Comb(Comb(Comb(Const("TyBiCons",_),tName),sType),tType) -> Tyapp ((implode (readStringList tName)),[revTypeMatch sType;revTypeMatch tType])
      | _ -> failwith "Invalid type";;

  (*Currently in development - will always return False for now for testing purposes*)
  let rec termToConstruction = function
      |  Const(cName,cType) -> makeQuoConstComb cName (matchType cType)
      |  Var(vName,vType) -> makeQuoVarComb vName (matchType vType)
      |  Comb(exp1, exp2) -> makeAppComb (termToConstruction exp1) (termToConstruction exp2)
      |  Abs(exp1, exp2) -> makeAbsComb (termToConstruction exp1) (termToConstruction exp2)
      |  Quote(e,t) when type_of e = t -> makeQuoComb (termToConstruction e)
      |  Hole(e,t) -> e
      |  _ -> failwith "Malformed term cannot be made into a construction"

  let rec constructionToTerm = function
      | Comb(Comb(Const("QuoConst",_),strList),tyConv) -> Const(implode (readStringList strList),revTypeMatch tyConv)
      | Comb(Comb(Const("QuoVar",_),strList),tyConv) -> Var(implode (readStringList strList),revTypeMatch tyConv)
      | Comb(Comb(Const("App",_),t1),t2) -> Comb(constructionToTerm t1,constructionToTerm t2)
      | Comb(Comb(Const("Abs",_),t1),t2) -> Abs(constructionToTerm t1,constructionToTerm t2)
      | Comb(Const("Quo",_),t) -> let ct = constructionToTerm t in Quote(ct,type_of ct)
      | other when type_of(other) = Tyapp("epsilon",[]) -> Hole(other,type_of other)
      | _ -> failwith "constructionToTerm"

  let TERM_TO_CONSTRUCTION tm = match tm with
      |  Quote(exp,t) when type_of exp = t -> Sequent([],safe_mk_eq tm (termToConstruction exp))
      |  Quote(_,_) -> failwith "TERM_TO_CONSTRUCTION: BAD QUOTE"
      | _ -> failwith "TERM_TO_CONSTRUCTION"
  
  let CONSTRUCTION_TO_TERM tm = try Sequent([],safe_mk_eq tm (mk_quote (constructionToTerm tm))) with Failure _ -> failwith "CONSTRUCTION_TO_TERM"


  (*These conversion functions can be used on their own but mainly will be used to construct tactics. They will search through a term for the first applicable instance and return the result of applying
  the relevant function to it*)

  let rec TERM_TO_CONSTRUCTION_CONV tm = match tm with
    | Const(a,b) -> failwith "TERM_TO_CONSTRUCTION_CONV"
    | Quote(_,_) -> TERM_TO_CONSTRUCTION tm
    | Comb(a,b) -> try TERM_TO_CONSTRUCTION_CONV a with Failure _ -> try TERM_TO_CONSTRUCTION_CONV b with Failure _ -> failwith "TERM_TO_CONSTRUCTION_CONV"
    | _ -> failwith "TERM_TO_CONSTRUCTION_CONV"

  let rec makeUnquotedQuote quo = match quo with
    | Const(a,ty) -> Const(a,ty)    
    | Var(a,ty) -> Var(a,ty)
    | Comb(l,r) -> Comb(makeUnquotedQuote l, makeUnquotedQuote r)
    | Abs(l,r) -> Abs(makeUnquotedQuote l, makeUnquotedQuote r)
    | Quote(a,ty) -> let muq = makeUnquotedQuote a in
        Quote(muq,qcheck_type_of muq) 
    | Hole(e,ty) -> (dest_quote e)

  (*Unquote will "cancel" out the hole and quotation operators*)
  (*ttu = term to unquote -> unquote (Q_ H_ Q_ 3 _Q _H _Q) (Q_ 3 _Q) = Q_ 3 _Q*)
  let UNQUOTE trm = match trm with
    | Quote(e,t) -> Sequent([],safe_mk_eq trm (makeUnquotedQuote trm )) 
    | _ -> failwith "UNQUOTE: THIS IS NOT A QUOTE"

  (*Convert to automatically unquote any possible quotes in first "layer" of a term, will fail if any holes are not "filled in", use UNQUOTE to unquote specific terms*)
  let rec UNQUOTE_CONV tm = 
    let rec unqint trm =
      (match trm with
        | Comb(a,b) -> Comb(unqint a, unqint b)
        | Abs(a,b) -> Abs(unqint a, unqint b)
        | Quote(e,ty) -> let muq = makeUnquotedQuote e in Quote(muq,qcheck_type_of muq)
        | Hole(e,ty) -> failwith "UNQUOTE_CONV: Hole outside quotaton"
        | other -> other) in
    let ntm = unqint tm in
    if tm = ntm then failwith "UNQUOTE_CONV" else
    Sequent([],safe_mk_eq tm ntm)

  (*There needs to be a way for the logic to mark a term for "reconstruction", as epsilon terms destroy their original terms. This will be done with a function constant.*)
  let INTERNAL_TTC tm = match tm with
    | Comb(Const("TTC",_),a) -> Sequent ([], safe_mk_eq tm (termToConstruction a))
    | _ -> failwith "INTERNAL_TTC"

  let rec INTERNAL_TTC_CONV tm = match tm with
    | Comb(Const("TTC",_),_) -> INTERNAL_TTC tm
    | Comb(a,b) -> (try INTERNAL_TTC_CONV a with Failure _ -> try INTERNAL_TTC_CONV b with Failure _ -> failwith "INTERNAL_TTC_CONV")
    | _ -> failwith "INTERNAL_TTC_CONV"


(* ------------------------------------------------------------------------- *)
(* Evaluation handling.                                                      *)
(* ------------------------------------------------------------------------- *)

  let rec attempt_type_fix tm type_desired type_actual =
    let rec instlist l1 l2 = 
      (*Check that the lists are of the same size and are not empty*)
      if length l1 <> length l2 then fail() else
      if length l1 = 0 then [] else
      (*If two elements are the same, ignore them, move to next element*)
      if (hd l1) <> (hd l2) then
      let ta = hd l1 and td = hd l2 in
      if is_vartype ta then [(td,ta)] @ (instlist (tl l1) (tl l2)) else
      if length (snd (dest_type ta)) > 0 then (instlist (snd (dest_type ta)) (snd (dest_type td))) @ (instlist (tl l1) (tl l2))  else fail()
      else instlist (tl l1) (tl l2)
    in
    (*When fixing function types recursively, they may end up equal after the first few iterations, so this ends recursion early*)
    if type_desired = type_actual then tm else
    (*Variable types can be replaced freely*)
    if is_vartype type_actual then inst [type_desired,type_actual] tm else
    (*The term has a definite type, so if we are attempting to replace it with a variable type, the eval is invalid*)
    if is_vartype type_desired then fail() else
    (*if This is not a function or constructed type, the type given to eval is invalid*)
    let tName,args = dest_type type_actual in
    let dName,dArgs = dest_type type_desired in
    if length args = 0  || dName <> tName then fail() else
    (*Generate a type instantiation list based on the differences in type and applies it to the term*)
    inst (instlist args dArgs) tm 

  let EVAL_QUOTE tm =    
    if not (is_eval tm) then failwith "EVAL_QUOTE: Not an evaluation" else
    let rec handleVar tm = match tm with
      | Var(a,b) -> Var(a,b)
      | Comb(a,b) -> Comb(handleVar a,handleVar b)
      | Quote(e,ty) -> Quote(handleVar e,ty)
      | Hole(e,ty) -> Hole(handleVar e, ty)
      | other -> other
    in
    match dest_eval tm with
      | Quote(e,ty),ety -> let e = handleVar e in if ety = type_of e then Sequent([], safe_mk_eq tm e) else (try 
          let fixed_term = (attempt_type_fix e ety (type_of e)) in 
            (*Need to check the fixed term vs given type - instantiating (=) to A -> num -> bool would work but get instantiated to A -> A -> bool,
              so if a valid type was given, it should match the instantiation*)
            if type_of fixed_term = ety then Sequent ([], safe_mk_eq tm fixed_term) else fail() with Failure _ -> failwith "Could not evaluate to given type")
      | _ -> failwith "EVAL_QUOTE: Term to eval must be a quotation"

  let rec EVAL_QUOTE_CONV tm = match tm with
    | Comb(a,b) -> (try (EVAL_QUOTE_CONV a) with Failure _ -> try (EVAL_QUOTE_CONV b) with Failure _ -> failwith "EVAL_QUOTE_CONV")
    | Abs(a,b) -> (try (EVAL_QUOTE_CONV a) with Failure _ -> try (EVAL_QUOTE_CONV b) with Failure _ -> failwith "EVAL_QUOTE_CONV")
    | Eval(e,ty) -> EVAL_QUOTE tm
    | _ -> failwith "EVAL_QUOTE_CONV"


(* ------------------------------------------------------------------------- *)
(* Inference rules of quotation.                                             *)
(* ------------------------------------------------------------------------- *)

  let LAW_OF_QUO tm = match tm with
  | Quote(e,ty) -> Sequent([], safe_mk_eq tm (Comb(Const("TTC",Tyapp("fun",[Tyvar "A";Tyapp("epsilon",[])])),e)))
  | _ -> failwith "LAW_OF_QUO"

  let VAR_DISQUO tm = match tm with
  | Eval(Comb(Const("quo",Tyapp("fun",[Tyapp("epsilon",[]);Tyapp("epsilon",[])])),Comb(Comb(Const("QuoVar",Tyapp("fun",[Tyapp("list",[Tyapp("char",[])]);Tyapp("fun",[Tyapp("type",[]);Tyapp("epsilon",[])])])),a),b)),c) -> Sequent([],safe_mk_eq tm (Comb(Comb(Const("QuoVar",Tyapp("fun",[Tyapp("list",[Tyapp("char",[])]);Tyapp("fun",[Tyapp("type",[]);Tyapp("epsilon",[])])])),a),b)))
  | _ -> failwith "VAR_DISQUO"

  let CONST_DISQUO tm = match tm with
  | Eval(Comb(Const("quo",Tyapp("fun",[Tyapp("epsilon",[]);Tyapp("epsilon",[])])),Comb(Comb(Const("QuoConst",Tyapp("fun",[Tyapp("list",[Tyapp("char",[])]);Tyapp("fun",[Tyapp("type",[]);Tyapp("epsilon",[])])])),a),b)),c) -> Sequent([],safe_mk_eq tm (Comb(Comb(Const("QuoConst",Tyapp("fun",[Tyapp("list",[Tyapp("char",[])]);Tyapp("fun",[Tyapp("type",[]);Tyapp("epsilon",[])])])),a),b)))
  | _ -> failwith "VAR_DISQUO"

  (*Defining local mk_imp function to make the other three axioms easier to implement*)
  let internal_make_imp a b = Comb(Comb(Const("==>",makeHolFunction (makeHolType "bool" []) (makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),a),b)


  let QUOTABLE tm = match type_of tm with
  | Tyapp("epsilon",[]) -> let iet =  Comb(Comb(Const("isExprType",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "type" []) (makeHolType "bool" []))),(termToConstruction tm)),matchType (Tyapp("epsilon",[]))) in
                           Sequent([],(internal_make_imp iet (safe_mk_eq (Eval(Comb(Const("Quo",makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" [])),(termToConstruction tm)),Tyapp("epsilon",[]))) tm)))
  | _ -> failwith "QUOTABLE"

  let ABS_SPLIT var tm = 
  if not (is_var var) then failwith "ABS_SPLIT" else
  match type_of tm with
  | Tyapp("epsilon",[]) -> let iet =  Comb(Comb(Const("isExprType",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "type" []) (makeHolType "bool" []))),(termToConstruction tm)),matchType (type_of tm)) in
                           let ifi = Comb(Const("~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("isFreeIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction var),termToConstruction tm)) in
                           let anticed = Comb(Comb(Const("/\\",makeHolFunction (makeHolType "bool" []) (makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),iet),ifi) in 
                           let conclud = safe_mk_eq (Eval(Comb(Comb(Const("abs",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))),termToConstruction var),tm),(makeHolFunction (type_of var) ((type_of tm))))) (Abs(var,Eval(tm,((type_of tm))))) in
                           Sequent([], internal_make_imp anticed conclud)
  | _ -> failwith "ABS_SPLIT"

  let APP_SPLIT tm1 tm2 = if (not (type_of tm1 = Tyapp("epsilon",[]))) or (not (type_of tm2 = Tyapp("epsilon",[]))) then failwith "APP_SPLIT" else
    let iet1 =  Comb(Comb(Const("isExprType",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "type" []) (makeHolType "bool" []))),tm1),matchType (makeHolFunction (type_of tm1) (type_of tm2))) in
    let iet2 =  Comb(Comb(Const("isExprType",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "type" []) (makeHolType "bool" []))),tm2),matchType (type_of tm2)) in
    let anticed = Comb(Comb(Const("/\\",makeHolFunction (makeHolType "bool" []) (makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),iet1),iet2) in  
    let conclud = safe_mk_eq (Eval(Comb(Comb(Const("app",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "epsilon" []))),tm1),tm2),((type_of tm1)))) (Comb(Eval(tm1,makeHolFunction (type_of tm1) (type_of tm2)),Eval(tm2,(type_of tm2)))) in
                           Sequent([], internal_make_imp anticed conclud)

  (*Axiom B11 (1)*)
  let BETA_EVAL var beta = if not ((is_var var) || ((type_of beta) = Tyapp("epsilon",[]))) then failwith "BETA_EVAL" else
  let lhs = Comb(Abs(var,Eval(beta,Tyvar "B")),var) in
  let rhs = Eval(beta,Tyvar "B") in
  Sequent([], safe_mk_eq lhs rhs)

  (*Axiom B11 (2)*)
  let BETA_REVAL var alpha beta = if not ((is_var var) || ((type_of beta) = Tyapp("epsilon",[])) || (type_of alpha) = Tyapp("epsilon",[])) then failwith "BETA_EVAL" else
  let iet =  Comb(Comb(Const("isExprType",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "type" []) (makeHolType "bool" []))),(termToConstruction (Comb(Abs(var,beta),alpha)))),matchType (type_of beta)) in
  let ifi = Comb(Const("~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("isFreeIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction var),(termToConstruction (Comb(Abs(var,beta),alpha))))) in
  let anticed = Comb(Comb(Const("/\\",makeHolFunction (makeHolType "bool" []) (makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),iet),ifi) in  
  let lhs = Comb(Abs(var,Eval(beta,(type_of beta))),alpha) in
  let rhs = Eval(Comb(Abs(var,beta),alpha),(type_of beta)) in
  let conclud = safe_mk_eq lhs rhs in
  Sequent([], internal_make_imp anticed conclud)

 (*Axiom B12*)
  let NOT_FREE_OR_EFFECTIVE var tm = if not (is_var var) then failwith "NOT_FREE_OR_EFFECTIVE" else
  let ifi = Comb(Const("~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("isFreeIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction var),termToConstruction tm)) in
  let nei = Comb(Const( "~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("effectiveIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction var),termToConstruction tm)) in
  Sequent([], internal_make_imp ifi nei)

  (*Axiom B13*)
  let NEITHER_EFFECTIVE x y tm1 tm2 = if not ((is_var x) || (is_var y)) then failwith "NEITHER_EFFECTIVE" else
  let nei1 = Comb(Const( "~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("effectiveIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction y),termToConstruction tm1)) in
  let nei2 = Comb(Const( "~",(makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),Comb(Comb(Const("effectiveIn",makeHolFunction (makeHolType "epsilon" []) (makeHolFunction (makeHolType "epsilon" []) (makeHolType "bool" []))),termToConstruction x),termToConstruction tm2)) in
  let disjunct_nei = Comb(Comb(Const("\\/",makeHolFunction (makeHolType "bool" []) (makeHolFunction (makeHolType "bool" []) (makeHolType "bool" []))),nei1),nei2) in
  let lhs = Comb(Abs(x,Abs(y,tm2)),tm1) in
  let rhs = Abs(y,Comb(Abs(x,tm2),tm1)) in
  let fin = safe_mk_eq lhs rhs in 
  Sequent([],internal_make_imp disjunct_nei fin)

  (*For evaluation substiution conversions to beta evaluations*)
  let EVAL_VSUB (tm:thm) (trm:term) = 
  if not (is_eval trm) then
  failwith "EVAL_VSUB"
  else
  let asl = fst (dest_thm tm) in
  if not (asl = []) then
  failwith "EVAL_VSUB: Assumptions not allowed in theorem"
  else
  let v,res = dest_eq (concl tm) in
  Sequent((fst (dest_thm tm)), (safe_mk_eq trm (Comb(Abs(v,trm),res))))

  let rec MATCH_ASMS_TO_EVAL asm tm full = 
      let rec VarInTerm vr trm = 
        let rec Q_VarInTerm vr trm = match trm with
          | Hole(t,ty) -> VarInTerm vr trm
          | Quote(t,ty) -> Q_VarInTerm vr trm
          | Comb(a,b) -> (Q_VarInTerm vr trm) || (Q_VarInTerm vr trm)
          | _ -> false
        in
      match trm with
      | Var (_,_) -> (dest_var vr) = (dest_var trm)
      | Const (_,_) -> false
      | Comb (a,b) -> (VarInTerm vr a) || (VarInTerm vr b)
      | Abs (a,b) -> not ((dest_var vr) = (dest_var a)) && VarInTerm vr b
      | Quote (e,ty) -> Q_VarInTerm vr e
      | Hole (e,ty) -> Q_VarInTerm vr e
      | Eval(e,ty) -> VarInTerm vr e
      in
      match asm with
      | a :: rest -> (try
      (*All failures result in skipping to the next item in the list*)
      let l,r = dest_eq a in 
      if not (is_var l) then fail() else
      if (VarInTerm l tm) then
      EVAL_VSUB (Sequent ([],safe_mk_eq l r)) tm
      else
      fail() 
    with Failure _ ->  MATCH_ASMS_TO_EVAL rest tm asm)
    | _ -> failwith "Unknown"
    | [] -> REFL tm
  (*Meant for use on goal states to apply assumptions availible in the goal to evals, such as when doing case analysis*)
  let rec EVAL_GOAL_VSUB (asm,tm) = 
  match tm with
  | Comb(a,b) | Abs(a,b) -> (try EVAL_GOAL_VSUB (asm,a) with Failure _ -> try EVAL_GOAL_VSUB (asm,b) with Failure _ -> failwith "EVAL_GOAL_VSUB")
  | Eval(e,b) -> (MATCH_ASMS_TO_EVAL asm tm asm)
  | _ -> failwith "EVAL_GOAL_VSUB"



(* ------------------------------------------------------------------------- *)
(* Handling of axioms.                                                       *)
(* ------------------------------------------------------------------------- *)

  let the_axioms = ref ([]:thm list)

  let axioms() = !the_axioms

  let new_axiom tm =
    if Pervasives.compare (type_of tm) bool_ty = 0 then
      let th = Sequent([],tm) in
       (the_axioms := th::(!the_axioms); th)
    else failwith "new_axiom: Not a proposition"

(* ------------------------------------------------------------------------- *)
(* Handling of (term) definitions.                                           *)
(* ------------------------------------------------------------------------- *)
  let the_definitions = ref ([]:thm list)

  let definitions() = !the_definitions

  let new_basic_definition tm =
    match tm with
      Comb(Comb(Const("=",_),Var(cname,ty)),r) ->
        if not(freesin [] r) then failwith "new_definition: term not closed"
        else if not (subset (type_vars_in_term r) (tyvars ty))
        then failwith "new_definition: Type variables not reflected in constant"
        else let c = new_constant(cname,ty); Const(cname,ty) in
             let dth = Sequent([],safe_mk_eq c r) in
             the_definitions := dth::(!the_definitions); dth
    | _ -> failwith "new_basic_definition"

(* ------------------------------------------------------------------------- *)
(* Handling of type definitions.                                             *)
(*                                                                           *)
(* This function now involves no logical constants beyond equality.          *)
(*                                                                           *)
(*             |- P t                                                        *)
(*    ---------------------------                                            *)
(*        |- abs(rep a) = a                                                  *)
(*     |- P r = (rep(abs r) = r)                                             *)
(*                                                                           *)
(* Where "abs" and "rep" are new constants with the nominated names.         *)
(* ------------------------------------------------------------------------- *)

  let new_basic_type_definition tyname (absname,repname) (Sequent(asl,c)) =
    if exists (can get_const_type) [absname; repname] then 
      failwith "new_basic_type_definition: Constant(s) already in use" else
    if not (asl = []) then
      failwith "new_basic_type_definition: Assumptions in theorem" else
    let P,x = try dest_comb c
              with Failure _ ->
                failwith "new_basic_type_definition: Not a combination" in
    if not(freesin [] P) then
      failwith "new_basic_type_definition: Predicate is not closed" else
    let tyvars = sort (<=) (type_vars_in_term P) in
    let _ = try new_type(tyname,length tyvars)
            with Failure _ ->
                failwith "new_basic_type_definition: Type already defined" in
    let aty = Tyapp(tyname,tyvars)
    and rty = type_of x in
    let absty = Tyapp("fun",[rty;aty]) and repty = Tyapp("fun",[aty;rty]) in
    let abs = (new_constant(absname,absty); Const(absname,absty))
    and rep = (new_constant(repname,repty); Const(repname,repty)) in
    let a = Var("a",aty) and r = Var("r",rty) in
    Sequent([],safe_mk_eq (Comb(abs,mk_comb(rep,a))) a),
    Sequent([],safe_mk_eq (Comb(P,r))
                          (safe_mk_eq (mk_comb(rep,mk_comb(abs,r))) r))

end;;

include Hol;;

(* ------------------------------------------------------------------------- *)
(* Stuff that didn't seem worth putting in.                                  *)
(* ------------------------------------------------------------------------- *)

let mk_fun_ty ty1 ty2 = mk_type("fun",[ty1; ty2]);;
let bty = mk_vartype "B";;

let is_eq tm =
  match tm with
    Comb(Comb(Const("=",_),_),_) -> true
  | _ -> false;;

let mk_eq =
  let eq = mk_const("=",[]) in
  fun (l,r) ->
    try let ty = type_of l in
        let eq_tm = inst [ty,aty] eq in
        mk_comb(mk_comb(eq_tm,l),r)
    with Failure _ -> failwith "mk_eq";;

(* ------------------------------------------------------------------------- *)
(* Tests for alpha-convertibility (equality ignoring names in abstractions). *)
(* ------------------------------------------------------------------------- *)

let aconv s t = alphaorder s t = 0;;

(* ------------------------------------------------------------------------- *)
(* Comparison function on theorems. Currently the same as equality, but      *)
(* it's useful to separate because in the proof-recording version it isn't.  *)
(* ------------------------------------------------------------------------- *)

let equals_thm th th' = dest_thm th = dest_thm th';;

