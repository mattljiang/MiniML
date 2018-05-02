(*
                         CS 51 Final Project
                        MiniML -- Expressions
                             Spring 2018
*)

(*......................................................................
  Abstract syntax of MiniML expressions
 *)

type unop =
  | Negate
;;

type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string ;;

(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
   match exp with
  | Var x -> SS.singleton x
  | Num _n -> SS.empty
  | Bool _b -> SS.empty
  | Unop (_u, e) -> free_vars e
  | Binop (_b, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1)
                                (SS.union (free_vars e2) (free_vars e3))
  | Fun (y, e) -> SS.diff (free_vars e) (SS.singleton y)
  | Let (y, def, body) -> SS.union (free_vars def)
                          (SS.diff (free_vars body) (SS.singleton y))
  | Letrec (f, def, body) -> SS.diff (SS.union (free_vars def) (free_vars body))
                             (SS.singleton f)
  | Raise -> SS.empty
  | Unassigned -> SS.singleton "Unassigned"
  | App (p, q) -> SS.union (free_vars p) (free_vars q) ;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname =
  let ctr = ref (-1) in
  fun () ->
    ctr := !ctr + 1;
    "var" ^ string_of_int (!ctr) ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp
   repl = P, not constrained to a value to allow substition of
   expressions like 12 + y*)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  if not (SS.mem var_name (free_vars exp)) then exp
  else
    match exp with
    | Var x -> if x = var_name then repl else Var x
    | Num n -> Num n
    | Bool b -> Bool b
    | Unop (u, e) -> Unop (u, subst var_name repl e)
    | Binop (b, e1, e2) -> Binop (b, subst var_name repl e1,
                                     subst var_name repl e2)
    | Conditional (e1, e2, e3) -> Conditional (subst var_name repl e1,
                                               subst var_name repl e2,
                                               subst var_name repl e3)
    | Fun (y, e) -> if y = var_name then Fun (y, e)
                    else if not (SS.mem y (free_vars repl))
                    then Fun (y, subst var_name repl e)
                    else let z = new_varname () in
                         let subst_z = subst y (Var z) e in
                         Fun (z, subst var_name repl subst_z)
    | Let (y, def, body) ->
                if y = var_name then Let (y, subst var_name repl def, body)
                else if not (SS.mem y (free_vars repl)) then
                  Let (y, subst var_name repl def, subst var_name repl body)
                else let z = new_varname () in
                     let subst_z = subst y (Var z) body in
                     Let (z, subst var_name repl def, subst var_name repl
                                                                        subst_z)
    | Letrec (f, def, body) ->
                   if f = var_name then Letrec (f, def, body)
                   else if not (SS.mem f (free_vars repl)) then
                     Letrec (f, subst var_name repl def, subst var_name repl
                                                                           body)
                   else let z = new_varname () in
                        let subst_z_body = subst f (Var z) body in
                        let subst_z_def = subst f (Var z) def in
                        Letrec (z, subst var_name repl subst_z_def,
                                   subst var_name repl subst_z_body)
    | Raise -> Raise
    | Unassigned -> Unassigned
    | App (p, q) -> App (subst var_name repl p, subst var_name repl q) ;;

(*......................................................................
  String representations of expressions
 *)

(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  let binop_help b e1 e2 : string =
    (exp_to_concrete_string e1) ^ b ^ (exp_to_concrete_string e2) in
  match exp with
  | Var x -> x
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unop (u, e) -> (match u with
                    Negate -> "~-" ^ exp_to_concrete_string e)
  | Binop (b, e1, e2) -> (match b with
                          | Plus -> binop_help " + " e1 e2
                          | Minus -> binop_help " - " e1 e2
                          | Times -> binop_help " * " e1 e2
                          | Equals -> binop_help " = " e1 e2
                          | LessThan -> binop_help " < " e1 e2)
  | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^
                                " then " ^ exp_to_concrete_string e2 ^
                                " else " ^ exp_to_concrete_string e3
  | Fun (y, e) -> "fun " ^ y ^ " -> " ^ exp_to_concrete_string e
  | Let (y, def, body) -> "let " ^ y ^ " = " ^ exp_to_concrete_string def ^
                          " in " ^ exp_to_concrete_string body
  | Letrec (f, def, body) -> " let rec " ^ f ^ " = " ^
                             exp_to_concrete_string def ^
                             " in " ^ exp_to_concrete_string body
  | Raise -> "raise (Some_Exception)"
  | Unassigned -> "temporarily unassigned"
  | App (p, q) -> exp_to_concrete_string p ^ " " ^ exp_to_concrete_string q ;;

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  let binop_help b e1 e2 : string =
    "Binop (" ^ b ^ ", " ^
    exp_to_abstract_string e1 ^ ", " ^
    exp_to_abstract_string e2 ^ ")" in
  match exp with
  | Var x -> "Var " ^ x
  | Num n -> "Num " ^ string_of_int n
  | Bool b -> "Bool " ^ string_of_bool b
  | Unop (u, e) ->
    (match u with Negate -> "Unop (Negate, " ^ exp_to_abstract_string e ^ ")")
  | Binop (b, e1, e2) -> (match b with
                          | Plus -> binop_help "Plus" e1 e2
                          | Minus -> binop_help "Minus" e1 e2
                          | Times -> binop_help "Times" e1 e2
                          | Equals -> binop_help "Equals" e1 e2
                          | LessThan -> binop_help "LessThan" e1 e2)
  | Conditional (e1, e2, e3) -> "Conditional (" ^ exp_to_abstract_string e1 ^
                                ", " ^ exp_to_abstract_string e2 ^ ", " ^
                                exp_to_abstract_string e3 ^ ")"
  | Fun (y, e) -> "Fun (" ^ y ^ ", " ^ exp_to_abstract_string e
  | Let (y, def, body) -> "Let (" ^ y ^ ", " ^ exp_to_abstract_string def ^
                          ", " ^ exp_to_abstract_string body ^ ")"
  | Letrec (f, def, body) -> "Letrec (" ^ f ^ ", " ^ exp_to_abstract_string def
                             ^ ", " ^ exp_to_abstract_string body ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (p, q) -> "App (" ^ exp_to_abstract_string p ^ ", " ^
                  exp_to_abstract_string q ^ ")" ;;
