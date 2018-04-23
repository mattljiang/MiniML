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
  | Var v -> SS.singleton v                         (* variables *)
  | Num n -> SS.empty                          (* integers *)
  | Bool b -> SS.empty                      (* booleans *)
  | Unop (u, e) -> free_vars e
  | Binop (b, e1, e2) -> SS.union (free_vars e1) (free_vars e2)      (* binary operators *)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1)
                                (SS.union (free_vars e2) (free_vars e3))  (* if then else *)
  | Fun (v, e) -> SS.diff (free_vars e) (SS.singleton v)                 (* function definitions *)
  | Let (v, e1, e2) -> SS.union (free_vars e2)
                       (SS.diff (free_vars e1) (SS.singleton v))
  | Letrec (v, e1, e2) -> SS.union (free_vars e2)
                          (SS.diff (free_vars e1) (SS.singleton v))                           (* recursive local naming *)
  | Raise -> SS.empty                              (* exceptions *)
  | Unassigned -> SS.empty                          (* (temporarily) unassigned *)
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2)                  (* function applications *) ;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname () : varid =
  failwith "new_varname not implemented" ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp
   repl = P*)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  if not (SS.mem var_name (free_vars exp)) then exp else
  match exp with
  | Var x -> if x = var_name then repl else Var x                         (* variables *)
  | Num n -> Num n                          (* integers *)
  | Bool b -> Bool b                     (* booleans *)
  | Unop (u, e) -> Unop (u, subst var_name repl e)
  | Binop (b, e1, e2) -> Binop (b, subst var_name repl e1, subst var_name repl e2)    (* binary operators *)
  | Conditional (e1, e2, e3) -> Conditional (subst var_name repl e1,
                                             subst var_name repl e2,
                                             subst var_name repl e3)  (* if then else *)
  | Fun (y, e) -> if x = var_name then Fun (y, e)
                  else if not (SS.mem y (free_vars repl))
                  then Fun (y, subst var_name repl e)
                  else let z = new_var in
                       let subst_z = subst y (Var z) e in
                       Fun (z, subst var_name repl subst_z)                  (* function definitions *)
  | Let (y, e1, e2) ->
                if y = var_name then Let (y, subst var_name repl e1, e2)
                else if not (SS.mem y (free_vars repl))
                then Let (y, subst var_name repl e1, subst var_name repl e2)
                else let z = new_var in
                    let subst_z = subst y (Var z) e2 in
                    Fun (z, subst var_name repl e1, subst var_name repl subst_z)

  Let (v, subst var_name repl e1, subst var_name repl e2)
  | Letrec (v, e1, e2) -> Letrec (v, subst var_name repl e1, subst var_name repl e2)                        (* recursive local naming *)
  | Raise -> Raise                             (* exceptions *)
  | Unassigned -> Unassigned                         (* (temporarily) unassigned *)
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2)               (* function applications *) ;;

(*......................................................................
  String representations of expressions
 *)


(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)

let rec exp_to_concrete_string (exp : expr) : string =
  let binop_help b e1 e2 : string =
    (exp_to_concrete_string e1) ^ b ^ (exp_to_concrete_string e2) in
   match exp with
    | Var v -> v                         (* variables *)
    | Num n -> string_of_int n                          (* integers *)
    | Bool b -> string_of_bool b                        (* booleans *)
    | Unop (u, e) -> (match u with
                     Negate -> "~-" ^ exp_to_concrete_string e)                 (* unary operators *)
    | Binop (b, e1, e2) -> (match b with
                            | Plus -> binop_help " + " e1 e2
                            | Minus -> binop_help " - " e1 e2
                            | Times -> binop_help " * " e1 e2
                            | Equals -> binop_help " = " e1 e2
                            | LessThan -> binop_help " < " e1 e2)      (* binary operators *)
    | Conditional (e1, e2, e3) -> "if " ^ exp_to_concrete_string e1 ^
                                  " then " ^ exp_to_concrete_string e2 ^
                                  " else " ^ exp_to_concrete_string e3     (* if then else *)
    | Fun (v, e) -> "let fun " ^ v ^ " -> " ^ exp_to_concrete_string e                  (* function definitions *)
    | Let (v, e1, e2) -> "let " ^ v ^ " = " ^ exp_to_concrete_string e1 ^
                         " in " ^ exp_to_concrete_string e2    (* local naming *)
    | Letrec (v, e1, e2) -> " let rec " ^ v ^ " = " ^ exp_to_concrete_string e1 ^
                            " in " ^ exp_to_concrete_string e2        (* recursive local naming *)
    | Raise -> "raise (Some_Exception)"                               (* exceptions *)
    | Unassigned -> "temporarily unassigned"                           (* (temporarily) unassigned *)
    | App (e1, e2) -> match e1 with
                      Fun (v, e) -> "(fun " ^ v ^ " -> " ^ e ^
                                    ") (" ^ exp_to_concrete_string e2 ^ ")"  ;;                (* function applications *)
(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let exp_to_abstract_string (exp : expr) : string =
    failwith "exp_to_abstract_string not implemented" ;;
