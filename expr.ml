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
let free_vars (exp : expr) : varidset =
  failwith "free_vars not implemented" ;;

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
   Substitute repl for free occurrences of var_name in exp *)
let subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  failwith "subst not implemented" ;;

(*......................................................................
  String representations of expressions
 *)


(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let binop_help b e1 e2 : string =
  (exp_to_concrete_string e1) ^ b ^ (exp_to_concrete_string e2) in
let rec exp_to_concrete_string (exp : expr) : string =
 match exp with
  | Var v -> v                         (* variables *)
  | Num n -> string_of_int v                          (* integers *)
  | Bool b -> string_of_bool b                        (* booleans *)
  | Unop (u, e) -> match u with
                   Negate -> "~-" ^ exp_to_concrete_string e                 (* unary operators *)
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
                                  ") (" ^ exp_to_concrete_string e2 ^ ")"                  (* function applications *)
(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let exp_to_abstract_string (exp : expr) : string =
    failwith "exp_to_abstract_string not implemented" ;;
