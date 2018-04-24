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
  | Let (v, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
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
  (*let y = def in body
            Q      R   *)
  | Let (y, def, body) ->
                (*if y = var_name, then you replace var_name with what it was defined earlier on
                  e.g. let x = X + 5 in x + 3 [X |-> 12]*)
                if y = var_name then Let (y, subst var_name repl def, body)
                (*if y <> var_name and...
                  ...y is not in repl (aka P), then subst var_name with P in def and body
                  e.g. let y = x + 5 in x + y [x |-> 12]*)
                else if not (SS.mem y (free_vars repl))
                then Let (y, subst var_name repl def, subst var_name repl body)
                (*...y is in repl (aka P), then change y to z to avoid capture
                  e.g.let y = 5 in x (y + 1) [x |-> fun w -> y]
                      let Y = 5 in (fun w -> Y) (y + 1)
                      -instead of returning y + 1, the Y will be captured and return 5
                      ...so...
                      let z = 5 in x (z + 1) [x |-> fun w -> y]
                      let z = 5 in (fun w -> y) (y + 1)
                      OR
                      let y = 5 in x + y [x |-> y, defined earlier as 12]
                      let y = 5 in y + y
                      :- 10 (WRONG)
                      let z = 5 in x + z [x |-> y, defined earlier as 12]
                      let z = 5 in y + z
                      :- 17 (RIGHT)
                        *)
                else let z = new_var in
                    let subst_z = subst y (Var z) body in
                    Let (z, subst var_name repl def, subst var_name repl subst_z)
  | Letrec (y, def, body) ->
                if y = var_name then Let (y, def, body)
                else if not (SS.mem y (free_vars repl))
                then Let (y, subst var_name repl def, subst var_name repl body)
                else let z = new_var in
                     let subst_z = subst y (Var z) body in
                     Let (z, subst var_name repl def, subst var_name repl subst_z)
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
  let binop_help b e1 e2 : string =
    "Unop (" ^ b ^ ", " ^
    exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2 ^ ")" in
    match exp with
    | Var v -> "Var " ^ v                         (* variables *)
    | Num n -> "Num " ^ string_of_int n                          (* integers *)
    | Bool b -> "Bool " ^ string_of_bool b                        (* booleans *)
    | Unop (u, e) -> (match u with
                     Negate -> "Unop (Negate, " ^ exp_to_abstract_string e ^ ")"
    | Binop (b, e1, e2) -> (match b with
                            | Plus -> binop_help "Plus" e1 e2
                            | Minus -> binop_help "Minus" e1 e2
                            | Times -> binop_help "Times" e1 e2
                            | Equals -> binop_help "Equals" e1 e2
                            | LessThan -> binop_help "LessThan" e1 e2)      (* binary operators *)
    | Conditional (e1, e2, e3) -> "Conditional (" ^ exp_to_abstract_string e1 ^
                                  ", " ^ exp_to_abstract_string e2 ^ ", " ^
                                  exp_to_abstract_string e3 ^ ")"
    | Fun (v, e) -> "Fun (" ^ v ^ ", " ^ exp_to_abstract_string e                  (* function definitions *)
    | Let (v, e1, e2) -> "Let (" ^ v ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^
                         exp_to_abstract_string e2 ^ ")"
    | Letrec (v, e1, e2) -> "Letrec (" ^ v ^ ", " ^ exp_to_abstract_string e1 ^
                            ", " ^ exp_to_abstract_string e2 ^ ")"        (* recursive local naming *)
    | Raise -> "Raise"                               (* exceptions *)
    | Unassigned -> "Unassigned"                           (* (temporarily) unassigned *)
    | App (e1, e2) -> "App (" ^ exp_to_abstract_string e1 ^ ", " ^
                      exp_to_abstract_string e2 ")" ;;
