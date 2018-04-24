(*
                         CS 51 Final Project
                         MiniML -- Evaluation
                             Spring 2018
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)

open Expr ;;

(* Exception for evaluator runtime, generated by a runtime error *)
exception EvalError of string ;;
(* Exception for evaluator runtime, generated by an explicit "raise" construct *)
exception EvalException ;;


(*......................................................................
  Environments and values
 *)

module type Env_type = sig
    type env
    type value =
      | Val of expr
      | Closure of (expr * env)
    val create : unit -> env
    val close : expr -> env -> value
    val lookup : env -> varid -> value
    val extend : env -> varid -> value ref -> env
    val env_to_string : env -> string
    val value_to_string : ?printenvp:bool -> value -> string
  end

module Env : Env_type =
  struct
    type env = (varid * value ref) list
     and value =
       | Val of expr
       | Closure of (expr * env)

    (* Creates an empty environment *)
    let create () : env = [] ;;

    (* Creates a closure from an expression and the environment it's
       defined in *)
    let close (exp : expr) (env : env) : value =
      failwith "close not implemented" ;;

    (* Looks up the value of a variable in the environment *)
    let lookup (env : env) (varname : varid) : value =
      failwith "lookup not implemented" ;;

    (* Returns a new environment just like env except that it maps the
       variable varid to loc *)
    let extend (env : env) (varname : varid) (loc : value ref) : env =
      failwith "extend not implemented" ;;

    (* Returns a printable string representation of a value; the flag
       printenvp determines whether to include the environment in the
       string representation when called on a closure *)
    let value_to_string ?(printenvp : bool = true) (v : value) : string =
      failwith "value_to_string not implemented" ;;

    (* Returns a printable string representation of an environment *)
    let env_to_string (env : env) : string =
      failwith "env_to_string not implemented" ;;
  end
;;


(*......................................................................
  Evaluation functions

  Returns a result of type value of evaluating the expression exp
  in the environment env. We've provided an initial implementation
  for a trivial evaluator, which just converts the expression
  unchanged to a value and returns it, along with "stub code" for
  three more evaluators: a substitution model evaluator and dynamic
  and lexical environment model versions.

  Each evaluator is of type expr -> Env.env -> Env.value for
  consistency, though some of the evaluators don't need an
  environment, and some will only return values that are "bare
  values" (that is, not closures). *)

(* The TRIVIAL EVALUATOR, which leaves the expression to be evaluated
   essentially unchanged, just converted to a value for consistency
   with the signature of the evaluators. *)

let eval_t (exp : expr) (_env : Env.env) : Env.value =
  (* coerce the expr, unchanged, into a value *)
  Env.Val exp ;;

(* The SUBSTITUTION MODEL evaluator -- to be completed *)

let rec eval_s (exp : expr) (env : Env.env) : Env.value =
  let exp_of_eval q : expr =
    (match eval_s q env with
    | Val exp -> exp
    | Closure (exp, env) -> exp) in
  match exp with
    | Var v -> raise (EvalError "Unbound variable")                         (* variables *)
    | Num n -> Val (Num n)                          (* integers *)
    | Bool b -> Val (Bool b)                        (* booleans *)
    | Unop (u, e) -> (match exp_of_eval e with
                      | Num n -> (match u with Negate -> Val (Num ~-n))
                      | _ -> raise (EvalError "Not an integer"))
    | Binop (b, e1, e2) -> (match eval_s e1 env, eval_s e2 env with
                              Val (Num n1), Val (Num n2) -> (match b with
                                | Plus -> Val (Num (n1 + n2))
                                | Minus -> Val (Num (n1 - n2))
                                | Times -> Val (Num (n1 * n2))
                                | Equals -> Val (Bool (n1 = n2))
                                | LessThan -> Val (Bool (n1 < n2))))
    | Conditional (e1, e2, e3) -> (match eval_s e1 env with
                                   | Val (Bool b) ->
                                    if b then eval_s e2 env else eval_s e3 env
                                   | _ -> raise (EvalError "Invalid condition"))
    | Fun (y, e) -> Val (Fun (y, e))              (* function definitions *)
    | Let (y, def, body) -> eval_s (subst y (exp_of_eval def) body) env
    | Letrec (y, def, body) ->
                let def' = exp_of_eval (subst y (Letrec (y, def, Var y)) def) in
                eval_s (subst y def' body) env
    | Raise -> Val (Raise)
    | Unassigned -> Val (Unassigned)
    | App (e1, e2) ->
        eval_s (match exp_of_eval e1 with
             | Fun (y, e) -> subst y e2 e
             | _ -> raise (EvalError "Not a function")) env ;;

(* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator -- to be
   completed *)

let eval_d (_exp : expr) (_env : Env.env) : Env.value =
  failwith "eval_d not implemented" ;;

(* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator -- optionally
   completed as (part of) your extension *)

let eval_l (_exp : expr) (_env : Env.env) : Env.value =
  failwith "eval_l not implemented" ;;

(* Connecting the evaluators to the external world. The REPL in
   miniml.ml uses a call to the single function evaluate defined
   here. Initially, evaluate is the trivial evaluator eval_t. But you
   can define it to use any of the other evaluators as you proceed to
   implement them. (We will directly unit test the four evaluators
   above, not the evaluate function, so it doesn't matter how it's set
   when you submit your solution.) *)

let evaluate = eval_s ;;
