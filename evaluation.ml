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
      Closure (exp, env) ;;

    (* Looks up the value of a variable in the environment *)
    let lookup (env : env) (varname : varid) : value =
      try
        let _i, v = List.find (fun elt -> fst elt = varname) env in !v
      with
      | Not_found -> raise (EvalError "Unbound variable") ;;

    (* Returns a new environment just like env except that it maps the
       variable varid to loc *)
    let extend (env : env) (varname : varid) (loc : value ref) : env =
      try
        let _i, v = List.find (fun elt -> fst elt = varname) env in
        v := !loc; env
      with
      | Not_found -> (varname, loc) :: env ;;

    (* Returns a printable string representation of a value; the flag
       printenvp determines whether to include the environment in the
       string representation when called on a closure *)
    let rec value_to_string ?(printenvp : bool = true) (v : value) : string =
(*       raise (EvalError "value_to_string not implemented") ;;
 *)      match v with
      | Val exp -> exp_to_concrete_string exp
      | Closure (exp, env) ->
                            if printenvp
                            then exp_to_concrete_string exp ^ " START CLOSURE ENV: " ^ env_to_string env
                            else exp_to_concrete_string exp

    (* Returns a printable string representation of an environment *)
    and env_to_string (env : env) : string =
(*       raise (EvalError "env_to_string not implemented") ;;
 *)    match env with
      | [] -> "END ENVIRONMENT"
      | (i, v) :: t -> "(" ^ i ^ ", " ^ value_to_string !v ^ ") " ^
                        env_to_string t ;;
  end
;;

open Env ;;

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
(* let exp_of_eval eval e: expr =
  (match eval e env with
  | Val exp -> exp
  | Closure (exp, env) -> exp) in *)

let rec eval_s (exp : expr) (env : Env.env) : Env.value =
  (* let exp_of_eval = exp_of_eval eval_s in *)
  let exp_of_eval e: expr =
    (match eval_s e env with
    | Val exp -> exp
    | Closure (exp, _env) -> exp) in
(*   let rec eval_help (exp: expr) : expr =
 *)  match exp with
    | Var _x -> raise (EvalError "Unbound variable")
    | Num n -> Val (Num n)
    | Bool b -> Val (Bool b)
    | Unop (u, e) -> (match exp_of_eval e with
                      | Num n -> (match u with Negate -> Val (Num ~-n))
                      | _ -> raise (EvalError "Invalid operation"))
    | Binop (b, e1, e2) -> (match exp_of_eval e1, exp_of_eval e2 with
                              | Num n1, Num n2 -> (match b with
                                | Plus -> Val (Num (n1 + n2))
                                | Minus -> Val (Num (n1 - n2))
                                | Times -> Val (Num (n1 * n2))
                                | Equals -> Val (Bool (n1 = n2))
                                | LessThan -> Val (Bool (n1 < n2)))
                              | Bool b1, Bool b2 -> (match b with
                                | Equals -> Val (Bool (b1 = b2))
                                | LessThan -> Val (Bool (b1 < b2))
                                | _ -> raise (EvalError "Invalid operation"))
                              | _ -> raise (EvalError "Invalid operation"))
    | Conditional (e1, e2, e3) -> (match exp_of_eval e1 with
                                   | Bool b ->
                                        if b then eval_s e2 env
                                        else eval_s e3 env
                                   | _ -> raise (EvalError "Invalid condition"))
    | Fun (y, e) -> Val (Fun (y, e))
    | Let (y, def, body) -> eval_s (subst y (exp_of_eval def) body) env
    | Letrec (f, def, body) ->
                let def' = exp_of_eval (subst f (Letrec (f, def, Var f)) def) in
                eval_s (subst f def' body) env
    | Raise -> Val (Raise)
    | Unassigned -> Val (Unassigned)
    | App (p, q) ->
        eval_s (match exp_of_eval p with
             | Fun (y, e) -> subst y q e
             | _ -> raise (EvalError "Invalid function application")) env ;;

(* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator -- to be
   completed *)

let rec eval_d (exp : expr) (env : Env.env) : Env.value =
  let exp_of_eval e: expr =
    (match eval_d e env with
    | Val exp -> exp
    | Closure (exp, _env) -> exp) in
  match exp with
    | Var v -> lookup env v
    | Num n -> Val (Num n)
    | Bool b -> Val (Bool b)
    | Unop (u, e) -> (match exp_of_eval e with
                      | Num n -> (match u with Negate -> Val (Num ~-n))
                      | _ -> raise (EvalError "Invalid operation"))
    | Binop (b, e1, e2) -> (match exp_of_eval e1, exp_of_eval e2 with
                              | Num n1, Num n2 -> (match b with
                                | Plus -> Val (Num (n1 + n2))
                                | Minus -> Val (Num (n1 - n2))
                                | Times -> Val (Num (n1 * n2))
                                | Equals -> Val (Bool (n1 = n2))
                                | LessThan -> Val (Bool (n1 < n2)))
                              | Bool b1, Bool b2 -> (match b with
                                | Equals -> Val (Bool (b1 = b2))
                                | LessThan -> Val (Bool (b1 < b2))
                                | _ -> raise (EvalError "Invalid operation"))
                              | _ -> raise (EvalError "Invalid operation"))
    | Conditional (e1, e2, e3) -> (match exp_of_eval e1 with
                                   | Bool b ->
                                        if b then eval_d e2 env
                                        else eval_d e3 env
                                   | _ -> raise (EvalError "Invalid condition"))
    | Fun (y, e) -> Val (Fun (y, e))
    | Let (y, def, body) -> eval_d body (extend env y (ref (eval_d def env)))
    | Letrec (f, def, body) -> let unass = ref (Val Unassigned) in
                               let extendenv = extend env f unass in
                               let def' = eval_d def extendenv in
                               unass := def';
                               eval_d body extendenv
    | Raise -> Val (Raise)
    | Unassigned -> Val (Unassigned)
    | App (p, q) -> match exp_of_eval p with
                    | Fun (x, b) -> eval_d b (extend env x (ref (eval_d q env)))
                    | _ -> raise (EvalError "Invalid function application") ;;

(* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator -- optionally
   completed as (part of) your extension *)

let rec eval_l (exp : expr) (env : Env.env) : Env.value =
(*   failwith "not implemented";; *)
  let exp_of_eval e : expr =
    (match eval_l e env with
    | Val exp -> exp
    | Closure (exp, _env) -> exp) in
  match exp with
    | Var v -> lookup env v
    | Num n -> Val (Num n)
    | Bool b -> Val (Bool b)
    | Unop (u, e) -> (match exp_of_eval e with
                      | Num n -> (match u with Negate -> Val (Num ~-n))
                      | _ -> raise (EvalError "Invalid operation"))
    | Binop (b, e1, e2) -> (match exp_of_eval e1, exp_of_eval e2 with
                              | Num n1, Num n2 -> (match b with
                                | Plus -> Val (Num (n1 + n2))
                                | Minus -> Val (Num (n1 - n2))
                                | Times -> Val (Num (n1 * n2))
                                | Equals -> Val (Bool (n1 = n2))
                                | LessThan -> Val (Bool (n1 < n2)))
                              | Bool b1, Bool b2 -> (match b with
                                | Equals -> Val (Bool (b1 = b2))
                                | LessThan -> Val (Bool (b1 < b2))
                                | _ -> raise (EvalError "Invalid operation"))
                              | _ -> raise (EvalError "Invalid operation"))
    | Conditional (e1, e2, e3) -> (match exp_of_eval e1 with
                                   | Bool b ->
                                        if b then eval_l e2 env
                                        else eval_l e3 env
                                   | _ -> raise (EvalError "Invalid condition"))
    | Fun (y, e) -> Closure (Fun (y, e), env)
    | Let (y, def, body) -> eval_l body (extend env y (ref (eval_l def env)))
    | Letrec (f, def, body) -> let unass = ref (Val Unassigned) in
                               let extendenv = extend env f unass in
                               let def' = eval_l def extendenv in
                               unass := def';
                               eval_l body extendenv
    | Raise -> Val (Raise)
    | Unassigned -> Val (Unassigned)
    | App (p, q) -> Printf.printf "%s" (env_to_string env);
                    match eval_l p env with
                    | Closure (Fun (x, def), env_closure) ->
                          eval_l def (extend env_closure x (ref (eval_l q env)))
                    | _ -> raise (EvalError "Invalid function application") ;;

(* Connecting the evaluators to the external world. The REPL in
   miniml.ml uses a call to the single function evaluate defined
   here. Initially, evaluate is the trivial evaluator eval_t. But you
   can define it to use any of the other evaluators as you proceed to
   implement them. (We will directly unit test the four evaluators
   above, not the evaluate function, so it doesn't matter how it's set
   when you submit your solution.) *)

let evaluate = eval_l ;;
