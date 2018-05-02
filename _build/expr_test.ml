open Expr ;;
open Printf ;;
open Miniml ;;

(**.............................................................................
Testing Framework
**)

type test = {label : string;
             content : bool Lazy.t;
             time : int;
             fail_msg : string} ;;

type status =
  | Passed
  | Failed of string
  | Raised_exn of string
  | Timed_out of int

(*running tests in timed framework*)
exception Timeout ;;

let sigalrm_handler =
  Sys.Signal_handle (fun _ -> raise Timeout) ;;
let timeout (time : int) (delayed : 'a Lazy.t) : 'a =
let old_behavior =
  Sys.signal Sys.sigalrm sigalrm_handler in
let reset_sigalrm () =
  ignore (Unix.alarm 0);
  Sys.set_signal Sys.sigalrm old_behavior in
  ignore (Unix.alarm time);
let res = Lazy.force delayed in
  reset_sigalrm (); res ;;

(*runs test and passes to continue: passed, failed, timeout or exception*)
let run_test ({label; time; content; fail_msg} : test)
             (continue : string -> status -> unit)
             : unit = try
                        if timeout time content
                        then continue label Passed
                        else continue label (Failed fail_msg)
                      with
                      | Timeout -> continue label (Timed_out time)
                      | exn -> continue label
                      (Raised_exn (Printexc.to_string exn))

(*prints the test result passed in from run_test*)
let continue label status =
  match status with
  | Passed -> printf "%s: passed\n" label
  | Failed msg ->
  printf "%s: failed %s\n" label msg
  | Timed_out secs ->
  printf "%s: timed out in %d\n" label secs
  | Raised_exn msg ->
  printf "%s: raised %s\n" label msg ;;

(*runs test over list of tests*)
let report (tests: test list) : unit =
  List.iter (fun test -> run_test test continue) tests ;;

let test ?(fail_msg="somehow") ?(time=5) label content =
  { label = label;
    content = content;
    fail_msg = fail_msg;
    time = time } ;;

(**.............................................................................
Tests
**)
let x : expr = str_to_exp ("x ;;") ;;
let y : expr = str_to_exp ("y ;;") ;;
let f : expr = str_to_exp ("f ;;") ;;

(**expressions for testing free_vars **)
let fun_test0 : expr = str_to_exp ("fun x -> x + 9 ;;") ;;
let let_test0 : expr = str_to_exp ("let y = y in y + 5 ;;") ;;
let let_test01 : expr = str_to_exp ("let f = fun x -> if x = 0 then 1
                                                      else y * f * (x-1) in
                                      f 4 + y ;;") ;;

(**expressions for testing subst **)
let cond_test : expr = str_to_exp ("if x then 9 else y ;;") ;;
let cond_test_1 : expr = str_to_exp ("if 12 then 9 else y ;;") ;;
let cond_test_2 : expr = str_to_exp ("if true then 9 else y ;;") ;;

let fun_test : expr = str_to_exp ("fun x -> y + 9 ;;") ;;
let fun_test_2 : expr = str_to_exp ("fun x -> 12 + 9 ;;") ;;
let fun_test_3 : expr = str_to_exp ("fun var0 -> x + 9 ;;") ;;

let let_test : expr = str_to_exp ("let y = x + 9 in x + y + 5 ;;") ;;
let let_test_2 : expr = str_to_exp ("let y = 12 + 9 in 12 + y + 5 ;;") ;;
let let_test_3 : expr = str_to_exp ("let var1 = 12 + y + 9 in
                                                       12 + y + var1 + 5 ;;") ;;
let let_test_3_def : expr = str_to_exp ("12 + y ;;") ;;
let let_test2 : expr = str_to_exp ("let x = fun y -> x in x ;;") ;;
let let_test2_1 : expr = str_to_exp ("let x = fun y -> 12 in x ;;") ;;


let letrec_test : expr = str_to_exp ("let rec f = fun x -> if x = 0 then 1
                                                           else y * f * (x-1) in
                                      f 4 + y ;;") ;;
let letrec_test_2 : expr = str_to_exp
                   ("let rec f = fun x -> if x = 0 then 1 else 12 * f * (x-1) in
                     f 4 + 12 ;;") ;;
let letrec_test_3 : expr = str_to_exp
              ("let rec var2 = fun x -> if x = 0 then 1 else f * var2 * (x-1) in
                var2 4 + f ;;") ;;

let raise_test : expr = str_to_exp ("x = raise ;;") ;;
let raise_test_1 : expr = str_to_exp ("12 = raise ;;") ;;

let unassigned_test : expr = str_to_exp ("x = Unassigned ;;") ;;
let unassigned_test_1 : expr = str_to_exp ("12 = Unassigned ;;") ;;


let func : expr = str_to_exp ("fun x -> x + 9 ;;") ;;
let app_test : expr = str_to_exp ("f (f 5) ;;") ;;
let app_test_1 : expr = str_to_exp ("(fun x -> x + 9)
                                     ((fun x -> x + 9) 5) ;;") ;;
let app_test2 : expr = str_to_exp ("(fun x -> x + 9) (5 + x) ;;") ;;
let app_test2_1 : expr = str_to_exp ("(fun x -> x + 9) (5 + 12) ;;") ;;

let app_twoargs : expr = str_to_exp ("let x = 12 in let y = x in f x y ;;") ;;

let func_twoargs : expr = str_to_exp ("fun x -> fun y -> x + y ;;") ;;
let func_twoargs2 : expr = str_to_exp ("fun x -> fun y -> x + y + z ;;") ;;
let func_twoargs2_1 : expr = str_to_exp ("fun x -> fun y -> x + y + 12 ;;") ;;

let double_let : expr = str_to_exp ("let f = x in let f = y in 9;;") ;;
let double_let_1 : expr = str_to_exp ("let f = 12 in let f = y in 9;;") ;;

let tests =
[
test "subst x 3*4 x" (lazy (subst "x" (Binop (Times, Num 3, Num 4)) x =
                                                  Binop (Times, Num 3, Num 4)));
test "subst x 12 9" (lazy (subst "x" (Num 12) (Num 9) = Num 9));
test "subst x 12 y" (lazy (subst "x" (Num 12) y = y));
test "subst x 12 x" (lazy (subst "x" (Num 12) x = Num 12));
test "subst x 12 -x" (lazy (subst "x" (Num 12) (Unop (Negate, x)) =
                                                        Unop (Negate, Num 12)));
test "subst x 12 x*y" (lazy (subst "x" (Num 12) (Binop (Times, x, y)) =
                                                     Binop (Times, Num 12, y)));

test "subst x 12 cond_test" (lazy (subst "x" (Num 12) cond_test = cond_test_1));
test "subst x true cond_test" (lazy (subst "x" (Bool true) cond_test =
                                                                  cond_test_2));

test "subst x 12 fun_test" (lazy (subst "x" (Num 12) fun_test = fun_test));
test "subst y 12 fun_test" (lazy (subst "y" (Num 12) fun_test = fun_test_2));
test "subst y x fun_test" (lazy (subst "y" x fun_test = fun_test_3));

test "subst y 12 let_test" (lazy (subst "y" (Num 12) let_test = let_test));
test "subst x 12 let_test" (lazy (subst "x" (Num 12) let_test = let_test_2));
test "subst x 12+y let_test" (lazy (subst "x" let_test_3_def
                                                        let_test = let_test_3));
test "subst x 12 let_test2" (lazy (subst "x" (Num 12) let_test2 = let_test2_1));

test "subst f 12 letrec_test" (lazy (subst "f" (Num 12) letrec_test =
                                                                  letrec_test));
test "subst y 12 letrec_test" (lazy (subst "y" (Num 12) letrec_test =
                                                                  letrec_test_2));
test "subst y f letrec_test" (lazy (subst "y" f letrec_test = letrec_test_3));

test "subst x 12 raise_test" (lazy (subst "x" (Num 12) raise_test =
                                                                 raise_test_1));
test "subst x 12 unassigned_test" (lazy (subst "x" (Num 12) unassigned_test =
                                                            unassigned_test_1));

test "subst f func (f 5)" (lazy (subst "f" func (App (f, Num 5)) =
                                                            App (func, Num 5)));
test "subst f func (f (f 5))" (lazy (subst "f" func app_test = app_test_1));
test "subst x 12 (func 5)" (lazy (subst "x" (Num 12) (App (func, Num 5)) =
                                                            App (func, Num 5)));
test "subst x 12 (func (5+x))" (lazy (subst "x" (Num 12) app_test2 =
                                                                  app_test2_1));
test "subst x 12 app_twoargs" (lazy (subst "x" (Num 12) app_twoargs =
                                                                  app_twoargs));

test "subst x 12 func_twoargs" (lazy (subst "x" (Num 12) func_twoargs =
                                                                 func_twoargs));
test "subst z 12 func_twoargs2" (lazy (subst "z" (Num 12) func_twoargs2 =
                                                              func_twoargs2_1));

test "subst x 12 double_let" (lazy (subst "x" (Num 12) double_let =
                                                                 double_let_1));

test "free_vars x" (lazy (free_vars x = vars_of_list ["x"]));
test "free_vars x*x" (lazy (free_vars (Binop (Times, x, x)) =
                                                           vars_of_list ["x"]));
test "free_vars 9" (lazy (free_vars (Num 9) = vars_of_list []));
test "free_vars true" (lazy (free_vars (Bool true) = vars_of_list []));
test "free_vars ~-x" (lazy (free_vars (Unop (Negate, x)) = vars_of_list ["x"]));
test "free_vars x*9" (lazy (free_vars (Binop (Times, x, Num 9)) =
                                                           vars_of_list ["x"]));
test "free_vars x*y" (lazy (free_vars (Binop (Times, x, y)) =
                                                      vars_of_list ["x"; "y"]));

test "free_vars cond_test" (lazy (free_vars cond_test =
                                                      vars_of_list ["x"; "y"]));

test "free_vars fun_test0" (lazy (free_vars fun_test0 = vars_of_list []));
test "free_vars fun_test" (lazy (free_vars fun_test = vars_of_list ["y"]));
test "free_vars app_twoargs" (lazy (free_vars app_twoargs = vars_of_list ["f"]));

test "free_vars let_test" (lazy (free_vars let_test = vars_of_list ["x"]));
test "free_vars let_test0" (lazy (free_vars let_test0 = vars_of_list ["y"]));
test "free_vars let_test01" (lazy (free_vars let_test01 =
                                                      vars_of_list ["f"; "y"]));
test "free_vars let_test2" (lazy (free_vars let_test2 = vars_of_list ["x"]));


test "free_vars letrec_test" (lazy (free_vars letrec_test =
                                                           vars_of_list ["y"]));
test "free_vars letrec_test_2" (lazy (free_vars letrec_test_2 =
                                                              vars_of_list []));

test "free_vars raise_test_1" (lazy (free_vars raise_test_1 = vars_of_list []));
(* don't know why this fails, in utop free_vars returns this set *)
test "free_vars unassigned_test_1" (lazy (free_vars unassigned_test_1 =
                                                  vars_of_list ["Unassigned"]));

test "free_vars double_let" (lazy (free_vars double_let =
                                                      vars_of_list ["x"; "y"]));

test "free_vars app_test" (lazy (free_vars app_test = vars_of_list ["f"]));
test "free_vars app_test_1" (lazy (free_vars app_test_1 = vars_of_list []));
test "free_vars app_test2" (lazy (free_vars app_test2 = vars_of_list ["x"]));
test "free_vars app_test2_1" (lazy (free_vars app_test2_1 = vars_of_list []))
];;

report tests ;;
