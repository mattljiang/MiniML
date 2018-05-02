open Expr ;;
open Printf ;;
open Miniml ;;
open Evaluation ;;

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

let env = Env.create () ;;

let x : expr = str_to_exp ("x ;;") ;;
let y : expr = str_to_exp ("y ;;") ;;
let f : expr = str_to_exp ("f ;;") ;;

(**expressions for testing free_vars **)
let fun_test0 : expr = str_to_exp ("fun x -> x + 9 ;;") ;;
let let_test0 : expr = str_to_exp ("let y = y in y + 5 ;;") ;;
let let_test01 : expr = str_to_exp ("let f = fun x -> if x = 0 then 1
                                                      else f * (x-1) in
                                      f 4 ;;") ;;
let let_test02 : expr = str_to_exp ("let y = 3 in fun x -> y + 9 ;;") ;;

let let_test02_1 : expr = str_to_exp ("fun x -> 3 + 9;;") ;;
let let_test02_2 : expr = str_to_exp ("fun x -> y + 9;;") ;;

let app_test0 : expr = str_to_exp ("(fun x -> x = 3) true ;;") ;;
let app_test01 : expr = str_to_exp ("3 4 ;;") ;;


(**expressions for testing subst **)
let cond_test : expr = str_to_exp ("if x then 1 else 0 ;;") ;;
let cond_test_1 : expr = str_to_exp ("if 12 then 1 else 0 ;;") ;;
let cond_test_2 : expr = str_to_exp ("if true then 1 else 0 ;;") ;;

let fun_test : expr = str_to_exp ("fun x -> y + 9 ;;") ;;
let fun_test_2 : expr = str_to_exp ("fun x -> 12 + 9 ;;") ;;
let fun_test_3 : expr = str_to_exp ("fun var0 -> x + 9 ;;") ;;

let let_test : expr = str_to_exp ("let y = x + 9 in x + y + 5 ;;") ;;
let let_test_2 : expr = str_to_exp ("let y = 12 + 9 in 12 + y + 5 ;;") ;;
let let_test_3 : expr = str_to_exp ("let var1 = 12 + y + 9 in
                                                       12 + y + var1 + 5 ;;") ;;
let let_test_3_def : expr = str_to_exp ("12 + y ;;") ;;
let let_test2 : expr = str_to_exp ("let x = fun y -> x in x ;;") ;;


let letrec_test : expr = str_to_exp ("let rec f = fun x -> if x = 0 then 1
                                      else x * f (x - 1) in f 4 ;;") ;;

let raise_test : expr = str_to_exp ("x = raise ;;") ;;
let raise_test_1 : expr = str_to_exp ("12 = raise ;;") ;;

let unassigned_test : expr = str_to_exp ("x = Unassigned ;;") ;;
let unassigned_test_1 : expr = str_to_exp ("12 = Unassigned ;;") ;;


let func : expr = str_to_exp ("fun x -> x + 9 ;;") ;;
let app_test : expr = str_to_exp ("f (f 5) ;;") ;;
let app_test_1 : expr = str_to_exp ("(fun x -> x + 9)
                                     ((fun x -> x + 9) 5) ;;") ;;
let app_test2 : expr = str_to_exp ("(fun x -> x + 9) (5 + x) ;;") ;;

let app_twoargs : expr = str_to_exp ("let x = 12 in let y = x in f x y ;;") ;;

let func_twoargs : expr = str_to_exp ("fun x -> fun y -> x + y ;;") ;;
let func_twoargs2 : expr = str_to_exp ("fun x -> fun y -> x + y + z ;;") ;;
let func_twoargs2_1 : expr = str_to_exp ("fun x -> fun y -> x + y + 12 ;;") ;;

let double_let : expr = str_to_exp ("let f = x in let f = y in 9 ;;") ;;
let double_let_1 : expr = str_to_exp ("let f = 12 in let f = y in 9 ;;") ;;

let lexscope_test : expr = str_to_exp ("let x = 1 in
                                        let f = fun y -> x + y in
                                        let x = 2 in
                                        f 3 ;;") ;;
let lexscope_test2 : expr = str_to_exp ("let f = fun x -> fun y -> x + y
                                                                 in f 2 3;;") ;;
let lexscope_test3 : expr = str_to_exp("let twice = fun f -> fun x -> f (f x) in
                                         let square = fun x -> x * x in
                                         twice square 3;;") ;;
let new_test (label : string) (eval : expr -> Env.env -> Env.value)
             (exp : expr) (result : Env.value) : test =
             test label (lazy (eval exp env = result)) ;;


let tests =
[
new_test "eval_s x [exn]" eval_s x (Val x);
new_test "eval_s 9" eval_s (Num 9) (Val (Num 9));
new_test "eval_s true" eval_s (Bool true) (Val (Bool true));

new_test "eval_s ~-9" eval_s (Unop (Negate, Num 9)) (Val (Num (-9)));
new_test "eval_s ~-true [exn]" eval_s (Unop (Negate, Bool true)) (Val x);

new_test "eval_s 9+5" eval_s (Binop (Plus, Num 9, Num 5)) (Val (Num 14));
new_test "eval_s 9*5" eval_s (Binop (Times, Num 9, Num 5)) (Val (Num 45));
new_test "eval_s 9-5" eval_s (Binop (Minus, Num 9, Num 5)) (Val (Num 4));
new_test "eval_s 9=5" eval_s (Binop (Equals, Num 9, Num 5)) (Val (Bool false));
new_test "eval_s 9<5" eval_s (Binop (LessThan, Num 9, Num 5)) (Val (Bool false));

new_test "eval_s false<false [exn]" eval_s (Binop
                                    (LessThan, Bool false, Bool false)) (Val x);
new_test "eval_s false=false" eval_s (Binop (Equals, Bool false, Bool false))
                                                              (Val (Bool true));
new_test "eval_s 9+true [exn]" eval_s (Binop (Plus, Num 9, Bool true)) (Val x);
new_test "eval_s cond_test_1 [exn]" eval_s cond_test_1 (Val x);
new_test "eval_s cond_test_2" eval_s cond_test_2 (Val (Num 1));

new_test "eval_s fun_test0" eval_s fun_test0 (Val fun_test0);
new_test "eval_s fun_test" eval_s fun_test (Val fun_test);
new_test "eval_s let_test0 [exn]" eval_s let_test0 (Val x);

new_test "eval_s let_test01 [exn]" eval_s let_test01 (Val x);
new_test "eval_s let_test02" eval_s let_test02 (Val (let_test02_1));
new_test "eval_s let_test [exn]" eval_s let_test (Val (x));
new_test "eval_s let_test_2" eval_s let_test_2 (Val (Num 38));
new_test "eval_s let_test2" eval_s let_test2 (Val (Fun ("y", x)));
new_test "eval_s letrec_test" eval_s letrec_test (Val (Num 24));

new_test "eval_s raise_test_1 [exn]" eval_s raise_test_1 (Val x);
new_test "eval_s unassigned_test_1 [exn]" eval_s unassigned_test_1 (Val x);

new_test "eval_s app_test0 [exn]" eval_s app_test0 (Val x);
new_test "eval_s app_test01 [exn]" eval_s app_test01 (Val x);
new_test "eval_s f (f 5)" eval_s (Let ("f", func, app_test)) (Val (Num 23));
new_test "eval_s app_test_1" eval_s app_test_1 (Val (Num 23));
new_test "eval_s app_test2 [exn]" eval_s app_test2 (Val x);

new_test "eval_s func_twoargs" eval_s func_twoargs (Val func_twoargs);
new_test "eval_s double_let [exn]" eval_s double_let (Val x);

new_test "eval_s lexscope_test" eval_s lexscope_test (Val (Num 4));
new_test "eval_s lexscope_test2" eval_s lexscope_test2 (Val (Num 5));
new_test "eval_s lexscope_test3" eval_s lexscope_test3 (Val (Num 81));


new_test "eval_d x [exn]" eval_d x (Val x);
new_test "eval_d 9" eval_d (Num 9) (Val (Num 9));
new_test "eval_d true" eval_d (Bool true) (Val (Bool true));

new_test "eval_d ~-9" eval_d (Unop (Negate, Num 9)) (Val (Num (-9)));
new_test "eval_d ~-true [exn]" eval_d (Unop (Negate, Bool true)) (Val x);

new_test "eval_d 9+5" eval_d (Binop (Plus, Num 9, Num 5)) (Val (Num 14));
new_test "eval_d 9*5" eval_d (Binop (Times, Num 9, Num 5)) (Val (Num 45));
new_test "eval_d 9-5" eval_d (Binop (Minus, Num 9, Num 5)) (Val (Num 4));
new_test "eval_d 9=5" eval_d (Binop (Equals, Num 9, Num 5)) (Val (Bool false));
new_test "eval_d 9<5" eval_d (Binop (LessThan, Num 9, Num 5)) (Val (Bool false));

new_test "eval_d false<false [exn]" eval_d (Binop
                                    (LessThan, Bool false, Bool false)) (Val x);
new_test "eval_d false=false" eval_d (Binop (Equals, Bool false, Bool false))
                                                              (Val (Bool true));
new_test "eval_d 9+true [exn]" eval_d (Binop (Plus, Num 9, Bool true)) (Val x);
new_test "eval_d cond_test_1 [exn]" eval_d cond_test_1 (Val x);
new_test "eval_d cond_test_2" eval_d cond_test_2 (Val (Num 1));

new_test "eval_d fun_test0" eval_d fun_test0 (Val fun_test0);
new_test "eval_d fun_test [exn]" eval_d fun_test (Val fun_test);
new_test "eval_d let_test0 [exn]" eval_d let_test0 (Val x);

new_test "eval_d let_test01 [exn]" eval_d let_test01 (Val x);
new_test "eval_d let_test02" eval_d let_test02 (Val (let_test02_2));
new_test "eval_d let_test [exn]" eval_d let_test (Val (x));
new_test "eval_d let_test_2" eval_d let_test_2 (Val (Num 38));
new_test "eval_d let_test2" eval_d let_test2 (Val (Fun ("y", x)));
new_test "eval_d letrec_test" eval_d letrec_test (Val (Num 24));

new_test "eval_d raise_test_1 [exn]" eval_d raise_test_1 (Val x);
new_test "eval_d unassigned_test_1 [exn]" eval_d unassigned_test_1 (Val x);

new_test "eval_d app_test0 [exn]" eval_d app_test0 (Val x);
new_test "eval_d app_test01 [exn]" eval_d app_test01 (Val x);
new_test "eval_d f (f 5)" eval_d (Let ("f", func, app_test)) (Val (Num 23));
new_test "eval_d app_test_1" eval_d app_test_1 (Val (Num 23));
new_test "eval_d app_test2 [exn]" eval_d app_test2 (Val x);

new_test "eval_d func_twoargs" eval_d func_twoargs (Val func_twoargs);
new_test "eval_d double_let [exn]" eval_d double_let (Val x);

new_test "eval_d lexscope_test" eval_d lexscope_test (Val (Num 5));
new_test "eval_d lexscope_test2 [exn]" eval_d lexscope_test2 (Val x);
new_test "eval_d lexscope_test3 [exn]" eval_d lexscope_test3 (Val x);

new_test "eval_l x [exn]" eval_l x (Val x);
new_test "eval_l 9" eval_l (Num 9) (Val (Num 9));
new_test "eval_l true" eval_l (Bool true) (Val (Bool true));

new_test "eval_l ~-9" eval_l (Unop (Negate, Num 9)) (Val (Num (-9)));
new_test "eval_l ~-true [exn]" eval_l (Unop (Negate, Bool true)) (Val x);

new_test "eval_l 9+5" eval_l (Binop (Plus, Num 9, Num 5)) (Val (Num 14));
new_test "eval_l 9*5" eval_l (Binop (Times, Num 9, Num 5)) (Val (Num 45));
new_test "eval_l 9-5" eval_l (Binop (Minus, Num 9, Num 5)) (Val (Num 4));
new_test "eval_l 9=5" eval_l (Binop (Equals, Num 9, Num 5)) (Val (Bool false));
new_test "eval_l 9<5" eval_l (Binop (LessThan, Num 9, Num 5)) (Val (Bool false));

new_test "eval_l false<false [exn]" eval_l (
                              Binop (LessThan, Bool false, Bool false)) (Val x);
new_test "eval_l false=false" eval_l (Binop (Equals, Bool false, Bool false))
                                                              (Val (Bool true));
new_test "eval_l 9+true [exn]" eval_l (Binop (Plus, Num 9, Bool true)) (Val x);
new_test "eval_l cond_test_1 [exn]" eval_l cond_test_1 (Val x);
new_test "eval_l cond_test_2" eval_l cond_test_2 (Val (Num 1));

new_test "eval_l fun_test0" eval_l fun_test0 (Val fun_test0);
new_test "eval_l fun_test" eval_l fun_test (Val fun_test);
new_test "eval_l let_test0 [exn]" eval_l let_test0 (Val x);

new_test "eval_l let_test01 [exn]" eval_l let_test01 (Val x);
new_test "eval_l let_test [exn]" eval_l let_test (Val (x));
new_test "eval_l let_test_2" eval_l let_test_2 (Val (Num 38));
new_test "eval_l letrec_test" eval_l letrec_test (Val (Num 24));

new_test "eval_l raise_test_1 [exn]" eval_l raise_test_1 (Val x);
new_test "eval_l unassigned_test_1 [exn]" eval_l unassigned_test_1 (Val x);

new_test "eval_l app_test0 [exn]" eval_l app_test0 (Val x);
new_test "eval_l app_test01 [exn]" eval_l app_test01 (Val x);
new_test "eval_l f (f 5)" eval_l (Let ("f", func, app_test)) (Val (Num 23));
new_test "eval_l app_test_1" eval_l app_test_1 (Val (Num 23));
new_test "eval_l app_test2 [exn]" eval_l app_test2 (Val x);

new_test "eval_l double_let [exn]" eval_l double_let (Val x);

new_test "eval_l lexscope_test" eval_l lexscope_test (Val (Num 4));
new_test "eval_l lexscope_test2" eval_l lexscope_test2 (Val (Num 5));
new_test "eval_l lexscope_test3" eval_l lexscope_test3 (Val (Num 81));
];;

report tests ;;
