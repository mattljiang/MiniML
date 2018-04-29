open Expr ;;
open Printf ;;
open Miniml ;;

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

let let_test : expr = str_to_exp ("let y = x + 9 in x + y + 5 ;;")
let let_test_2 : expr = str_to_exp ("let y = 12 + 9 in 12 + y + 5 ;;")
let tests =
[ test "subst x 12 9"    (lazy (subst "x" (Num 12) (Num 9) = (Num 9)));
  test "subst y 12 let_test_1" (lazy (subst "y" (Num 12) let_test = let_test));
  test "subst x 12 let_test_2" (lazy (subst "x" (Num 12) let_test = let_test_2));

(*   test "subst f 12 letrec" (lazy (subst "f" (Num 12) (Let))) *)
];;

report tests ;;
