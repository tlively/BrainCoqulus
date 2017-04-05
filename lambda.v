Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import ZArith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.Program.Tactics.
Import ListNotations.

Load parse.

(* Lambda Calculus with 0-indexed De Bruijn indices *)
Inductive Lambda : Set :=
| l_var : nat -> Lambda
| l_out : Lambda -> Lambda
| l_lam : Lambda -> Lambda
| l_app : Lambda -> Lambda -> Lambda.

Section LambdaParsing.

  Local Inductive LambdaTree : Set :=
  | lam_end
  | lam_lam (t: LambdaTree)
  | lam_dot (t: LambdaTree)
  | lam_out (t: LambdaTree)
  | lam_wsp (t: LambdaTree)
  | lam_id (str: string) (t: LambdaTree)
  | lam_paren (inner: LambdaTree) (t: LambdaTree).

  Local Definition ParseState := @Parse.ParseState LambdaTree.

  Function parse_lambdatree_state (l: list ascii): ParseState :=
    match l with
    | [] => Parse.ok lam_end []
    | hd :: tl =>
      match parse_lambdatree_state tl with
      | Parse.error => Parse.error
      | Parse.ok cur stack =>
        match hd with
        | "032"%char
        | "009"%char
        | "010"%char
        | "013"%char =>
          match cur with
          | lam_wsp _ => Parse.ok cur stack
          | _ => Parse.ok (lam_wsp cur) stack
          end
        | "\"%char => Parse.ok (lam_lam cur) stack
        | "."%char => Parse.ok (lam_dot cur) stack
        | "^"%char => Parse.ok (lam_out cur) stack
        | ")"%char => Parse.ok (lam_end) (cur :: stack)
        | "("%char =>
          match stack with
          | [] => Parse.error
          | next :: stack' => Parse.ok (lam_paren cur next) stack'
          end
        | _ =>
          match cur with
          | lam_id str next => Parse.ok (lam_id (String hd str) next) stack
          | _ => Parse.ok (lam_id (String hd EmptyString) cur) stack
          end
        end
      end
    end.

  Function lambda_strip_wsp (t: LambdaTree): LambdaTree :=
    match t with
    | lam_end => lam_end
    | lam_wsp t' => lambda_strip_wsp t'
    | lam_lam t' => lam_lam (lambda_strip_wsp t')
    | lam_dot t' => lam_dot (lambda_strip_wsp t')
    | lam_out t' => lam_out (lambda_strip_wsp t')
    | lam_id s t' => lam_id s (lambda_strip_wsp t')
    | lam_paren inner t' =>
      lam_paren (lambda_strip_wsp inner) (lambda_strip_wsp t')
    end.

  Local Inductive NamedLambda : Set :=
  | nl_var (s: string)
  | nl_lam (s: string) (e: NamedLambda)
  | nl_out (e: NamedLambda)
  | nl_app (e1: NamedLambda) (e2: NamedLambda).

  Function app_of_lambda_list (ls: list NamedLambda) {measure List.length ls}:
    option NamedLambda :=
    match ls with
    | [] => None
    | e :: [] => Some e
    | e1 :: e2 :: tl => app_of_lambda_list ((nl_app e1 e2) :: tl)
    end.
  intuition.
  Defined.

  Function named_lambda_of_tree (acc: list NamedLambda) (t: LambdaTree):
    option NamedLambda :=
    match t with
    | lam_end => app_of_lambda_list (rev acc)
    | lam_wsp _ => None
    | lam_lam (lam_id s (lam_dot t')) =>
      match named_lambda_of_tree [] t' with
      | None => None
      | Some e => Some (nl_lam s e)
      end
    | lam_lam _ | lam_dot _ => None
    | lam_out t' =>
      match named_lambda_of_tree [] t' with
      | None => None
      | Some e => Some (nl_out e)
      end
    | lam_id s t' => named_lambda_of_tree (nl_var s :: acc) t'
    | lam_paren inner t' =>
      match named_lambda_of_tree [] inner with
      | None => None
      | Some e => named_lambda_of_tree (e :: acc) t'
      end
    end.

  Function parse_named_lambda (s: string): option NamedLambda :=
    match parse_lambdatree_state (Parse.chars_of_string s) with
    | Parse.error => None
    | Parse.ok cur stack =>
      match stack with
      | _ :: _ => None
      | [] => named_lambda_of_tree [] (lambda_strip_wsp cur)
      end
    end.

  Example named_id: parse_named_lambda "\x.x" = Some (nl_lam "x" (nl_var "x")).
  auto. Qed.

  Example named_true:
    parse_named_lambda "\x.\y.x" = Some (nl_lam "x" (nl_lam "y" (nl_var "x"))).
  auto. Qed.

  Example named_false:
    parse_named_lambda " \ x . \ y  .  (y  ) " =
    Some (nl_lam "x" (nl_lam "y" (nl_var "y"))).
  auto. Qed.

  Example named_out:
    parse_named_lambda "\x.^x" = Some (nl_lam "x" (nl_out (nl_var "x"))).
  auto. Qed.

  Example named_Y:
    parse_named_lambda "\f.(\x.f (x x)) (\x.f (x x))" =
    let fn_app := nl_app (nl_var "f") (nl_app (nl_var "x") (nl_var "x")) in
    Some (nl_lam "f" (nl_app (nl_lam "x" fn_app) (nl_lam "x" fn_app))).
  auto. Qed.

  Example named_parens:
    parse_named_lambda "(((\x.(((x))))))" = Some (nl_lam "x" (nl_var "x")).
  auto. Qed.

  Example named_apps:
    parse_named_lambda "x y z w" =
    Some (nl_app (
              nl_app (
                  nl_app (nl_var "x") (nl_var "y")
                ) (nl_var "z")
            ) (nl_var "w")).
  auto. Qed.

  Example named_bad_lambdas: parse_named_lambda "\\x.x" = None.
  auto. Qed.

  Example named_bad_dots: parse_named_lambda "\x..x" = None.
  auto. Qed.

  Example named_bad_parens: parse_named_lambda "\x.((x)" = None.
  auto. Qed.

  Example named_bad_parens2: parse_named_lambda "\x.x ()" = None.
  auto. Qed.

  Function index_of (x: string) (l: list string): option nat :=
    match l with
    | [] => None
    | hd :: tl =>
      if string_dec hd x then Some 0
      else match index_of x tl with
           | Some i => Some (S i)
           | None => None
           end
    end.

  Function lambda_strip_names (l: NamedLambda) (xs: list string):
    option Lambda :=
    match l with
    | nl_var x =>
      match index_of x xs with
      | Some n => Some (l_var n)
      | None => None
      end
    | nl_lam x e =>
      match lambda_strip_names e (x :: xs) with
      | Some e' => Some (l_lam e')
      | None => None
      end
    | nl_out e =>
      match lambda_strip_names e xs with
      | Some e' => Some (l_out e')
      | None => None
      end
    | nl_app e1 e2 =>
      match (lambda_strip_names e1 xs, lambda_strip_names e2 xs) with
      | (Some e1', Some e2') => Some (l_app e1' e2')
      | _ => None
      end
    end.

  Function parse_lambda (s: string): option Lambda :=
    match parse_named_lambda s with
    | None => None
    | Some nl => lambda_strip_names nl []
    end.

  Example lambda_id: parse_lambda "\x.x" = Some (l_lam (l_var 0)).
  auto. Qed.

  Example lambda_true:
    parse_lambda "\x.\y.x" = Some (l_lam (l_lam (l_var 1))).
  auto. Qed.

  Example lambda_false:
    parse_lambda " \ x . \ y  .  (y  ) " =  Some (l_lam (l_lam (l_var 0))).
  auto. Qed.

  Example lambda_out:
    parse_lambda "\x.^x" = Some (l_lam (l_out (l_var 0))).
  auto. Qed.

  Example lambda_Y:
    parse_lambda "\f.(\x.f (x x)) (\x.f (x x))" =
    let fn_app := l_app (l_var 1) (l_app (l_var 0) (l_var 0)) in
    Some (l_lam (l_app (l_lam fn_app) (l_lam fn_app))).
  auto. Qed.

  Example lambda_parens:
    parse_lambda "(((\x.(((x))))))" = Some (l_lam (l_var 0)).
  auto. Qed.

  Example lambda_apps:
    parse_lambda "x y z w" = None.
  auto. Qed.

End LambdaParsing.

Function lambda_replace (e: Lambda) (x: Lambda) (n: nat): Lambda :=
  match e with
  | l_var m => if m =? n then x else e
  | l_lam e' => l_lam (lambda_replace e' x (S n))
  | l_out e' => l_out (lambda_replace e' x n)
  | l_app e1 e2 => l_app (lambda_replace e1 x n) (lambda_replace e2 x n)
  end.

Function count_apps (e: Lambda): option nat :=
  match e with
  | l_var 0 => Some 0
  | l_app (l_var 1) e' =>
    match count_apps e' with
    | Some n => Some (S n)
    | None => None
    end
  | _ => None
  end.

Function nat_of_lambda (e: Lambda): option nat :=
  match e with
  | l_lam (l_lam e') => count_apps e'
  | _ => None
  end.

(* Call by value semantics *)
Function lambda_step (e: Lambda): (option Lambda * option nat) :=
  match e with
  | l_var _ => (None, None)
  | l_lam e' => (None, None)
  | l_out e' =>
    match lambda_step e' with
    | (Some e'', n) => (Some (l_out e''), n)
    | (None, None) => (Some e', nat_of_lambda e')
    | (None, _) => (None, None)
    end
  | l_app e1 e2 =>
    match lambda_step e1 with
    | (Some e1', n) => (Some (l_app e1' e2), n)
    | (None, _) =>
      match lambda_step e2 with
      | (Some e2', n) => (Some (l_app e1 e2'), n)
      | (None, _) =>
        match e1 with
        | l_lam e1' => (Some (lambda_replace e1' e2 0), None)
        | _ => (None, None)
        end
      end
    end
  end.

(* (* non-CBV semantics *) *)
(* Function lambda_step (e: Lambda): (option Lambda * option nat) := *)
(*   match e with *)
(*   | l_var _ => (None, None) *)
(*   | l_lam e' => *)
(*     match lambda_step e' with *)
(*     | (Some e'', n) => (Some (l_lam e''), n) *)
(*     | (None, _) => (None, None) *)
(*     end *)
(*   | l_out e' => *)
(*     match lambda_step e' with *)
(*     | (Some e'', n) => (Some (l_out e''), n) *)
(*     | (None, None) => (Some e', nat_of_lambda e') *)
(*     | (None, _) => (None, None) *)
(*     end *)
(*   | l_app e1 e2 => *)
(*     match lambda_step e1 with *)
(*     | (Some e1', n) => (Some (l_app e1' e2), n) *)
(*     | (None, _) => *)
(*       match lambda_step e2 with *)
(*       | (Some e2', n) => (Some (l_app e1 e2'), n) *)
(*       | (None, _) => *)
(*         match e1 with *)
(*         | l_lam e1' => (Some (lambda_replace e1' e2 0), None) *)
(*         | _ => (None, None) *)
(*         end *)
(*       end *)
(*     end *)
(*   end. *)

Inductive LambdaState :=
| lambda_state (output: list nat) (l: Lambda).

(* DEBUGGING! *)
Function lambda_steps (l: Lambda) (fuel: nat): (Lambda * nat) :=
  match fuel with
  | 0 => (l, fuel)
  | S f =>
    match lambda_step l with
    | (Some l', _) => lambda_steps l' f
    | _ => (l, fuel)
    end
  end.

(* TODO: test me *)
Function lambda_run (state: LambdaState) (fuel: nat): option (list nat) :=
  match fuel with
  | 0 => None
  | S f =>
    match state with
    | lambda_state out e =>
      match lambda_step e with
      | (Some e', None) => lambda_run (lambda_state out e') f
      | (Some e', Some n) => lambda_run (lambda_state (out ++ [n]) e') f
      | (None, _) => Some out
      end
    end
  end.

Definition l_id := l_lam (l_var 0).

Function parse_def (s: string): Lambda :=
  match parse_lambda s with
  | Some l => l
  | None => l_id
  end.

(* TODO: test/prove these *)
Definition l_zero := parse_def "\f.\x.x".
Definition l_succ := parse_def "\n.\f.\x.f (n f x)".
Definition l_true := parse_def "\x.\y.x".
Definition l_false := parse_def "\x.\y.y".
Definition l_empty := parse_def "\f.f (\x.\y.\x) (\x.x)".
Definition l_cons := parse_def "\a.\l.\f.f (\x.\y.y) (\f.f a l)".
Definition l_isempty := parse_def "\l.l (\x.\y.x)".
Definition l_head := parse_def "\l.l (\x.\y.y) (\x.\y.x)".
Definition l_tail := parse_def "\l.l (\x.\y.y) (\x.\y.y)".

Function lambda_unfold_nat (n: nat): Lambda :=
  match n with
  | 0 => l_var 0
  | S n' => l_app (l_var 1) (lambda_unfold_nat n')
  end.

Definition lambda_of_nat (n: nat): Lambda :=
  l_lam (l_lam (lambda_unfold_nat n)).

(* TODO: Reduce before returning *)
Function lambda_of_nats (ns: list nat): Lambda :=
  match ns with
  | [] => l_empty
  | hd :: tl => l_lam (l_app (l_app (l_var 0) (l_lam (l_lam (l_var 0)))) (l_lam (l_app (l_app (l_var 0) (lambda_of_nat hd)) (lambda_of_nats tl))))
  end.

(* The important interpreter as far as the spec is concerned *)
Function interpret_lambda (prog: string) (input: list nat) (f: nat):
  option (list nat) :=
  match parse_lambda prog with
  | None => None
  | Some l => lambda_run (lambda_state [] (l_app l (lambda_of_nats input))) f
  end.


Eval compute in lambda_run (lambda_state [] (l_app (parse_def "\x.^(x (\x.\y.y) (\x.\y.x))") (lambda_of_nats [72]))) 20.


Function nats_of_string (str: string): list nat :=
  match str with
  | EmptyString => []
  | String a str' => nat_of_ascii a :: (nats_of_string str')
  end.

Function string_of_nats (ns: list nat): string :=
  match ns with
  | [] => EmptyString
  | n :: ns' => String (ascii_of_nat n) (string_of_nats ns')
  end.

Function interpret_lambda_readable (prog: string) (input: string) (f: nat):
  string :=
  match interpret_lambda prog (nats_of_string input) f with
  | None => EmptyString
  | Some ns => string_of_nats ns
  end.

Eval compute in parse_named_lambda "\input.((\head. ^ (head input)) \l.(\x.\y.y) (\x.\y.x))".

Eval compute in interpret_lambda "\input.((\head. ^ (head input)) (\l.l (\x.\y.y) (\x.\y.x)))" [72] 100.

Eval compute in interpret_lambda_readable "\input.((\head. ^ (head input)) (\l.l (\x.\y.y) (\x.\y.x)))" "!" 100.

Definition THETA := "((\x.\y.(y (\z.x x y z))) (\x.\y.(y (\z.x x y z))))"%string.
Definition ISEMPTY := "(\l.l (\x.\y.x))"%string.
Definition HEAD := "(\l.l (\x.\y.y) (\x.\y.x))"%string.
Definition TAIL := "(\l.l (\x.\y.y) (\x.\y.y))"%string.

Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  0.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  1.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  2.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  3.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  4.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  5.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  6.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  7.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  8.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  9.
Eval compute in lambda_steps
                  (l_app (parse_def ("\input." ++
                                        THETA ++
                                        "(\f.\l.("++ISEMPTY++" l)" ++
                                        "(\x.x)" ++
                                        "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
                                        "input"))
                         (lambda_of_nats [0;1]))
                  10.


Eval compute in
    interpret_lambda_readable
      ("\input." ++
         THETA ++
         "(\f.\l.("++ISEMPTY++" l)" ++
                "(\x.x)" ++
                "((\_.f ("++TAIL++"l)) ^("++HEAD++ "l)))" ++
         "input")
      "Hello, world!" 20000.



Eval compute in interpret_lambda_readable "\input.(\f.\g.(g (\h. f f g h))) (\f.\g.(g (\h. f f g h))) (\f.\l.(l (\x.\y.x)) (\x.x) ((\_.f (l \x.\y.y) (\x.\y.y)) ^ (l (\x.\y.y) (\x.\y.x)))) input" "He" 30000.

(* TODO: Hello world *)
