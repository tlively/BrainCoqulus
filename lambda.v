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
| l_lam : Lambda -> Lambda
| l_app : Lambda -> Lambda -> Lambda.

Function lambda_replace (e: Lambda) (x: Lambda) (n: nat): Lambda :=
  match e with
  | l_var m => if m =? n then x else e
  | l_lam e' => l_lam (lambda_replace e' x (S n))
  | l_app e1 e2 => l_app (lambda_replace e1 x n) (lambda_replace e2 x n)
  end.

(* TODO: Do we want CBV instead? *)
Function lambda_step (e: Lambda): option Lambda :=
  match e with
  | l_var _ => None
  | l_lam e' =>
    match lambda_step e' with
    | Some e'' => Some (l_lam e'')
    | None => None
    end
  | l_app (l_lam e1) e2 => Some (lambda_replace e1 e2 0)
  | l_app e1 e2 =>
    match lambda_step e1 with
    | Some e1' => Some (l_app e1' e2)
    | None =>
      match lambda_step e2 with
      | Some e2' => Some (l_app e1 e2')
      | None => None
      end
    end
  end.

Function lambda_run (e: Lambda) (fuel: nat): option Lambda :=
  match fuel with
  | 0 => None
  | S f =>
    match lambda_step e with
    | None => Some e
    | Some e' => lambda_run e' f
    end
  end.

Section LambdaParsing.

  Local Inductive LambdaTree : Set :=
  | lam_end
  | lam_lam (t: LambdaTree)
  | lam_dot (t: LambdaTree)
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
    | lam_id s t' => lam_id s (lambda_strip_wsp t')
    | lam_paren inner t' =>
      lam_paren (lambda_strip_wsp inner) (lambda_strip_wsp t')
    end.

  Local Inductive NamedLambda : Set :=
  | nl_var (s: string)
  | nl_lam (s: string) (e: NamedLambda)
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
      match  named_lambda_of_tree [] t' with
      | None => None
      | Some e => Some (nl_lam s e)
      end
    | lam_lam _ | lam_dot _ => None
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
      let stripped := lambda_strip_names e (x :: xs) in
      match stripped with
      | Some e' => Some (l_lam e')
      | None => None
      end
    | nl_app e1 e2 =>
      let stripped := (lambda_strip_names e1 xs, lambda_strip_names e2 xs) in
      match stripped with
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
