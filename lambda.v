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
Load sml.

Module Lambda.

  (* Lambda Calculus with 0-indexed De Bruijn indices *)
  Inductive Lambda : Set :=
  | var : nat -> Lambda
  | out : Lambda -> Lambda
  | lam : Lambda -> Lambda
  | app : Lambda -> Lambda -> Lambda.

  (* For debugging lambda programs *)
  Function print_lambda (l: Lambda): string :=
    match l with
    | var n =>
      (String (ascii_of_nat (n + (nat_of_ascii "0"%char))) EmptyString)
    | out l' => "^("%string ++ (print_lambda l') ++ ")"%string
    | lam l' => "(\."%string ++ (print_lambda l') ++ ")"%string
    | app l1 l2 => "("%string ++ (print_lambda l1) ++ " "%string
                      ++ (print_lambda l2) ++ ")"%string
    end.

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

    Function app_of_lambda_list (ls: list NamedLambda)
             {measure List.length ls}: option NamedLambda :=
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
        | Some e => app_of_lambda_list (rev ((nl_lam s e) :: acc))
        end
      | lam_lam _ | lam_dot _ => None
      | lam_out t' =>
        match named_lambda_of_tree [] t' with
        | None => None
        | Some e => app_of_lambda_list (rev ((nl_out e) :: acc))
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

    Example named_id:
      parse_named_lambda "\x.x" = Some (nl_lam "x" (nl_var "x")).
    auto. Qed.

    Example named_true:
      parse_named_lambda "\x.\y.x" =
      Some (nl_lam "x" (nl_lam "y" (nl_var "x"))).
    auto. Qed.

    Example named_false:
      parse_named_lambda " \ x . \ y  .  (y  ) " =
      Some (nl_lam "x" (nl_lam "y" (nl_var "y"))).
    auto. Qed.

    Example named_out:
      parse_named_lambda "\x.^x" = Some (nl_lam "x" (nl_out (nl_var "x"))).
    auto. Qed.

    Example named_out_app:
      parse_named_lambda "\x.(\y.y) ^x" =
      Some (nl_lam "x" (nl_app (nl_lam "y" (nl_var "y"))
                               (nl_out (nl_var "x")))).
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
      Some (nl_app (nl_app (nl_app (nl_var "x") (nl_var "y"))
                           (nl_var "z"))
                   (nl_var "w")).
    auto. Qed.

    Example named_inner_app:
      parse_named_lambda "\x.(\y.y) \z.z" =
      Some (nl_lam "x" (nl_app (nl_lam "y" (nl_var "y"))
                               (nl_lam "z" (nl_var "z")))).
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
        | Some n => Some (var n)
        | None => None
        end
      | nl_lam x e =>
        match lambda_strip_names e (x :: xs) with
        | Some e' => Some (lam e')
        | None => None
        end
      | nl_out e =>
        match lambda_strip_names e xs with
        | Some e' => Some (out e')
        | None => None
        end
      | nl_app e1 e2 =>
        match (lambda_strip_names e1 xs, lambda_strip_names e2 xs) with
        | (Some e1', Some e2') => Some (app e1' e2')
        | _ => None
        end
      end.

    Function parse_lambda (s: string): option Lambda :=
      match parse_named_lambda s with
      | None => None
      | Some nl => lambda_strip_names nl []
      end.

    Example lambda_id: parse_lambda "\x.x" = Some (lam (var 0)).
    auto. Qed.

    Example lambda_true:
      parse_lambda "\x.\y.x" = Some (lam (lam (var 1))).
    auto. Qed.

    Example lambda_false:
      parse_lambda " \ x . \ y  .  (y  ) " =  Some (lam (lam (var 0))).
    auto. Qed.

    Example lambda_out:
      parse_lambda "\x.^x" = Some (lam (out (var 0))).
    auto. Qed.

    Example lambda_Y:
      parse_lambda "\f.(\x.f (x x)) (\x.f (x x))" =
      let fn_app := app (var 1) (app (var 0) (var 0)) in
      Some (lam (app (lam fn_app) (lam fn_app))).
    auto. Qed.

    Example lambda_parens:
      parse_lambda "(((\x.(((x))))))" = Some (lam (var 0)).
    auto. Qed.

    Example lambda_apps:
      parse_lambda "x y z w" = None.
    auto. Qed.

  End LambdaParsing.

  Function lambda_replace (e: Lambda) (x: Lambda) (n: nat): Lambda :=
    match e with
    | var m => if m =? n then x else e
    | lam e' => lam (lambda_replace e' x (S n))
    | out e' => out (lambda_replace e' x n)
    | app e1 e2 => app (lambda_replace e1 x n) (lambda_replace e2 x n)
    end.

  Function count_apps (e: Lambda): option nat :=
    match e with
    | var 0 => Some 0
    | app (var 1) e' =>
      match count_apps e' with
      | Some n => Some (S n)
      | None => None
      end
    | _ => None
    end.

  Function nat_of_lambda (e: Lambda): option nat :=
    match e with
    | lam (lam e') => count_apps e'
    | _ => None
    end.

  (* Call by value semantics *)
  Function lambda_step (e: Lambda): option (Lambda * option nat) :=
    match e with
    | var _ => None
    | lam _ => None
    | out e' =>
      match lambda_step e' with
      | Some (e'', n) => Some (out e'', n)
      | None => Some (e', nat_of_lambda e')
      end
    | app e1 e2 =>
      match lambda_step e1 with
      | Some (e1', n) => Some (app e1' e2, n)
      | None =>
        match lambda_step e2 with
        | Some (e2', n) => Some (app e1 e2', n)
        | None =>
          match e1 with
          | lam e1' => Some (lambda_replace e1' e2 0, None)
          | _ => None
          end
        end
      end
    end.

  Inductive LambdaState :=
  | l_state (output: list nat) (l: Lambda).

  Function lambda_steps (state: LambdaState) (fuel: nat):
    (LambdaState * nat) :=
    match fuel with
    | 0 => (state, fuel)
    | S f =>
      match state with
      | l_state output e =>
        match lambda_step e with
        | Some (e', None) => lambda_steps (l_state output e') f
        | Some (e', Some n) => lambda_steps (l_state (output ++ [n]) e') f
        | None => (state, fuel)
        end
      end
    end.

  Function lambda_run (state: LambdaState) (fuel: nat): option LambdaState :=
    match lambda_steps state fuel with
    | (_, 0) => None
    | (state' , _) => Some state'
    end.

  Inductive LambdaNorm :=
  | norm (l: Lambda) (term: lambda_step l = None)
         (no_free: forall l' n, lambda_replace l l' n = l).

  Function get_lam (ln: LambdaNorm): Lambda :=
    match ln with norm l _ _ => l end.

  Definition l_id: LambdaNorm.
    refine (norm (lam (var 0)) _ _); auto.
  Defined.

  Function parse_def (s: string): Lambda :=
    match parse_lambda s with
    | Some l => l
    | None => get_lam l_id
    end.

  Definition ZERO := "(\f.\x.x)"%string.
  Definition SUCC := "(\n.\f.\x.f (n f x))"%string.
  Definition TRUE := "(\x.\y.x)"%string.
  Definition FALSE := "(\x.\y.y)"%string.
  Definition EMPTY := "(\f.f (\x.\y.x) (\x.x))"%string.
  Definition CONS := "(\a.\l.\f.f (\x.\y.y) (\f.f a l))"%string.
  Definition ISEMPTY := "(\l.l (\x.\y.x))"%string.
  Definition HEAD := "(\l.l (\x.\y.y) (\x.\y.x))"%string.
  Definition TAIL := "(\l.l (\x.\y.y) (\x.\y.y))"%string.
  Definition Z := "(\f.(\x.f (\y. x x y))(\x.f (\y. x x y)))"%string.

  Definition l_zero: LambdaNorm.
    refine (norm (parse_def ZERO) _ _); auto.
  Defined.

  Definition l_succ: LambdaNorm.
    refine (norm (parse_def SUCC) _ _); auto.
  Defined.

  Definition l_true: LambdaNorm.
    refine (norm (parse_def TRUE) _ _); auto.
  Defined.

  Definition l_false: LambdaNorm.
    refine (norm (parse_def FALSE) _ _); auto.
  Defined.

  Definition l_empty: LambdaNorm.
    refine (norm (parse_def EMPTY) _ _); auto.
  Defined.

  Definition l_cons: LambdaNorm.
    refine (norm (parse_def CONS) _ _); auto.
  Defined.

  Definition l_isempty: LambdaNorm.
    refine (norm (parse_def ISEMPTY) _ _); auto.
  Defined.

  Definition l_head: LambdaNorm.
    refine (norm (parse_def HEAD) _ _); auto.
  Defined.

  Definition l_tail: LambdaNorm.
    refine (norm (parse_def TAIL) _ _); auto.
  Defined.

  Definition l_z: LambdaNorm.
    refine (norm (parse_def Z) _ _); auto.
  Defined.

  Lemma isempty_correct_emp:
    exists f,
      lambda_run (l_state [] (app (get_lam l_isempty) (get_lam l_empty))) f =
      Some (l_state [] (get_lam l_true)).
  Proof.
    exists 10.
    auto.
  Qed.

  Lemma isempty_correct_cons (hd tl: LambdaNorm):
    exists f,
      lambda_run
        (l_state [] (app (get_lam l_isempty)
                         (app (app (get_lam l_cons) (get_lam hd))
                              (get_lam tl)))) f =
      Some (l_state [] (get_lam l_false)).
  Proof.
    exists 7.
    destruct hd, tl.
    unfold lambda_run.
    simpl.
    unfold ISEMPTY; simpl.
    rewrite term.
    simpl.
    now rewrite term0.
  Qed.

  Eval compute in lambda_steps
        (l_state [] (app (get_lam l_head)
                         (app (app (get_lam l_cons) (get_lam l_zero))
                              (get_lam l_empty)))) 9.

  Lemma head_correct (hd tl: LambdaNorm):
    exists f,
      lambda_run
        (l_state [] (app (get_lam l_head)
                         (app (app (get_lam l_cons) (get_lam hd))
                              (get_lam tl)))) f =
      Some (l_state [] (get_lam hd)).
  Proof.
    exists 10.
    destruct hd, tl.
    unfold lambda_run; simpl.
    rewrite term.
    unfold HEAD, CONS; simpl.
    rewrite term0; simpl.
    repeat rewrite no_free.
    repeat rewrite no_free0.
    rewrite term.
    simpl.
    rewrite term0.
    rewrite no_free.
    now rewrite term.
  Qed.

  Lemma tail_correct (hd tl: LambdaNorm):
    exists f,
      lambda_run
        (l_state [] (app (get_lam l_tail)
                         (app (app (get_lam l_cons) (get_lam hd))
                              (get_lam tl)))) f =
      Some (l_state [] (get_lam tl)).
  Proof.
    exists 10.
    destruct hd, tl.
    unfold lambda_run; simpl.
    rewrite term.
    unfold HEAD, CONS; simpl.
    rewrite term0; simpl.
    repeat rewrite no_free.
    repeat rewrite no_free0.
    rewrite term.
    simpl.
    now repeat rewrite term0.
  Qed.

  Function lambda_unfold_nat (n: nat): Lambda :=
    match n with
    | 0 => var 0
    | S n' => app (var 1) (lambda_unfold_nat n')
    end.

  Definition lambda_of_nat (n: nat): Lambda :=
    lam (lam (lambda_unfold_nat n)).

  (* TODO: Reduce before returning *)
  Function lambda_of_nats (ns: list nat): Lambda :=
    match ns with
    | [] => get_lam l_empty
    | hd :: tl => lam (app (app (var 0) (lam (lam (var 0))))
                           (lam (app (app (var 0) (lambda_of_nat hd))
                                     (lambda_of_nats tl))))
    end.

  (* The important interpreter as far as the spec is concerned *)
  Function interpret_lambda (prog: string) (input: list nat) (f: nat):
    option (list nat) :=
    match parse_lambda prog with
    | None => None
    | Some l =>
      match lambda_run (l_state [] (app l (lambda_of_nats input))) f with
      | None => None
      | Some (l_state output _) => Some output
      end
    end.

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

  Definition lambda_echo: string :=
    "\input."++Z++" (\f.\l.("++ISEMPTY++" l)"++
                          "(\_.\x.x)"++
                          "(\_.(\_.f ("++TAIL++" l)) ^("++HEAD++" l))"++
                          "(\x.x))"++
                    "input".

  Example lambda_hello:
    interpret_lambda_readable lambda_echo "Hello, world!" 364 =
    "Hello, world!"%string.
  Proof. auto. Qed.

  Fixpoint lambda_to_sml (l : Lambda) (ret_addr: option nat) : list SMProgram :=
    match l with
    | var n => match ret_addr with
      | None => [SML.get n SML.sm_end]
      | Some addr => [SML.get n (SML.push addr SML.jump)]
    | out e => match lambda_to_sml e ret_addr with
      | hd :: tl => (SML.out hd) :: tl
      | [] => [] (* error *)
    | lam e => match lambda_to_sml e ret_addr with
      | [] => [] (* error *)
      | lst => lst ++ []
      
    | app e1 e2 => match lambda_to_sml e2 ret_addr with
      | [] => []
      | lst => lst ++ [SML.push((List.length lst) - 1)


      match e1 with
      | lam e1' => 
      | _ => []
      end.

End Lambda.
