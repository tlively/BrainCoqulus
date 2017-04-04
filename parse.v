Require Import Strings.String.
Require Import Strings.Ascii.
Require Import OrderedType OrderedTypeEx.
Import ListNotations.

Module Parse.

  Inductive ParseState {AST: Type}: Type :=
  | ok (cur: AST) (stack: list AST)
  | error.

  Function chars_of_string (str: string): list ascii :=
    match str with
    | EmptyString => []
    | String a str' => a :: (chars_of_string str')
    end.

  Function string_of_chars (l: list ascii): string :=
    match l with
    | [] => EmptyString
    | a :: l' => String a (string_of_chars l')
    end.

  Lemma chars_of_string_of_chars_inv (l: list ascii):
    chars_of_string (string_of_chars l) = l.
  Proof.
    induction l; auto.
    rewrite string_of_chars_equation, chars_of_string_equation.
    now rewrite IHl.
  Qed.

End Parse.
