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

(* BF Program Type *)
Inductive BF : Set :=
| bf_end : BF
| bf_right : BF -> BF (* > *)
| bf_left : BF -> BF  (* < *)
| bf_inc : BF -> BF   (* + *)
| bf_dec : BF -> BF   (* - *)
| bf_out : BF -> BF   (* . *)
| bf_in : BF -> BF    (* , *)
| bf_loop : BF -> BF -> BF.  (* [...] *)

(* The number of nodes in a BF *)
Function bf_size (bf: BF): nat :=
  match bf with
  | bf_end => 1
  | bf_right bf'
  | bf_left bf'
  | bf_inc bf'
  | bf_dec bf'
  | bf_in bf'
  | bf_out bf' => S (bf_size bf')
  | bf_loop inner bf' => S (bf_size inner + (bf_size bf'))
  end.

Section BFPrinting.
  Local Fixpoint bf_str_measure (state: BF * list BF): nat :=
    let (bf, stack) := state in
    fold_left (fun acc bf => acc + (bf_size bf)) (bf :: stack) 0.

  Local Lemma lt_a0_lt_fold (bfs: list BF) (a0: nat):
    fold_left (fun acc bf => acc + (bf_size bf)) bfs a0 <
    fold_left (fun acc bf => acc + (bf_size bf)) bfs (S a0).
  Proof.
    revert a0; induction bfs; auto; intros.
    replace (a :: bfs) with ([a] ++ bfs) by intuition.
    rewrite fold_left_app; simpl.
    auto.
  Qed.

  Function bf_to_string (state: BF * list BF)
           {measure bf_str_measure state}: string :=
    let (bf, stack) := state in
    match bf with
    | bf_end =>
      match stack with
      | [] => EmptyString
      | bf' :: stack' => String "]" (bf_to_string (bf', stack'))
      end
    | bf_right bf' => String ">" (bf_to_string (bf', stack))
    | bf_left bf' => String "<" (bf_to_string (bf', stack))
    | bf_inc bf' => String "+" (bf_to_string (bf', stack))
    | bf_dec bf' => String "-" (bf_to_string (bf', stack))
    | bf_out bf' => String "." (bf_to_string (bf', stack))
    | bf_in bf' => String "," (bf_to_string (bf', stack))
    | bf_loop inner bf' => String "[" (bf_to_string (inner, (bf' :: stack)))
    end.
  Proof.
    all: intros; subst; simpl; apply lt_a0_lt_fold.
  Defined.

  Function string_of_bf (bf: BF): string :=
    bf_to_string (bf, []).

  Example print_all_bf_commands:
    string_of_bf
      (bf_loop
         (bf_right (bf_left (bf_inc (bf_dec (bf_out (bf_in bf_end))))))
         bf_end)
    = "[><+-.,]"%string. auto.
  Qed.
End BFPrinting.

Section BFParsing.
  Local Inductive ParseState: Type :=
  | parse_ok (str: string) (acc: BF) (stack: list BF)
  | parse_eof (acc: BF) (stack: list BF)
  | parse_error.

  Local Fixpoint parse_state_size (state: ParseState): nat :=
    match state with
    | parse_ok str _ _  => String.length str
    | parse_eof _ _ | parse_error => 0
    end.

  Function bf_parse (state: ParseState)
           {measure parse_state_size state}: ParseState :=
    match state with
    | parse_error
    | parse_eof _ _ => parse_error
    | parse_ok str acc stack =>
      match str with
      | EmptyString => parse_eof acc stack
      | String ">" str' => bf_parse (parse_ok str' (bf_right acc) stack)
      | String "<" str' => bf_parse (parse_ok str' (bf_left acc) stack)
      | String "+" str' => bf_parse (parse_ok str' (bf_inc acc) stack)
      | String "-" str' => bf_parse (parse_ok str' (bf_dec acc) stack)
      | String "." str' => bf_parse (parse_ok str' (bf_out acc) stack)
      | String "," str' => bf_parse (parse_ok str' (bf_in acc) stack)
      | String "]" str' => bf_parse (parse_ok str' bf_end (acc :: stack))
      | String "[" str' =>
        match stack with
        | [] => parse_error
        | acc' :: stack' => bf_parse (parse_ok str' (bf_loop acc acc') stack')
        end
      | String _ str' => bf_parse (parse_ok str' acc stack)
      end
    end.
  Proof.
    all: intros; subst; unfold parse_state_size; simpl; auto.
  Defined.

  Function rev_string (acc: string) (str: string): string :=
    match str with
    | EmptyString => acc
    | String c str' => rev_string (String c acc) str'
    end.

  Function parse_bf (bf: string): option BF :=
    match bf_parse (parse_ok (rev_string EmptyString bf) bf_end []) with
    | parse_ok _ _ _ | parse_error => None
    | parse_eof _ (_ :: _) => None
    | parse_eof ast [] => Some ast
    end.

  Example parse_all_bf_commands:
    parse_bf "[><+-.,]" =
    Some (bf_loop
            (bf_right (bf_left (bf_inc (bf_dec (bf_out (bf_in bf_end))))))
            bf_end).
  auto. Qed.

  Example parse_nesting_bf:
    parse_bf "[[[][]]][]" =
    Some (bf_loop
            (bf_loop
               (bf_loop bf_end (bf_loop bf_end bf_end))
               bf_end)
            (bf_loop bf_end bf_end)).
  auto. Qed.

  Example parse_empty_bf:
    parse_bf EmptyString = Some bf_end.
  auto. Qed.

  Example parse_bf_bad_left:
    parse_bf "[[]" = None.
  auto. Qed.

  Example parse_bf_bad_right:
    parse_bf "[]]" = None.
  auto. Qed.
End BFParsing.

Hint Unfold string_of_bf parse_bf.

(* TODO: Prove this *)
(* Idea: change parser to build from front instead of back to
eliminate string reversal *)
Lemma parse_print_inverse (bf: BF): parse_bf (string_of_bf bf) = Some bf.
  unfold string_of_bf.
  induction bf; auto.
  - rewrite bf_to_string_equation.
    unfold parse_bf.
    simpl.

  unfold string_of_bf.
  unfold parse_bf.
  remember (bf, []) as state.
  revert bf Heqstate.
  functional induction (bf_to_string state); intros; auto.
  - replace bf with bf_end by congruence; auto.
  - assert (bf' :: stack' = []) by congruence; discriminate.
  - replace bf with (bf_right bf') by congruence.


(* BF Interpreter *)
(* A BFTape is a map from [nat] indices to [Z] values *)
Module NatMap := FMapList.Make Nat_as_OT.
Definition BFTape := NatMap.t Z.

Definition tape_get (tape: BFTape) (ptr: nat): Z :=
  match (NatMap.find ptr tape) with
  | Some x => x
  | None => 0
  end.

Definition tape_set (tape: BFTape) (ptr: nat) (x: Z): BFTape :=
  NatMap.add ptr x tape.

Definition tape_inc (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.succ (tape_get tape ptr)).

Definition tape_dec (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.pred (tape_get tape ptr)).

(* `bf' is the current state of the program, while `resets' is the
stack of programs to reset to at the end of a loop *)
(* TODO: Generalize to all tape languages *)
Inductive BFState : Type :=
  bf_state (bf: BF)
           (resets: list BF)
           (ptr: nat)
           (tape: BFTape)
           (input: list Z)
           (output: list Z).

Function state_init (bf: BF) (input: list Z): BFState :=
  bf_state bf [] 0 (NatMap.empty Z) input [].

Function state_output (state: BFState): list Z :=
  match state with bf_state _ _ _ _ _ output => output end.

Function bf_step (state: BFState): option BFState :=
  match state with
  | bf_state bf resets ptr tape input output =>
    match bf with
     | bf_end =>
       match resets with
        | [] => None
        | bf' :: resets' =>
          Some (bf_state bf' resets' ptr tape input output)
        end
     | bf_right bf' =>
       Some (bf_state bf' resets (S ptr) tape input output)
     | bf_left bf' =>
       Some (bf_state bf' resets (pred ptr) tape input output)
     | bf_inc bf' =>
       Some (bf_state bf' resets ptr (tape_inc tape ptr) input output)
     | bf_dec bf' =>
       Some (bf_state bf' resets ptr (tape_dec tape ptr) input output)
     | bf_out bf' =>
       Some (bf_state bf' resets ptr tape input (output ++ [tape_get tape ptr]))
     | bf_in bf' =>
       match input with
        | [] =>
          Some (bf_state bf' resets ptr (tape_set tape ptr 0) input output)
        | x :: input' =>
          Some (bf_state bf' resets ptr (tape_set tape ptr x) input' output)
        end
     | bf_loop inner_bf bf' =>
       if Z.eqb (tape_get tape ptr) Z.zero then
         Some (bf_state bf' resets ptr tape input output)
       else
          Some (bf_state inner_bf (bf :: resets) ptr tape input output)
     end
  end.

(* TODO: Use N as fuel with {measure N.to_nat fuel} *)
Function bf_run (state: BFState) (fuel: nat): option (list Z) :=
  match fuel with
  | 0 => None
  | S f =>
    match bf_step state with
    | None => Some (state_output state)
    | Some state' => bf_run state' f
    end
  end.

Function z_of_ascii (a: ascii): Z :=
  Z.of_nat (nat_of_ascii a).

Function ascii_of_z (z: Z): option ascii :=
  match z with
  | Zpos p => Some (ascii_of_pos p)
  | _ => None
  end.

Function opt_list_len {A: Type} (l: option (list A)): nat :=
  match l with
  | Some l => List.length l
  | None => 0
  end.

Function string_of_zs (out: list Z): string :=
  match out with
  | [] => EmptyString
  | z :: zs' =>
    match ascii_of_z z with
    | None => EmptyString
    | Some a => String a (string_of_zs zs')
    end
  end.

Function zs_of_string (str: string): list Z :=
  match str with
  | EmptyString => []
  | String a str' => z_of_ascii a :: (zs_of_string str')
  end.

(* The important interpreter as far as the spec is concerned *)
Function interpret_bf (prog: string) (zs: list Z) (f: nat): option (list Z) :=
  match parse_bf prog with
  | None => None
  | Some bf => bf_run (state_init bf zs) f
  end.

Function interpret_bf_readable (prog: string) (input: string) (f:nat): string :=
  match interpret_bf prog (zs_of_string input) f with
  | None => EmptyString
  | Some zs => string_of_zs zs
  end.

Example hello_world_bf:
  interpret_bf_readable "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.
                        +++++++..+++.>++.<<+++++++++++++++.>.+++.------.
                        --------.>+. newline in next cell" "" 401 =
  "Hello World!"%string. auto.
