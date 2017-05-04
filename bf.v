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

Load bfn.
Import BFN.

Module BF.

  (* BF Program Type *)
  Inductive BF : Type :=
  | bf_end : BF
  | bf_right : BF -> BF (* > *)
  | bf_left : BF -> BF  (* < *)
  | bf_inc : BF -> BF   (* + *)
  | bf_dec : BF -> BF   (* - *)
  | bf_out : BF -> BF   (* . *)
  | bf_in : BF -> BF    (* , *)
  | bf_loop : BF -> BF -> BF.  (* [...] *)

  Section BFPrinting.

    Function chars_of_bf (bf: BF): list ascii :=
      match bf with
      | bf_end => []
      | bf_right bf' =>  ">"%char :: (chars_of_bf bf')
      | bf_left bf' => "<"%char :: (chars_of_bf bf')
      | bf_inc bf' => "+"%char :: (chars_of_bf bf')
      | bf_dec bf' => "-"%char :: (chars_of_bf bf')
      | bf_out bf' => "."%char :: (chars_of_bf bf')
      | bf_in bf' => ","%char :: (chars_of_bf bf')
      | bf_loop inner bf' =>
        "["%char :: (chars_of_bf inner) ++ ["]"%char] ++ (chars_of_bf bf')
      end.

    Function print_bf (bf: BF): string :=
      Parse.string_of_chars (chars_of_bf bf).

    Example print_all_bf_commands:
      print_bf
        (bf_loop
           (bf_right (bf_left (bf_inc (bf_dec (bf_out (bf_in bf_end))))))
           bf_end)
      = "[><+-.,]"%string. auto.
    Qed.

  End BFPrinting.

  Section BFParsing.

    Local Definition ParseState := @Parse.ParseState BF.
    Local Definition chars_of_string := Parse.chars_of_string.

    Function parse_bf_state (l: list ascii): ParseState :=
      match l with
      | [] => Parse.ok bf_end []
      | hd :: tl =>
        match parse_bf_state tl with
        | Parse.error => Parse.error
        | Parse.ok cur stack =>
          match hd with
          | ">"%char => Parse.ok (bf_right cur) stack
          | "<"%char => Parse.ok (bf_left cur) stack
          | "+"%char => Parse.ok (bf_inc cur) stack
          | "-"%char => Parse.ok (bf_dec cur) stack
          | "."%char => Parse.ok (bf_out cur) stack
          | ","%char => Parse.ok (bf_in cur) stack
          | "]"%char => Parse.ok bf_end (cur :: stack)
          | "["%char =>
            match stack with
            | [] => Parse.error
            | next :: stack' => Parse.ok (bf_loop cur next) stack'
            end
          | _ => Parse.ok cur stack
          end
        end
      end.

    Function parse_bf (str: string): option BF :=
      match parse_bf_state (chars_of_string str) with
      | Parse.error => None
      | Parse.ok _ (_ :: _) => None
      | Parse.ok bf [] => Some bf
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
(*
  Lemma bf_helper (bf1 bf1': BF):
    parse_bf_state (chars_of_bf bf1) = Parse.ok bf1' [] ->
    bf1 = bf1'.
  Proof.
  Admitted.

  Lemma bf_print_parse_loop (bf1 bf2: BF):
    forall bf1' bf2',
      parse_bf_state (chars_of_bf bf1) = Parse.ok bf1' [] ->
      parse_bf_state (chars_of_bf bf2) = Parse.ok bf2' [] ->
      parse_bf_state ("["%char :: (chars_of_bf bf1) ++ ["]"%char]
                         ++ (chars_of_bf bf2))
      = Parse.ok (bf_loop bf1 bf2) [].
  Proof.
  Admitted.

  Lemma bf_print_parse_chars_inv (bf: BF):
    parse_bf_state (chars_of_bf bf) = Parse.ok bf [].
  Proof.
    induction bf; auto;
      rewrite chars_of_bf_equation, parse_bf_state_equation;
      try (rewrite IHbf; auto).
    now apply (bf_print_parse_loop _ _ bf1 bf2).
  Qed.

  (* Removes the parser from the trusted computing base *)
  Theorem bf_print_parse_inv (bf: BF): parse_bf (print_bf bf) = Some bf.
  Proof.
    unfold parse_bf, print_bf; rewrite Parse.chars_of_string_of_chars_inv.
    now rewrite bf_print_parse_chars_inv.
  Qed.
  *)

  (* BF Interpreter *)
  Inductive BFState : Type :=
    | running (ast: BF)
              (resets: list BF)
              (ptr: nat)
              (tape: BFTape.Tape)
              (input: list nat)
              (output: list nat)
    | halted (output: list nat).

  Function bf_step (s: BFState): BFState :=
    match s with
    | halted _ => s
    | running bf resets ptr tape input output =>
      match bf with
      | bf_end =>
        match resets with
        | [] => halted output
        | bf' :: resets' =>
          running bf' resets' ptr tape input output
        end
      | bf_right bf' =>
        running bf' resets (S ptr) tape input output
      | bf_left bf' =>
        running bf' resets (pred ptr) tape input output
      | bf_inc bf' =>
        running bf' resets ptr (BFTape.inc tape ptr) input output
      | bf_dec bf' =>
        running bf' resets ptr (BFTape.dec tape ptr) input output
      | bf_out bf' =>
        running bf' resets ptr tape input (output ++ [BFTape.get tape ptr])
      | bf_in bf' =>
        match input with
        | [] =>
          running bf' resets ptr (BFTape.put tape ptr 0) input output
        | x :: input' =>
          running bf' resets ptr (BFTape.put tape ptr x) input' output
        end
      | bf_loop inner_bf bf' =>
        if (BFTape.get tape ptr) =? 0 then
          running bf' resets ptr tape input output
        else
          running inner_bf (bf :: resets) ptr tape input output
      end
    end.

  Function exec_init (prog: BF) (input: list nat): BFState :=
    running prog [] 0 BFTape.empty input [].

  Definition interpret_bf (prog: BF) (input: list nat) (fuel: nat): option (list nat) :=
    match Utils.run bf_step (exec_init prog input) fuel with
    | running _ _ _ _ _ _ => None
    | halted output => Some output
    end.
  Function string_of_nats (out: list nat): string :=
    match out with
    | [] => EmptyString
    | n :: ns' => String (ascii_of_nat n) (string_of_nats ns')
    end.

  Function nats_of_string (str: string): list nat :=
    match str with
    | EmptyString => []
    | String a str' => nat_of_ascii a :: (nats_of_string str')
    end.

  Function interpret_bf_readable (prog: string) (input: string) (f: nat):
    string :=
    match parse_bf prog with
    | None => EmptyString
    | Some bf =>
      match interpret_bf  bf (nats_of_string input) f with
      | None => EmptyString
      | Some output => string_of_nats output
      end
    end.

  Example hello_world_bf:
    interpret_bf_readable "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.
                        +++++++..+++.>++.<<+++++++++++++++.>.+++.------.
                        --------.>+. newline in next cell" "" 401 =
    "Hello World!"%string. Proof. auto. Qed.

  Function bf_of_bfn (bfn: BFN) {measure bfn_weight bfn}: BF.BF :=
    match bfn with
    | bfn_end => bf_end
    | bfn_right 0 bfn'
    | bfn_left 0 bfn'
    | bfn_inc 0 bfn'
    | bfn_dec 0 bfn'
    | bfn_out 0 bfn'
    | bfn_in 0 bfn' => bf_of_bfn bfn'
    | bfn_right (S n) bfn' => bf_right (bf_of_bfn (bfn_right n bfn'))
    | bfn_left (S n) bfn' => bf_left (bf_of_bfn (bfn_left n bfn'))
    | bfn_inc (S n) bfn' => bf_inc (bf_of_bfn (bfn_inc n bfn'))
    | bfn_dec (S n) bfn' => bf_dec (bf_of_bfn (bfn_dec n bfn'))
    | bfn_out (S n) bfn' => bf_out (bf_of_bfn (bfn_out n bfn'))
    | bfn_in (S n) bfn' => bf_in (bf_of_bfn (bfn_in n bfn'))
    | bfn_loop inner bfn' => bf_loop (bf_of_bfn inner) (bf_of_bfn bfn')
    end.
  Proof.
    all: intros; auto; simpl; omega.
  Defined.

  Example translate_left_bfn:
    parse_bf "<<<<+++++++" =
    Some (bf_of_bfn (bfn_left 4 (bfn_inc 7 bfn_end))).
  auto. Qed.

  Lemma bfn_replace_loops:
    forall (bfn1 bfn2: BFN),
      bf_of_bfn (bfn_loop bfn1 bfn2) =
      bf_loop (bf_of_bfn bfn1) (bf_of_bfn bfn2).
  Proof.
    intros.
    rewrite bf_of_bfn_equation.
    reflexivity.
  Qed.

  Function bf_state_of_bfn_state (state: BFNState): BFState :=
    match state with
    | BFN.halted output => halted output
    | BFN.running bfn resets ptr tape input output =>
      running (bf_of_bfn bfn) (map bf_of_bfn resets)
                     ptr tape input output
    end.

  Lemma bf_of_bfn_sim_step:
    forall (s: BFNState),
      bf_step (bf_state_of_bfn_state s) = bf_state_of_bfn_state (bfn_step s).
  Proof.
    intros.
    destruct s; unfold bf_state_of_bfn_state;
      [ | rewrite bfn_step_equation; auto ].
    induction ast.
    destruct resets;
      rewrite bfn_step_equation;
      now unfold bf_state_of_bfn_state.
    6: destruct input.
    1-7: induction n;
      rewrite bf_of_bfn_equation;
      now rewrite bfn_step_equation.
    rewrite bf_of_bfn_equation.
    rewrite bfn_step_equation.
    unfold bf_step.
    destruct (BFTape.get tape ptr).
    now replace (0 =? 0) with true by auto.
    replace (S n =? 0) with false by auto; simpl.
    now rewrite bfn_replace_loops.
  Qed.

  Lemma bf_of_bfn_sim:
    forall (fuel: nat) (s: BFNState),
      Utils.run bf_step (bf_state_of_bfn_state s) fuel =
      bf_state_of_bfn_state (Utils.run bfn_step s fuel).
  Proof.
    induction fuel; auto.
    simpl; intros.
    rewrite <- IHfuel.
    now rewrite bf_of_bfn_sim_step.
  Qed.

  Lemma bf_of_bfn_correct:
    forall (bfn: BFN) (input output: list nat),
      (exists fuel, interpret_bfn bfn input fuel = Some output) ->
      (exists fuel, interpret_bf (bf_of_bfn bfn) input fuel = Some output).
  Proof.
    intros.
    destruct H as [fuel]; exists fuel.
    rewrite <- H; clear H.
    unfold interpret_bf, interpret_bfn.
    replace (exec_init (bf_of_bfn bfn) input) with
    (bf_state_of_bfn_state (BFN.exec_init bfn input)) by auto.
    rewrite bf_of_bfn_sim.
    remember (@Utils.run (BFNState) bfn_step
                         (BFN.exec_init bfn input) fuel) as result.
    destruct result;
      now unfold bf_state_of_bfn_state.
    Qed.

End BF.
