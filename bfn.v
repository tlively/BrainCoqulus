Require Import Bool.BoolEq.
Require Import Logic.FunctionalExtensionality.
Load bf.
Import BF.

Module BFN.

  (* Layer 1 above BF: BFN Program Type. Repeat each command N times *)
  Inductive BFN : Set :=
  | bfn_end : BFN
  | bfn_right : nat -> BFN -> BFN (* > *)
  | bfn_left : nat -> BFN -> BFN  (* < *)
  | bfn_inc : nat -> BFN -> BFN   (* + *)
  | bfn_dec : nat -> BFN -> BFN   (* - *)
  | bfn_out : nat -> BFN -> BFN   (* . *)
  | bfn_in : nat -> BFN -> BFN    (* , *)
  | bfn_loop : BFN -> BFN -> BFN.  (* [...] *)

  (* BFN Semantics *)
  Definition BFNState := @BFTape.ExecState BFN.
  Definition running := @BFTape.running BFN.

  Function bfn_weight (bfn: BFN): nat :=
    match bfn with
    | bfn_end => 0
    | bfn_right n bfn'
    | bfn_left n bfn'
    | bfn_inc n bfn'
    | bfn_dec n bfn'
    | bfn_out n bfn'
    | bfn_in n bfn' => (S n) + bfn_weight bfn'
    | bfn_loop inner bfn' => S ((bfn_weight inner) + (bfn_weight bfn'))
    end.

  Function bfn_state_weight (s: BFNState): nat :=
    match s with
    | BFTape.running bfn _ _ _ _ _ => bfn_weight bfn
    | BFTape.halted _ => 0
    end.

  Function bfn_step (s: BFNState) {measure bfn_state_weight s}: BFNState :=
    match s with
    | BFTape.halted _ => s
    | BFTape.running bfn resets ptr tape input output =>
      match bfn with
      | bfn_end =>
        match resets with
        | [] => BFTape.halted output
        | bfn' :: resets' =>
          running bfn' resets' ptr tape input output
        end
      | bfn_right 0 bfn'
      | bfn_left 0 bfn'
      | bfn_inc 0 bfn'
      | bfn_dec 0 bfn'
      | bfn_out 0 bfn'
      | bfn_in 0 bfn' => bfn_step (running bfn' resets ptr tape input output)
      | bfn_right (S n) bfn' =>
        running (bfn_right n bfn') resets (S ptr) tape input output
      | bfn_left (S n) bfn' =>
        running (bfn_left n bfn') resets (pred ptr) tape input output
      | bfn_inc (S n) bfn' =>
        running (bfn_inc n bfn') resets ptr (BFTape.inc tape ptr) input output
      | bfn_dec (S n) bfn' =>
        running (bfn_dec n bfn') resets ptr (BFTape.dec tape ptr) input output
      | bfn_out (S n) bfn' =>
        running (bfn_out n bfn') resets ptr tape input
                    (output ++ [BFTape.get tape ptr])
      | bfn_in (S n) bfn' =>
        match input with
        | [] =>
          running (bfn_in n bfn') resets ptr (BFTape.put tape ptr 0)
                      input output
        | x :: input' =>
          running (bfn_in n bfn') resets ptr (BFTape.put tape ptr x)
                      input' output
        end
      | bfn_loop inner_bfn bfn' =>
        if (BFTape.get tape ptr) =? 0 then
          running bfn' resets ptr tape input output
        else
          running inner_bfn (bfn :: resets) ptr tape input output
      end
    end.
  Proof.
    all: intros; auto; simpl; omega.
  Qed.

  (* Key function for translation correctness *)
  Definition interpret_bfn (prog: BFN) (input: list nat) (fuel: nat):
    option (list nat) := BFTape.interpret bfn_step prog input fuel.

  Function bf_of_bfn (bfn: BFN) {measure bfn_weight bfn}: BF :=
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
  Admitted.

  Function bf_state_of_bfn_state (state: BFNState): BFState :=
    match state with
    | BFTape.halted output => BFTape.halted output
    | BFTape.running bfn resets ptr tape input output =>
      BFTape.running (bf_of_bfn bfn) (map bf_of_bfn resets)
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
    unfold interpret_bf, interpret_bfn, BFTape.interpret.
    replace (BFTape.exec_init (bf_of_bfn bfn) input) with
    (bf_state_of_bfn_state (BFTape.exec_init bfn input)) by auto.
    rewrite bf_of_bfn_sim.
    remember (Utils.run bfn_step (BFTape.exec_init bfn input) fuel) as result.
    (* Both instances should have been remembered! *)
    destruct result;
      now unfold bf_state_of_bfn_state.
  Admitted.

End BFN.
