Require Import Bool.BoolEq.
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
  Definition state := @BFTape.state BFN.

  Function bfn_step (s: BFNState): option BFNState :=
    match s with
    | BFTape.state bfn resets ptr tape input output =>
      match bfn with
      | bfn_end =>
        match resets with
        | [] => None
        | bfn' :: resets' =>
          Some (state bfn' resets' ptr tape input output)
        end
      | bfn_right n bfn' =>
        Some (state bfn' resets (n + ptr) tape input output)
      | bfn_left n bfn' =>
        Some (state bfn' resets (ptr - n) tape input output)
      | bfn_inc n bfn' =>
        Some (state bfn' resets ptr
                    (BFTape.put tape ptr (n + (BFTape.get tape ptr)))
                    input output)
      | bfn_dec n bfn' =>
        Some (state bfn' resets ptr
                    (BFTape.put tape ptr ((BFTape.get tape ptr) - n))
                    input output)
      | bfn_out (S n) bfn' =>
        Some (state (bfn_out n bfn') resets ptr tape input
                    (output ++ [BFTape.get tape ptr]))
      | bfn_in (S n) bfn' =>
        match input with
        | [] =>
          Some (state (bfn_in n bfn') resets ptr (BFTape.put tape ptr 0)
                      input output)
        | x :: input' =>
          Some (state (bfn_in n bfn') resets ptr (BFTape.put tape ptr x)
                      input' output)
        end
      | bfn_out 0 bfn'
      | bfn_in 0 bfn' => Some (state bfn' resets ptr tape input output)
      | bfn_loop inner_bfn bfn' =>
        if (BFTape.get tape ptr) =? 0 then
          Some (state bfn' resets ptr tape input output)
        else
          Some (state inner_bfn (bfn :: resets) ptr tape input output)
      end
    end.

  (* Key function for translation correctness *)
  Definition interpret_bfn (prog: BFN) (input: list nat) (fuel: nat):
    option (list nat) := BFTape.interpret bfn_step prog input fuel.

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

  (* TODO: Prove bf_of_bfn_correct *)
  Lemma bf_of_bfn_correct:
    forall (bfn: BFN) (input output: list nat),
      (exists fuel, interpret_bfn bfn input fuel = Some output) ->
      (exists fuel, interpret_bf (bf_of_bfn bfn) input fuel = Some output).
  Proof.
    induction bfn; intros.
    destruct H, x; compute in H; try discriminate.
    replace output with (@nil nat) in * by congruence; exists 1; auto.
    1-6: induction n.
    1,3,5,7,9,11: rewrite bf_of_bfn_equation; apply IHbfn; clear IHbfn.
    1-6: destruct H, x; [ compute in H; discriminate | ].
    1-6: rewrite <- H; clear H.
    1-6: exists x.
    1-6: unfold interpret_bfn, BFTape.interpret, BFTape.exec_init.
    1-6: cbn; auto.
    1-2: unfold state.
    1-2: replace (BFTape.put BFTape.empty 0 0) with (BFTape.empty); auto.
    1-2: admit.
    (* H contradics premise of IHn *)

    Restart.
    intro; functional induction (bf_of_bfn bfn); intros; destruct H.
    destruct x; compute in H; try discriminate.
    replace output with (@nil nat) by congruence; exists 1; auto.
    1-6: apply IHb; clear IHb.
    1-6: rewrite <- H; clear H.
    1-6: destruct x; [ exists 0; auto | ].
    1-6: exists x; unfold interpret_bfn, BFTape.interpret, BFTape.exec_init.
    1-6: cbn; auto.
    induction n.
    destruct x; [ exists 0; auto | ].
    cbn in H.
    exists x.
    destruct x; auto.
    cbn.
    (* Needed to revert more things *)

    Restart.
    intros; destruct H as [fuel].
    revert input output fuel H.
    unfold interpret_bf, interpret_bfn, BFTape.interpret, BFTape.exec_init.
    remember 0 as ptr; clear Heqptr; revert ptr.
    remember BFTape.empty as tape; clear Heqtape; revert tape.
    remember (@nil nat) as acc; clear Heqacc; revert acc.
    functional induction (bf_of_bfn bfn); intros. (* Try induction bfn *)
    destruct fuel; compute in H; try discriminate.
    replace output with acc by congruence; exists 1; auto.
    1-6: destruct fuel; [ exists 0; auto | ].
    1-6: apply IHb with (fuel:=fuel); clear IHb.
    1-6: rewrite <- H; clear H.
    1-6: cbn; try rewrite Nat.sub_0_r.
    1-6: unfold BFTape.put; try rewrite <- beq_nat_refl; auto.
    (* Zero cases finished, this proof strategy might work *)

    Restart.
    intros; destruct H as [fuel].
    revert input output fuel H.
    unfold interpret_bf, interpret_bfn, BFTape.interpret, BFTape.exec_init.
    remember 0 as ptr; clear Heqptr; revert ptr.
    remember BFTape.empty as tape; clear Heqtape; revert tape.
    remember (@nil nat) as acc; clear Heqacc; revert acc.
    induction bfn.
    1: intros.
    1: destruct fuel; compute in H; try discriminate.
    1: replace output with acc by congruence; exists 1; auto.
    1-6: induction n; intros.
    1-12: destruct fuel; [ simpl in H; try discriminate | ].
    (* take care of case 1 *)
    cbn in H; rewrite bf_of_bfn_equation.
    generalize (IHbfn _ _ _ _ _ _ H); intros Hx.
    destruct Hx as [fuel' Hx].
    now exists fuel'.

End BFN.
