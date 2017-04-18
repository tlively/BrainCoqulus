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
        Some (state bfn' resets (ptr + n) tape input output)
      | bfn_left n bfn' =>
        Some (state bfn' resets (ptr - n) tape input output)
      | bfn_inc n bfn' =>
        Some (state bfn' resets ptr
                    (BFTape.put tape ptr ((BFTape.get tape ptr) + n))
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

  (* Translation BFN -> BF *)
  Function repeat_com (fn : BF -> BF) (n : nat) (bf: BF) : BF :=
    match n with
    | 0 => bf_end  (* should probably not be used *)
    | 1 => fn bf
    | S m => fn (repeat_com fn m bf)
    end.

  Function bf_of_bfn (bfn: BFN): BF :=
    match bfn with
    | bfn_end => bf_end
    | bfn_right n bfn' => repeat_com bf_right n (bf_of_bfn bfn')
    | bfn_left n bfn' => repeat_com bf_left n (bf_of_bfn bfn')
    | bfn_inc n bfn' => repeat_com bf_inc n (bf_of_bfn bfn')
    | bfn_dec n bfn' => repeat_com bf_dec n (bf_of_bfn bfn')
    | bfn_out n bfn' => repeat_com bf_out n (bf_of_bfn bfn')
    | bfn_in n bfn' => repeat_com bf_in n (bf_of_bfn bfn')
    | bfn_loop bfn1 bfn2 => bf_loop (bf_of_bfn bfn1) (bf_of_bfn bfn2)
    end.

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
    intros.
    destruct H.
    functional induction (bf_of_bfn bfn).
    - destruct x; compute in H; try discriminate.
      exists 1; auto.
  Admitted.

End BFN.
