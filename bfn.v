Require Import Bool.BoolEq.
Require Import Logic.FunctionalExtensionality.

Load jsml.
Load bftape.

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

  Inductive BFNState : Type :=
    | running (ast: BFN)
              (resets: list BFN)
              (ptr: nat)
              (tape: BFTape.Tape)
              (input: list nat)
              (output: list nat)
    | halted (output: list nat).

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
    | running bfn _ _ _ _ _ => bfn_weight bfn
    | halted _ => 0
    end.

  Function bfn_step (s: BFNState) {measure bfn_state_weight s}: BFNState :=
    match s with
    | halted _ => s
    | running bfn resets ptr tape input output =>
      match bfn with
      | bfn_end =>
        match resets with
        | [] => halted output
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

  Function exec_init (prog: BFN) (input: list nat): BFNState :=
    running prog [] 0 BFTape.empty input [].

  Definition interpret_bfn (prog: BFN) (input: list nat) (fuel: nat): option (list nat) :=
    match Utils.run bfn_step (exec_init prog input) fuel with
    | running _ _ _ _ _ _ => None
    | halted output => Some output
    end.

  (* JSML -> BFN. Stub. *)
  Function bfn_of_jsm (jsm : JSML.JSMProgram * list JSML.JSMProgram) :=
    let (main, fn_table) := jsm in
    main.

End BFN.
