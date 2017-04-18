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


  Fixpoint repeat_com (fn : BF -> BF) (n : nat) (bf: BF) : BF :=
    match n with
    | 0 => bf_end  (* should probably not be used *)
    | 1 => fn bf
    | S m => fn (repeat_com fn m bf)
    end.

  Fixpoint bfn_to_bf (bfn: BFN): BF :=
    match bfn with
    | bfn_end => bf_end
    | bfn_right n bfn' => repeat_com bf_right n (bfn_to_bf bfn')
    | bfn_left n bfn' => repeat_com bf_left n (bfn_to_bf bfn')
    | bfn_inc n bfn' => repeat_com bf_inc n (bfn_to_bf bfn')
    | bfn_dec n bfn' => repeat_com bf_dec n (bfn_to_bf bfn')
    | bfn_out n bfn' => repeat_com bf_out n (bfn_to_bf bfn')
    | bfn_in n bfn' => repeat_com bf_in n (bfn_to_bf bfn')
    | bfn_loop bfn1 bfn2 => bf_loop (bfn_to_bf bfn1) (bfn_to_bf bfn2)
    end.

  Example parse_left_bfn:
    parse_bf "<<<<+++++++" =
    Some (bfn_to_bf (bfn_left 4 (bfn_inc 7 bfn_end))).
  auto. Qed.

End BFN.
