Require Import ZArith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.

Inductive BF : Set :=
| bf_eof : BF
| bf_right : BF -> BF (* > *)
| bf_left : BF -> BF  (* < *)
| bf_inc : BF -> BF   (* + *)
| bf_dec : BF -> BF   (* - *)
| bf_out : BF -> BF   (* . *)
| bf_in : BF -> BF    (* , *)
| bf_loop : BF -> BF -> BF.  (* [...] *)

(* A BFTape is a map from [nat] indices to [Z] values *)
Module NatMap := FMapList.Make Nat_as_OT.
Definition BFTape := NatMap.t Z.
