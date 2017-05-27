Require Import Arith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.
Import ListNotations.

Module BFTape.

  (* A BFTape is a map from [nat] indices to [nat] values *)
  Module NatMap := FMapList.Make Nat_as_OT.
  Definition Tape := NatMap.t nat.

  Definition empty := NatMap.empty nat.

  Definition get (tape: Tape) (ptr: nat): nat :=
    match (NatMap.find ptr tape) with
    | Some x => x
    | None => 0
    end.

  Definition put (tape: Tape) (ptr: nat) (x: nat): Tape :=
    NatMap.add ptr x tape.

  Definition inc (tape: Tape) (ptr: nat): Tape :=
    put tape ptr (S (get tape ptr)).

  Definition dec (tape: Tape) (ptr: nat): Tape :=
    put tape ptr (pred (get tape ptr)).

  Definition tape_of_list (lst :list nat): Tape :=
    let fix helper (lst: list nat) (ptr: nat): Tape :=
        match lst with
        | [] => empty
        | hd :: tl =>
          let rest := helper tl (S ptr) in
          put rest ptr hd
        end
    in helper lst 0.

  Definition list_of_tape (t: Tape) (n: nat): list nat :=
    map (get t) (seq 0 n).

End BFTape.
