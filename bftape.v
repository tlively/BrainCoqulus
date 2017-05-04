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
    if x =? get tape ptr then tape else NatMap.add ptr x tape.

  Definition inc (tape: Tape) (ptr: nat): Tape :=
    put tape ptr (S (get tape ptr)).

  Definition dec (tape: Tape) (ptr: nat): Tape :=
    put tape ptr (pred (get tape ptr)).

End BFTape.
