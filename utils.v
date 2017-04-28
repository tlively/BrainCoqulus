Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Module Utils.

  (* TODO: Use N as fuel with {measure N.to_nat fuel} *)
  Function run {State: Type} (step: State -> State)
           (state: State) (fuel: nat): State :=
    match fuel with
    | 0 => state
    | S f => run step (step state) f
    end.

  (* Monads ftw! *)
  Definition bind {A B : Type} (a: option A) (f : A -> option B) :=
    match a with
    | None => None
    | Some a => f a
    end.

End Utils.

Notation "a >>= f" := (Utils.bind a f) (at level 50, left associativity).
