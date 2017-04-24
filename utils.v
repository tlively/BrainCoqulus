Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Module Utils.
  (* TODO: Use N as fuel with {measure N.to_nat fuel} *)
  Function run {State: Type} (step: State -> option State)
           (state: State) (output: State -> list nat)
           (fuel: nat): option (list nat) :=
    match fuel with
    | 0 => None
    | S f =>
      match step state with
      | None => Some (output state)
      | Some state' => run step state' output f
      end
    end.
End Utils.