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

  (* Tape language execution state.
     `ast' is the current state of the program, while `resets' is the
     stack of programs to reset to at the end of a loop *)
  Inductive ExecState {A: Type} : Type :=
    state (ast: A)
          (resets: list A)
          (ptr: nat)
          (tape: Tape)
          (input: list nat)
          (output: list nat).

  Function exec_init {A: Type} (prog: A) (input: list nat): ExecState :=
    state prog [] 0 BFTape.empty input [].

  Function exec_output {A: Type } (state: @ExecState A): list nat :=
    match state with state _ _ _ _ _ output => output end.

  (* TODO: Use N as fuel with {measure N.to_nat fuel} *)
  Function run {A: Type} (step: @ExecState A -> option (@ExecState A))
           (state: @ExecState A) (fuel: nat): option (list nat) :=
    match fuel with
    | 0 => None
    | S f =>
      match step state with
      | None => Some (exec_output state)
      | Some state' => run step state' f
      end
    end.

  Definition interpret {A: Type} (step: @ExecState A -> option (@ExecState A))
           (prog: A) (input: list nat) (fuel: nat): option (list nat) :=
    run step (exec_init prog input) fuel.

End BFTape.