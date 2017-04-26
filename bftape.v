Require Import Arith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.
Import ListNotations.

Load utils.

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

  (* Tape language execution state.
     `ast' is the current state of the program, while `resets' is the
     stack of programs to reset to at the end of a loop *)
  Inductive ExecState {A: Type} : Type :=
    | running (ast: A)
              (resets: list A)
              (ptr: nat)
              (tape: Tape)
              (input: list nat)
              (output: list nat)
    | halted (output: list nat).

  Function exec_init {A: Type} (prog: A) (input: list nat): ExecState :=
    running prog [] 0 BFTape.empty input [].

  Definition interpret {A: Type} (step: @ExecState A -> @ExecState A)
             (prog: A) (input: list nat) (fuel: nat): option (list nat) :=
    match Utils.run step (exec_init prog input) fuel with
    | running _ _ _ _ _ _ => None
    | halted output => Some output
    end.

End BFTape.
