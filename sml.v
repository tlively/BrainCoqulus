Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Module StackMachine.

  Inductive Item : Set :=
  | item_nat : nat -> Item
  | item_tuple : list Item -> Item.

  Inductive SMProgram : Set :=
  | push : nat -> SMProgram -> SMProgram
  | pop : SMProgram -> SMProgram
  | get : nat -> SMProgram -> SMProgram. (*
  | rotate : nat -> SMProgram -> SMProgram
  | pack : nat -> SMProgram -> SMProgram
  | unpack : SMProgram -> SMProgram
  | add : SMProgram -> SMProgram
  | call : SMProgram -> SMProgram
  | out : SMProgram -> SMProgram. *)


  Definition Stack := list Item.

  Inductive SMState :=
    state (ast: SMProgram)
          (fn_table: list SMProgram)
          (stack: Stack)
          (input: list nat)
          (output: list nat).

  Definition failsafe_tl {A: Type} (l: list A) :=
    match l with
    | [] => []
    | _ :: tl => tl
    end.



  (* Monads ftw! *)
  Definition bind {A B : Type} (a: option A) (f : A -> option B) :=
    match a with
    | None => None
    | Some a => f a
    end.

  Definition tl_error {A} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _ :: tl => Some tl
    end.

  Function sm_step (s: SMState): option SMState :=

    match s with
    | state smp fn_table stack input output =>
      let state_from_stack (smp': SMProgram) (stack : Stack) :=
        Some (state smp' fn_table stack input output)
      in
      match smp with
      | push n smp' => state_from_stack smp' ((item_nat n) :: stack)
      | pop smp'=> bind (tl_error stack) (state_from_stack smp')
      | get n smp' =>
        let new_stack := bind (nth_error stack n) (fun a => Some (a :: stack)) 
        in bind new_stack (state_from_stack smp')
      end
    end.
