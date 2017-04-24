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
  | get : nat -> SMProgram -> SMProgram
  (*| rotate : nat -> SMProgram -> SMProgram *)
  | pack : nat -> SMProgram -> SMProgram
  | unpack : SMProgram -> SMProgram
  | call : SMProgram -> SMProgram
  | out : SMProgram -> SMProgram.


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

  Notation "a >>= f" := (bind a f) (at level 50, left associativity).

  Definition tl_error {A} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _ :: tl => Some tl
    end.

  Definition hd_error {A} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | hd :: _ => Some hd
    end.

  Fixpoint stack_pack (n : nat) (s: Stack) :=
  match n with
  | 0 => Some s
  | S 0 => match s with
    | k :: tl => Some ((item_tuple [k]) :: tl)
    | _ => None
    end
  | S n => (stack_pack n s) >>= (fun s =>
    match s with
    | item_tuple l :: k :: tl => Some ((item_tuple (l ++ [k])) :: tl)
    | _ => None
    end)
  end.

  Example stack_pack_simple:
    stack_pack 2 [item_nat 0; item_nat 1] = Some [item_tuple [item_nat 0; item_nat 1]].
  simpl. auto.
  

  Fixpoint stack_unpack (s: Stack) :=
    match s with
    | [] => None
    | hd :: tl => match hd with
      | item_nat _ => None
      | item_tuple lst => Some (lst ++ tl)
      end
    end.

  Lemma stack_pack_unpack (s s': Stack) (n: nat):
    n > 0 ->
    (stack_pack n s) = Some s' ->
    (stack_pack n s) >>= stack_unpack = Some s.
  Proof.
    admit.
  Admitted.

  Function sm_step (s: SMState): option SMState :=
    match s with
    | state smp fn_table stack input output =>
      let state_from_stack (smp': SMProgram) (stack : Stack) :=
        Some (state smp' fn_table stack input output)
      in match smp with
      | push n smp' => state_from_stack smp' ((item_nat n) :: stack)
      | pop smp'=> (tl_error stack) >>= (state_from_stack smp')
      | get n smp' =>
        let new_stack := (nth_error stack n) >>= (fun a => Some (a :: stack)) 
        in new_stack >>= (state_from_stack smp')
      | pack n smp' => (stack_pack n stack) >>= (state_from_stack smp')
      | unpack n smp' => (stack_unpack stack) >>= (state_from_stack smp')
      | call smp' => match stack with
        | (item_nat id) :: tl => (nth_error fn_table id) >>= (fun smp =>
          Some (state smp fn_table tl input output))
        | _ => None
        end
      end
    end.
