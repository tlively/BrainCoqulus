Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.


Load utils.
Load lambda.

Module SML.

  Inductive Item : Set :=
  | item_nat : nat -> Item
  | item_tuple : list Item -> Item.

  Inductive SMProgram : Set :=
  | sm_end : SMProgram
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
    | running (ast: SMProgram)
          (to_return: list SMProgram)
          (fn_table: list SMProgram)
          (stack: Stack)
          (output: list nat)

    | error (output: list nat)
    | halted (output: list nat).

  Definition failsafe_tl {A: Type} (l: list A) :=
    match l with
    | [] => []
    | _ :: tl => tl
    end.

  Definition tl_error {A} (l : list A) : option (list A) :=
    match l with
    | [] => None
    | _ :: tl => Some tl
    end.

  Definition hd_error {A} (l : list A) : option A :=
    match l with
    | [] => None
    | hd :: _ => Some hd
    end.

  Fixpoint stack_pack (n : nat) (s: Stack) :=
  match n with
  | 0 | S 0=> Some s
  | S (S 0) => match s with
    | l :: k :: tl => Some ((item_tuple (l :: [k])) :: tl)
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
  Proof. simpl. auto. Qed.
  
  Eval compute in stack_pack 2 ([item_tuple [item_nat 0; item_nat 1]; item_nat 2; item_nat 3;
         item_nat 4]).
  
  Fixpoint stack_unpack (s: Stack) :=
    match s with
    | [] => None
    | hd :: tl => match hd with
      | item_nat _ => None
      | item_tuple lst => Some (lst ++ tl)
      end
    end.

  (*Lemma stack_pack_unpack (s s': Stack) (n: nat):
    n > 0 ->
    (stack_pack n s) = Some s' ->
    (stack_pack n s) >>= stack_unpack = Some s.
  Proof.
  Admitted.*)

  Definition sm_bind {A : Type} (a: option A) (f : A -> SMState) (output: list nat) :=
    match a with
    | None => error output
    | Some a => f a
    end.

  Definition sm_step (s: SMState): SMState :=
    match s with
    | halted _ => s
    | error _ => s
    | running smp ret_list fn_table stack output =>
      let state_from_stack (smp': SMProgram) (stack : Stack) :=
        running smp' ret_list fn_table stack output
      in match smp with
      | sm_end => match ret_list with
        | [] => halted output
        | smp' :: tl => running smp' tl fn_table stack output
        end
      | push n smp' => state_from_stack smp' ((item_nat n) :: stack)
      | pop smp'=> sm_bind (tl_error stack) (state_from_stack smp') output
      | get n smp' =>
        let new_stack := (nth_error stack n) >>= (fun a => Some (a :: stack))
        in sm_bind new_stack (state_from_stack smp') output
      | pack n smp' => sm_bind (stack_pack n stack) (state_from_stack smp') output
      | unpack smp' => sm_bind (stack_unpack stack) (state_from_stack smp') output
      | call smp' => match stack with
        | (item_nat id) :: tl => sm_bind (nth_error fn_table id) 
            (fun smp => running smp (smp' :: ret_list) fn_table tl output) output
        | _ => error output
        end
      | out smp' => let out_char := 
        match stack with
        | (item_nat o) :: _ => Some o
        | _ => None
        end in 
        sm_bind out_char (fun o => running smp' ret_list fn_table stack (o :: output)) output
      end
    end.

  (* TODO: Abstract the functions below along with the stuff in bftape.v *)
  Definition exec_output (state: SMState): list nat :=
    match state with 
    | running _ _ _ _ output => output 
    | halted output => output
    | error output => output
    end.

  Definition exec_init (fn_table: list SMProgram) : SMState :=
    match fn_table with
    | smp :: _ => running smp [] fn_table [] []
    | [] => error []
    end.

  Definition interpret (fn_table: list SMProgram) (fuel: nat): list nat :=
    exec_output (Utils.run sm_step (exec_init fn_table) fuel). 

  Example push_simple:
    interpret [push 3 (out sm_end)] 20 = [3].
  Proof. auto. Qed.

  Example jump_simple:
    interpret [push 1 (out (call (push 2 (out sm_end)))); push 3 (out sm_end)] 20 = [2; 3; 1].
  Proof. auto. Qed.


  Fixpoint append (sm1 sm2: SMProgram) : SMProgram :=
    match sm1 with
    | sm_end => sm2
    | push n smp' => push n (append smp' sm2) 
    | pop smp' => pop (append smp' sm2)
    | get n smp' => get n (append smp' sm2)
    | pack n smp' => pack n (append smp' sm2)
    | unpack smp' => unpack (append smp' sm2)
    | call smp' => call (append smp' sm2)
    | out smp' => out (append smp' sm2)
    end.

  Definition stack_diff (smp: SMProgram) : nat :=
    0.

Notation "s1 +++ s2" := (append s1 s2) (at level 50, left associativity).

 Fixpoint lambda_to_sml (l : Lambda.Lambda) (fn_table: list SMProgram) (depth: nat) : SMProgram * list SMProgram :=
    match l with
    | Lambda.var n => let known_stack_size := 3 in
      ((get (known_stack_size - n) sm_end), fn_table)
    | Lambda.lam e => let (body, c1) := lambda_to_sml e fn_table (depth + 1) in
      let diff := (stack_diff body) + depth in
      let fn := body +++ (pack diff sm_end) in
      (push (List.length c1) sm_end, c1 ++ [fn])
    | Lambda.app e1 e2 => 
      let (f, c1) := lambda_to_sml e1 fn_table depth in
      let (v, c2) := lambda_to_sml e2 c1 depth in
      ((v +++ f) +++ (unpack (call sm_end)), c2)
    | Lambda.out e => let (body, c) := lambda_to_sml e fn_table depth in
      (body +++ (out sm_end), c)
    end.

  Eval compute in (Lambda.parse_lambda "(\y.\x.x)(\x.x)").
  Eval compute in (match (Lambda.parse_lambda "(\y. \x.x) (\x. x)") with
      | Some x => lambda_to_sml x [] 0
      | None => (sm_end, [])
      end).

End SML.
