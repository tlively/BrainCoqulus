Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Load lambda.
Load stack.

Module SML.

  Inductive SMCommand : Set :=
  | push (n: nat)
  | del (n: nat)
  | get (n: nat)
  | pack (n: nat)
  | unpack
  | cond_get (n k: nat)
  | call
  | inc
  | dec
  | read
  | out.

  Definition SMProgram := list SMCommand.
  Definition Stack := Stack.Stack.

  Function stack_call (s: Stack) (fn_table: list SMProgram)
           {measure Stack.stack_weight s}: (option Stack) * SMProgram  :=
    match Stack.stack_unpack s with
    | None => (None, [])
    | Some stack =>
      match stack with
      | Stack.snil => (None, [])
      | Stack.stuple t s' => stack_call stack fn_table
      | Stack.snat fid s' =>
        match nth_error fn_table fid with
        | None => (None, [])
        | Some fn => (Some s', fn)
        end
      end
    end.
  Proof.
    intros.
    destruct s; simpl in *; try discriminate.
    assert (Stack.stack_append s1 s2 = Stack.stuple t s') by congruence.
    functional inversion H; subst; simpl in *; try omega.
    clear H teq.
    induction s; simpl in *; try omega.
  Defined.

  Inductive SMState :=
    | running (smp: SMProgram)
          (returns: list SMProgram)
          (fn_table: list SMProgram)
          (stack: Stack)
          (input: list nat)
          (output: list nat)
    | halted (output: list nat)
    | error.

  Definition sm_step (s: SMState): SMState :=
    match s with
    | halted _ | error => s
    | running smp rets fn_table stack input output =>
      match smp with
      | [] =>
        match rets with
        | smp' :: rets' => running smp' rets' fn_table stack input output
        | _ => halted output
        end
      | push n :: smp' =>
        running smp' rets fn_table (Stack.snat n stack) input output
      | del n :: smp' =>
        match Stack.stack_del n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | get n :: smp' =>
        match Stack.stack_get n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | pack n :: smp' =>
        match Stack.stack_pack n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | unpack :: smp' =>
        match Stack.stack_unpack stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | cond_get n k :: smp' =>
        match stack with
        | Stack.snat 0 _ =>
          match Stack.stack_get n stack with
          | Some stack' => running smp' rets fn_table stack' input output
          | None => error
          end
        | Stack.snat _ _ =>
          match Stack.stack_get k stack with
          | Some stack' => running smp' rets fn_table stack' input output
          | None => error
          end
        | _ => error
        end
      | call :: smp' =>
        match stack_call stack fn_table with
        | (Some stack', smf) =>
          running smf (smp' :: rets) fn_table stack' input output
        | (None, _) => error
        end
      | inc :: smp' =>
        match Stack.stack_inc stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | dec :: smp' =>
        match Stack.stack_dec stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | read :: smp' =>
        match input with
        | [] =>  running smp' rets fn_table (Stack.snat 0 stack) [] output
        | a :: tl => running smp' rets fn_table (Stack.snat a stack) tl output
        end
      | out :: smp' =>
        match Stack.stack_out stack with
        | Some a => running smp' rets fn_table stack input (output ++ [a])
        | None => error
        end
      end
    end.

  Definition exec_init (main: SMProgram) (fn_table: list SMProgram) (input : list nat) : SMState :=
    running main [] fn_table Stack.snil input [].

  Definition interpret_sm (prog: SMProgram * list SMProgram) (input : list nat) (fuel: nat):
    option (list nat) :=
    let (main, fn_table) := prog in
    match Utils.run sm_step (exec_init main fn_table input) fuel with
    | halted output => Some output
    | _ => None
    end.

  Example push_simple:
    interpret_sm ([push 3; out], []) [] 20 = Some [3].
  Proof. auto. Qed.

  Example call_simple:
    interpret_sm ([push 0; out; call; push 2; out], [[push 3; out]]) [] 9 = Some [0; 3; 2].
  Proof. auto. Qed.

  Inductive Ctx :=
  | ctx (smp: SMProgram) (fn_table: list SMProgram) (n_args stack_size: nat).

  Function lambda_to_sml (l: Lambda.Lambda) (c: Ctx): Ctx :=
    match c with
    | ctx smp fn_table n_args stack_size =>
      match l with
      | Lambda.var n =>
        ctx (smp ++ [get (stack_size - n - 1)]) fn_table n_args (S stack_size)
      | Lambda.lam e =>
        match lambda_to_sml e (ctx [] fn_table (S n_args) (S n_args)) with
        | ctx body fn_table' _ stack_size' =>
          (* remove arguments at end of body, leaving only return val *)
          let body := body ++ (repeat (del 1) (S n_args)) in
          (* retrieve args and create closure *)
          let smp := smp ++ (repeat (get (stack_size - 1)) n_args)
                         ++ [push (List.length fn_table')]
                         ++ [pack (S n_args)] in
          ctx smp (fn_table' ++ [body]) n_args (S stack_size')
        end
      | Lambda.app e1 e2 =>
        match lambda_to_sml e1 (lambda_to_sml e2 c) with
        | ctx smp fn_table' _ stack_size' =>
          ctx (smp ++ [call]) fn_table' n_args (pred stack_size')
        end
      | Lambda.out e =>
        match lambda_to_sml e c with
        | ctx smp fn_table' _ stack_size' =>
          let smp := smp ++ [push 0; push 0; get 2; call; call; out; del 0] in
          ctx smp fn_table' n_args stack_size'
        end
      end
    end.

  (* Start context with a placeholder for !add. Assume input
     list already on stack *)
  Function sml_of_lambda (l: Lambda.Lambda): (SMProgram * list SMProgram) :=
    match lambda_to_sml l (ctx [] [[inc]] 0 (* 1 *) 0) with
    | ctx smp fn_table _ _ =>
      (* TODO: Add input injection code before smp *)
      ((* bootstrap ++ *) smp (* ++ [call] *), fn_table)
    end.

    Example run_trans_out_2:
    match (Lambda.parse_lambda "^(\f.\x.f (f x))") with
    | Some l => interpret_sm (sml_of_lambda l) [] 27
    | None => None
    end = Some [2].
  Proof. auto. Qed.

  Example run_trans_out_f_id_2:
    match (Lambda.parse_lambda "^((\x.\y.y) (\x.x) (\f.\x.f (f x)))") with
    | Some l => interpret_sm (sml_of_lambda l) [] 42
    | None => None
    end = Some [2].
  Proof. auto. Qed.

  Fixpoint bump_function_ids_by (n : nat) (smp : SMProgram) : SMProgram :=
    match smp with
    | [] => []
    | push m :: smp' => push (m + n) :: (bump_function_ids_by n smp')
    | hd :: smp' => hd :: (bump_function_ids_by n smp')
    end.


  Definition sm_table_from_program (prog : SMProgram * list SMProgram) 
    : list SMProgram := 
    let (smp, fn_table) := prog in
    smp :: (map (bump_function_ids_by 1) fn_table).

  Fixpoint make_library (progs : list (SMProgram * list SMProgram)) : list SMProgram :=
  match progs with
  | [] => []
  | (body, table) :: tl => 
    let new_lib := map (bump_function_ids_by 1) (make_library tl) in
    body :: new_lib ++ (map (bump_function_ids_by (List.length (body :: new_lib))) table)
  end.

  Definition force_parse_lambda l := match Lambda.parse_lambda l with
    | Some l => l
    | None => Lambda.var 0 (* Bogus *)
    end.

  Definition nil := sml_of_lambda (force_parse_lambda Lambda.EMPTY).
  Definition cons := sml_of_lambda (force_parse_lambda Lambda.CONS).
  Definition zero := sml_of_lambda (force_parse_lambda Lambda.ZERO).
  Definition succ := sml_of_lambda (force_parse_lambda Lambda.SUCC).

  Definition std_lib := make_library [nil; cons; zero; succ].


End SML.
