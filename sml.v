Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Load utils.
Load lambda.

Module SML.

  (* TODO: stack_equiv showing empty and singleton tuples can be reduced *)
  Inductive Stack: Set :=
  | snil
  | snat (n: nat) (s: Stack)
  | stuple (t: Stack) (s: Stack).

  Function stack_prefix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some snil
    | S n' =>
      match s with
      | snil => None
      | snat m s =>
        match stack_prefix n' s with
        | None => None
        | Some s' => Some (snat m s')
        end
      | stuple t s =>
        match stack_prefix n' s with
        | None => None
        | Some s' => Some (stuple t s')
        end
      end
    end.

  Function stack_postfix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some s
    | S n' =>
      match s with
      | snil => None
      | snat _ s'
      | stuple _ s' => stack_postfix n' s'
      end
    end.

  Function stack_append (s1 s2: Stack): Stack :=
    match s1 with
    | snil => s2
    | snat n s => snat n (stack_append s s2)
    | stuple t s => stuple t (stack_append s s2)
    end.

  Inductive SMCommand : Set :=
  | push (n: nat)
  | del (n: nat)
  | get (n: nat)
  | pack (n: nat)
  | unpack
  | call
  | inc
  | out.

  Definition SMProgram := list SMCommand.

  Inductive SMState :=
    | running (smp: SMProgram)
          (returns: list SMProgram)
          (fn_table: list SMProgram)
          (stack: Stack)
          (output: list nat)
    | halted (output: list nat)
    | error.

  Function stack_del (n: nat) (s: Stack): option Stack :=
    match (s, n) with
    | (snil, _) => None
    | (snat _ s, 0)
    | (stuple _ s, 0) => Some s
    | (snat m s, S n) =>
      match stack_del n s with
      | None => None
      | Some s' => Some (snat m s')
      end
    | (stuple t s, S n) =>
      match stack_del n s with
      | None => None
      | Some s' => Some (stuple t s')
      end
    end.

  Function stack_get (n: nat) (s: Stack): option Stack :=
    match stack_postfix n s with
    | None | Some snil => None
    | Some (snat m _) => Some (snat m s)
    | Some (stuple t _) => Some (stuple t s)
    end.

  Example stack_prefix_ex:
    forall s, stack_prefix 1 (snat 3 s) = Some (snat 3 snil).
  Proof. intros; auto. Qed.

  Function stack_pack (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 | 1 => Some s
    | _ =>
      match (stack_prefix n s, stack_postfix n s) with
      | (Some t, Some s') => Some (stuple t s')
      | _ => None
      end
    end.

  Example stack_pack_simple:
    stack_pack 2 (snat 0 (snat 1 snil)) =
    Some (stuple (snat 0 (snat 1 snil)) snil).
  Proof. auto. Qed.

  Example stack_pack_nested:
    forall tl,
      stack_pack 3 (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 tl))) =
      Some (stuple (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 snil)))
                   tl).
  Proof. intros; auto. Qed.

  Function stack_unpack (s: Stack): option Stack :=
    match s with
    | snil => None
    | snat _ _ => Some s
    | stuple t s => Some (stack_append t s)
    end.

  Function stack_weight (s: Stack): nat :=
    match s with
    | snil => 0
    | snat _ s' => S (stack_weight s')
    | stuple t s' => S (stack_weight t + stack_weight s')
    end.

  Function stack_call (s: Stack) (fn_table: list SMProgram)
           {measure stack_weight s}: (option Stack) * SMProgram :=
    match stack_unpack s with
    | None => (None, [])
    | Some stack =>
      match stack with
      | snil => (None, [])
      | stuple t s' => stack_call stack fn_table
      | snat fid s' =>
        match nth_error fn_table fid with
        | None => (None, [])
        | Some fn => (Some s', fn)
        end
      end
    end.
  Proof.
    intros.
    destruct s; simpl in *; try discriminate.
    assert (stack_append s1 s2 = stuple t s') by congruence.
    functional inversion H; subst; simpl in *; try omega.
    clear H teq.
    induction s; simpl in *; try omega.
  Defined.

  Function stack_inc (s: Stack): option Stack :=
    match s with
    | snat m s' => Some (snat (S m) s')
    | _ => None
    end.

  Function stack_out (s: Stack): (option nat) :=
    match s with
    | snat m s' => Some m
    | _ => None
    end.

  Definition sm_step (s: SMState): SMState :=
    match s with
    | halted _ | error => s
    | running smp rets fn_table stack output =>
      match smp with
      | [] =>
        match rets with
        | smp' :: rets' => running smp' rets' fn_table stack output
        | _ => halted output
        end
      | push n :: smp' =>
        running smp' rets fn_table (snat n stack) output
      | del n :: smp' =>
        match stack_del n stack with
        | Some stack' => running smp' rets fn_table stack' output
        | None => error
        end
      | get n :: smp' =>
        match stack_get n stack with
        | Some stack' => running smp' rets fn_table stack' output
        | None => error
        end
      | pack n :: smp' =>
        match stack_pack n stack with
        | Some stack' => running smp' rets fn_table stack' output
        | None => error
        end
      | unpack :: smp' =>
        match stack_unpack stack with
        | Some stack' => running smp' rets fn_table stack' output
        | None => error
        end
      | call :: smp' =>
        match stack_call stack fn_table with
        | (Some stack', smf) =>
          running smf (smp' :: rets) fn_table stack' output
        | (None, _) => error
        end
      | inc :: smp' =>
        match stack_inc stack with
        | Some stack' => running smp' rets fn_table stack' output
        | None => error
        end
      | out :: smp' =>
        match stack_out stack with
        | Some a => running smp' rets fn_table stack (output ++ [a])
        | None => error
        end
      end
    end.

  Definition exec_init (main: SMProgram) (fn_table: list SMProgram) : SMState :=
    running main [] fn_table snil [].

  Definition interpret (prog: SMProgram * list SMProgram) (fuel: nat):
    option (list nat) :=
    let (main, fn_table) := prog in
    match Utils.run sm_step (exec_init main fn_table) fuel with
    | halted output => Some output
    | _ => None
    end.

  Example push_simple:
    interpret ([push 3; out], []) 20 = Some [3].
  Proof. auto. Qed.

  Example call_simple:
    interpret ([push 0; out; call; push 2; out], [[push 3; out]]) 9 = Some [0; 3; 2].
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
    | Some l => interpret (sml_of_lambda l) 27
    | None => None
    end = Some [2].
  Proof. auto. Qed.

  Example run_trans_out_f_id_2:
    match (Lambda.parse_lambda "^((\x.\y.y) (\x.x) (\f.\x.f (f x)))") with
    | Some l => interpret (sml_of_lambda l) 42
    | None => None
    end = Some [2].
  Proof. auto. Qed.

End SML.
