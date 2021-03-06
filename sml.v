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
           {measure Stack.weight s}: (option Stack) * SMProgram  :=
    match Stack.unpack s with
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
    assert (Stack.append s1 s2 = Stack.stuple t s') by congruence.
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
        match Stack.del n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | get n :: smp' =>
        match Stack.get n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | pack n :: smp' =>
        match Stack.pack n stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | unpack :: smp' =>
        match Stack.unpack stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | cond_get n k :: smp' =>
        match Stack.cond_get stack n k with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | call :: smp' =>
        match stack_call stack fn_table with
        | (Some stack', smf) =>
          running smf (smp' :: rets) fn_table stack' input output
        | (None, _) => error
        end
      | inc :: smp' =>
        match Stack.inc stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | dec :: smp' =>
        match Stack.dec stack with
        | Some stack' => running smp' rets fn_table stack' input output
        | None => error
        end
      | read :: smp' =>
        match input with
        | [] =>  running smp' rets fn_table (Stack.snat 0 stack) [] output
        | a :: tl => running smp' rets fn_table (Stack.snat a stack) tl output
        end
      | out :: smp' =>
        match Stack.out stack with
        | Some a => running smp' rets fn_table stack input (output ++ [a])
        | None => error
        end
      end
    end.

  Inductive Ctx :=
  | ctx (smp: SMProgram) (fn_table: list SMProgram) (n_args stack_size: nat).

  Definition inc_fid := 1.

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
          ctx smp (fn_table' ++ [body]) n_args (S stack_size)
        end
      | Lambda.app e1 e2 =>
        match lambda_to_sml e1 (lambda_to_sml e2 c) with
        | ctx smp fn_table' _ stack_size' =>
          ctx (smp ++ [call]) fn_table' n_args (pred stack_size')
        end
      | Lambda.out e =>
        match lambda_to_sml e c with
        | ctx smp fn_table' _ stack_size' =>
          let smp :=
              smp ++ [push 0; push inc_fid; get 2; call; call; out; del 0] in
          ctx smp fn_table' n_args stack_size'
        end
      end
    end.

  (* Compile lambda to SML without the runtime *)
  Definition lambda_to_sml_fns (l: Lambda.Lambda): list SMProgram :=
    match lambda_to_sml l (ctx [] [] 0 0) with
    | ctx _ fn_table _ _ => fn_table
    end.

  Example app_correct: lambda_to_sml_fns
                         (Lambda.lam
                            (Lambda.app
                               (Lambda.app
                                  (Lambda.var 0)
                                  (Lambda.lam (Lambda.var 0)))
                               (Lambda.lam (Lambda.var 0)))) =
                       [[get 1; del 1; del 1];
                          [get 1; del 1; del 1];
                          [get 0; push 0; pack 2; get 1; push 1; pack 2;
                             get 2; call; call; del 1]].
  Proof.
    auto.
  Qed.

  (* Building Library that reads the input *)
  Fixpoint bump_function_ids_by (n : nat) (smp : SMProgram) : SMProgram :=
    match smp with
    | [] => []
    | push m :: smp' => push (m + n) :: (bump_function_ids_by n smp')
    | hd :: smp' => hd :: (bump_function_ids_by n smp')
    end.

  Definition lib_weight (progs: list (list SMProgram)): nat :=
    List.length progs.

  Function make_library (progs: list (list SMProgram))
           {measure lib_weight progs}: list SMProgram :=
    match progs with
    | [] => []
    | table :: tl =>
      table ++ (make_library
                  (map (map (bump_function_ids_by (List.length table))) tl))
    end.
  Proof.
    intros; unfold lib_weight; rewrite map_length; simpl; omega.
  Defined.

  Definition runtime_lib: list SMProgram :=
    let inc_fns := [[inc]] in
    let nil_fns := lambda_to_sml_fns (Lambda.parse_def Lambda.EMPTY) in
    let cons_fns := lambda_to_sml_fns (Lambda.parse_def Lambda.CONS) in
    let zero_fns := lambda_to_sml_fns (Lambda.parse_def Lambda.ZERO) in
    let succ_fns := lambda_to_sml_fns (Lambda.parse_def Lambda.SUCC) in
    let lib := make_library [[[]]; inc_fns; nil_fns] in
    let nil_fid := List.length lib - 1 in
    let lib := make_library [lib; cons_fns] in
    let cons_fid := List.length lib - 1 in
    let lib := make_library [lib; zero_fns] in
    let zero_fid := List.length lib - 1 in
    let lib := make_library [lib; succ_fns] in
    let succ_fid := List.length lib - 1 in
    let church_fns :=
        let start := List.length lib in
        (* ret_zero [n] *)
        [[del 0; push zero_fid];
           (* do_church_work [n] *)
           [dec; push (start + 2); call; push succ_fid; call];
           (* church [n] *)
           [push (start + 0); push (start + 1); get 2; cond_get 2 1;
              del 1; del 1; del 1; call]] in
    let lib := lib ++ church_fns in
    let church_fid := List.length lib - 1 in
    let enc_list_fns :=
        let start := List.length lib in
        (* ret_nil [n] *)
        [[del 0; push nil_fid];
           (* do_list_enc_work [n] *)
           [push (start + 2); call; get 1; del 2; push church_fid; call;
              push cons_fid; call; call];
           (* list_enc [] *)
           [push (start + 0); push (start + 1); read; cond_get 2 1;
              del 2; del 2; call]] in
    lib ++ enc_list_fns.

  Lemma inc_fid_correct: nth_error runtime_lib inc_fid = Some [inc].
  Proof. auto. Qed.

  (* This is the core routine that compiles from lambda calculus and injects
     the input handling code for the SML runtime *)
  Definition sml_of_lambda (l: Lambda.Lambda): (SMProgram * list SMProgram) :=
    let read_list_fid := List.length runtime_lib - 1 in
    match lambda_to_sml l (ctx [push read_list_fid; call] runtime_lib 0 1) with
    | ctx smp fn_table _ _ => (smp ++ [call], fn_table)
    end.

  (* SML Interpreter *)
  Definition exec_init (main: SMProgram) (fn_table: list SMProgram)
             (input: list nat): SMState :=
    running main [] fn_table Stack.snil input [].

  Definition debug_sm (prog: SMProgram * list SMProgram) (input: list nat)
             (fuel: nat): SMState :=
    let (main, fn_table) := prog in
    Utils.run sm_step (exec_init main fn_table input) fuel.

  Definition interpret_sm (prog: SMProgram * list SMProgram) (input: list nat)
             (fuel: nat): option (list nat) :=
    let (main, fn_table) := prog in
    match Utils.run sm_step (exec_init main fn_table input) fuel with
    | halted output => Some output
    | _ => None
    end.

  (* Examples *)
  Example push_simple:
    interpret_sm ([push 3; out], []) [] 20 = Some [3].
  Proof. auto. Qed.

  Example call_simple:
    interpret_sm ([push 0; out; call; push 2; out],
                  [[push 3; out]]) [] 9 = Some [0; 3; 2].
  Proof. auto. Qed.

  Definition parse_lambda_and_compile (lambda_prog : string) :=
    (Lambda.parse_lambda lambda_prog)
      >>= (fun l => Some (sml_of_lambda l)).

  Definition compile_and_interpret (lambda_prog: string) (input: list nat)
             (f: nat): option (list nat) :=
    (parse_lambda_and_compile lambda_prog)
      >>= (fun l => interpret_sm l input f).

  Example run_trans_out_2:
    compile_and_interpret "\_.^(\f.\x.f (f x))" [] 50 = Some [2].
  Proof. auto. Qed.

  Example run_trans_out_f_id_2:
    compile_and_interpret "\_.^((\x.\y.y) (\x.x) (\f.\x.f (f x)))" [] 69 =
    Some [2].
  Proof. auto. Qed.

  Example run_trans_with_input_1:
    compile_and_interpret "\l.^(l (\x.\y.y) (\x.\y.x))" [5] 337 = Some [5].
  Proof. auto. Qed.

  Example run_trans_echo:
    compile_and_interpret Lambda.lambda_echo [1;2;3] 1673 = Some([1;2;3]).
  Proof. auto. Qed.

End SML.
