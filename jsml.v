Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Load sml.

Module JSML.
  Inductive JSMCommand: Set :=
  | push (n: nat)
  | del (n: nat)
  | get (n: nat)
  | pack (n: nat)
  | unpack
  | cond_get (n k: nat)
  | inc
  | dec
  | read
  | out.

  Definition JSMProgram := list JSMCommand.
  Definition Stack := Stack.Stack.

  Inductive JSMState :=
    | running (smp: JSMProgram)
          (fn_table: list JSMProgram)
          (stack: Stack)
          (input: list nat)
          (output: list nat)
    | halted (output: list nat)
    | error.

  (* This is the same as stack_call in SML. *)
  Function stack_jump (s: Stack) (fn_table: list JSMProgram)
           {measure Stack.weight s}: (option Stack) * JSMProgram  :=
    match Stack.unpack s with
    | None => (None, [])
    | Some stack =>
      match stack with
      | Stack.snil => (None, [])
      | Stack.stuple t s' => stack_jump stack fn_table
      | Stack.snat 0 _ => (None, [])
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

  Function jsm_step (s: JSMState): JSMState :=
    match s with
    | halted _ | error => s
    | running smp fn_table stack input output =>
      match smp with
      | [] =>
        match stack_jump stack fn_table with
        | (Some stack', smf) => running smf fn_table stack' input output
        | (None, _) => error
        end
      | push n :: smp' =>
        running smp' fn_table (Stack.snat n stack) input output
      | del n :: smp' =>
        match Stack.del n stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | get n :: smp' =>
        match Stack.get n stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | pack n :: smp' =>
        match Stack.pack n stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | unpack :: smp' =>
        match Stack.unpack stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | cond_get n k :: smp' =>
        match Stack.cond_get stack n k with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | inc :: smp' =>
        match Stack.inc stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | dec :: smp' =>
        match Stack.dec stack with
        | Some stack' => running smp' fn_table stack' input output
        | None => error
        end
      | read :: smp' =>
        match input with
        | [] =>  running smp' fn_table (Stack.snat 0 stack) [] output
        | a :: tl => running smp' fn_table (Stack.snat a stack) tl output
        end
      | out :: smp' =>
        match Stack.out stack with
        | Some a => running smp' fn_table stack input (output ++ [a])
        | None => error
        end
      end
    end.

  Definition exec_init (main: JSMProgram) (fn_table: list JSMProgram)
            (input: list nat): JSMState :=
    running main fn_table Stack.snil input [].

  Definition interpret_jsm (prog: JSMProgram * list JSMProgram)
             (input: list nat)(fuel: nat): option (list nat) :=
    let (main, fn_table) := prog in
    match Utils.run jsm_step (exec_init main fn_table input) fuel with
    | halted output => Some output
    | _ => None
    end.

  Function jsmc_of_smc (smc: SML.SMCommand): JSMCommand :=
    match smc with
    | SML.push n => push n
    | SML.get n => get n
    | SML.pack n => pack n
    | SML.del n => del n
    | SML.unpack => unpack
    | SML.cond_get n k => cond_get n k
    | SML.call => pack 0 (* no-op *)
    | SML.inc => inc
    | SML.dec => dec
    | SML.read => read
    | SML.out => out
    end.

  Function jsmp_of_smp (smp: SML.SMProgram) (len: nat)
          (calls: list JSMProgram): (JSMProgram * list JSMProgram) :=
    match smp with
    | [] => ([], calls)
    | SML.call :: smp' =>
      let (jsmp, calls) := jsmp_of_smp smp' len calls in
      ([push (len + List.length calls); get 1; del 2], calls ++ [jsmp])
    | smc :: smp' =>
      let (jsmp, calls) := jsmp_of_smp smp' len calls in
      (jsmc_of_smc smc :: jsmp, calls)
  end.

  Function jsm_table_of_sm_table (fn_table: list SML.SMProgram)
           (start: list JSMProgram) (calls: list JSMProgram) (n: nat):
    (list JSMProgram) :=
    match fn_table with
    | [] => start ++ calls
    | smp :: tl =>
       let (jsmp, calls') := jsmp_of_smp smp n calls in
       jsm_table_of_sm_table tl (start ++ [jsmp]) calls' n
    end.

  Function jsm_of_sm (sm: SML.SMProgram * list SML.SMProgram):
    (JSMProgram * list JSMProgram) :=
    let (main, fn_table) := sm in
    let (main', calls') := jsmp_of_smp main (List.length fn_table) [] in
    (main', jsm_table_of_sm_table fn_table [] calls' (List.length fn_table)).

  (*
  Theorem jsml_of_sml_correct :
  forall (sm: SML.SMProgram * list SML.SMProgram) (input output: list nat),
      (exists fuel, SML.interpret_sm sm input fuel = Some output) ->
      (exists fuel, interpret_jsm (jsm_of_sm sm) input fuel = Some output).
  Proof.
    intros.
    destruct H as [fuel]; exists fuel.
    rewrite <- H; clear H.
    unfold interpret_jsm, SML.interpret_sm.
    (* finish proof... *)
  Admitted.
  *)

End JSML.
