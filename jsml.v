Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Load sml.

Module JSML.
  Inductive JSMCommand : Set :=
  | push (n: nat)
  | del (n: nat)
  | get (n: nat)
  | pack (n: nat)
  | unpack

  | inc
  | out.

  Definition JSMProgram := list JSMCommand.
  Definition Stack := Stack.Stack.

  Inductive JSMState :=
    | running (smp: JSMProgram)
          (fn_table: list JSMProgram)
          (stack: Stack)
          (output: list nat)
    | halted (output: list nat)
    | error.

  Function stack_jump (s : Stack) (fn_table : list JSMProgram) 
           {measure Stack.stack_weight s} :=
    match Stack.stack_unpack s with
    | None => (None, [])
    | Some stack =>
      match stack with
      | Stack.snil => (None, [])
      | Stack.stuple t s' => stack_jump stack fn_table
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

  Function jsm_step (s: JSMState): JSMState :=
    match s with
    | halted _ | error => s
    | running smp fn_table stack output =>
      match smp with
      | [] =>
        match stack_jump stack fn_table with
        | (Some stack', smf) =>
          running smf fn_table stack' output
        | (None, _) => halted output
        end
      | push n :: smp' =>
        running smp' fn_table (Stack.snat n stack) output
      | del n :: smp' =>
        match Stack.stack_del n stack with
        | Some stack' => running smp' fn_table stack' output
        | None => error
        end
      | get n :: smp' =>
        match Stack.stack_get n stack with
        | Some stack' => running smp' fn_table stack' output
        | None => error
        end
      | pack n :: smp' =>
        match Stack.stack_pack n stack with
        | Some stack' => running smp' fn_table stack' output
        | None => error
        end
      | unpack :: smp' =>
        match Stack.stack_unpack stack with
        | Some stack' => running smp' fn_table stack' output
        | None => error
        end
      | inc :: smp' =>
        match Stack.stack_inc stack with
        | Some stack' => running smp' fn_table stack' output
        | None => error
        end
      | out :: smp' =>
        match Stack.stack_out stack with
        | Some a => running smp' fn_table stack (output ++ [a])
        | None => error
        end
      end
    end.

  Definition exec_init (main: JSMProgram) (fn_table: list JSMProgram) : JSMState :=
    running main fn_table Stack.snil [].

  Definition interpret_jsm (prog: JSMProgram * list JSMProgram) (fuel: nat):
    option (list nat) :=
    let (main, fn_table) := prog in
    match Utils.run jsm_step (exec_init main fn_table) fuel with
    | halted output => Some output
    | _ => None
    end.

  Function jsmp_of_smp (smp : SML.SMProgram) (len : nat) (calls : list JSMProgram) : (JSMProgram * list JSMProgram) :=
    match smp with
    | SML.push n :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (push n :: jsmp, calls)
      end
    | SML.get n :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (get n :: jsmp, calls)
      end
    | SML.pack n :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (pack n :: jsmp, calls)
      end
    | SML.del n :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (del n :: jsmp, calls)
      end
    | SML.unpack :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (unpack :: jsmp, calls)
      end
    | SML.out :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (out :: jsmp, calls)
      end
    | SML.inc :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => (inc :: jsmp, calls)
      end
    | SML.call :: smp' =>
      match jsmp_of_smp smp' len calls with
      | (jsmp, calls) => ([push (len + List.length calls); get 1; del 2], calls ++ [jsmp])
      end
    | [] => ([], calls)
  end.

  Function jsm_of_sm' (fn_table : list SML.SMProgram) (start : list JSMProgram) 
           (calls : list JSMProgram) (n : nat) : (list JSMProgram) :=
    match fn_table with
    | [] => start ++ calls
    | smp :: tl =>
       match jsmp_of_smp smp n calls with
       | (jsmp, calls') => jsm_of_sm' tl (start ++ [jsmp]) calls' n
       end
    end.
    
  Function jsm_of_sm (sm : SML.SMProgram * list SML.SMProgram) : (JSMProgram * list JSMProgram) :=
    match sm with
    | (main, fn_table) =>
      match jsmp_of_smp main (List.length fn_table) [] with
      | (main', calls') => 
          (main', jsm_of_sm' fn_table [] calls' (List.length fn_table))
      end
    end.

  Theorem jsml_of_sml_correct :
  forall (sm : SML.SMProgram * list SML.SMProgram) (input output: list nat),
      (exists fuel, SML.interpret_sm sm fuel = Some output) ->
      (exists fuel, interpret_jsm (jsm_of_sm sm) fuel = Some output).
  Proof.
    intros.
    destruct H as [fuel]; exists fuel.
    rewrite <- H; clear H.
    unfold interpret_jsm, SML.interpret_sm.
    (* finish proof... *)
  Admitted.
  
  
  (* NOT USEFUL: I was doing the wrong direction. Keeping it here just because...
  Function smp_of_jsmp (jsmp : JSMProgram) : SML.SMProgram :=
    match jsmp with
    | push n :: jsmp' => SML.push n :: (smp_of_jsmp jsmp')
    | del n :: jsmp' => SML.del n :: (smp_of_jsmp jsmp')
    | get n :: jsmp' => SML.get n :: (smp_of_jsmp jsmp')
    | pack n :: jsmp' => SML.pack n :: (smp_of_jsmp jsmp')
    | unpack :: jsmp' => SML.unpack :: (smp_of_jsmp jsmp')
    | out :: jsmp' => SML.out :: (smp_of_jsmp jsmp')
    | inc :: jsmp' => SML.inc :: (smp_of_jsmp jsmp')
    | [] => [SML.call]
    end.

  Function sm_of_jsm (jsmp : JSMProgram * list JSMProgram) : SML.SMProgram * list SML.SMProgram :=
    match jsmp with
    | (main, fn_table) => (smp_of_jsmp main, List.map smp_of_jsmp fn_table)
    end.
  *)

End JSML.
