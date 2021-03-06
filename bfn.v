Require Import Bool.BoolEq.
Require Import Logic.FunctionalExtensionality.

Load jsml.
Load bftape.

Module BFN.

  (* Layer 1 above BF: BFN Program Type. Repeat each command N times *)
  Inductive BFN : Set :=
  | bfn_end : BFN
  | bfn_right : nat -> BFN -> BFN (* > *)
  | bfn_left : nat -> BFN -> BFN  (* < *)
  | bfn_inc : nat -> BFN -> BFN   (* + *)
  | bfn_dec : nat -> BFN -> BFN   (* - *)
  | bfn_out : nat -> BFN -> BFN   (* . *)
  | bfn_in : nat -> BFN -> BFN    (* , *)
  | bfn_loop : BFN -> BFN -> BFN  (* [...] *)
  | label : string -> BFN -> BFN.

  Inductive BFNState : Type :=
    | running (ast: BFN)
              (resets: list BFN)
              (ptr: nat)
              (tape: BFTape.Tape)
              (input: list nat)
              (output: list nat)
    | halted (output: list nat).

  Function bfn_weight (bfn: BFN): nat :=
    match bfn with
    | bfn_end => 0
    | bfn_right n bfn'
    | bfn_left n bfn'
    | bfn_inc n bfn'
    | bfn_dec n bfn'
    | bfn_out n bfn'
    | bfn_in n bfn' => (S n) + bfn_weight bfn'
    | bfn_loop inner bfn' => S ((bfn_weight inner) + (bfn_weight bfn'))
    | label string bfn' => S (bfn_weight bfn')
    end.

  Function bfn_state_weight (s: BFNState): nat :=
    match s with
    | running bfn _ _ _ _ _ => bfn_weight bfn
    | halted _ => 0
    end.

  Function bfn_step (s: BFNState) {measure bfn_state_weight s}: BFNState :=
    match s with
    | halted _ => s
    | running bfn resets ptr tape input output =>
      match bfn with
      | bfn_end =>
        match resets with
        | [] => halted output
        | bfn' :: resets' =>
          running bfn' resets' ptr tape input output
        end
      | bfn_right 0 bfn'
      | bfn_left 0 bfn'
      | bfn_inc 0 bfn'
      | bfn_dec 0 bfn'
      | bfn_out 0 bfn'
      | bfn_in 0 bfn' => bfn_step (running bfn' resets ptr tape input output)
      | bfn_right (S n) bfn' =>
        running (bfn_right n bfn') resets (S ptr) tape input output
      | bfn_left (S n) bfn' =>
        running (bfn_left n bfn') resets (pred ptr) tape input output
      | bfn_inc (S n) bfn' =>
        running (bfn_inc n bfn') resets ptr (BFTape.inc tape ptr) input output
      | bfn_dec (S n) bfn' =>
        running (bfn_dec n bfn') resets ptr (BFTape.dec tape ptr) input output
      | bfn_out (S n) bfn' =>
        running (bfn_out n bfn') resets ptr tape input
                    (output ++ [BFTape.get tape ptr])
      | bfn_in (S n) bfn' =>
        match input with
        | [] =>
          running (bfn_in n bfn') resets ptr (BFTape.put tape ptr 0)
                      input output
        | x :: input' =>
          running (bfn_in n bfn') resets ptr (BFTape.put tape ptr x)
                      input' output
        end
      | bfn_loop inner_bfn bfn' =>
        if (BFTape.get tape ptr) =? 0 then
          running bfn' resets ptr tape input output
        else
          running inner_bfn (bfn :: resets) ptr tape input output
      | label str bfn' => running bfn' resets ptr tape input output
      end
    end.
  Proof.
    all: intros; auto; simpl; omega.
  Defined.

  Function exec_init (prog: BFN) (input: list nat): BFNState :=
    running prog [] 0 BFTape.empty input [].

Definition debug_bfn (prog: BFN) (input: list nat) (fuel: nat) :=
    Utils.run bfn_step (exec_init prog input) fuel.


  Definition interpret_bfn (prog: BFN) (input: list nat) (fuel: nat): option (list nat) :=
    match Utils.run bfn_step (exec_init prog input) fuel with
    | running _ _ _ _ _ _ => None
    | halted output => Some output
    end.

  Function bfn_append bfn1 bfn2 :=
    match bfn1 with
    | bfn_end => bfn2
    | bfn_right n bfn' => bfn_right n (bfn_append bfn' bfn2)
    | bfn_left n bfn' => bfn_left n (bfn_append bfn' bfn2)
    | bfn_inc n bfn' => bfn_inc n (bfn_append bfn' bfn2)
    | bfn_dec n bfn' => bfn_dec n (bfn_append bfn' bfn2)
    | bfn_out n bfn' => bfn_out n (bfn_append bfn' bfn2)
    | bfn_in n bfn' => bfn_in n (bfn_append bfn' bfn2)
    | bfn_loop inner bfn' => bfn_loop inner (bfn_append bfn' bfn2)
    | label str bfn' => label str (bfn_append bfn' bfn2)
    end.

  Notation "a & f" := (bfn_append a f) (at level 50, left associativity).

  Fixpoint repeat (n : nat) (bfn : BFN) : BFN :=
    match n with
    | 0 => bfn_end
    | S m => bfn & (repeat m bfn)
    end.

  Definition KELL_SIZE := 4.
  Definition kl := bfn_left KELL_SIZE bfn_end.
  Definition kr := bfn_right KELL_SIZE bfn_end.
  Definition unmark := bfn_right (KELL_SIZE - 2) (bfn_inc 1 (bfn_left (KELL_SIZE -2) bfn_end)).
  Definition mark := bfn_right (KELL_SIZE - 2) (bfn_loop (bfn_dec 1 bfn_end) (bfn_left (KELL_SIZE -2) bfn_end)).
  Definition next_marked := (bfn_right (KELL_SIZE - 2) kr) & (bfn_loop kr (bfn_left (KELL_SIZE - 2) bfn_end)).
  Definition prev_marked := bfn_right (KELL_SIZE - 2) kl & bfn_loop kl (bfn_left (KELL_SIZE - 2) bfn_end).
  Definition prev := kl & bfn_loop kl bfn_end.
  Definition next := kr & bfn_loop kr bfn_end.
  Definition to_scratch := bfn_right (KELL_SIZE - 1) bfn_end.
  Definition from_scratch := bfn_left (KELL_SIZE - 1) bfn_end.
  Definition to_scratch_val := bfn_right (KELL_SIZE - 2) bfn_end.
  Definition from_scratch_val := bfn_left (KELL_SIZE - 2) bfn_end.

  Definition copy_to_scratch (offset:nat):BFN :=
    let move := KELL_SIZE - 1 - offset in
    bfn_right offset (bfn_loop (bfn_dec 1 (bfn_right move (bfn_inc 1 (bfn_left move bfn_end)))) (bfn_left offset bfn_end)).

  Definition copy_cell (offset:nat):BFN :=
    copy_to_scratch(offset) & to_scratch & (bfn_loop (bfn_dec 1 from_scratch & bfn_right offset bfn_end) from_scratch).

  Definition get (n:nat):BFN :=
    unmark & kr & mark & kl & (repeat (n+1) prev) & kr & mark & (bfn_loop ((copy_cell 0) & (copy_cell 1) & next_marked & unmark & prev_marked & unmark & kr & (mark & bfn_end)) next_marked).

  Definition empty_kell := (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_left 4 (bfn_right 2 (bfn_inc 1 (bfn_left 2 bfn_end)))))))))))).
  Definition empty_item :=
    empty_kell & mark & kr & (bfn_loop (empty_kell & kr) (prev_marked & unmark)).
  Definition shift_kell := (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_loop (bfn_dec 1 bfn_end) (bfn_right 1 (bfn_left 4 (bfn_right 4 (bfn_loop (bfn_dec 1 (bfn_left 4 (bfn_inc 1 (bfn_right 4 bfn_end)))) (bfn_left 4 (bfn_right 5 (bfn_loop (bfn_dec 1 (bfn_left 4 (bfn_inc 1 (bfn_right 4 bfn_end)))) (bfn_left 4 (bfn_right 1 (bfn_inc 1 (bfn_right 4 (bfn_loop (bfn_dec 1 bfn_end) (bfn_inc 1 (bfn_left 6 bfn_end))))))))))))))))))))).
  Definition sik := shift_kell & kr & kr & (bfn_loop (kl & shift_kell & kr & kr) (kl & prev)).
  Definition shift_item := next & kl & (bfn_loop (sik & kl) sik).

  Definition stack_top := kr & (bfn_loop (bfn_loop kr kr) kl).

  Definition shove_zero_gap := bfn_left 2 (bfn_loop ((bfn_left (KELL_SIZE - 2) shift_item) & (bfn_left 2 bfn_end)) (bfn_right 2 kl) & shift_item).

  Definition del (n : nat):BFN :=
    match n with
    | 0 => prev & empty_item & mark
    | S _ => (repeat (n-1) (prev & kr & mark & kl)) & prev & prev & shift_item & next & mark & next_marked & (bfn_loop (kl & shove_zero_gap & kr & unmark & next & mark & next_marked) (prev_marked & stack_top))
    end.

  Definition if_else (nonzero zero : BFN) :=
    to_scratch & bfn_loop (bfn_dec 1 bfn_end) (bfn_inc 1 kr) & bfn_loop (bfn_dec 1 bfn_end) kl & from_scratch & bfn_loop nonzero to_scratch & kr & bfn_loop (from_scratch & kl & bfn_inc 1 to_scratch & kr & bfn_dec 1 bfn_end) kl & bfn_loop (from_scratch & zero & to_scratch) from_scratch.

  Definition if_else_val (nonzero zero : BFN) :=
    to_scratch_val & bfn_loop (bfn_dec 1 bfn_end) (bfn_inc 1 kr) & bfn_loop (bfn_dec 1 bfn_end) kl & from_scratch_val & bfn_loop nonzero to_scratch_val & kr & bfn_loop (from_scratch_val & kl & bfn_inc 1 to_scratch_val & kr & bfn_dec 1 bfn_end) kl & bfn_loop (from_scratch_val & zero & to_scratch_val) from_scratch_val.

  Definition pack (n : nat) : BFN :=
    ((repeat n prev) & (kr)) & (repeat n ((bfn_inc 1 kr) & (bfn_loop (bfn_inc 1 kr) bfn_end))).

  Definition unpack : BFN :=
    prev & kr & bfn_dec 1 (if_else (kr & bfn_loop (bfn_dec 1 kr) bfn_end) (bfn_inc 1 next)).

  Definition push (n : nat) : BFN :=
    unmark & kr & unmark & bfn_inc 1 (bfn_right 1 (bfn_inc n (bfn_right (KELL_SIZE - 1) bfn_end))).

  Definition out : BFN :=
    kl & bfn_right 1 (bfn_out 1 (bfn_left 1 kr)).

  Definition inc : BFN :=
    kl & bfn_right 1 (bfn_inc 1 (bfn_left 1 kr)).

  Definition dec : BFN :=
    kl & bfn_right 1 (bfn_dec 1 (bfn_left 1 kr)).

  Definition read : BFN :=
    kl & bfn_right 1 (bfn_in 1 (bfn_left 1 kr)).

  Definition unpack_until_nat : BFN :=
    kl & bfn_dec 1 (bfn_loop (bfn_inc 1 kr & unpack & kl & bfn_dec 1 bfn_end) (bfn_inc 1 kr)) & stack_top.

  Definition cond_get (n k : nat) :=
    kl & bfn_right 1 (if_else_val (stack_top & get k) (stack_top & get n)).

  (* Compiles a single JSMProgram to BFN. *)
  Function bfn_of_jsmp (main : JSML.JSMProgram) :=
    match main with
    | JSML.push n :: jsmp => label "push" (push n & bfn_of_jsmp jsmp)
    | JSML.del n :: jsmp => label "del" (del n & bfn_of_jsmp jsmp)
    | JSML.get n :: jsmp => label "get" (get n & bfn_of_jsmp jsmp)
    | JSML.pack n :: jsmp => label "pack" (pack n & bfn_of_jsmp jsmp)
    | JSML.unpack :: jsmp => label "unpack" (unpack & bfn_of_jsmp jsmp)
    | JSML.cond_get n k :: jsmp => label "cond_get" (cond_get n k & bfn_of_jsmp jsmp)
    | JSML.inc :: jsmp => label "inc" (inc & bfn_of_jsmp jsmp)
    | JSML.dec :: jsmp => label "dec" (dec & bfn_of_jsmp jsmp)
    | JSML.read :: jsmp => label "read" (read & bfn_of_jsmp jsmp)
    | JSML.out :: jsmp => label "out" (out & bfn_of_jsmp jsmp)
    | [] => bfn_end
    end.

  (* Builds the switch statement in BFN, which is essentially accessing the
     function table based on the top of the stack. *)
  Function switch (fn_table : list JSML.JSMProgram) :=
    match fn_table with
    | [] => stack_top (* maybe delete argument? *)
    | hd :: tl =>
        if_else_val (bfn_dec 1 (switch tl))
        (bfn_left 1 stack_top & del 0 & bfn_of_jsmp hd & stack_top)
    end.

  (* Compiles the JSM function table to a loop that unpacks the first item on
     the stack, performs a while loop with the function table switch. *)
  Function bfn_of_jsm_table (fn_table : list JSML.JSMProgram) :=
    match fn_table with
    | [] => bfn_end
    | hd :: tl =>
        unpack_until_nat & kl &
        bfn_right 1 (bfn_loop (bfn_dec 1 (switch fn_table))
        (unpack_until_nat & kl & bfn_right 1 bfn_end))
    end.

  (* The full BFN program runs main, and then simply goes into the function
     table loop (due to jump semantics). *)
  Function bfn_of_jsm (jsm : JSML.JSMProgram * list JSML.JSMProgram) :=
    let (main, fn_table) := jsm in
    label "main" (bfn_of_jsmp main) & label "fn_table" (bfn_of_jsm_table fn_table).

  (* TESTS *)
(*  Eval compute in debug_bfn (bfn_of_jsmp [JSML.push 1; JSML.push 2; JSML.push 3; JSML.push 4; JSML.push 5; JSML.pack 6; JSML.pack 2; JSML.unpack]) [] 800.

  Example bfn_of_jsmpl_push :
    interpret_bfn (bfn_of_jsmp [JSML.push 2; JSML.push 3; JSML.out]) [] 100 = Some [3].
  Proof. auto. Qed.

  Example bfn_of_jsmp1_del_0 :
    interpret_bfn (bfn_of_jsmp [JSML.push 10; JSML.push 20; JSML.del 0; JSML.out]) [] 700 = Some [10].
  Proof. auto. Qed.

  Example bfn_of_jsmp1_del_1 :
    interpret_bfn (bfn_of_jsmp [JSML.push 10; JSML.push 20; JSML.del 1; JSML.out]) [] 3000 = Some [20].
  Proof. auto. Qed.

  Definition main_test := [JSML.push 0; JSML.push 0; JSML.push 1; JSML.push 0; JSML.push 2].
  Definition fn_table_test := [[JSML.inc; JSML.inc; JSML.out; JSML.del 0]; [JSML.inc; JSML.inc; JSML.inc; JSML.inc; JSML.inc; JSML.out; JSML.del 0]].

  Eval compute in (bfn_of_jsm (main_test, fn_table_test)).
  Eval compute in debug_bfn (bfn_of_jsm (main_test, fn_table_test)) [] 1060.

  (* !!!!!!! *)
  Example bfn_of_jsm_table_ex1 :
    interpret_bfn (bfn_of_jsm (main_test, fn_table_test)) [] 1000 = Some [5;2].
  Proof. auto. Qed.

  Example bfn_of_jsmp1_del_1 :
    interpret_bfn (bfn_of_jsmp [JSML.push 10; JSML.push 20; JSML.del 1; JSML.out]) [] 1700 = Some [20].
  Proof. auto. Qed.

  Eval compute in debug_bfn (bfn_of_jsmp [JSML.push 5; JSML.push 2; JSML.push 3; JSML.del 1; JSML.out]) [] 2000.
  Eval compute in debug_bfn (bfn_of_jsmp [JSML.push 5; JSML.push 2; JSML.push 3; JSML.del 2; JSML.out]) [] 350.
  Eval compute in debug_bfn (bfn_of_jsmp [JSML.push 1; JSML.push 2; JSML.del 1; JSML.out]) [] .
  Eval compute in bfn_of_jsmp [JSML.push 1].
  Eval compute in interpret_bfn (bfn_of_jsmp [JSML.push 1; JSML.push 2; JSML.out]) [] 50.

  Example bfn_of_jsmp1 :
    interpret_bfn (bfn_of_jsmp [JSML.push 1]) [] 20 = Some [].
  Proof. simpl. auto. Qed.
*)

  (* FIXME: I think this is broken right now *)
  Definition tape_of_stack (stack: Stack.Stack) :=
    let fix list_of_stack (n: nat) (stack:Stack.Stack) : list nat :=
      match stack with
      | Stack.snil => []
      | Stack.snat hd rest => (list_of_stack n rest) ++ [n;0;1;0;n+1;hd;1;0]
      | Stack.stuple t rest => (list_of_stack n rest) ++ [n;0;1;0] ++ (list_of_stack (n + 1) t)
      end
    in BFTape.tape_of_list (list_of_stack 0 stack).
 Eval compute in tape_of_stack ((Stack.snat 5 Stack.snil)).
 Eval compute in tape_of_stack ((Stack.stuple (Stack.snat 5 Stack.snil) Stack.snil)).
 
  Definition bfn_state_of_jsm_state (state: JSML.JSMState): BFNState :=
    match state with
    | JSML.halted output => halted output
    | JSML.running smp fn_table stack input output =>
      running (bfn_of_jsm (smp, fn_table)) [] ((Stack.weight stack) * KELL_SIZE) (tape_of_stack stack) input output
    | error => halted []
    end.
  Eval compute in bfn_state_of_jsm_state (JSML.running [] [] (Stack.snat 5 Stack.snil) [] []).
  Eval compute in bfn_state_of_jsm_state (JSML.running [] [] (Stack.stuple (Stack.snat 5 Stack.snil) Stack.snil) [] []).
  
  Eval compute in bfn_state_of_jsm_state (JSML.running [] [] (Stack.stuple (Stack.snat 3 (Stack.snat 2 Stack.snil)) (Stack.snat 1 Stack.snil)) [] []).
  
  (*Lemma bfn_of_jsm_correct:
    forall (jsm: JSML.JSMProgram * list JSML.JSMProgram) (input output: list nat),
      (exists fuel, JSML.interpret_jsm jsm input fuel = Some output) ->
      (exists fuel, interpret_bfn (bfn_of_jsm jsm) input fuel = Some output).
  Proof.
    intros.
    destruct H as [fuel]; exists fuel.
    rewrite <- H; clear H.
    unfold interpret_bfn, JSML.interpret_jsm.
    replace (exec_init (bfn_of_jsm jsm) input) with
    (bfn_state_of_jsm_state (JSML.exec_init jsm input)) by auto.
*)
End BFN.
