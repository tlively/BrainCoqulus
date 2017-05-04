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
  | label : string -> BFN -> BFN
  | assert : (nat -> bool) -> string -> BFN -> BFN.
  
  Inductive BFNState : Type :=
    | running (ast: BFN)
              (resets: list BFN)
              (ptr: nat)
              (tape: BFTape.Tape)
              (input: list nat)
              (output: list nat)
    | halted (output: list nat)
    | error (msg: string).

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
    | assert b string bfn' => S (bfn_weight bfn')
    end.

  Function bfn_state_weight (s: BFNState): nat :=
    match s with
    | running bfn _ _ _ _ _ => bfn_weight bfn
    | halted _ | error _ => 0
    end.

  Function bfn_step (s: BFNState) {measure bfn_state_weight s}: BFNState :=
    match s with
    | halted _ | error _ => s
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
      | assert truth msg bfn' => match truth ptr with
         | true => running bfn' resets ptr tape input output
         | false => error msg
         end
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
    | error msg => None
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
    | assert truth str bfn' => assert truth str (bfn_append bfn' bfn2)
    end.

  Notation "a & f" := (bfn_append a f) (at level 50, left associativity).
  
  Fixpoint repeat (n : nat) (bfn : BFN) : BFN :=
    match n with
    | 0 => bfn_end
    | S m => bfn & repeat m bfn
    end.
  
  Definition prev :=
    label "prev" (bfn_left 3 (bfn_loop (bfn_left 3 bfn_end) bfn_end)).
    
  Definition next :=
    label "next" (bfn_right 3 (bfn_loop (bfn_right 3 bfn_end) bfn_end)).
    
  Definition zero_cell :=
    label "zero_cell" (bfn_loop (bfn_dec 1 bfn_end) bfn_end).
    
  Definition scc_right :=
    label "scc_right" zero_cell & (bfn_right 1 (bfn_loop (bfn_dec 1 (bfn_left 1 (bfn_inc 1 (bfn_right 1 (bfn_end))))) 
    (bfn_left 1 bfn_end))).
  
  Definition scc_left :=
    label "scc_left" zero_cell & (bfn_left 1 (bfn_loop (bfn_dec 1 (bfn_right 1 (bfn_inc 1 (bfn_left 1 bfn_end)))) 
    (bfn_right 1 bfn_end))).
    
  Definition skk := 
    label "skk" zero_cell & (bfn_right 1 zero_cell) & (bfn_right 1 scc_right) & 
    (bfn_loop (bfn_dec 1 (bfn_right 1 (bfn_inc 1 (bfn_left 3 (bfn_inc 1 (bfn_right 2 bfn_end)))))) 
      ((bfn_right 3 scc_left) & 
    (bfn_loop (bfn_dec 1 (bfn_left 1 (bfn_inc 1 (bfn_left 3 (bfn_inc 1 (bfn_right 4 bfn_end)))))) 
      (bfn_left 5 bfn_end)))).
      
  Definition sik :=
    label "sik" (skk & (bfn_right 6 (bfn_loop ((bfn_left 3 skk) & bfn_right 6 bfn_end) (bfn_left 3 prev)))).

  Definition shift_item :=
    label "shift_item" next & (bfn_left 3 (bfn_loop (sik & bfn_left 3 bfn_end) sik)).
    
  Definition zero_item :=
    label "zero_item" (bfn_right 2 (zero_cell & (bfn_right 1 zero_cell) & (bfn_left 3 bfn_end))).

  (* JSML -> BFN. Stub. *)
  Function bfn_of_jsm (main : JSML.JSMProgram) :=
    match main with
    | JSML.push n :: jsmp =>
      let bfn := bfn_of_jsm jsmp in
       (bfn_right 3 (bfn_inc 1 (bfn_right 1 (bfn_inc n (bfn_right 2 bfn))))) (* need to zero? *)
    | JSML.del n :: jsmp =>
      let bfn := bfn_of_jsm jsmp in
      label "del" (repeat (n+1) prev) & (repeat n (shift_item & next)) & zero_item & bfn
    | JSML.out :: jsmp =>
      bfn_left 2 (bfn_out 1 (bfn_right 2 (bfn_of_jsm jsmp)))
    | _ => bfn_end
    end.
  
  Example bfn_of_jsml_push :
    interpret_bfn (bfn_of_jsm [JSML.push 20; JSML.push 10; JSML.out]) [] 60 = Some [10].
  Proof. auto. Qed.
  
  Example bfn_of_jsm1_del_0 :
    interpret_bfn (bfn_of_jsm [JSML.push 10; JSML.push 20; JSML.del 0; JSML.out]) [] 700 = Some [10].
  Proof. auto. Qed.
  
  
  Example bfn_of_jsm1_del_1 :
    interpret_bfn (bfn_of_jsm [JSML.push 10; JSML.push 20; JSML.del 1; JSML.out]) [] 1700 = Some [20].
  Proof. auto. Qed. 
  
  
  Example bfn_of_jsm1_del_1 :
    interpret_bfn (bfn_of_jsm [JSML.push 10; JSML.push 20; JSML.del 1; JSML.out]) [] 1700 = Some [20].
  Proof. auto. Qed.
 
 
  
  Eval compute in debug_bfn (bfn_of_jsm [JSML.push 5; JSML.push 2; JSML.push 3; JSML.del 1; JSML.out]) [] 2000.
  
 
  Eval compute in debug_bfn (bfn_of_jsm [JSML.push 5; JSML.push 2; JSML.push 3; JSML.del 2; JSML.out]) [] 350.
 
  
  Eval compute in debug_bfn (bfn_of_jsm [JSML.push 1; JSML.push 2; JSML.del 1; JSML.out]) [] .
  
  
  Eval compute in bfn_of_jsm [JSML.push 1].
  Eval compute in interpret_bfn (bfn_of_jsm [JSML.push 1; JSML.push 2; JSML.out]) [] 50.
  
  
  Example bfn_of_jsm1 :
    interpret_bfn (bfn_of_jsm [JSML.push 1]) [] 20 = Some [].
  Proof. simpl. auto. Qed.
    
    

End BFN.
