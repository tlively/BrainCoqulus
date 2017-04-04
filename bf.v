Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import ZArith.
Require FMapList.
Require Import OrderedType OrderedTypeEx.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Coq.Program.Tactics.
Import ListNotations.

Load parse.

(* BF Program Type *)
Inductive BF : Set :=
| bf_end : BF
| bf_right : BF -> BF (* > *)
| bf_left : BF -> BF  (* < *)
| bf_inc : BF -> BF   (* + *)
| bf_dec : BF -> BF   (* - *)
| bf_out : BF -> BF   (* . *)
| bf_in : BF -> BF    (* , *)
| bf_loop : BF -> BF -> BF.  (* [...] *)

Section BFPrinting.

  Function chars_of_bf (bf: BF): list ascii :=
    match bf with
    | bf_end => []
    | bf_right bf' =>  ">"%char :: (chars_of_bf bf')
    | bf_left bf' => "<"%char :: (chars_of_bf bf')
    | bf_inc bf' => "+"%char :: (chars_of_bf bf')
    | bf_dec bf' => "-"%char :: (chars_of_bf bf')
    | bf_out bf' => "."%char :: (chars_of_bf bf')
    | bf_in bf' => ","%char :: (chars_of_bf bf')
    | bf_loop inner bf' =>
      "["%char :: (chars_of_bf inner) ++ ["]"%char] ++ (chars_of_bf bf')
    end.

  Function print_bf (bf: BF): string :=
    Parse.string_of_chars (chars_of_bf bf).

  Example print_all_bf_commands:
    print_bf
      (bf_loop
         (bf_right (bf_left (bf_inc (bf_dec (bf_out (bf_in bf_end))))))
         bf_end)
    = "[><+-.,]"%string. auto.
  Qed.

End BFPrinting.

Section BFParsing.

  Local Definition ParseState := @Parse.ParseState BF.
  Local Definition chars_of_string := Parse.chars_of_string.

  Function parse_bf_state (l: list ascii): ParseState :=
    match l with
    | [] => Parse.ok bf_end []
    | hd :: tl =>
      match parse_bf_state tl with
      | Parse.error => Parse.error
      | Parse.ok cur stack =>
        match hd with
        | ">"%char => Parse.ok (bf_right cur) stack
        | "<"%char => Parse.ok (bf_left cur) stack
        | "+"%char => Parse.ok (bf_inc cur) stack
        | "-"%char => Parse.ok (bf_dec cur) stack
        | "."%char => Parse.ok (bf_out cur) stack
        | ","%char => Parse.ok (bf_in cur) stack
        | "]"%char => Parse.ok bf_end (cur :: stack)
        | "["%char =>
          match stack with
          | [] => Parse.error
          | next :: stack' => Parse.ok (bf_loop cur next) stack'
          end
        | _ => Parse.ok cur stack
        end
      end
    end.

  Function parse_bf (str: string): option BF :=
    match parse_bf_state (chars_of_string str) with
    | Parse.error => None
    | Parse.ok _ (_ :: _) => None
    | Parse.ok bf [] => Some bf
    end.

  Example parse_all_bf_commands:
    parse_bf "[><+-.,]" =
    Some (bf_loop
            (bf_right (bf_left (bf_inc (bf_dec (bf_out (bf_in bf_end))))))
            bf_end).
  auto. Qed.

  Example parse_nesting_bf:
    parse_bf "[[[][]]][]" =
    Some (bf_loop
            (bf_loop
               (bf_loop bf_end (bf_loop bf_end bf_end))
               bf_end)
            (bf_loop bf_end bf_end)).
  auto. Qed.

  Example parse_empty_bf:
    parse_bf EmptyString = Some bf_end.
  auto. Qed.

  Example parse_bf_bad_left:
    parse_bf "[[]" = None.
  auto. Qed.

  Example parse_bf_bad_right:
    parse_bf "[]]" = None.
  auto. Qed.

End BFParsing.

Lemma bf_print_parse_loop (bf1 bf2: BF):
  forall bf1' bf2',
    parse_bf_state (chars_of_bf bf1) = Parse.ok bf1' [] ->
    parse_bf_state (chars_of_bf bf2) = Parse.ok bf2' [] ->
    parse_bf_state ("["%char :: (chars_of_bf bf1) ++ ["]"%char]
                                  ++ (chars_of_bf bf2))
    = Parse.ok (bf_loop bf1 bf2) [].
Proof.
Admitted.

Lemma bf_print_parse_chars_inv (bf: BF):
  parse_bf_state (chars_of_bf bf) = Parse.ok bf [].
Proof.
  induction bf; auto;
    rewrite chars_of_bf_equation, parse_bf_state_equation;
    try (rewrite IHbf; auto).
  now apply (bf_print_parse_loop _ _ bf1 bf2).
Qed.

(* Removes the parser from the trusted computing base *)
Theorem bf_print_parse_inv (bf: BF): parse_bf (print_bf bf) = Some bf.
Proof.
  unfold parse_bf, print_bf; rewrite Parse.chars_of_string_of_chars_inv.
  now rewrite bf_print_parse_chars_inv.
Qed.

(* BF Interpreter *)
(* A BFTape is a map from [nat] indices to [Z] values *)
Module NatMap := FMapList.Make Nat_as_OT.
Definition BFTape := NatMap.t Z.

Definition tape_get (tape: BFTape) (ptr: nat): Z :=
  match (NatMap.find ptr tape) with
  | Some x => x
  | None => 0
  end.

Definition tape_set (tape: BFTape) (ptr: nat) (x: Z): BFTape :=
  NatMap.add ptr x tape.

Definition tape_inc (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.succ (tape_get tape ptr)).

Definition tape_dec (tape: BFTape) (ptr: nat): BFTape :=
  tape_set tape ptr (Z.pred (tape_get tape ptr)).

(* `bf' is the current state of the program, while `resets' is the
stack of programs to reset to at the end of a loop *)
(* TODO: Generalize to all tape languages *)
Inductive BFState : Type :=
  bf_state (bf: BF)
           (resets: list BF)
           (ptr: nat)
           (tape: BFTape)
           (input: list Z)
           (output: list Z).

Function state_init (bf: BF) (input: list Z): BFState :=
  bf_state bf [] 0 (NatMap.empty Z) input [].

Function state_output (state: BFState): list Z :=
  match state with bf_state _ _ _ _ _ output => output end.

Function bf_step (state: BFState): option BFState :=
  match state with
  | bf_state bf resets ptr tape input output =>
    match bf with
     | bf_end =>
       match resets with
        | [] => None
        | bf' :: resets' =>
          Some (bf_state bf' resets' ptr tape input output)
        end
     | bf_right bf' =>
       Some (bf_state bf' resets (S ptr) tape input output)
     | bf_left bf' =>
       Some (bf_state bf' resets (pred ptr) tape input output)
     | bf_inc bf' =>
       Some (bf_state bf' resets ptr (tape_inc tape ptr) input output)
     | bf_dec bf' =>
       Some (bf_state bf' resets ptr (tape_dec tape ptr) input output)
     | bf_out bf' =>
       Some (bf_state bf' resets ptr tape input (output ++ [tape_get tape ptr]))
     | bf_in bf' =>
       match input with
        | [] =>
          Some (bf_state bf' resets ptr (tape_set tape ptr 0) input output)
        | x :: input' =>
          Some (bf_state bf' resets ptr (tape_set tape ptr x) input' output)
        end
     | bf_loop inner_bf bf' =>
       if Z.eqb (tape_get tape ptr) Z.zero then
         Some (bf_state bf' resets ptr tape input output)
       else
          Some (bf_state inner_bf (bf :: resets) ptr tape input output)
     end
  end.

(* TODO: Use N as fuel with {measure N.to_nat fuel} *)
Function bf_run (state: BFState) (fuel: nat): option (list Z) :=
  match fuel with
  | 0 => None
  | S f =>
    match bf_step state with
    | None => Some (state_output state)
    | Some state' => bf_run state' f
    end
  end.

Function z_of_ascii (a: ascii): Z :=
  Z.of_nat (nat_of_ascii a).

Function ascii_of_z (z: Z): option ascii :=
  match z with
  | Zpos p => Some (ascii_of_pos p)
  | _ => None
  end.

Function opt_list_len {A: Type} (l: option (list A)): nat :=
  match l with
  | Some l => List.length l
  | None => 0
  end.

Function string_of_zs (out: list Z): string :=
  match out with
  | [] => EmptyString
  | z :: zs' =>
    match ascii_of_z z with
    | None => EmptyString
    | Some a => String a (string_of_zs zs')
    end
  end.

Function zs_of_string (str: string): list Z :=
  match str with
  | EmptyString => []
  | String a str' => z_of_ascii a :: (zs_of_string str')
  end.

(* The important interpreter as far as the spec is concerned *)
Function interpret_bf (prog: string) (zs: list Z) (f: nat): option (list Z) :=
  match parse_bf prog with
  | None => None
  | Some bf => bf_run (state_init bf zs) f
  end.

Function interpret_bf_readable (prog: string) (input: string) (f:nat): string :=
  match interpret_bf prog (zs_of_string input) f with
  | None => EmptyString
  | Some zs => string_of_zs zs
  end.

Example hello_world_bf:
  interpret_bf_readable "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.
                        +++++++..+++.>++.<<+++++++++++++++.>.+++.------.
                        --------.>+. newline in next cell" "" 401 =
  "Hello World!"%string. auto.
