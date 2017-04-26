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
Load bftape.

Print BFTape.

Module BF.

  (* BF Program Type *)
  Inductive BF : Type :=
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

  Lemma bf_helper (bf1 bf1': BF):
    parse_bf_state (chars_of_bf bf1) = Parse.ok bf1' [] ->
    bf1 = bf1'.
  Proof.
  Admitted.

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
  Definition BFState := @BFTape.ExecState BF.
  Definition running := @BFTape.running BF.

  Function bf_step (s: BFState): BFState :=
    match s with
    | BFTape.halted _ => s
    | BFTape.running bf resets ptr tape input output =>
      match bf with
      | bf_end =>
        match resets with
        | [] => BFTape.halted output
        | bf' :: resets' =>
          BFTape.running bf' resets' ptr tape input output
        end
      | bf_right bf' =>
        running bf' resets (S ptr) tape input output
      | bf_left bf' =>
        running bf' resets (pred ptr) tape input output
      | bf_inc bf' =>
        running bf' resets ptr (BFTape.inc tape ptr) input output
      | bf_dec bf' =>
        running bf' resets ptr (BFTape.dec tape ptr) input output
      | bf_out bf' =>
        running bf' resets ptr tape input (output ++ [BFTape.get tape ptr])
      | bf_in bf' =>
        match input with
        | [] =>
          running bf' resets ptr (BFTape.put tape ptr 0) input output
        | x :: input' =>
          running bf' resets ptr (BFTape.put tape ptr x) input' output
        end
      | bf_loop inner_bf bf' =>
        if (BFTape.get tape ptr) =? 0 then
          running bf' resets ptr tape input output
        else
          running inner_bf (bf :: resets) ptr tape input output
      end
    end.

  (* Key function for correctness property *)
  Definition interpret_bf (prog: BF) (input: list nat) (fuel: nat):
    option (list nat) := BFTape.interpret bf_step prog input fuel.

  Function string_of_nats (out: list nat): string :=
    match out with
    | [] => EmptyString
    | n :: ns' => String (ascii_of_nat n) (string_of_nats ns')
    end.

  Function nats_of_string (str: string): list nat :=
    match str with
    | EmptyString => []
    | String a str' => nat_of_ascii a :: (nats_of_string str')
    end.

  Function interpret_bf_readable (prog: string) (input: string) (f: nat):
    string :=
    match parse_bf prog with
    | None => EmptyString
    | Some bf =>
      match interpret_bf  bf (nats_of_string input) f with
      | None => EmptyString
      | Some output => string_of_nats output
      end
    end.

  Example hello_world_bf:
    interpret_bf_readable "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.
                        +++++++..+++.>++.<<+++++++++++++++.>.+++.------.
                        --------.>+. newline in next cell" "" 401 =
    "Hello World!"%string. Proof. auto. Qed.

End BF.
