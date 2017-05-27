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

Load jsml.
Load bftape.

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

  Fixpoint bf_append bf1 bf2 :=
    match bf1 with
    | bf_end => bf2
    | bf_right bf' => bf_right (bf_append bf' bf2)
    | bf_left bf' => bf_left (bf_append bf' bf2)
    | bf_inc bf' => bf_inc (bf_append bf' bf2)
    | bf_dec bf' => bf_dec (bf_append bf' bf2)
    | bf_out bf' => bf_out (bf_append bf' bf2)
    | bf_in bf' => bf_in (bf_append bf' bf2)
    | bf_loop inner bf' => bf_loop inner (bf_append bf' bf2)
    end.

  Notation "a & f" := (bf_append a f) (at level 50, left associativity).

  Fixpoint repeat (n: nat) (bf: BF): BF :=
    match n with
    | 0 => bf_end
    | S m => bf & (repeat m bf)
    end.

  Section BFPrinting.

    Fixpoint chars_of_bf (bf: BF): list ascii :=
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

    Definition print_bf (bf: BF): string :=
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

    Fixpoint parse_bf_state (l: list ascii): ParseState :=
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

    Definition parse_bf (str: string): option BF :=
      match parse_bf_state (chars_of_string str) with
      | Parse.error => None
      | Parse.ok _ (_ :: _) => None
      | Parse.ok bf [] => Some bf
      end.

    Definition parse_bf_def (str: string): BF :=
      match parse_bf str with
      | Some bf => bf
      | None => bf_end
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

  Inductive BFState : Type :=
  | running (ast: BF)
            (resets: list BF)
            (ptr: nat)
            (tape: BFTape.Tape)
            (input: list nat)
            (output: list nat)
  | halted (output: list nat).

  Fixpoint bf_step (s: BFState): BFState :=
    match s with
    | halted _ => s
    | running bf resets ptr tape input output =>
      match bf with
      | bf_end =>
        match resets with
        | [] => halted output
        | bf' :: resets' =>
          running bf' resets' ptr tape input output
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

  Definition exec_init (prog: BF) (input: list nat): BFState :=
    running prog [] 0 BFTape.empty input [].

  Definition interpret_bf (prog: BF) (input: list nat) (fuel: nat):
    option (list nat) :=
    match Utils.run bf_step (exec_init prog input) fuel with
    | running _ _ _ _ _ _ => None
    | halted output => Some output
    end.

  Fixpoint string_of_nats (out: list nat): string :=
    match out with
    | [] => EmptyString
    | n :: ns' => String (ascii_of_nat n) (string_of_nats ns')
    end.

  Fixpoint nats_of_string (str: string): list nat :=
    match str with
    | EmptyString => []
    | String a str' => nat_of_ascii a :: (nats_of_string str')
    end.

  Fixpoint interpret_bf_readable (prog: string) (input: string) (f: nat):
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

  Section BFofJSM.

    (* value logical cells on both sides with separators at
    `nest_level'. Values of separator cells set to 0. *)
    Fixpoint list_of_stack (s: Stack.Stack) (nest_level: nat): list nat :=
      match s with
      | Stack.snil => []
      | Stack.snat n Stack.snil => [(S nest_level); n]
      | Stack.stuple inner Stack.snil => list_of_stack inner (S nest_level)
      | Stack.snat n s' =>
        (list_of_stack s' nest_level)
          ++ (nest_level :: 0 :: [S nest_level; n])
      | Stack.stuple inner s' =>
        (list_of_stack s' nest_level)
          ++ (nest_level :: 0 :: (list_of_stack inner (S nest_level)))
      end.

    Definition tape_of_stack (s: Stack.Stack): BFTape.Tape :=
      BFTape.tape_of_list ([0;0] ++ (list_of_stack s 0) ++ [0;0]).

    Definition debug_bf (prog: BF) (tape: BFTape.Tape) (ptr size: nat)
               (input: list nat) (fuel: nat):
      (string * list string * list (nat * nat)) :=
      match Utils.run bf_step (running prog [] ptr tape input []) fuel with
      | halted _ => (""%string, [], [])
      | running bf rst ptr tape _ _ =>
        let l := combine (BFTape.list_of_tape tape size) (seq 0 size) in
        let mapper (x: nat * nat) :=
            let (v, i) := x in
            (v, if i =? ptr then 1 else 0) in
        (print_bf bf, map print_bf rst, map mapper l)
      end.

    Definition push (n: nat): BF :=
      (parse_bf_def ">>[-]+>[-]") & (repeat n (parse_bf_def "+")) &
      (parse_bf_def ">[-]>[-]<").

    Definition del (n: nat): BF := bf_end.

    Definition get (n: nat): BF :=
      (* Move to start *)
      (repeat (S n) (parse_bf_def "<<[<<]")) & (parse_bf_def ">>") &
      (* Move tag to end *)
      (bf_loop ((repeat (S n) (parse_bf_def ">>[>>]")) &
                (parse_bf_def ">>+<<") &
                (repeat (S n) (parse_bf_def "<<[<<]")) &
                (parse_bf_def ">>-")) bf_end) &
      (* Move val to end *)
      (bf_right (bf_loop ((parse_bf_def ">[>>]") &
                          (repeat n (parse_bf_def ">>[>>]")) &
                          (parse_bf_def ">>>+<<<") &
                          (repeat (S n) (parse_bf_def "<<[<<]")) &
                          (parse_bf_def ">-")) bf_end)) &
      (* Move next tag and value to end *)
      (bf_right
         (bf_loop (
              (* Mark new end *)
              (repeat (n+2) (parse_bf_def ">>[>>]")) & (bf_inc bf_end) &
              (* Move to start *)
              (repeat (n+2) (parse_bf_def "<<[<<]")) & (parse_bf_def ">>") &
              (* Move tag to end *)
              (bf_loop ((repeat (n+2) (parse_bf_def ">>[>>]")) &
                        (parse_bf_def "<<+") &
                        (repeat (n+2) (parse_bf_def "<<[<<]")) &
                        (parse_bf_def ">>-")) bf_end) &
              (* Move val to end *)
              (bf_right (bf_loop ((parse_bf_def ">[>>]") &
                                  (repeat (S n) (parse_bf_def ">>[>>]")) &
                                  (parse_bf_def "<+<") &
                                  (repeat (n+2) (parse_bf_def "<<[<<]")) &
                                  (bf_right (bf_dec (bf_end)))) bf_end)) &
              (* Mark previous tag and value *)
              (parse_bf_def "<<<+>+>") &
              (* Unmark end tag *)
              (repeat (n+2) (parse_bf_def ">>[>>]")) & (parse_bf_def "<<-") &
              (repeat (n+2) (parse_bf_def "<<[<<]")) &
              (* Move to new start *)
              (parse_bf_def ">>")) bf_end)) &
      (* Mark last tag and value *)
      (parse_bf_def "<+<+").
    (* TODO: Deal with hole *)

    Definition pack (n: nat): BF :=
      if n <=? 1 then bf_end else
        (repeat (n-1) (parse_bf_def "<<<<[+>>+<<<<<<]+>>+<<")) &
        (parse_bf_def "<<<<[+>>+<<<<<<]>>+[>>]").

    Definition unpack: BF := parse_bf_def "<<[<<]>>[->>]".

    Definition cond_get (n k: nat) :=
      bf_end.

    Definition inc: BF := parse_bf_def "<+>".

    Definition dec: BF := parse_bf_def "<->".

    Definition read: BF := parse_bf_def ">>[-]+>,>[-]>[-]<".

    Definition out: BF := parse_bf_def "<.>".

  (* Compiles a single JSMProgram to BFN. *)
  Function bf_of_jsmp (main: JSML.JSMProgram) :=
    match main with
    | [] => bf_end
    | JSML.push n :: jsmp => push n & bf_of_jsmp jsmp
    | JSML.del n :: jsmp => del n & bf_of_jsmp jsmp
    | JSML.get n :: jsmp => get n & bf_of_jsmp jsmp
    | JSML.pack n :: jsmp => pack n & bf_of_jsmp jsmp
    | JSML.unpack :: jsmp => unpack & bf_of_jsmp jsmp
    | JSML.cond_get n k :: jsmp => cond_get n k & bf_of_jsmp jsmp
    | JSML.inc :: jsmp => inc & bf_of_jsmp jsmp
    | JSML.dec :: jsmp => dec & bf_of_jsmp jsmp
    | JSML.read :: jsmp => read & bf_of_jsmp jsmp
    | JSML.out :: jsmp => out & bf_of_jsmp jsmp
    end.

  End BFofJSM.

End BF.
