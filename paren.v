Require Import OrderedType OrderedTypeEx.
Import ListNotations.

Inductive Paren :=
| paren_end
| paren_nop (p: Paren)
| paren (inner p: Paren).

Inductive ParenNode :=
| pnode_open
| pnode_nop
| pnode_close.

Function print_paren (p: Paren): list ParenNode :=
  match p with
  | paren_end => []
  | paren_nop p' => pnode_nop :: (print_paren p')
  | paren inner p' => [pnode_open] ++ (print_paren inner) ++ [pnode_close]
                                   ++ (print_paren p')
  end.

Inductive ParenParseState :=
| ok (next: Paren) (stack: list Paren)
| error.

Function parse_paren_state (ps: list ParenNode): ParenParseState :=
  match ps with
  | [] => ok paren_end []
  | hd :: tl =>
    match parse_paren_state tl with
    | error => error
    | ok cur stack =>
      match hd with
      | pnode_nop => ok (paren_nop cur) stack
      | pnode_close => ok paren_end (cur :: stack)
      | pnode_open =>
        match stack with
        | [] => error
        | next :: stack' => ok (paren cur next) stack'
        end
      end
    end
  end.

Function parse_paren (ps: list ParenNode): option Paren :=
  match parse_paren_state ps with
  | error => None
  | ok p (_ :: _) => None
  | ok p [] => Some p
  end.

Example paren_print_parse_end:
  parse_paren (print_paren paren_end) = Some paren_end.
auto. Qed.

Example paren_print_parse_nop:
  parse_paren (print_paren (paren_nop paren_end)) = Some (paren_nop paren_end).
auto. Qed.

Example paren_print_parse_nesting:
  let prog := (paren
                 (paren (paren_nop paren_end) paren_end)
                 (paren paren_end paren_end)) in
  parse_paren (print_paren prog) = Some prog.
auto. Qed.

(* TODO: Prove this *)
Lemma paren_print_parse_parens (p1 p2: Paren):
    parse_paren_state (print_paren p1) = ok p1 [] ->
    parse_paren_state (print_paren p2) = ok p2 [] ->
    parse_paren_state (pnode_open :: (print_paren p1) ++ [pnode_close]
                                  ++ (print_paren p2))
    = ok (paren p1 p2) [].
Proof.
Admitted.

Lemma paren_print_parse_state_inverse (p: Paren):
  parse_paren_state (print_paren p) = ok p [].
Proof.
  induction p; rewrite print_paren_equation, parse_paren_state_equation;
    [| rewrite IHp | apply (paren_print_parse_parens)]; auto.
Qed.

Theorem paren_print_parse_inverse (p: Paren):
  parse_paren (print_paren p) = Some p.
Proof.
  unfold parse_paren; now rewrite paren_print_parse_state_inverse.
Qed.
