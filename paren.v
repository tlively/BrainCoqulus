Require Import OrderedType OrderedTypeEx.
Import ListNotations.

Inductive Paren :=
| paren_end
| paren_nop (p: Paren)
| paren (inner p: Paren).

Function paren_append (p1 p2: Paren) :=
  match p1 with
  | paren_end => p2
  | paren_nop p' => paren_nop (paren_append p' p2)
  | paren inner p' => paren inner (paren_append p' p2)
  end.

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

Definition parse_init := ok paren_end [].

Function parse_paren_state (init_state: ParenParseState)
         (ps: list ParenNode): ParenParseState :=
  match ps with
  | [] => init_state
  | hd :: tl =>
    match parse_paren_state init_state tl with
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
  match parse_paren_state parse_init ps with
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

Lemma paren_parse_app (state: ParenParseState) (str1 str2: list ParenNode):
  parse_paren_state state (str1 ++ str2) =
  parse_paren_state (parse_paren_state state str2) str1.
Proof.
  revert state str2.
  induction str1; intros; auto.
  rewrite <- app_comm_cons.
  rewrite parse_paren_state_equation.
  symmetry.
  rewrite parse_paren_state_equation.
  now rewrite <- IHstr1.
Qed.

Lemma paren_print_parse_app (p1 p2: Paren):
  parse_paren_state parse_init (print_paren p2

(* TODO: Prove this *)
Lemma paren_print_parse_parens (p1 p2: Paren):
    parse_paren_state parse_init (print_paren p1) = ok p1 [] ->
    parse_paren_state parse_init (print_paren p2) = ok p2 [] ->
    parse_paren_state parse_init (pnode_open :: (print_paren p1) ++ [pnode_close]
                                  ++ (print_paren p2))
    = ok (paren p1 p2) [].
Proof.
Admitted.

Lemma paren_print_parse_state_inverse (p: Paren):
  parse_paren_state parse_init (print_paren p) = ok p [].
Proof.
  induction p; unfold parse_init in *;
    rewrite print_paren_equation, parse_paren_state_equation;
    [| rewrite IHp | apply (paren_print_parse_parens)]; auto.
Qed.

Theorem paren_print_parse_inverse (p: Paren):
  parse_paren (print_paren p) = Some p.
Proof.
  unfold parse_paren; now rewrite paren_print_parse_state_inverse.
Qed.
