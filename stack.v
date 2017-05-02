Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Module Stack.
  (* TODO: stack_equiv showing empty and singleton tuples can be reduced *)
  Inductive Stack: Set :=
  | snil
  | snat (n: nat) (s: Stack)
  | stuple (t: Stack) (s: Stack).

  Function stack_prefix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some snil
    | S n' =>
      match s with
      | snil => None
      | snat m s =>
        match stack_prefix n' s with
        | None => None
        | Some s' => Some (snat m s')
        end
      | stuple t s =>
        match stack_prefix n' s with
        | None => None
        | Some s' => Some (stuple t s')
        end
      end
    end.

  Function stack_postfix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some s
    | S n' =>
      match s with
      | snil => None
      | snat _ s'
      | stuple _ s' => stack_postfix n' s'
      end
    end.

  Function stack_append (s1 s2: Stack): Stack :=
    match s1 with
    | snil => s2
    | snat n s => snat n (stack_append s s2)
    | stuple t s => stuple t (stack_append s s2)
    end.

  Function stack_del (n: nat) (s: Stack): option Stack :=
    match (s, n) with
    | (snil, _) => None
    | (snat _ s, 0)
    | (stuple _ s, 0) => Some s
    | (snat m s, S n) =>
      match stack_del n s with
      | None => None
      | Some s' => Some (snat m s')
      end
    | (stuple t s, S n) =>
      match stack_del n s with
      | None => None
      | Some s' => Some (stuple t s')
      end
    end.

  Function stack_get (n: nat) (s: Stack): option Stack :=
    match stack_postfix n s with
    | None | Some snil => None
    | Some (snat m _) => Some (snat m s)
    | Some (stuple t _) => Some (stuple t s)
    end.

  Example stack_prefix_ex:
    forall s, stack_prefix 1 (snat 3 s) = Some (snat 3 snil).
  Proof. intros; auto. Qed.

  Function stack_pack (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 | 1 => Some s
    | _ =>
      match (stack_prefix n s, stack_postfix n s) with
      | (Some t, Some s') => Some (stuple t s')
      | _ => None
      end
    end.

  Example stack_pack_simple:
    stack_pack 2 (snat 0 (snat 1 snil)) =
    Some (stuple (snat 0 (snat 1 snil)) snil).
  Proof. auto. Qed.

  Example stack_pack_nested:
    forall tl,
      stack_pack 3 (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 tl))) =
      Some (stuple (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 snil)))
                   tl).
  Proof. intros; auto. Qed.

  Function stack_unpack (s: Stack): option Stack :=
    match s with
    | snil => None
    | snat _ _ => Some s
    | stuple t s => Some (stack_append t s)
    end.

  Function stack_weight (s: Stack): nat :=
    match s with
    | snil => 0
    | snat _ s' => S (stack_weight s')
    | stuple t s' => S (stack_weight t + stack_weight s')
    end.

  Function stack_inc (s: Stack): option Stack :=
    match s with
    | snat m s' => Some (snat (S m) s')
    | _ => None
    end.

  Function stack_dec (s: Stack): option Stack :=
    match s with
    | snat m s' => Some (snat (pred m) s')
    | _ => None
    end.

  Function stack_out (s: Stack): (option nat) :=
    match s with
    | snat m s' => Some m
    | _ => None
    end.

End Stack.