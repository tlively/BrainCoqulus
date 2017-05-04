Require Import Arith.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Module Stack.
  (* TODO: equiv showing empty and singleton tuples can be reduced *)
  Inductive Stack: Set :=
  | snil
  | snat (n: nat) (s: Stack)
  | stuple (t: Stack) (s: Stack).

  Function prefix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some snil
    | S n' =>
      match s with
      | snil => None
      | snat m s =>
        match prefix n' s with
        | None => None
        | Some s' => Some (snat m s')
        end
      | stuple t s =>
        match prefix n' s with
        | None => None
        | Some s' => Some (stuple t s')
        end
      end
    end.

  Function postfix (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 => Some s
    | S n' =>
      match s with
      | snil => None
      | snat _ s'
      | stuple _ s' => postfix n' s'
      end
    end.

  Function append (s1 s2: Stack): Stack :=
    match s1 with
    | snil => s2
    | snat n s => snat n (append s s2)
    | stuple t s => stuple t (append s s2)
    end.

  Function del (n: nat) (s: Stack): option Stack :=
    match (s, n) with
    | (snil, _) => None
    | (snat _ s, 0)
    | (stuple _ s, 0) => Some s
    | (snat m s, S n) =>
      match del n s with
      | None => None
      | Some s' => Some (snat m s')
      end
    | (stuple t s, S n) =>
      match del n s with
      | None => None
      | Some s' => Some (stuple t s')
      end
    end.

  Function get (n: nat) (s: Stack): option Stack :=
    match postfix n s with
    | None | Some snil => None
    | Some (snat m _) => Some (snat m s)
    | Some (stuple t _) => Some (stuple t s)
    end.

  Example prefix_ex:
    forall s, prefix 1 (snat 3 s) = Some (snat 3 snil).
  Proof. intros; auto. Qed.

  Function pack (n: nat) (s: Stack): option Stack :=
    match n with
    | 0 | 1 => Some s
    | _ =>
      match (prefix n s, postfix n s) with
      | (Some t, Some s') => Some (stuple t s')
      | _ => None
      end
    end.

  Example pack_simple:
    pack 2 (snat 0 (snat 1 snil)) =
    Some (stuple (snat 0 (snat 1 snil)) snil).
  Proof. auto. Qed.

  Example pack_nested:
    forall tl,
      pack 3 (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 tl))) =
      Some (stuple (snat 1
                         (stuple (snat 2 (snat 3 snil))
                                 (snat 4 snil)))
                   tl).
  Proof. intros; auto. Qed.

  Function unpack (s: Stack): option Stack :=
    match s with
    | snil => None
    | snat _ _ => Some s
    | stuple t s => Some (append t s)
    end.

  Function cond_get (stack : Stack) (n : nat) (k : nat) :=
    match stack with
    | Stack.snat 0 _ => Stack.get n stack
    | Stack.snat _ _ => Stack.get k stack
    | _ => None
    end.

  Function weight (s: Stack): nat :=
    match s with
    | snil => 0
    | snat _ s' => S (weight s')
    | stuple t s' => S (weight t + weight s')
    end.

  Function inc (s: Stack): option Stack :=
    match s with
    | snat m s' => Some (snat (S m) s')
    | _ => None
    end.

  Function dec (s: Stack): option Stack :=
    match s with
    | snat m s' => Some (snat (pred m) s')
    | _ => None
    end.

  Function out (s: Stack): (option nat) :=
    match s with
    | snat m s' => Some m
    | _ => None
    end.
End Stack.
