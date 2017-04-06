type lam_tree =
  | Lam_end
  | Lam_lam of lam_tree
  | Lam_dot of  lam_tree
  | Lam_out of lam_tree
  | Lam_wsp of lam_tree
  | Lam_id of string * lam_tree
  | Lam_paren of lam_tree * lam_tree

type parse_state =
  | Ok of lam_tree * (lam_tree list)
  | Error


let rec parse_lambdatree_state (l: char list): parse_state =
    match l with
    | [] -> Ok (Lam_end, [])
    | hd :: tl ->
      (match parse_lambdatree_state tl with
       | Error -> Error
       | Ok (cur, stack) ->
          (match hd with
           | ' ' | '\t' | '\n' ->
              (match cur with
               | Lam_wsp _ -> Ok (cur, stack)
               | _ -> Ok ((Lam_wsp cur), stack))
           | '\\' -> Ok ((Lam_lam cur), stack)
           | '.' -> Ok ((Lam_dot cur), stack)
           | '^' -> Ok ((Lam_out cur), stack)
           | ')' -> Ok ((Lam_end), (cur :: stack))
           | '(' ->
              (match stack with
               | [] -> Error
               | next :: stack' -> Ok ((Lam_paren cur next), stack'))
           | _ ->
              (match cur with
               | Lam_id str next -> Ok ((Lam_id (String hd str) next), stack)
               | _ -> Ok ((Lam_id (String hd EmptyString) cur), stack))))

let rec lambda_strip_wsp (t: Lam_tree): Lam_tree =
    match t with
    | Lam_end -> Lam_end
    | Lam_wsp t' -> lambda_strip_wsp t'
    | Lam_lam t' -> Lam_lam (lambda_strip_wsp t')
    | Lam_dot t' -> Lam_dot (lambda_strip_wsp t')
    | Lam_out t' -> Lam_out (lambda_strip_wsp t')
    | Lam_id s t' -> Lam_id s (lambda_strip_wsp t')
    | Lam_paren inner t' ->
      Lam_paren (lambda_strip_wsp inner) (lambda_strip_wsp t')
    end.

  Local Inductive NamedLambda : Set =
  | nl_var (s: string)
  | nl_lam (s: string) (e: NamedLambda)
  | nl_out (e: NamedLambda)
  | nl_app (e1: NamedLambda) (e2: NamedLambda).

  Function app_of_lambda_list (ls: list NamedLambda) {measure List.length ls}:
    option NamedLambda =
    match ls with
    | [] -> None
    | e :: [] -> Some e
    | e1 :: e2 :: tl -> app_of_lambda_list ((nl_app e1 e2) :: tl)
    end.
  intuition.
  Defined.

  Function named_lambda_of_tree (acc: list NamedLambda) (t: lam_tree):
    option NamedLambda =
    match t with
    | lam_end -> app_of_lambda_list (rev acc)
    | lam_wsp _ -> None
    | lam_lam (lam_id s (lam_dot t')) ->
      match named_lambda_of_tree [] t' with
      | None -> None
      | Some e -> Some (nl_lam s e)
      end
    | lam_lam _ | lam_dot _ -> None
    | lam_out t' ->
      match named_lambda_of_tree [] t' with
      | None -> None
      | Some e -> Some (nl_out e)
      end
    | lam_id s t' -> named_lambda_of_tree (nl_var s :: acc) t'
    | lam_paren inner t' ->
      match named_lambda_of_tree [] inner with
      | None -> None
      | Some e -> named_lambda_of_tree (e :: acc) t'
      end
    end.

  Function parse_named_lambda (s: string): option NamedLambda =
    match parse_lambdatree_state (Parse.chars_of_string s) with
    | Error -> None
    | Ok cur stack ->
      match stack with
      | _ :: _ -> None
      | [] -> named_lambda_of_tree [] (lambda_strip_wsp cur)
      end
    end.

  Example named_id: parse_named_lambda "\x.x" = Some (nl_lam "x" (nl_var "x")).
  auto. Qed.

  Example named_true:
    parse_named_lambda "\x.\y.x" = Some (nl_lam "x" (nl_lam "y" (nl_var "x"))).
  auto. Qed.

  Example named_false:
    parse_named_lambda " \ x . \ y  .  (y  ) " =
    Some (nl_lam "x" (nl_lam "y" (nl_var "y"))).
  auto. Qed.

  Example named_out:
    parse_named_lambda "\x.^x" = Some (nl_lam "x" (nl_out (nl_var "x"))).
  auto. Qed.

  Example named_Y:
    parse_named_lambda "\f.(\x.f (x x)) (\x.f (x x))" =
    let fn_app = nl_app (nl_var "f") (nl_app (nl_var "x") (nl_var "x")) in
    Some (nl_lam "f" (nl_app (nl_lam "x" fn_app) (nl_lam "x" fn_app))).
  auto. Qed.

  Example named_parens:
    parse_named_lambda "(((\x.(((x))))))" = Some (nl_lam "x" (nl_var "x")).
  auto. Qed.

  Example named_apps:
    parse_named_lambda "x y z w" =
    Some (nl_app (
              nl_app (
                  nl_app (nl_var "x") (nl_var "y")
                ) (nl_var "z")
            ) (nl_var "w")).
  auto. Qed.

  Example named_bad_lambdas: parse_named_lambda "\\x.x" = None.
  auto. Qed.

  Example named_bad_dots: parse_named_lambda "\x..x" = None.
  auto. Qed.

  Example named_bad_parens: parse_named_lambda "\x.((x)" = None.
  auto. Qed.

  Example named_bad_parens2: parse_named_lambda "\x.x ()" = None.
  auto. Qed.

  Function index_of (x: string) (l: list string): option nat =
    match l with
    | [] -> None
    | hd :: tl ->
      if string_dec hd x then Some 0
      else match index_of x tl with
           | Some i -> Some (S i)
           | None -> None
           end
    end.

  Function lambda_strip_names (l: NamedLambda) (xs: list string):
    option Lambda =
    match l with
    | nl_var x ->
      match index_of x xs with
      | Some n -> Some (l_var n)
      | None -> None
      end
    | nl_lam x e ->
      match lambda_strip_names e (x :: xs) with
      | Some e' -> Some (l_lam e')
      | None -> None
      end
    | nl_out e ->
      match lambda_strip_names e xs with
      | Some e' -> Some (l_out e')
      | None -> None
      end
    | nl_app e1 e2 ->
      match (lambda_strip_names e1 xs, lambda_strip_names e2 xs) with
      | (Some e1', Some e2') -> Some (l_app e1' e2')
      | _ -> None
      end
    end.

  Function parse_lambda (s: string): option Lambda =
    match parse_named_lambda s with
    | None -> None
    | Some nl -> lambda_strip_names nl []
    end.

  Example lambda_id: parse_lambda "\x.x" = Some (l_lam (l_var 0)).
  auto. Qed.

  Example lambda_true:
    parse_lambda "\x.\y.x" = Some (l_lam (l_lam (l_var 1))).
  auto. Qed.

  Example lambda_false:
    parse_lambda " \ x . \ y  .  (y  ) " =  Some (l_lam (l_lam (l_var 0))).
  auto. Qed.

  Example lambda_out:
    parse_lambda "\x.^x" = Some (l_lam (l_out (l_var 0))).
  auto. Qed.

  Example lambda_Y:
    parse_lambda "\f.(\x.f (x x)) (\x.f (x x))" =
    let fn_app = l_app (l_var 1) (l_app (l_var 0) (l_var 0)) in
    Some (l_lam (l_app (l_lam fn_app) (l_lam fn_app))).
  auto. Qed.

  Example lambda_parens:
    parse_lambda "(((\x.(((x))))))" = Some (l_lam (l_var 0)).
  auto. Qed.

  Example lambda_apps:
    parse_lambda "x y z w" = None.
  auto. Qed.
