From Coq Require Import List.
Import ListNotations.

Inductive exp :=
  con (x: nat)
| add (e: exp) (e: exp)
| sub (e: exp) (e: exp).

Implicit Types (x: nat) (e: exp).

Fixpoint eval e : nat :=
  match e with
  | con x => x
  | add e1 e2 => eval e1 + eval e2
  | sub e1 e2 => eval e1 - eval e2
  end.

Compute eval (sub (add (con 3) (con 5)) (con 2)).

Implicit Types (A C: list nat).

Fixpoint run C A : list nat :=
  match C, A with
    nil, A => A
  | 0::C', x1::x2::A' => run C' (x1+x2::A')
  | 1::C', x1::x2::A' => run C' (x1-x2::A')
  | S(S x)::C', A => run C' (x::A)
  | _, _ => nil
  end.

Compute run [5;7;1] [].

Fixpoint com e : list nat :=
  match e with
    con x => [S(S x)]
  | add e1 e2 => com e2 ++ com e1 ++ [0]
  | sub e1 e2 => com e2 ++ com e1 ++ [1]
  end.

Compute com (sub (add (con 3) (con 5)) (con 2)).
Compute run (com (sub (add (con 3) (con 5)) (con 2))).

Theorem correctness e C A :
  run (com e ++ C) A = run C (eval e :: A).
Proof.
  revert C A.
  induction e as [x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 ];
    intros C A; cbn.
  - reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1.reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
Qed.

Corollary correctness' e :
  run (com e) nil = [eval e].
Proof.
  rewrite <-(app_nil_r (com e)).
  rewrite correctness.
  reflexivity.
Qed.

Implicit Type L: list exp.

Fixpoint dcom C L : list exp :=
  match C, L with
    nil, L => L
  | 0::C', e1::e2::L' => dcom C' (add e1 e2 :: L')
  | 1::C', e1::e2::L' => dcom C' (sub e1 e2 :: L')
  | S(S x)::C', L => dcom C' (con x::L)
  | _, _ => nil
  end.

Compute dcom [0;3;0;5;2] [].

Theorem dcom_correct e C L :
  dcom (com e ++ C) L = dcom C (e::L).
Proof.
  revert C L.
  induction e as [x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 ];
    intros C L; cbn.
  - reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
Qed.

Corollary dcom_correct' e :
  dcom (com e) nil = [e].
Proof.
  rewrite <-(app_nil_r (com e)).
  rewrite dcom_correct.
  reflexivity.
Qed.

