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
  | 0::x::C', A => run C' (x::A)
  | 1::C', x1::x2::A' => run C' (x1+x2::A')
  | 2::C', x1::x2::A' => run C' (x1-x2::A')
  | _, _ => nil
  end.

Compute run [0;3;0;5;2] [].

Fixpoint com e : list nat :=
  match e with
    con x => [0;x]
  | add e1 e2 => com e2 ++ com e1 ++ [1]
  | sub e1 e2 => com e2 ++ com e1 ++ [2]
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
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. cbn. reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. cbn. reflexivity.
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
  | 0::x::C', L => dcom C' (con x::L)
  | 1::C', e1::e2::L' => dcom C' (add e1 e2 :: L')
  | 2::C', e1::e2::L' => dcom C' (sub e1 e2 :: L')
  | _, _ => nil
  end.

Compute dcom [0;3;0;5;2] [].

Theorem dcom_correct e C L :
  dcom (com e ++ C) L = dcom C (e::L).
Proof.
  revert C L.
  induction e as [x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 ];
    intros C L; cbn.
  - trivial.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. trivial.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. trivial.
Qed.

Corollary dcom_correct' e :
  dcom (com e) nil = [e].
Proof.
  rewrite <-(app_nil_r (com e)).
  rewrite dcom_correct.
  trivial.
Qed.

