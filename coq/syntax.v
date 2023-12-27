(*** Abstract Syntax *)
From Coq Require Import List.
Import ListNotations.


(*** Lists *)
Print list.

Fixpoint concat {X} (A B : list X) : list X :=
  match A with
  | nil => B
  | cons x A => cons x (concat A B)
  end.

Definition elim_list {X} (p: list X -> Type)
  : p nil ->
    (forall x A, p A -> p (cons x A)) -> 
    forall A, p A
  := fun f1 f2 => fix f A :=
    match A with
    | nil => f1
    | cons x A => f2 x A (f A)
    end.

Fact concat_nil X (A : list X) :
  concat A nil = A.
Proof.
  revert A.
  refine (elim_list _ _ _).
  - cbn. reflexivity.
  - intros x A  IH.
    cbn. f_equal. exact IH.
Qed.

Fact concat_nil' X (A : list X) :
  concat A nil = A.
Proof.
  induction A as [|x A IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact associativity X (A B C : list X) :
  concat (concat A B) C = concat A (concat B C).
Proof.
  revert A.
  refine (elim_list _ _ _).
  - cbn. reflexivity.
  - intros x A IH.
    cbn. f_equal. exact IH.
Qed.

Fact associativity' X (A B C : list X) :
  concat (concat A B) C = concat A (concat B C).
Proof.
  induction A as [|x A IH]; cbn. reflexivity.
  f_equal. exact IH.
Qed.

(*** Expressions and Codes *)

(* First time we use Coq's BNF format for an inductive type *)
Inductive exp :=
  con (x: nat)
| add (e: exp) (e: exp)
| sub (e: exp) (e: exp).

(* Implicit Types (x: nat) (e: exp). *)

Fixpoint eval e : nat :=
  match e with
  | con x => x
  | add e1 e2 => eval e1 + eval e2
  | sub e1 e2 => eval e1 - eval e2
  end.

Compute eval (sub (add (con 3) (con 5)) (con 2)).

(* Implicit Types (A C: list nat). *)

Fixpoint run C A : list nat :=
  match C, A with
    nil, A => A
  | 0::C', x1::x2::A' => run C' (x1+x2::A')
  | 1::C', x1::x2::A' => run C' (x1-x2::A')
  | S(S x)::C', A => run C' (x::A)
  | _, _ => nil
  end.

Compute run [5;7;1] [].

(*** Eliminator for Expressions *)

Check exp_rect.

Definition elim_exp (p: exp -> Type) 
  : (forall x, p (con x)) ->
    (forall e1 e2, p e1 -> p e2 -> p (add e1 e2)) ->
    (forall e1 e2, p e1 -> p e2 -> p (sub e1 e2)) ->
    forall e, p e
  := fun f1 f2 f3 => fix f e :=
    match e with
    | con x => f1 x
    | add e1 e2 => f2 e1 e2 (f e1) (f e2)
    | sub e1 e2 => f3 e1 e2 (f e1) (f e2)
    end.

(*** Compiler *)

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
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
  - rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
Qed.

Corollary correctness' e :
  run (com e) nil = [eval e].
Proof.
  rewrite <-(app_nil_r (com e)).
  rewrite correctness.
  reflexivity.
Qed.

(*** Decompiler *)

(* Implicit Type L: list exp. *)

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



