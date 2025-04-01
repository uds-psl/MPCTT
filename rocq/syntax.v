(*** MPCTT, Chapter Abstract Syntax *)

From Stdlib Require Import List.
Import ListNotations.

(*** Expressions and Codes *)

(* First time we use Rocq's BNF format for an inductive type *)
Inductive exp :=
  con (x: nat)
| add (e: exp) (e: exp)
| sub (e: exp) (e: exp).

Fixpoint eval e : nat :=
  match e with
  | con x => x
  | add e1 e2 => eval e1 + eval e2
  | sub e1 e2 => eval e1 - eval e2
  end.

Compute eval (sub (add (con 3) (con 5)) (con 2)).

Fixpoint run C A : list nat :=
  match C, A with
  | nil, A => A
  | 0::C', x1::x2::A' => run C' (x1+x2::A')
  | 1::C', x1::x2::A' => run C' (x1-x2::A')
  | S(S x)::C', A => run C' (x::A)
  | _, _ => nil
  end.

Compute run [4+2;7+2;1] [].

(* Rocq compiles all matches into basic matches *)
Set Printing All.
Print run.
Unset Printing All.

(*** Compiler *)

Fixpoint com e : list nat :=
  match e with
  | con x => [S(S x)]
  | add e1 e2 => com e2 ++ com e1 ++ [0]
  | sub e1 e2 => com e2 ++ com e1 ++ [1]
  end.

Compute com (sub (add (con 3) (con 5)) (con 2)).
Compute run (com (sub (add (con 3) (con 5)) (con 2))).

Theorem correctness e C A :
  run (com e ++ C) A = run C (eval e :: A).
Proof.
  revert C A.
  induction e as [x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2];
    intros C A.
  - cbn. reflexivity.
  - cbn. rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
  - cbn. rewrite <-app_assoc, IH2. rewrite <-app_assoc, IH1. reflexivity.
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
  | nil, L => L
  | 0::C', e1::e2::L' => dcom C' (add e1 e2 :: L')
  | 1::C', e1::e2::L' => dcom C' (sub e1 e2 :: L')
  | S(S x)::C', L => dcom C' (con x::L)
  | _, _ => nil
  end.

Compute dcom (com (add (con 3) (sub (con 7) (con 5)))) [].
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

(*** List Basics *)

Module List.
  Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

  Arguments nil {X}.
  Arguments cons {X}.

  
  Goal forall X (x:X) A,
      cons x A <> nil.
  Proof.
    congruence.
  Qed.

  Goal forall X (x:X) A,
      cons x A <> nil.
  Proof.
    intros * H.
    change match cons x A with nil => True | cons _ _ => False end.
    rewrite H. easy.
  Qed.
 
  Goal forall X (x:X) A x' A',
      cons x A = cons x' A' -> x = x' /\ A = A'.
  Proof.
    intros * H.
    change match cons x A with nil => True | cons x A => x = x' /\ A = A' end.
    rewrite H. easy.
  Qed.
    
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
    pattern A. revert A. apply elim_list.
    - reflexivity.
    - intros x A IH.
      cbn. congruence.
  Qed.

  Fact concat_asso X (A B C : list X) :
    concat (concat A B) C = concat A (concat B C).
  Proof.
    pattern A. revert A. apply elim_list.
    - reflexivity.
    - intros x A IH.
      cbn. congruence.
  Qed.

  Fixpoint rev {X} (A : list X) : list X :=
    match A with
    | nil => nil
    | cons x A => concat (rev A) (cons x nil)
    end.

  Goal forall X (A B: list X),
      rev (concat A B) = concat (rev B) (rev A).
  Proof.
    intros *.
    induction A as [|x A IH].
    - cbn. rewrite concat_nil. reflexivity.
    - cbn. rewrite IH. apply concat_asso.
  Qed.
End List.

(*** Expression Basics *)

From Stdlib Require Import Lia.

Module Exp.
  Inductive exp :=
  | con : nat -> exp
  | add : exp -> exp -> exp
  | sub : exp -> exp -> exp.

  Goal forall e1 e2 e1' e2',
      add e1 e2 <> sub e1' e2'.
  Proof.
    congruence.
  Qed.

  Goal forall e1 e2 e1' e2',
      add e1 e2 <> sub e1' e2'.
  Proof.
    intros * H.
    change match add e1 e2 with add _ _ => False | _ => True end.
    rewrite H. easy.
  Qed.
  
  Goal forall e1 e2 e1' e2',
      add e1 e2 = add e1' e2' -> e1 = e1' /\ e2 = e2'.
  Proof.
    intros * H. split; congruence.
  Qed.
  
  Goal forall e1 e2 e1' e2',
      add e1 e2 = add e1' e2' -> e1 = e1' /\ e2 = e2'.
  Proof.
    intros * H.
    change match add e1 e2 with add e1 e2 => e1 = e1' /\ e2 = e2' | _ => True end.
    rewrite H. easy.
  Qed.
  
  Fixpoint eval e : nat :=
    match e with
    | con x => x
    | add e1 e2 => eval e1 + eval e2
    | sub e1 e2 => eval e1 - eval e2
  end.

  Fixpoint swap e : exp :=
    match e with
    | con x => con x
    | add e1 e2 => add (swap e2) (swap e1)
    | sub e1 e2 => sub (swap e1) (swap e2)
    end.

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

  Goal forall e, eval e = eval (swap e).
  Proof.
    apply elim_exp.
    - intros x. reflexivity.
    - intros e1 e2 IH1 IH2.
      cbn. lia.
    - intros e1 e2 IH1 IH2.
      cbn. congruence.
  Qed.
End Exp.
      


