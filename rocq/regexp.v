(*** Regular Expressions *)
From Coq Require Import Arith Lia List.
Import ListNotations.
Definition dec X := sum X (X -> False).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Inductive exp: Type :=
| Sym (x: nat)
| Nul
| One
| Add (s t: exp)
| Mul (s t: exp)
| Star (s: exp).

Implicit Types s t : exp.
Implicit Types A B : list nat.

Reserved Notation "A |- s" (at level 70).
Inductive sat : list nat -> exp -> Type :=
| SSym x : [x] |- Sym x
| SOne : [] |- One
| SAddL A s t : A |- s -> A |- Add s t
| SAddR A s t : A |- t -> A |- Add s t
| SMul A B s t : A |- s -> B |- t -> A ++ B |- Mul s t
| SStar1 s : [] |- Star s
| SStar2 A B s : A |- s -> B |- Star s -> A ++ B |- Star s
where "A |- s" := (sat A s).

Definition sat_inv
  : forall {A s}, A |- s ->
    match s return Type with
    | Sym x => A = [x]
    | Nul => False
    | One => A = []
    | Add s t => sum (A |- s) (A |- t)
    | Mul s t => Sigma A1 A2, prod (A = A1++A2) (prod (A1 |- s ) (A2 |- t))
    | Star s => sum (A = [])
                   (Sigma A1 A2, prod (A = A1++A2)
                                    (prod (A1 |- s) (A2 |- Star s)))
    end.
Proof.
  intros A s a.
  destruct a as [x| |A s t H |A s t H |A B s t Hs Ht|s|A B s Hs Ht].
  - reflexivity.
  - reflexivity.
  - left. exact H.
  - right. exact H.
  - exists A, B. easy.
  - left. reflexivity.
  - right. exists A, B. easy.
Defined.

(*** Facts about Star *)

Fact star1 A s :
  A |- s -> A |- Star s.
Proof.
  intros H. rewrite <-(app_nil_r A).
  constructor. exact H. constructor.
Qed.

Fact star2 A B s :
  A |- Star s -> B |- Star s -> A ++ B |- Star s.
Proof.
  revert A s.
  enough (forall A u, A |- u ->
                     match u return Type with
                     | Star s => B |- u -> A ++ B |- u
                     | _ => True
                     end) as H.
  { intros A s H1. apply (H A (Star s) H1). } 
  induction 1 as [| | | | | |A1 A2 s Hs _ _ IHt];
    try exact I.
  - easy.
  - intros H.
    rewrite <- app_assoc. constructor; auto.
Qed.

Fact equiv1 A s t :
    A |- Mul (Star s) (Star s) <=> A |- Star s.
Proof.
  split.
  - intros (A1&A2&->&H1&H2) % sat_inv.
    apply star2; assumption.
  - intros H. change A with ([]++A).
    constructor. constructor. exact H.
Qed.

Fact star3 A s :
  A |- Star (Star s) -> A |- Star s.
Proof.
  revert A s.
  enough (forall A u, A |- u ->
                     match u return Type with
                     | Star (Star s) => A |- Star s
                     | _ => True
                     end) as H.
  { intros A s H1. apply (H A (Star (Star s)) H1). } 
  induction 1 as [ | | | | | |A1 A2 s Hs _ _ IHt];
    try exact I.
  all: destruct s as [| | | | |s]; try exact I.
  - constructor.
  - apply star2. exact Hs. exact IHt.
Qed.

Fact equiv2 A s :
    A |- Star (Star s) <=> A |- Star s.
Proof.
  split.
  - apply star3.
  - apply star1.
Qed.

(*** Derivatives *)

Definition eps_dec s :
  dec ([] |- s).
Proof.
  induction s as [x| | |s IHs t IHt|s IHs t IHt|s IH].
  - right. intros H.  discriminate (sat_inv H).
  - right. intros H.  apply (sat_inv H).
  - left. constructor.
  - destruct IHs as [IHs|IHs].
    + left. apply SAddL, IHs.
    + destruct IHt as [IHt|IHt].
      * left. apply SAddR, IHt.
      * right. intros H. destruct (sat_inv H); easy.
  - destruct IHs as [IHs|IHs].
    + destruct IHt as [IHt|IHt].
      * left. change ([] ++ [] |- Mul s t).
        constructor; assumption.
      * right. intros H.
        destruct (sat_inv H) as (A1&A2&H1&_&H2).
        destruct A1, A2; try discriminate H1. easy.
    + right. intros H.
        destruct (sat_inv H) as (A1&A2&H1&H2&_).
        destruct A1, A2; try discriminate H1. easy.
  - left. constructor.
Defined.

Fixpoint deriv x s : exp :=
  match s with
  | Sym y => if Nat.eq_dec x y then One else Nul
  | Nul => Nul
  | One => Nul
  | Add s t => Add (deriv x s) (deriv x t)
  | Mul s t => if eps_dec s
              then Add (Mul (deriv x s) t) (deriv x t)
              else Mul (deriv x s) t
  | Star s => Mul (deriv x s) (Star s)
  end.

Lemma star4 x A s :
  x::A |- Star s -> Sigma A1 A2, prod (A = A1++A2) (prod (x::A1 |- s) (A2 |- Star s)).
Proof.
  revert x A s.
  enough (forall A s, A |- s -> match A, s return Type with
                         | x::A, Star s => Sigma A1 A2, prod (A = A1++A2)
                                                        (prod (x::A1 |- s)
                                                              (A2 |- Star s))
                         | _, _ => True
                         end) as H.
  { intros x A s H1. apply (H _ _ H1). }
  induction 1 as [ | | | | | s |A B s Hs _ Ht IHt]; try exact I.
  1-2: destruct A; exact I.
  - destruct (A ++ B); exact I.
  - destruct A as [|x A]; cbn.
    + exact IHt.
    + exists A, B. easy.
Qed.

Fact deriv_correct x A s :
  x::A |- s <=> A |- deriv x s.
Proof.
  induction s as
      [y| | |s IHs t IHt|s IHs t IHt|s IH] in x, A |-*;
    cbn; split.
  - intros [= <- ->]%sat_inv.
    destruct Nat.eq_dec as [_|H1]. constructor. easy.
  - destruct Nat.eq_dec as [<-|H1]; intros H%sat_inv; revert H; cbn.
    + intros ->. constructor.
    + easy.
  - intros []%sat_inv.
  - intros []%sat_inv.
  - intros [=]%sat_inv. 
  - intros []%sat_inv.
  - intros [H|H]%sat_inv.
    + apply SAddL, IHs, H.
    + apply SAddR, IHt, H.
  - intros [H|H]%sat_inv.
    + apply SAddL, IHs, H.
    + apply SAddR, IHt, H.
  - intros (A1&A2&H1&H2&H3)%sat_inv.
    revert H1. destruct A1 as [|y A1]; cbn.
    + intros <-. destruct eps_dec as [H|H].
      * apply SAddR, IHt, H3.
      * easy.
    + intros [= <- ->]. destruct eps_dec as [H|H].
      * apply SAddL. constructor. apply IHs, H2. exact H3.
      * constructor. apply IHs, H2. exact H3.
  - destruct eps_dec as [H|H].
    + intros [H1|H1]%sat_inv.
      * revert H1. intros (A1&A2&->&H2&H3)%sat_inv.
        apply (SMul (x::A1)). apply IHs, H2. exact H3.
      * apply (SMul []). exact H. apply IHt, H1.
    + intros (A1&A2&->&H2&H3)%sat_inv.
      apply (SMul (x::A1)). apply IHs, H2. exact H3.
  - intros (A1&A2&->&H2&H3)%star4.
    apply SMul. apply IH, H2. exact H3.
  - intros (A1&A2&->&H2&H3)%sat_inv.
    apply (SStar2 (x::A1)). apply IH, H2. exact H3.
Qed.

Definition sat_dec A s :
  dec (A |- s).
Proof.
  induction A as [|x A IH] in s |-*.
  - apply eps_dec.
  - specialize (IH (deriv x s)) as [H1|H1].
    + left. apply deriv_correct, H1.
    + right. contradict H1. apply deriv_correct, H1.
Defined.


(*** Certifying Solver *)

Definition solve s :
  (Sigma A, A |- s) + (forall A, A |- s -> False).
Proof.
  induction s as [x| | |s IHs t IHt|s IHs t IHt|s _].
  - left. exists [x]. constructor.
  - right. intros A H. apply (sat_inv H).
  - left. exists []. constructor.
  - destruct IHs as [[A IHs]|IHs].
    + left. exists A. apply SAddL, IHs.
    + destruct IHt as [[B IHt]|IHt].
      * left. exists B. apply SAddR, IHt.
      * right. intros A [H|H] % sat_inv.
        -- eapply IHs, H.
        -- eapply IHt, H.
  - destruct IHs as [[A IHs]|IHs].
    + destruct IHt as [[B IHt]|IHt].
      * left. exists (A ++ B). constructor; assumption.
      * right. intros C H. 
        destruct (sat_inv H) as (_&B&_&_&H3).
        eapply IHt, H3.
    + right. intros C H. 
      destruct (sat_inv H) as (A'&_&_&H2&_).
      eapply IHs, H2.
  - left. exists []. constructor.
Defined.

