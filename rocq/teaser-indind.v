From Stdlib Require Import Lia.

(*** Inductive Comparisons *)

Inductive le (x: nat) : nat -> Prop :=
| leR : le x x 
| leS y : le x y -> le x (S y).

Fact le_correct x y :
  le x y -> x <= y.
Proof.
  induction 1 as [| y H IH].
  - lia.
  - lia.
Qed.

Fact le_complete x y :
  x <= y -> le x y.
Proof.
  induction y as [|y IH]; intros H.
  - assert (x = 0) as -> by lia.
    apply leR.
  - assert (x = S y \/ x <= y) as [->|H1] by lia.
    + apply leR.
    + apply leS, IH, H1.
Qed.

Definition elim (x: nat) (p: nat -> Prop)
  : p x ->
    (forall y, p y -> p (S y)) -> 
    forall y, le x y -> p y
  := fun e1 e2 => fix f _ a :=
    match a with
    | leR _ => e1
    | leS _ y a => e2 y (f y a)
    end.

Fact le_correct' x y :
  le x y -> x <= y.
Proof.
  revert y. apply elim.
  - lia.
  - lia.
Qed.


(*** Inductive Equality *)

Module EQ.

Inductive eq X (x: X) : X -> Prop :=
| Q : eq X x x.

Definition R 
  : forall X  (x y: X) (p: X -> Type),  eq X x y -> p x -> p y
  := fun X x _ p e => match e with
                   | Q _ _ => fun a => a
                   end.

Goal forall X x y, eq X x y <-> x = y.
Proof.
  intros *. split.
  - intros H. generalize (eq_refl x). apply R, H.
  - intros <-. apply Q.
Qed.
End EQ.


(*** Reflexive Transitive Closure *)

Module Star.
Section Star.
  Variable X : Type.
  Implicit Type R: X -> X -> Prop.

  Inductive star (R: X -> X -> Prop) (x: X) : X -> Prop :=
  | Nil : star R x x
  | Cons y z : R x y -> star R y z -> star R x z.

  Implicit Type p: X -> X -> Prop.
  Definition reflexive p := forall x, p x x.
  Definition transitive p := forall x y z, p x y -> p y z -> p x z.
  Definition incl p p' := forall x y, p x y -> p' x y.
 
  Fact star_incl R :
    incl R (star R).
  Proof.
    intros x y r. eapply Cons. exact r. apply Nil.
  Qed.

  Definition elim R (p: X -> X -> Prop)
    : (forall x, p x x) ->
      (forall x y z, R x y -> p y z -> p x z) -> 
      forall x y, star R x y -> p x y
    := fun f1 f2 => fix f x _ a :=
      match a with
      | Nil _ _ => f1 x
      | Cons _ _ x' z r a => f2 x x' z r (f x' z a)
      end.
 
  Fact star_trans R :
    transitive (star R).
  Proof.
    intros x y z.
    revert x y.
    refine (elim _ _ _ _).
    - easy.
    - intros x x' y r IH H.
      eapply Cons. exact r. auto.
  Qed.

  (** We may also use the automatically generated eliminator for star. *)

  Check star_ind.
  
  Goal 
    forall R, transitive (star R).
  Proof.
    intros R.
    induction 1 as [|x x' y r _ IH].
    - easy.
    - intros H. eapply Cons. exact r. auto.
  Qed.

  Fact least R p :
    reflexive p ->
    transitive p ->
    incl R p ->
    incl (star R) p.
  Proof.
    intros H1 H2 H3. hnf.
    apply elim.
    - exact H1.
    - intros x y z H%H3. apply H2, H.
  Qed.

  Fact idempotent R x y:
    star (star R) x y <-> star R x y.
  Proof.
    split.
    - apply least.
      + intros z. constructor.
      + apply star_trans.
      + easy.
    - apply star_incl.
  Qed.
End Star.
End Star.

(*** PI -> DPI ***)

Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.

Definition DPI := forall X (p: X -> Type) x u v, Sig p x u = Sig p x v -> u = v.

Goal DPI.
Proof.
  intros X p x u v e.
  change u with (pi2 (Sig p x u)).
  Fail rewrite e.
  Fail pattern (Sig p x u).
Abort.

Definition PI := forall (P: Prop) (a b : P), a = b.

Definition cast {X} [p: X -> Type] {x y: X}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Fact cast_eq X (x y: X) p (a: p x):
  cast eq_refl a = a.
Proof.
  reflexivity.
Qed.

Section UIP_DPI.
  Variable X: Type.

  Definition UIP := forall (x : X) (e: x = x), e = eq_refl.
  Definition K_Streicher := forall (x: X) (p: x = x -> Prop), p (eq_refl x) -> forall e, p e.
  Definition CD := forall (p: X -> Type) (x: X) (a: p x) (e: x = x), cast e a = a.
  Definition DPI' := forall (p: X -> Type) x u v, Sig p x u = Sig p x v -> u = v.
  
  Lemma L1 : UIP -> K_Streicher.
  Proof.
    intros H x p a e. hnf in H. rewrite H. exact a.
  Qed.

  Lemma L2 : K_Streicher -> CD.
  Proof.
    intros H p x a. hnf in H.  apply H. reflexivity.
  Qed.
  
  Lemma L3 : CD -> DPI'.
  Proof.
    intros H p x.
    enough (forall a b: sig p, a = b -> forall e: pi1 a = pi1 b, cast e (pi2 a) = pi2 b) as H'.
    - intros u v e'. apply (H' _ _ e' (eq_refl x)).
    - intros a b <-. hnf in H. apply H.
  Qed.
End UIP_DPI.

Goal PI -> DPI.
Proof.
  intros H X.
  apply L3, L2, L1.
  intros x e. apply H.
Qed.


