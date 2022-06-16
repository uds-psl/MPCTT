From Coq Require Import Arith Lia.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Definition nat_compl_ind (p: nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  induction x as [|x IH]; intros y H1.
  - exfalso. lia.
  - apply H. intros z H2. apply IH. lia.
Defined.

Definition le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  destruct (x-y) as [|z] eqn:E.
  - left. lia.
  - right. lia.
Qed.

Definition tobool {X Y} (a: X + Y) : bool :=
  if a then true else false.

Compute tobool (le_lt_dec 5 5).
Compute tobool (le_lt_dec 5 4).

(*** Euclidean Division *)

Definition delta x y a b := x = a * S y + b /\ b <= y.

Fact delta1 y :
  delta 0 y 0 0.
Proof.
  unfold delta. lia.
Qed.
Fact delta2 x y a b :
  delta x y a b -> b = y -> delta (S x) y (S a) 0.
Proof.
  unfold delta. lia.
Qed.
Fact delta3 x y a b :
  delta x y a b -> b <> y -> delta (S x) y a (S b).
Proof.
  unfold delta. lia.
Qed.

Definition delta_total :
  forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y.
  induction x as [|x (a&b&IH)].
  - exists 0, 0. apply delta1.
  - destruct (Nat.eq_dec b y) as [H|H].
    + exists (S a), 0. eapply delta2; eassumption.
    + exists a, (S b). apply delta3; assumption.
Defined.

(* Lia doesn't need the derivation rules *)

Goal forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y. unfold delta.
  induction x as [|x (a&b&IH)].
  - exists 0, 0. lia. 
  - destruct (Nat.eq_dec b y) as [H|H].
    + exists (S a), 0. lia.
    + exists a, (S b). lia.
Qed.

(* Computation is possible *)

Definition D x y := pi1 (delta_total x y).
Definition M x y := pi1 (pi2 (delta_total x y)).

Compute D 100 3.
Compute M 100 3.

Fact delta_DM x y :
delta x y (D x y) (M x y).
Proof.
  exact (pi2 (pi2 (delta_total x y))).
Qed.

Fixpoint Delta (x y: nat) : nat * nat :=
  match x with
  | 0 => (0,0)
  | S x' => let (a,b) := Delta x' y in
           if Nat.eq_dec b y then (S a, 0) else (a, S b)
  end.

Fact Delta_correct x y :
  delta x y (fst (Delta x y)) (snd (Delta x y)).
Proof.
  induction x as [|x IH]; cbn.
  - apply delta1.
  - destruct (Delta x y) as [a b]; cbn in *.
    destruct (Nat.eq_dec b y) as [H|H]; cbn.
    + eapply delta2; eassumption.
    + apply delta3; assumption.
Qed.

(*** Uniqueness of delta *)

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  assert (a < a' \/ a = a' \/ a' < a) as [H| [H|H]] by lia.
  - unfold delta;  nia.
  - unfold delta; lia.
  - unfold delta; nia.
    (* nia is an extension of lia that can handle multiplication *)
Qed.

(* Alternative inductive proof not relying on lia *)  
 
Fact delta_unique1 y a b a' b' :
  b <= y ->
  b' <= y ->
  a * S y + b = a' * S y + b' ->
  a = a' /\ b = b'.
Proof.
  intros H1 H2.
  induction a as [|a IH]  in a' |-* ; destruct a'; cbn.
  - easy. 
  - intros ->. exfalso. lia. 
  - intros <-. exfalso. lia.
  - specialize (IH a'). lia.
Qed.

Fact delta_unique2 x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  intros [-> H1] [H3 H2].
  eapply delta_unique1; eassumption.
Qed.

(* Example *)

Goal forall x y z, x * S (S z) + 1 <> y * S (S z) + 0.
Proof.
  intros x y z [H [=]] %delta_unique1; lia.
Qed.

(*** Repeated subtraction *)

Fact delta4 x y:
  x <= y -> delta x y 0 x.
Proof.
  unfold delta; lia.
Qed.

Fact delta5 x y a b:
  delta (x - S y) y a b -> x > y -> delta x y (S a) b.
Proof.
  unfold delta; lia.
Qed.

Goal forall x y,
    (D x y = if le_lt_dec x y then 0 else S (D (x - S y) y)) /\
    (M x y = if le_lt_dec x y then x else M (x - S y) y).
Proof.
  intros x y.
  apply (delta_unique x y).
  - apply delta_DM.
  - destruct (le_lt_dec x y) as [H|H].
    + apply delta4, H.
    + apply delta5.
      * apply delta_DM.
      * exact H.
Qed.

(* Euclidean Division with repeated subtraction *)
Module Repeated_Subtraction.

  Definition delta_tot :
    forall x y, Sigma a b, delta x y a b.
  Proof.
    intros x y. revert x.
    refine (nat_compl_ind _ _).
    intros x IH.
    destruct (le_lt_dec x y) as [H|H].
    - exists 0, x. unfold delta; lia.
    - specialize (IH (x - S y)) as (a&b&IH1&IH2). lia.
      exists (S a), b. unfold delta; lia.
  Defined.

  Definition D x y := pi1 (delta_total x y).
  Definition M x y := pi1 (pi2 (delta_total x y)).
  
  Compute D 1003 3.
  Compute M 1003 3.

End Repeated_Subtraction.

(* Equivalence relation spec and procedural spec *)

Implicit Type f : nat -> nat -> nat * nat.

Definition sat_delta f :=
  forall x y, delta x y (fst (f x y)) (snd (f x y)).

Fact cert_sat_delta :
  forall F: (forall x y, Sigma a b, delta x y a b),
    sat_delta (fun x y => (pi1 (F x y), pi1 (pi2 (F x y)))).
Proof.
  intros F x y. exact (pi2 (pi2 (F x y))).
Qed.

Definition rep_sub f x y :=
  if le_lt_dec x y then (0,x)
  else let (a,b) := f (x - S y) y in (S a, b).

Definition sat_rep_sub f :=
  forall x y, f x y = rep_sub f x y.

Fact rep_sub_delta f :
  sat_rep_sub f -> sat_delta f.
Proof.
  intros E x y. revert x.
  refine (nat_compl_ind _ _). intros x IH.
  rewrite E. unfold rep_sub.
  specialize (IH (x - S y)).
  destruct (f (x - S y) y) as [a b]; cbn in *.
  destruct (le_lt_dec x y) as [H|H]; cbn.
  - apply delta4, H.
  - apply delta5. 2:exact H. apply IH. lia.
Qed.
    
Lemma pair_eq X Y (a b: X * Y) :
  fst a = fst b /\ snd a = snd b -> a = b.
Proof.
  destruct a; destruct b; cbn; intuition congruence.
Qed.

Fact delta_rep_sub f :
  sat_delta f -> sat_rep_sub f.
Proof.
  intros H x y. apply pair_eq.
  apply (delta_unique x y). easy.
  unfold rep_sub.
  specialize (H (x - S y) y).
  destruct (f (x - S y) y) as [a b]; cbn in *.  
  destruct (le_lt_dec x y) as [H1|H1]; cbn.
  - apply delta4, H1.
  - apply delta5; easy. 
Qed.

(*** Predefined div and mod *)

Fact predefined_div_mod_delta x y :
  delta x y (x / S y) (x mod S y).
Proof.
  unfold delta.
  generalize (Nat.div_mod x (S y)).
  generalize (Nat.mod_upper_bound x (S y)).
  lia.
Qed.
