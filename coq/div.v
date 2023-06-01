From Coq Require Import Arith Lia.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sig (fun y => p)) ..))
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

Definition delta_cert :
  forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y.
  induction x as [|x (a&b&IH)].
  - exists 0, 0. unfold delta; lia.
  - destruct (Nat.eq_dec b y) as [H|H].
    + exists (S a), 0. unfold delta in *; lia.
    + exists a, (S b). unfold delta in *; lia.
Defined.

(* Computation is possible *)

Definition D x y := pi1 (delta_cert x y).
Definition M x y := pi1 (pi2 (delta_cert x y)).

Compute D 100 3.
Compute M 100 3.

Definition sat_delta f := forall x y, delta x y (fst (f x y)) (snd (f x y)).

Fact DM_sat_delta :
  sat_delta (fun x y => (D x y, M x y)).
Proof.
  exact (fun x y => pi2 (pi2 (delta_cert x y))).
 Qed.

Fixpoint Delta (x y: nat) : nat * nat :=
  match x with
  | 0 => (0,0)
  | S x' => let (a,b) := Delta x' y in
           if Nat.eq_dec b y then (S a, 0) else (a, S b)
  end.

Fact Delta_sat_delta :
  sat_delta Delta.
Proof.
  intros x y.
  induction x as [|x IH]; cbn.
  - unfold delta; lia.
  - destruct (Delta x y) as [a b]; cbn in *.
    destruct (Nat.eq_dec b y) as [H|H]; cbn.
    + unfold delta in *; lia.
    + unfold delta in *; lia.
Qed.

(*** Uniqueness of delta *)

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  unfold delta. intros H1 H2.
  enough (a = a') by lia.
  nia.
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

Definition agree {X Y Z} (f g: X -> Y -> Z) :=
  forall x y, f x y = g x y.
 
Lemma pair_eq X Y (a b: X * Y) :
  fst a = fst b /\ snd a = snd b -> a = b.
Proof.
  destruct a; destruct b; cbn; intuition congruence.
Qed.

Fact sat_delta_unique f g :
  sat_delta f -> sat_delta g -> agree f g.
Proof.
  intros H1 H2 x y.
  apply pair_eq. 
  eapply delta_unique; easy.
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
  - apply DM_sat_delta.
  - destruct (le_lt_dec x y) as [H|H].
    + unfold delta; lia.
    + generalize (DM_sat_delta (x - S y) y). cbn.
      unfold delta; lia.
Qed.

(* Euclidean Division with repeated subtraction *)
Module Repeated_Subtraction.

  Definition delta_cert_rep_sub :
    forall x y, Sigma a b, delta x y a b.
  Proof.
    intros x y. revert x.
    refine (nat_compl_ind _ _).
    intros x IH.
    destruct (le_lt_dec x y) as [H|H].
    - exists 0, x. unfold delta; lia.
    - specialize (IH (x - S y)) as (a&b&IH). lia.
      exists (S a), b. unfold delta in *; lia.
  Qed.

End Repeated_Subtraction.

(* Equivalence relation spec and procedural spec *)

Definition rep_sub (f: nat -> nat -> nat * nat) x y :=
  if le_lt_dec x y then (0,x)
  else let (a,b) := f (x - S y) y in (S a, b).

Fact rep_sub_delta f :
  agree f (rep_sub f) -> sat_delta f.
Proof.
  intros E x y. revert x.
  refine (nat_compl_ind _ _). intros x IH.
  specialize (IH (x - S y)).
  rewrite E. unfold rep_sub.
  destruct (f (x - S y) y) as [a b]; cbn in *.
  destruct (le_lt_dec x y) as [H|H]; cbn.
  - unfold delta in *; lia.
  - unfold delta in *; lia.
Qed.
   
Fact delta_rep_sub f :
  sat_delta f -> agree f (rep_sub f).
Proof.
  intros H.
  apply sat_delta_unique. exact H.
  intros x y. unfold rep_sub.
  destruct (le_lt_dec x y) as [H1|H1]; cbn.  
  - unfold delta; lia.
  - specialize (H (x - S y) y).
    destruct (f (x - S y) y) as [a b]; cbn in *.
    unfold delta in *; lia.
Qed.

Fact rep_sub_Delta :
  agree Delta (rep_sub Delta).
Proof.
  apply delta_rep_sub, Delta_sat_delta.
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
