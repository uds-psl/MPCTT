From Coq Require Import Arith Lia.
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Goal forall x y, x <= y <-> x - y = 0.
Proof.
  split; lia.
Qed.

Goal forall x y, x <= y <-> exists k, x + k = y.
Proof.
  split.
  - exists (y-x). lia.
  - intros [k <-]. lia.
Qed.

Fact le_tricho x y :
  x < y \/ x = y \/ y < x.
Proof.
  lia.
Qed.

(* lia cannot do sums *)
Lemma le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  induction x as [|x IH] in y |-*.
  - left. lia.
  - destruct y as [|y].
    + right. lia.
    + specialize (IH y) as [IH|IH].
      * left. lia.
      * right. lia.
Qed.

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

Fact delta_total :
  forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y.
  induction x as [|x (a&b&IH)].
  - exists 0, 0. apply delta1.
  - destruct (Nat.eq_dec b y) as [H|H].
    + exists (S a), 0. eapply delta2; eassumption.
    + exists a, (S b). apply delta3; assumption.
Defined.

Definition D x y := pi1 (delta_total x y).
Definition M x y := pi1 (pi2 (delta_total x y)).

Compute D 100 3.

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

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  intros [-> H1] [H3 H2].
  revert a' H3.
  induction a as [|a IH]; destruct a'; cbn.
  - easy. 
  - lia. 
  - lia.
  - specialize (IH a'). lia.
Qed.

Fact delta4 x y:
  x <= y -> delta x y 0 x.
Proof.
  unfold delta. cbn. easy.
Qed.

Fact delta5 x y a b:
  delta (x - S y) y a b -> x > y -> delta x y (S a) b.
Proof.
  unfold delta. cbn. rewrite <- plus_assoc.
  intros [<- H1] H2. lia.
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

Fact predefined_div_mod_delta x y :
  delta x y (x / S y) (x mod S y).
Proof.
  unfold delta.
  generalize (Nat.div_mod x (S y)).
  generalize (Nat.mod_upper_bound x (S y)).
  lia.
Qed.

(*** Complete Induction  *)

Definition nat_compl_ind (p: nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  induction x as [|x IH]; intros y H1.
  - exfalso. lia.
  - apply H. intros z H2. apply IH. lia.
Defined.
