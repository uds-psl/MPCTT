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

(** Euclidean Division *)

Definition delta x y a b := x = a * S y + b /\ b <= y.

Fact delta0 y :
  delta 0 y 0 0.
Proof.
  unfold delta. lia.
Qed.
Fact delta1 x y a b :
  delta x y a b -> b = y -> delta (S x) y (S a) 0.
Proof.
  unfold delta. lia.
Qed.
Fact delta2 x y a b :
  delta x y a b -> b <> y -> delta (S x) y a (S b).
Proof.
  unfold delta. lia.
Qed.

Fact delta_total :
  forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y.
  induction x as [|x (a&b&IH)].
  - exists 0, 0. apply delta0.
  - destruct (Nat.eq_dec b y) as [H|H].
    + exists (S a), 0. eapply delta1; eassumption.
    + exists a, (S b). apply delta2; assumption.
Defined.

Definition D x y := pi1 (delta_total x y).
Definition M x y := pi1 (pi2 (delta_total x y)).

Compute D 100 3.

Goal forall x y,
    x = D x y * S y + M x y
    /\ M x y <= y.
Proof.
  intros x y. exact (pi2 (pi2 (delta_total x y))).
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
  - apply delta0.
  - destruct (Delta x y) as [a b]; cbn in *.
    destruct (Nat.eq_dec b y) as [H|H]; cbn.
    + eapply delta1; eassumption.
    + apply delta2; assumption.
Qed.

(* Uniqueness is amazingly tricky; we offer 3 variants. *)

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  intros [-> H1] [H3 H2]. 
  enough (a = a') by lia. nia.
Qed.

Fact delta_unique' x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  intros [-> H1] [H3 H2]. 
  enough (a = a') by lia.
  enough (~ a < a' /\ ~ a' < a) by lia.
  split; intros H; revert H3.
  - clear H2.
    assert (a' = a + S (a' - S a)) as -> by lia. clear H.
    lia.
  - clear H1.
    assert (a = a' + S (a - S a')) as -> by lia. clear H.
    lia.
Qed.

Fact delta_unique'' x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  intros [-> H1] [H3 H2].
  revert a' H3.
  induction a as [|a IH]; destruct a'; cbn; intros H3.
  - auto.
  - exfalso. lia.
  - exfalso. clear IH. lia.
  - destruct (IH a') as [<- <-]. lia. auto.
Qed.

(** Complete Induction  *)

Definition nat_compl_ind (p: nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  induction x as [|x IH]; intros y H1.
  - exfalso. lia.
  - apply H. intros z H2. apply IH. lia.
Defined.
