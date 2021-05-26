Unset Elimination Schemes.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Module M.
  Inductive nat: Type := O | S (n: nat).

  Implicit Types (n x y: nat).

  Definition nat_elim (p: nat -> Type)
    : p O -> (forall n, p n -> p (S n)) -> forall n, p n
    := fun a f => fix F n := match n with O => a | S n' => f n' (F n') end.

  Fact S_O n:
      S n <> O.
  Proof.
    intros H.
    change (if S n then True else False).
    rewrite H. exact I.
  Qed.

  Fact S_injective n n' :
      S n = S n' -> n = n'.
  Proof.
    intros H. 
    change (match S n with O => True | S n => n = n' end).
    rewrite H. auto.
  Qed.

  Goal forall n,
      S n <> n.
  Proof.
    refine (nat_elim _ _ _).
    - apply S_O.
    - intros n IH H. eapply IH, S_injective, H.
  Qed.
End M.

(* From now on we use the predefined numbers from the library *)

Implicit Types x y z n k : nat.

Fact nat_eqdec : eqdec nat.
Proof.
  hnf.
  induction x as [|x IH]; destruct y.
  - left. reflexivity.
  - right. intros [=].
  - right. intros [=].
  - destruct (IH y) as [H|H].
    + left. f_equal. exact H.
    + right. intros [= H1]. apply H, H1.
Qed.

Lemma add_assoc x y z :
  x + y + z = x + (y +z).
Proof.
  induction x as [|x IH]; cbn; congruence.
Qed.

Lemma addO x :
  x + 0 = x.
Proof.
  induction x as [|x IH]; cbn; congruence.
Qed.

Lemma addS x y :
  x + S y = S (x + y).
Proof.
  induction x as [|x IH]; cbn. reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma add_comm x y :
  x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - rewrite addO. reflexivity.
  - rewrite addS, IH. reflexivity.
Qed.

Lemma add_injective x y y' :
  x + y = x + y' -> y = y'.
Proof.
  induction x as [|x IH]; cbn.
  - auto.
  - intros [= H]. apply IH, H.
Qed.

Lemma add_injectiveO x y :
  x + y = x -> y = 0.
Proof.
  induction x as [|x IH]; cbn.
  - auto.
  - intros [= H]. auto.
Qed.

(*** Subtraction *)


Fact sub_O_right x :
  x - 0 = x.
Proof.
  destruct x; reflexivity.
Qed.

Fact sub_add_right x y :
  x - (x + y) = 0.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Fact sub_xx x :
  x - x = 0.
Proof.
  pattern x at 2. rewrite <-(addO x). apply sub_add_right.
Qed.

Fact sub_add_left x y :
  (x + y) - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - apply sub_O_right.
  - exact IH.
Qed.

(*** Order *)


Definition le x y : Prop := x - y = 0.
Notation "x <= y" := (le x y).
Notation "x < y" := (le (S x) y).
Notation "x >= y" := (le y x).
Notation "x > y" := (le (S y) x).

Definition le_dec x y : dec ( x <= y).
Proof.
  induction x as [|x IH] in y |-*; destruct y.
  - left. reflexivity.
  - left. reflexivity.
  - right. cbv. intros [=].
  - apply IH.
Defined.

Fact le_eq_sub x y :
  x <= y -> x + (y - x) = y.
Proof.
  induction x as [|x IH] in y |-*; cbn.
  - intros _. apply sub_O_right.
  - destruct y; cbn.
    + intros [=].
    + intros H%IH. f_equal. apply H.
Qed.
 
Fact le_ex x y :
  x <= y <-> exists k, x + k = y.
Proof.
  split.
  - exists (y - x). apply le_eq_sub, H.
  - intros [k <-]. apply sub_add_right.
Qed.

Fact le_add x y :
  x <= x + y.
Proof.
  apply sub_add_right.
Qed.

Fact le_S x :
  x <= S x.
Proof.
  replace (S x) with (x + 1).
  - apply le_add.
  - rewrite addS, addO. reflexivity.
Qed.

Fact le_add_O x y :
  x + y <= x -> y = 0.
Proof.
  unfold le. rewrite sub_add_left. auto.
Qed.

Fact le_eq_O x :
  x <= 0 -> x = 0.
Proof.
  destruct x. auto. intros [=].
Qed.

Fact le_refl x :
  x <= x.
Proof.
  apply sub_xx.
Qed.

Fact le_trans x y z:
  x <= y -> y <= z -> x <= z.
Proof.
  intros [a <-]%le_ex [b <-]%le_ex.
  rewrite add_assoc. apply le_add.
Qed.
  
Fact le_anti x y :
  x <= y -> y <= x -> x = y.
Proof.
  intros [a <-]%le_ex->%le_add_O. symmetry. apply addO.
Qed.

Fact le_trans_lt_le x y z :
  x < y -> y <= z -> x < z.
Proof.
  intros [a <-]%le_ex [b <-]%le_ex.
  cbn. rewrite add_assoc. apply le_add.
Qed.
  
Fact le_strict_O x :
  ~ x < 0.
Proof.
  cbv. intros [=].
Qed.

Fact le_strict_add x y :
  ~ x + y < x.
Proof.
  unfold le. rewrite <-addS. rewrite sub_add_left. intros [=].
Qed.

Fact le_strict x :
  ~ x < x.
Proof.
  pattern x at 1. rewrite <-(addO x). apply le_strict_add.
Qed.

Fact le_add_right x y z :
  x <= y -> x <= y + z.
Proof.
  intros [a <-]%le_ex. rewrite add_assoc. apply le_add.
Qed.

Fact le_add_S x y :
  x <= y -> x <= S y.
Proof.
  replace (S y) with (y + 1).
  - apply le_add_right.
  - rewrite addS, addO. reflexivity.
Qed.

Fact le_sub x y :
  x - y <= x.
Proof.
  induction x as [|x IH] in y |-*.
  - reflexivity.
  - destruct y; cbn.
    + apply sub_xx.
    + eapply le_trans.
      * apply IH.
      * apply le_S.
Qed.

(*** Trichotomy *)

Fact le_tricho x y :
  (x < y) + (x = y) + (y < x).
Proof.
  induction x as [|x IH] in y |-*; destruct y.
  - auto.
  - left. left. reflexivity.
  - right. reflexivity.
  - destruct (IH y) as [[H|H]|H].
    + left. left. exact H.
    + left. right. f_equal. exact H.
    + right. exact H.
Defined.

Fact le_lt_eq x y :
  x <= y <=> (x < y) + (x = y).
Proof.
  split.
  - destruct (le_tricho x y) as [[H|H]|H].
    + auto.
    + auto.
    + intros H1. exfalso.
      eapply le_strict, le_trans_lt_le; eassumption.
  - intros [H|<-].
    + eapply le_trans. 2:exact H. apply le_S.
    + apply le_refl.
Qed.

Fact le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  induction x as [|x IH] in y |-*.
  - left. reflexivity.
  - destruct y.
    + right. reflexivity.
    + apply (IH y).
Defined.

Fact le_contra x y :
  ~ x > y -> x <= y.
Proof.
  destruct (le_lt_dec x y) as [H|H].
  - intros _. exact H.
  - intros H1. exfalso.  apply H1, H.
Qed.

Fact le_contra_eq x y :
  ~ x < y -> ~ y < x -> x = y.
Proof.
  intros H1%le_contra H2%le_contra.
  eapply le_anti; eassumption.
Qed.
  
Lemma bounded_forall_dec (p: nat -> Prop) k:
  (forall x, dec (p x)) -> dec (forall x, x < k -> p x).
Proof.
  intros H.
  induction k as [|k IH].
  - left. intros x []%le_strict_O.
  - destruct (H k) as [H1|H1].
    + destruct IH as [IH|IH].
      * left. intros x H2. change (x <= k) in H2.
        apply le_lt_eq in H2 as [H2| ->]; auto.
      * right. contradict IH. intros x H2. apply IH, le_add_S, H2.
    + right. contradict H1. apply H1, le_refl.
Qed.
