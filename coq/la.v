(*** Linear Arithmetic *)

From Coq Require Import Lia.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

(*** Constructor Laws *)

Goal forall x, S x <> 0.
Proof.
  intros x H.
  change (if S x then True else False).
  rewrite H. exact I.
Qed.

Goal forall x y, S x = S y -> x = y.
Proof.
  intros x y H.
  change (match S x with 0 => True | S z => z = y end).
  rewrite H. reflexivity.
Qed.

(*** Addition *)

Fact add_O x :
  x + 0 = x.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact add_S x y :
  x + S y = S (x + y).
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact add_comm x y :
  x + y = y + x.
Proof.
  induction y as [|y IH]; cbn.
  - apply add_O. 
  - rewrite <-IH. apply add_S.
Qed.

Fact add_S_add x :
  S x = x + 1.
Proof.
  rewrite add_comm. reflexivity.
Qed.

Fact add_asso x y z :
  (x + y) + z = x + (y + z).
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Fact add_eq_zero x y :
  x + y = 0 <-> x = 0 /\ y = 0.
Proof.
  destruct x; easy.
Qed.
  
Fact add_injective x y y' :
  x + y = x + y' -> y = y'.
Proof.
  induction x as [|x IH]; cbn.
  - easy.
  - intros [= H]. apply IH, H.
Qed.

Fact add_injective_O x y :
  x + y = x -> y = 0.
Proof.
  replace x with (x + 0) at 2.
  - apply add_injective.
  - apply add_O.
Qed.

Fact add_contra x y :
  x + S y <> x.
Proof.
  intros H%add_injective_O. easy.
Qed.

(*** Subtraction *)

Locate "-".
Print Nat.sub.
Arguments Nat.sub : simpl nomatch.


Fact sub_O x :
  x - 0 = x.
Proof.
  destruct x; reflexivity.
Qed.

Fact add_sub x y :
  x + y - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - destruct y; reflexivity.
  - exact IH.
Qed.

Fact sub_add x y z :
  x - (y + z) = x - y - z.
Proof.
  induction x as [|x IH] in y |-*; cbn.
  - reflexivity.
  - destruct y; cbn. reflexivity.
    apply IH.
Qed.

Fact sub_xx x :
  x - x = 0.
Proof.
  replace x with (x + 0) at 1.
  - apply add_sub.  
  - apply add_O.
Qed.

Fact sub_add_zero x y :
  x - (x + y) = 0.
Proof.
  rewrite sub_add, sub_xx. reflexivity.
Qed.

(*** Comparisons *)

Module Comparisons.
  
Notation "x <= y" := (x - y = 0) : nat_scope.
Notation "x < y" := (S x - y = 0) : nat_scope.
Notation "x >= y" := (y - x = 0) (only parsing) : nat_scope.
Notation "x > y" := (S y - x = 0) (only parsing) : nat_scope.
(* Negations ~(x < y) don't print correctly *)

Fact le_add x y :
  x <= x + y.
Proof.
  apply sub_add_zero.
Qed.

Fact le_refl x :
  x <= x.
Proof.
  replace x with (x + 0) at 2.
  - apply le_add.
  - apply add_O.
Qed.

Fact le_S x :
  x <= S x.
Proof.
  rewrite add_S_add. apply le_add.
Qed.

Fact le_sub x y :
  x - y <= x.
Proof.
  rewrite <-sub_add. rewrite add_comm. apply le_add.
Qed.

Fact le_add_char x y :
  x <= y  <-> x + (y - x) = y.
Proof.
  induction x as [|x IH] in y |-*; destruct y; cbn.
  1-3:easy.
  rewrite IH. intuition congruence.
Qed.

Fact le_anti x y :
  x <= y -> y <= x -> x = y.
Proof.
  intros H1%le_add_char H2. revert H1.
  rewrite H2. rewrite add_O. easy.
Qed.

Fact le_trans x y z:
  x <= y -> y <= z -> x <= z.
Proof.
  intros H1%le_add_char H2%le_add_char.
  rewrite <-H2. rewrite <-H1 at 1.
  rewrite add_asso.
  apply sub_add_zero.
Qed.

Fact lt_le_trans x y z:
  x < y -> y <= z -> x < z.
Proof.
  apply le_trans.
Qed.

Fact le_lt_trans x y z:
  x <= y -> y < z -> x < z.
Proof.
  apply (le_trans (S x) (S y) z).
Qed.

Fact lt_sub x y z :
  x - y = S z -> y < x.
Proof.
  induction x as [|x IH] in y |-*; cbn.
  - easy.
  - destruct y; cbn.
    + easy.
    + apply IH.
Qed.

(** Contra rules *)

Fact lt_contra_zero x :
  x < 0 -> False.
Proof.
  easy.
Qed.

Fact lt_contra_add x y :
  x + y < x -> False.
Proof.
  replace (S (x + y)) with (x + S y).
  - rewrite add_sub. easy.
  - rewrite add_S. reflexivity.
Qed.

Fact lt_contra_self x :
  x < x -> False.
Proof.
  replace x with (x + 0) at 1.
  - apply lt_contra_add.
  - apply add_O.
Qed.

Fact le_contra x y :
   x <= y <-> (y < x -> False).
Proof.
  induction y as [|y IH] in x |-*; destruct x; cbn.
  1-3: easy. apply IH.

Qed.

Fact lt_contra x y :
  x < y <-> (y <= x -> False).
Proof.
  apply le_contra.
Qed.

Fact lt_not_eq x y :
  (x < y -> False) -> (y < x -> False) -> x = y.
Proof.
  intros H1%lt_contra H2%lt_contra.
  apply le_anti; assumption.
Qed.

Fact add_le x y z :
  x + y <= z -> x <= z.
Proof.
  induction x as [|x IH] in z |-*; cbn.
  - easy.
  - destruct z; cbn.
    + easy.
    + apply IH.
Qed.

Fact exercise x y :
  y > 0 -> y - S x < y.
Proof.
  destruct y. easy.
  intros _. change (y - x <= y).
  rewrite <-sub_add.
  rewrite add_comm.
  apply sub_add_zero.
Qed.

(*** Arithmetc Tests and Deciders *)

Fact test_dec p (f: nat -> nat -> nat) :
  (forall x y, if f x y then p x y else ~p x y) ->
  forall x y, dec (p x y).
Proof.
  intros H x y. specialize (H x y).
  destruct (f x y); unfold dec; auto.
Qed.

Fact le_test x y :
  if x - y then x <= y else ~(x <= y).
Proof.
  destruct (x - y); easy.
Qed.
Fact lt_test x y :
  if S x - y then x < y else ~(x < y).
Proof.
  destruct (S x - y); easy.
Qed.
Fact eq_test x y :
  if (x - y) + (y - x) then x = y else ~(x = y).
Proof.
  destruct (_ + _) eqn:E.
  - apply add_eq_zero in E as [E1 E2].
    apply le_anti; assumption.
  - intros <-. rewrite sub_xx in E. easy.
Qed.

Definition le_dec x y : dec (x <= y).
Proof.
  eapply (test_dec (fun x y => x <= y)), le_test.
Qed.
Definition lt_dec x y : dec (x < y).
Proof.
  eapply (test_dec (fun x y => x < y)), lt_test.
Qed.
Definition eq_dec : eqdec nat.
Proof.
  hnf.
  eapply (test_dec (fun x y => x = y)), eq_test.
Qed.

Definition le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  destruct (le_dec x y) as [H|H].
  - left. exact H.
  - right. apply lt_contra, H.
Qed.

Definition le_lt_eq_dec x y :
  x <= y -> (x < y) + (x = y).
Proof.
  intros H1.
  destruct (eq_dec x y) as [H|H].
  - right. exact H.
  - left. apply lt_contra. contradict H.  apply le_anti; assumption.
Qed.

Definition tightness_dec x y :
  x <= y -> y <= S x -> (x=y) + (y = S x).
Proof.
  intros H1%le_lt_eq_dec H2%le_lt_eq_dec.
  destruct H1 as [H1|H1].
  2:{ auto. }
  destruct H2 as [H2|H2].
  2:{ auto. }
  exfalso.
  apply (lt_contra_self x).
  eapply lt_le_trans; eassumption.
Qed.

End Comparisons.

(*** Deciders with Lia *)

(* We now switch to Coq's definition of comparisons
   and handle linear arithmetic with the automation tactic lia *)       

Definition nat_eqdec :
  eqdec nat.
Proof.
  intros x y. unfold dec.
  destruct ((x - y) + (y - x)) eqn:?; intuition lia.
Qed.

Fact le_lt_dec x y :
  (x <= y) + (y < x).
Proof.
  destruct (x - y) eqn:?; intuition lia.
Qed.
  
Fact le_lt_eq_dec x y :
  x <= y -> (x < y) + (x = y).
Proof.
  destruct (S x - y) eqn:?; intuition lia.
Qed.

Fact tightness_dec x y :
  x <= y -> y <= S x -> (x = y) + (y = S x).
Proof.
  destruct (nat_eqdec x y); intuition lia.
Qed.

Section LiaTest.
  Variables x y z : nat.
  Variables P Q : Prop.

  Goal x <= y <-> x < y \/ x = y.
    Succeed lia. Abort.

  Goal ~ x > y <-> ~ x >= y \/ ~ x <> y.
    Succeed lia. Abort.
 
  Goal ~(x=y <-> x <> y).
    Succeed lia. Abort.
 
  Goal ~(P <-> ~P).
    Fail lia. Abort.
 
End LiaTest.



(*** Multiplication *)

Locate "*".
Print Nat.mul.

Fact mul_dist_add x y z :
  (x + y) * z = x * z + y * z.
Proof.
  induction x; cbn. reflexivity. rewrite IHx. lia.
Qed.

Fact mul_dist_sub x y z :
   (x - y) * z = x * z - y * z.
Proof.
  induction x in y |-*; cbn. reflexivity.
  destruct y; cbn. lia.
  replace (z + x * z - (z + y * z))
    with (x * z - y * z) by lia.
  apply IHx.
Qed.

Fact mul_asso x y z :
  x * (y * z) = x * y * z.
Proof.
  induction x; cbn. reflexivity.
  rewrite IHx. symmetry. apply mul_dist_add.
Qed.

Fact mul_comm_O x :
  x * 0 = 0.
Proof.
  induction x; cbn. reflexivity. exact IHx.
Qed.
Fact mul_comm_S x y :
  x * S y = x + x * y.
Proof.
  induction x; cbn. reflexivity.
  rewrite IHx. lia.
Qed.

Fact mul_comm x y :
  x * y = y * x.
Proof.
  induction y; cbn.
  - apply mul_comm_O.
  - rewrite <-IHy. apply mul_comm_S. 
Qed.

(** Tactic lia can do multiplications with nubers *)
Goal forall x y, (x + y) * 2 = 2 * x + 2 * y.
Proof.
  lia.
Qed.

Goal forall x y, (x - y) * 2 = 2 * x - 2 * y.
Proof.
  lia.
Qed.

(** Tactic nia proves all of the above theorems *)

Goal forall x y, x * y = y * x.
Proof.
  nia.
Qed.

Goal forall x y a, (x - y) * a = x * a - y * a.
Proof.
  nia.
Qed.
