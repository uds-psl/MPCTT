From Coq Require Import Arith Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decider p := (forall x, dec (p x)).
Notation unique p := (forall x x', p x -> p x' -> x = x').
Notation functional p := (forall x y y', p x y -> p x y' -> y = y').

Definition nat_eqdec : eqdec nat.
Proof.
  intros x y.
  destruct (x-y) eqn:E.
  - destruct (y-x) eqn:E'.
    + left; lia.
    + right; lia.
  - right; lia.
Defined.

Implicit Types (n k: nat).

Definition safe (p: nat -> Prop) n := forall k, p k -> k >= n.
Definition least (p: nat -> Prop) n := p n /\ safe p n.

Fact least_unique (p: nat -> Prop) :
  unique (least p).
Proof.
  intros x y [H1 H2] [H3 H4].
  enough (x <= y /\ y <= x) by lia. split.
  - apply H2, H3.
  - apply H4, H1.
Qed.

Fact safe_O p :
  safe p 0.
Proof.
  intros k _. lia.
Qed.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  intros H1 H2 k H3.
  specialize (H1 k H3).
  enough (k <> n) by lia.
  congruence.
Qed.

(*** Least witness functions *)

Section LWF.
  Variable p : nat -> Prop.

  Definition delta x y := (least p y /\ y < x) \/ (safe p x /\ y = x).
  Definition lwf f := forall x, delta x (f x).

  Fact delta_functional :
    functional delta.
  Proof.
    intros x y y' [[H1 H2]|[H2 ->]] [[H1' H2']|[H2' ->]].
    - eapply least_unique; eassumption.
    - exfalso. specialize H1 as [H1 _]. apply H2' in H1. lia.
    - exfalso. specialize H1' as [H1 _]. apply H2 in H1. lia.
    - reflexivity.
  Qed.

  Fact delta_least n x y :
    p n -> n <= x -> delta x y -> least p y.
   Proof.
     intros H1 H2 [[H3 _]|[H3 ->]]. exact H3.
     enough (n=x) as -> by easy.
     apply H3 in H1. lia.
   Qed.
   
   Fact lwf_least f n x :
     lwf f -> p n -> n <= x  -> least p (f x).
   Proof.
     intros H1 H2 H3.
     eapply delta_least.  exact H2. exact H3. apply H1.
   Qed.
  
   Variable p_dec : forall x, p x + (p x -> False).

   Fixpoint G x :=
     match x with
     | 0 => 0
     | S x => let y:= G x in if p_dec y then y else S x
     end.

   Fact G_lwf :
     lwf G.
   Proof.
     hnf.
     induction x as [|x IH]; cbn.
     - right. split. apply safe_O. reflexivity. 
     - destruct p_dec as [H|H].
       + left.
         destruct IH as [[IH1 IH]|[IH1 IH2]].
         * split. exact IH1. lia.
         * rewrite IH2 in *. split. easy. lia.
       + destruct IH as [IH|[IH1 IH2]].
         * exfalso. apply H, IH.
         * right. split. 2:reflexivity.
           apply safe_S. easy.  congruence.
   Qed.

   Fact G_least n x :
     p n -> n <= x  -> least p (G x).
   Proof.
     intros H1 H2.
     eapply lwf_least.
     - apply G_lwf.
     - exact H1.
     - exact H2.
   Qed.


   Fixpoint L n k :=
     match n with
     | 0 => k
     | S n => if p_dec k then k else L n (S k)
     end.

   Fact L_correct n k :
     safe p k -> delta (n + k) (L n k).
   Proof.
     induction n as [|n IH] in k |-*; cbn; intros H.
     - right. easy.
     - destruct p_dec as [H1|H1].
       + left. split. easy. lia.
       + specialize (IH (S k)).
         replace (S (n + k)) with (n + S k) by lia.
         apply IH. apply safe_S; assumption.
   Qed.

   Fact L_lwf :
     lwf (fun x => L x 0).
   Proof.
     intros x.
     replace x with (x + 0) at 1.
     apply L_correct. apply safe_O. lia.
   Qed.

   Definition delta_sat : forall x, sig (delta x).
   Proof.
     induction x as [|x IH].
     - exists 0. right. split. 2:reflexivity. apply safe_O.
     - destruct IH as [y IH].
       destruct (p_dec y) as [H|H].
       + exists y. left.
         destruct IH as [IH|[IH ->]]; unfold delta.
         * intuition lia.
         * split. easy. lia.
       + exists (S x).
         destruct IH as [IH|[IH ->]].
         * exfalso. apply H, IH.
         * right. split. 2:reflexivity.
           apply safe_S; assumption.
   Defined.

End LWF.

Fact lw_operator (p: nat -> Prop) :
  decider p -> sig p -> sig (least p).
Proof.
  intros d [n H]. exists (G p d n).
  eapply G_least. exact H. lia.
Qed.

Fact lw_exists (p: nat -> Prop) :
  decider p -> ex p -> ex (least p).
Proof.
  intros d [n H]. exists (G p d n).
  eapply G_least. exact H. lia.
Qed.

Fact least_dec (p: nat -> Prop) :
  decider p -> decider (least p).
Proof.
  intros d n.
  destruct (d n) as [H|H].
  - assert (H1: least p (G p d n)).
    { eapply G_least. exact H. lia. }
    destruct (nat_eqdec (G p d n) n) as [H2|H2].
    + left. congruence.
    + right. contradict H2. eapply least_unique; eassumption.
  - right. contradict H. apply H.
Qed.

(*** XM and least elements *)

Definition XM := forall P, P \/ ~P.

Fact xm_least_safe :
  XM -> forall p n, ex (least p) \/ safe p n.
Proof.
  intros H p.
  induction n as [|n IH].
  - right. apply safe_O.
  - destruct IH as [IH|IH].
    + left. exact IH.
    + specialize (H (p n)) as [H|H].
      * left. exists n. easy.
      * right. apply safe_S; assumption.
Qed.

Fact least_safe_ex_least :
  (forall p n, ex (least p) \/ safe p n) -> forall p, ex p -> ex (least p).
Proof.
  intros H p [n H1].
  specialize (H p n) as [H|H].
  * exact H.
  * exists n. easy.
Qed.

Fact ex_least_XM :
  (forall p, ex p -> ex (least p)) -> XM.
Proof.
  intros H P.
  destruct (H (fun x => if x then P else True)) as (n&H1&H2).
  + exists 1. exact I.
  + destruct n.
    * left. exact H1. 
    * right. intros H3. specialize (H2 0). hnf in H2. apply H2 in H3. lia.
Qed.


Fact ex_least_XM_equiv :
  (forall p, ex p -> ex (least p)) <-> XM.
Proof.
  split.
  - apply ex_least_XM.
  - intros H.  apply least_safe_ex_least, xm_least_safe, H.
Qed.
