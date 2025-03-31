From Coq Require Import Arith Lia.
Definition dec (X: Type) : Type :=  X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Definition nat_eqdec : eqdec nat.
Proof.
  hnf; induction x as [|x IH]; destruct y as [|y]; unfold dec in *.
  1-3: intuition congruence.
  destruct (IH y); intuition congruence.
Qed.
Notation sig := sigT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Definition injective {X Y} (f: X -> Y) := forall x x', f x = f x' -> x = x'.
Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).

Definition XM := forall P, P \/ ~P.

Implicit Types (n k : nat).

(*** Inductive Definition *)

(* We develop the inductive definition of lists from first principles
   not using Coq's automation support for inductive types. 
   This is for demonstration, not for practical use.
   Skip if not interested. *)       

Module IndDef.
Section IndDef.
  Variable X: Type.

  Inductive list: Type := nil | cons (x:X) (A: list).

  Implicit Types (x : X) (A B : list).

  Definition list_elim (p: list -> Type)
    : p nil -> (forall x A, p A -> p (cons x A)) -> forall A, p A
    := fun e1 e2 => fix f A := match A with nil => e1 | cons x A' => e2 x A' (f A') end.

  Fact cons_nil x A :
      cons x A <> nil.
  Proof.
    intros H.
    change (if cons x A then True else False).
    rewrite H. exact I.
  Qed.

  Fact cons_injective x x' A A' :
      cons x A = cons x' A' -> x = x' /\ A = A'.
  Proof.
    intros H. 
    change (match cons x A with nil => True | cons x A => x = x' /\ A = A' end).
    rewrite H. auto.
  Qed.

  Fact progress x A :
      cons x A <> A.
  Proof.
    revert A x.
    refine (list_elim _ _ _); intros x.
    - apply cons_nil.
    - intros A IH x'.
      intros [_ E] %cons_injective.
      eapply IH, E.
  Qed.

  Fact eqdec_list :
    eqdec X -> eqdec list.
  Proof.
    intros d. hnf.
    refine (list_elim _ _ _).
    - refine (list_elim _ _ _).
      + left. easy.
      + intros x B _. right.
        intros H; symmetry in H. revert H.
        apply cons_nil.
    - intros x A IH.
      refine (list_elim _ _ _).
      + right. apply cons_nil.
      + intros y B _.
        destruct (d x y) as [<- |H1].
        * specialize (IH B) as [<- |IH].
          -- left. easy.
          -- right. intros [_ E] %cons_injective. auto.
        * right. intros [E _] %cons_injective. auto.
  Qed.

  (* We now use Coq's automation support for inductive types *)

  Fact progress' x A :
      cons x A <> A.
  Proof.
    revert x.
    induction A as [|x A IH].
    - intros x [=].
    - intros x' [= -> H]. congruence. 
  Qed.

  Fact eqdec_list' :
    eqdec X -> eqdec list.
  Proof.
    intros d A B.
    induction A as [|x A IH] in B |-*;
      destruct B as [|y B].
    + left; easy.
    + right; easy.
    + right; easy.
    + destruct (d x y) as [<- |H1].
      * specialize (IH B) as [<- |H2].
        -- left. easy.
        -- right. intros [= <-]. auto.
      * right. intros [= <-]. auto.
  Qed.
End IndDef.
Check eqdec_list.
End IndDef.

(*** Membership *)

(* From now on we use Coq's predefined lists *)
From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Definition equi {X} (A B: list X) := A <<= B /\ B <<= A.
Notation "A == B" := (equi A B) (at level 70).


Fact eqdec_list X :
  eqdec X -> eqdec (list X).
Proof.
  intros d A B.
  induction A as [|x A IH] in B |-*;
    destruct B as [|y B].
  + left; easy.
  + right; easy.
  + right; easy.
  + destruct (d x y) as [<- |H1].
    * specialize (IH B) as [<- |H2].
      -- left. easy.
      -- right. intros [= <-]. auto.
    * right. intros [= <-]. auto.
Qed.

Section List.
  Variable X : Type.
  Implicit Types (x y : X) (A B : list X).
  
  Goal forall A B,
      length (A ++ B) = length A + length B.
  Proof.
    intros A B.
    induction A as [|x A IH]; cbn; congruence.
  Qed.
 
  Fact mem_ex x A :
    x el A -> exists A1 A2, A = A1 ++ x::A2.
  Proof.
    intros H.
    induction A as [|y A IH].
    - contradict H.
    - destruct H as [<-|H1].
      + exists [], A. reflexivity.
      + destruct (IH H1) as (A1&A2&->).
        exists (y::A1), A2. reflexivity.
  Qed.

  Variables X_eqdec: eqdec X.

  Fact mem_sum x a A :
    x el a :: A -> (x = a) + (x el A).
  Proof.
    intros H.
    destruct (X_eqdec x a) as [H1|H1].
    - left. exact H1.
    - right. destruct H as [H|H].
      + exfalso. auto.
      + exact H.
  Qed.
 
  Fact mem_sig x A :
    x el A -> Sigma A1 A2, A = A1 ++ x::A2.
  Proof.
    intros H.
    induction A as [|y A IH].
    - contradict H.
    - apply mem_sum in H as [<-|H1].
      + exists [], A. reflexivity.
      + destruct (IH H1) as (A1&A2&->).
        exists (y::A1), A2. reflexivity.
  Qed.
  
  Fact mem_dec x A :
    dec (x el A).
  Proof.
    induction A as [|a A IH].
    - right. auto.
    - destruct (X_eqdec x a) as [<-|H].
      + left. cbn. auto.
      + destruct IH as [IH|IH].
        * left. cbn. auto.
        * right. cbn. intuition.
  Qed.

  Definition list_dec (p: X -> Prop) A :
    decider p -> (Sigma x, x el A /\ p x) + (forall x, x el A -> ~p x).
  Proof.
    intros d.
    induction A as [|y A [(x&IH1&IH2)|IH]]; cbn.
    - intuition.
    - left. exists x. auto.
    - destruct (d y) as [H|H].
      + left. exists y. auto.
      + right. intros x [->|H1]; auto.
  Qed.

  (*** Inclusion and Equivalence *)

  Fact equi_refl A :
    A == A.
  Proof.
    unfold equi, incl. auto.
  Qed.
  
  Fact equi_symm A B :
    A == B -> B ==A.
  Proof.
    unfold equi, incl. intuition.
  Qed.
  
  Fact equi_trans A B C :
    A == B -> B == C -> A == C.
  Proof.
    unfold equi, incl. intuition.
  Qed.
 
  Fact mem_rear_ex {x A} :
    x el A -> exists A', A == x::A' /\ length A = S (length A').
  Proof.
    intros (A1&A2&->) %mem_ex.
    exists (A1++A2). split.
    - split; intros z; cbn; rewrite !in_app_iff; cbn; intuition.
      (* Note the use of setoid rewriting *)
    - rewrite !app_length. cbn. lia.
  Qed.

  (* Direct proof also possible *)
  Fact mem_rear_ex' {x A} :   
    x el A -> exists A', A == x::A' /\ length A = S (length A').
  Proof.     
    induction A as [|a A IH].
    - intros [].
    - intros [->|H].
      + exists A. split.
        * firstorder.
        * cbn. lia.
      + specialize (IH H) as (A'&IH1&IH2).
        exists (a::A'). split.
        * firstorder.
        * cbn. congruence.
  Qed.

  Fact mem_rear_sig {x A} :
    x el A -> Sigma A', A == x::A' /\ length A = S (length A').
  Proof.
    intros (A1&A2&->) %mem_sig.
    exists (A1++A2). cbn. split.
    - split; intros z; cbn; rewrite !in_app_iff; cbn; intuition.
    (* Note the use of setoid rewriting *)
    - rewrite !app_length. cbn. lia.
  Qed.
  
  (* Direct proof also possible *)
  Fact mem_rear_sig' {x A} :
    x el A -> Sigma A', A == x::A' /\ length A = S (length A').
  Proof.
    induction A as [|a A IH].
    - intros [].
    - intros [->|H] %mem_sum.
      + exists A. split.
        * firstorder.
        * cbn. lia.
      + specialize (IH H) as (A'&IH1&IH2).
        exists (a::A'). split.
        * firstorder.
        * cbn. congruence.
  Qed.

  (*** Nonrepeating Lists *)
  
  Fixpoint rep A : Prop :=
    match A with
    | [] => False
    | x::A => x el A \/ rep A
    end.
  
  Fixpoint nrep A : Prop :=
    match A with
    | [] => True
    | x::A => x nel A /\ nrep A
    end.
  
  Fact rep_nrep_False A :
    rep A -> nrep A -> False.
  Proof.
    induction A as [|x A IH]; cbn; tauto.
  Qed.

  Fact rep_plus_nrep A :
    rep A + nrep A.
  Proof.
    induction A as [|x A IH]; cbn.
    - auto.
    - destruct (mem_dec x A) as [H|H].
      + auto.
      + destruct IH as [IH|IH]; auto.
  Qed.

  Goal forall A, dec (rep A).
  Proof.
    intros A.
    generalize (rep_plus_nrep A), (rep_nrep_False A).
    unfold dec. tauto.
  Qed.

  Fact nrep_not_rep A :
    nrep A <-> ~rep A.
  Proof.
    generalize (rep_plus_nrep A), (rep_nrep_False A).
    tauto.
  Qed.

  Fact rep_not_nrep A :
    rep A <-> ~nrep A.
  Proof.
    generalize (rep_plus_nrep A), (rep_nrep_False A).
    tauto.
  Qed.

  Fact rep_sig A :
    rep A -> Sigma A1 x A2, A=A1++x::A2 /\ x el A2.
  Proof.
    induction A as [|x A IH].
    - intros [].
    - destruct (mem_dec x A) as [H|H].
      + intros _. exists [], x, A. easy.
      + intros H1.
        destruct IH as (A1&y&A2&IH1&IH2).
        * revert H H1. cbn. tauto.
        * subst A. exists (x::A1), y, A2. cbn. easy.
  Qed.

  Fact nrep_equiv :
    forall A, Sigma B, B == A /\ nrep B.
  Proof.
    induction A as [|x A (B&IH1&IH2)].
    - exists nil. cbn. auto using equi_refl.
    - destruct (mem_dec x A) as [H3|H3].
      + exists B. split. 2:exact IH2.
        split; intros z H.
        * cbn. right. apply IH1, H.
        * specialize H as [->|H]; apply IH1; assumption.
      + exists (x::B); cbn. split.
        * split; intros z [->|H]; cbn; auto; right; apply IH1, H.
        * split. 2: exact IH2. contradict H3. apply IH1, H3.
  Qed.
 
  Fact nrep_discriminate {A B} :
    nrep A -> length B < length A -> Sigma x, x el A /\ x nel B.
  Proof.
    induction A as [|a A IH] in B |-*; cbn.
    - lia.  (* computational falsity elimination *)
    - intros [H1 H2] H3.
      destruct (mem_dec a B) as [H|H].
      2: {exists a. auto. }
      destruct (mem_rear_sig H) as (B'&H4&H5).
      destruct (IH B' H2 ltac:(lia)) as (x&H6&H7).
      exists x. split.
      + auto.
      + contradict H7. apply H4 in H7 as [->|H7]; easy.
  Qed.
 
  Fact nrep_le A B :
    nrep A -> A <<= B -> length A <= length B.
  Proof.
    intros H1 H2.
    enough (length B < length A -> False) by lia.
    intros H3.
    destruct (nrep_discriminate H1 H3) as (x&H4&H5).
    auto.
   Qed.

  Fact nrep_length A B :
    nrep A -> nrep B -> A == B -> length A = length B.
  Proof.
    intros H1 H2 [H3 H4].
    enough (length A <= length B <= length A) by lia.
    split; eapply nrep_le; eassumption.
  Qed.

  Fact rep_length_lt A B :
    A <<= B -> length B < length A -> rep A.
  Proof.
    intros H1 H2. apply rep_not_nrep. intros H3.
    enough (length A <= length B) by lia.
    apply nrep_le; assumption.
  Qed.

  Fact nrep_nrep A B :
    nrep A -> A <<= B -> length B <= length A -> nrep B.
  Proof.
    intros H1 H2 H3.
    apply nrep_not_rep.
    intros (B1&x&B2&->&H5)%rep_sig.
    assert (H6: length A <= length (B1 ++ B2)).
    {  apply nrep_le. exact H1.
       intros z [H6|[<-|H6]] %H2 %in_app_iff; apply in_app_iff; auto. }
     revert H3 H6. rewrite !app_length. cbn. lia.
  Qed.

  Fact nrep_incl A B :
    nrep A -> A <<= B -> length B <= length A -> B <<= A.
  Proof.
    intros H1 H2 H3 x H4.
    destruct (mem_dec x A) as [H5|H5]. exact H5. exfalso.
    destruct (@nrep_discriminate (x::A) B) as (z&H6&H7).
    - easy.
    - cbn; lia.
    - destruct H6 as [->|H6]; auto.
  Qed.

  (* Proof not using discreteness *)
  Fact nrep_le_con A B : 
    nrep A -> A <<= B -> length A <= length B.
  Proof.
    (* Variant not using discreteness *)
    induction A as [|a A IH] in B |-*; cbn.
    - lia.
    - intros [H1 H2] H3.
      assert (a el B) as H by intuition.
      destruct (mem_rear_ex H) as (B'&H4&H5).
      enough (length A <= length B') by lia.
      apply IH. exact H2. firstorder congruence.
  Qed.

  (*** Coverings and Listings *)

  Definition covering A : Prop := forall x, x el A.
  Definition listing A : Prop := nrep A /\ covering A.

  Fact covering_listing A :
    covering A -> Sigma B: list X, listing B.
  Proof.
    intros H.
    destruct (nrep_equiv A) as (B&H1&H2).
    exists B. split. exact H2.
    intros x. apply H1, H.
  Qed.
  
  Fact listing_nrep A B :
    covering A -> nrep B -> length B <= length A.
  Proof.
    intros H1 H2. apply nrep_le. exact H2. intros x _. apply H1.
  Qed.

  Fact covering_nrep A B :
    covering A -> nrep B -> length A <= length B -> listing B.
  Proof.
    intros H1 H2 H3. split. exact H2.
    intros x. generalize (H1 x). revert x.
    eapply nrep_incl. exact H2. 2:exact H3.
    intros x _. apply H1.
  Qed.

  Fact listing_length_unique A B :
    listing A -> listing B -> length A = length B.
  Proof.
    intros H1 H2.
    apply nrep_length. {apply H1. } {apply H2. } split.
    - intros x _. apply H2.
    - intros x _. apply H1.
  Qed.
 
  
End List.

Arguments equi {X}.
Arguments list_dec {X}.
Arguments mem_dec {X}.
Arguments mem_sum {X}.
Arguments mem_rear_ex {X x A}.
Arguments nrep {X}.
Arguments rep {X}.

(*** Map *)

Fact map_injective {X Y f x A} :
  @injective X Y f -> f x el map f A -> x el A.
Proof.
  intros H (?&->%H&H2) %in_map_iff. exact H2.
Qed.

Fact nrep_map X Y f A :
  @injective X Y f -> nrep A -> nrep (map f A).
Proof.
  intros H.
  induction A as [|x A IH]; cbn.
  - auto.
  - intros [H2 H3]. split. 
    + contradict H2. eapply map_injective; eassumption.
    + auto.
Qed.

Lemma nrep_injective X Y (f: X -> Y) x x' A :
  f x = f x' -> x el A -> x' el A ->  nrep (map f A) -> x = x'.
Proof.
  intros H1.
  induction A as [|a A IH]; cbn.
  - intros [].
  - intros [->|H3] [->|H4] [H5 H6].
    + reflexivity.
    + contradict H5. apply in_map_iff. exists x'. easy.
    + contradict H5. apply in_map_iff. exists x. easy.
    + auto.
Qed.

(*** Lists of Numbers *)

Definition segment A := forall k, k el A <-> k < length A.
Definition serial (A: list nat) := forall n k, n el A -> k <= n -> k el A.

Fact segment_nil :
  segment [].
Proof.
  intros k. cbn; intuition; lia.
Qed.

Fact segment_equal A B :
  segment A -> segment B -> length A = length B -> A <<= B.
Proof.
  intros H1 H2 E x H3%H1. apply H2. lia.
Qed.

Fact segment_serial A :
  segment A -> serial A.
Proof.
  intros H1 n k H2 H3. apply H1. apply H1 in H2. lia.
Qed.

Definition segment_sigma :
  forall n, Sigma A, length A = n /\ nrep A /\ segment A.
Proof.
  induction n as [|n (A&IH1&IH2&IH3)].
  - exists [].  split. easy. split. easy. apply segment_nil.
  - exists (n::A). split; cbn. lia. split.
    + split. 2:exact IH2. intros H %IH3. lia.
    + intros k. split; cbn.
      * intros [<-|H %IH3]; lia.
      * intros H.
        destruct (nat_eqdec k n) as [->|H1]. now auto.
        right. apply IH3. lia.
Qed.

Fact segment_nrep A :
  segment A -> nrep A.
Proof.
  intros H1.
  destruct (segment_sigma (length A)) as (B&H2&H3&H4).
  eapply nrep_nrep. exact nat_eqdec. exact H3. 2:lia.
  apply segment_equal; easy.
Qed.

Definition nrep_nat_large_el {A: list nat} {n} :
  nrep A -> length A = S n -> Sigma k, k el A /\ k >= n.
Proof.
  intros H1 H2.
  destruct (list_dec (fun k => k >= n) A) as [(x&H3&H4)|H].
  - intros k.
    destruct (n-k) eqn:?; unfold dec; intuition lia.
  - eauto.
  - exfalso. (* computational exfalso *)
    destruct (segment_sigma n) as (B&H3&H4&H5).
    enough (length A <= length B) by lia.
    apply nrep_le. exact nat_eqdec. exact H1.
    intros x H6%H. apply H5; lia.
Qed.

Fact serial_segment A :
  serial A -> nrep A -> segment A.
Proof.
  intros H1 H2.
  destruct (length A) as [|n] eqn:E.
  - enough (A = []) as -> by apply segment_nil.
    destruct A. easy. cbn in E; lia.
  - destruct (nrep_nat_large_el H2 E) as (x&H4&H5).
    destruct (segment_sigma (S n)) as (B&H6&H7&H8).
    enough (equi A B) as [H9 H10].
    { hnf. hnf in H8. replace (length A) with (length B) by congruence.
      firstorder. }
    assert (H9: B <<= A).
    { intros k H9 %H8. eapply H1. exact H4. lia. }
    split. 2:exact H9.
    apply nrep_incl. exact nat_eqdec. exact H7. exact H9. lia.
Qed.

Fact nat_list_next :
  forall A: list nat, Sigma n, forall k, k el A -> k < n.
Proof.
  induction A as [|x A [n IH]].
  - exists 0. easy.
  - exists (S x + n). intros y [-> |H].
    + lia.
    + apply IH in H. lia.
Qed.

Fact infinite_list_next X :
  injection nat X -> forall A: list X, Sigma x, forall a, a el A -> a <> x.
Proof.
  intros [f g H] A.
  destruct (nat_list_next (map g A)) as [n H1].
  exists (f n). intros x H2 ->.
  enough (H3: g (f n) < n). { rewrite H in H3. lia. }
  apply H1. apply in_map_iff. eauto.
Qed.

(*** Position-Element Mappings *)
  
Section SubPos.
  Variable X : Type.
  Variable X_escape: X.
  Variable X_eqdec : eqdec X.
    
  Implicit Types (x : X) (A : list X).
 
  Fixpoint sub A n : X :=
    match A, n with
      [], _ => X_escape
    | x::A', 0 => x
    | x::A', S n' => sub A' n'
    end.

  Fixpoint pos A x : nat :=
    match A with
      [] => 0
    | y::A' => if X_eqdec y x then 0 else S (pos A' x)
    end.
  
  Fact sub_pos x A :
    x el A -> sub A (pos A x) = x.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [<-|H]. easy.
      intros [->|H1]. easy. auto.
  Qed.

  Fact pos_bnd A x :
    x el A -> pos A x < length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [->|H].
      + lia.
      + intros [->|H1].
        * easy.
        * apply IH in H1; lia.
  Qed.

  Fact sub_el A n :
    n < length A -> sub A n el A.
  Proof.
    induction A as [|y A IH] in n |-*; cbn.
    - lia.
    - destruct n.
      + auto.
      + intros H. right. apply IH. lia. 
  Qed.

  Fact pos_sub A n :
    nrep A -> n < length A -> pos A (sub A n) = n.
  Proof.
    induction A as [|y A IH] in n |-*.
    - cbn. lia.
    - intros [H1 H2] H3.
      destruct n as [|n]; cbn.
      { destruct X_eqdec as [_|H]. reflexivity. easy. }
      cbn in H3.
      destruct X_eqdec as [->|_].
      { contradict H1. apply sub_el. lia. }
      f_equal. apply IH. exact H2. lia.
  Qed.
End SubPos.

(*** Constructive Discrimination *)

Section Constructive.
  Variable X : Type.
  Implicit Types (x : X) (A : list X).
   
  Fact nrep_discriminate_ex {A B} :
    XM -> nrep A -> length B < length A -> exists x, x el A /\ x nel B.
  Proof.
    intros xm.
    induction A as [|a A IH] in B |-*; cbn.
    - lia.
    - intros [H1 H2] H3.
      destruct (xm (a el B)) as [H|H].
      2: {exists a. auto. }
      destruct (mem_rear_ex H) as (B'&H4&H5).
      destruct (IH B' H2 ltac:(lia)) as (x&H6&H7).
      exists x. split.
      + auto.
      + contradict H7. apply H4 in H7 as [->|H7]; easy.
  Qed.

  Fact neg_xm (P: Prop) {Q} :
    (P -> ~Q) -> (~P -> ~Q) -> ~Q.
  Proof.
    tauto.
  Qed.
  Fact neg_skip (Q: Prop) :
    Q -> ~ ~Q.
  Proof.
    tauto.
  Qed.
  Fact neg_skip' (P: Prop) {Q} :
    (P -> ~Q) -> ~ ~P -> ~Q.
  Proof.
    tauto.
  Qed.

  Fact nrep_discriminate_DN_ex {A B} :
    nrep A -> length B < length A -> ~ ~exists x, x el A /\ x nel B.
  Proof.
    induction A as [|a A IH] in B |-*; cbn.
    - lia.
    - intros [H1 H2] H3.
      apply (neg_xm (a el B)); intros H.
      2:{ apply neg_skip. exists a. auto. }
      destruct (mem_rear_ex H) as (B'&H4&H5).
      specialize (IH B' H2 ltac:(lia)).
      revert IH. apply neg_skip'. intros (x&H6&H7).
      apply neg_skip. exists x. split.
      + auto.
      + contradict H7. apply H4 in H7 as [->|H7]; easy.
  Qed.
End Constructive.

Section RemovalCard.
  Variable X : Type.
  Variable X_eqdec : eqdec X.
  Implicit Types (x : X) (A : list X).
 
  (*** Element Removal *)
  
  Fixpoint rem A x : list X :=
    match A with
      [] => []
    | y::A' => if X_eqdec y x then rem A' x else y::rem A' x
    end.

  Fact rem_el A x y :
    x el rem A y <-> x el A /\ x<> y.
  Proof.
    induction A as [|z A IH].
    - cbn. tauto.
    - cbn [rem].
      destruct (X_eqdec z y) as [<-|H]; cbn;
        intuition congruence.
  Qed.

  Fact rem_length_le A  x:
    length (rem A x) <= length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - lia.
    - destruct X_eqdec as [<-|H1]; cbn; lia.
  Qed.
  
  Fact rem_length_lt x A :
    x el A -> length (rem A x) < length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [->|H1].
      + generalize (rem_length_le A x). lia.
      + intros [->|H2]; cbn.
        * exfalso. easy.
        * apply IH in H2. lia.
  Qed.

  Fact rem_eq_nel A x :
    x nel A -> rem A x = A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros _. reflexivity.
    - destruct (X_eqdec y x) as [<-|H].
      + intros []. auto.
      + intros H1. f_equal. tauto.
  Qed.

  Fact rem_eq_cons x A :
    rem (x :: A) x = rem A x.
  Proof.
    cbn. destruct (X_eqdec x x) as [_|H]; tauto.
  Qed.

  Fact rem_eq_cons' x y A :
    x <> y -> rem (y::A) x = y::rem A x.
  Proof.
    cbn. destruct (X_eqdec y x) as [<-|H]; tauto.
  Qed.

  (*** Cardinality *)

  Fixpoint card A : nat :=
    match A with
      [] => 0
    | x:: A' => if mem_dec X_eqdec x A' then card A' else S (card A')
    end.

  Fact card_sig :
    forall A, Sigma B, B == A /\ nrep B /\ length B = card A.
  Proof.
    induction A as [|x A (B&IH1&IH2&IH3)]; cbn.
    - exists []. cbv; auto.
    - destruct mem_dec as [H|H].
      + exists B.
        enough (B == x :: A) by auto.
        split; intros z H1.
        * right. apply IH1, H1.
        * apply IH1. destruct H1 as [->|H1]; assumption.
      + exists (x::B). cbn. split. 2:split.
        *  split; intros z [->|H1].
           -- cbn. auto.
           -- right. apply IH1, H1.
           -- cbn; auto.
           -- right. apply IH1, H1.
        * split. 2: exact IH2. contradict H. apply IH1, H.
        * lia.
  Qed.

  Fact  card_agree A n :
    card A = n <-> exists B, B == A /\ nrep B /\ length B = n.
  Proof.
    split.
    - intros <-.
      destruct (card_sig A) as (B&H). exists B. exact H.
    - intros (B&H1&H2&<-).
      destruct (card_sig A) as (C&H4&H5&<-).
      apply nrep_length. 1-3:assumption.
      eapply equi_trans. exact H4. apply equi_symm, H1.
  Qed.
      
  Fact card_length A :
    card A <= length A.
  Proof.
    destruct (card_sig A) as (A'&H1&H2&<-).
    apply nrep_le. 1-2:easy. apply H1.
  Qed.
 
  Fact card_le A B :
    A <<= B -> card A <= card B.
  Proof.
    destruct (card_sig A) as (A'&H1&H2&<-).
    destruct (card_sig B) as (B'&H3&H4&<-).
    intros H5. eapply nrep_le. 1-2:easy. 
    intros z H6. apply H3, H5, H1, H6.
  Qed.
 
  Fact card_eq A B :
    A == B -> card A = card B.
  Proof.
    intros H.
    enough (card A <= card B /\ card B <= card A) by lia.
    split; apply card_le, H.
  Qed.
 
  Fact rep_card_length A :
    rep A <-> card A < length A.
  Proof.
    destruct (card_sig A) as (A'&H1&H2&<-).
    split.
    - intros H3.
      enough (length A <= length A' -> False) by lia. intros H4.
      eapply rep_not_nrep. easy. exact H3.
      eapply nrep_nrep. easy. exact H2. apply H1. exact H4.
    - apply rep_length_lt. easy. apply H1.
  Qed.
 
  Fact nrep_card_length A :
    nrep A <-> card A = length A.
  Proof.
    (* Note the use of setoid rewriting *)
    rewrite nrep_not_rep, rep_card_length.
    generalize (card_length A). lia. easy.
  Qed.

  Fixpoint Card A n : Prop :=
    match A, n with
    | nil, 0 => True
    | nil, S n' => False
    | x::A', 0 => False
    | x::A', S n' => if mem_dec X_eqdec x A' then Card A' (S n') else Card A' n'
    end.

  Fact Card_card A :
    Card A (card A).
  Proof.
    induction A as [|x A IH].
    - exact I.
    - cbn. destruct mem_dec as [H|H].
      + destruct A as [|y A].
        * destruct H.
        * exact IH.
      + exact IH.
  Qed.

  Fact Card_agree A n :
    Card A n <-> card A = n.
  Proof.
    split.
    - induction A as [|x A IH] in n |-*; destruct n; cbn.
      + auto.
      + intros [].
      + intros [].
      + destruct mem_dec as [H|H].
        * apply IH.
        * intros <-%IH. reflexivity.
    - intros <-.
      induction A as [|x A IH].
      + exact I.
      + cbn. destruct mem_dec as [H|H].
        * destruct A as [|y A].
          -- destruct H.
          -- exact IH.
        * exact IH.
    Qed.

  Fact card_rem_eq A x :
    x el A -> card A = S (card (rem A x)).
  Proof.
    intros H.
    replace (card A) with (card (x::(rem A x))).
    - cbn. destruct mem_dec as [H1|H1].
      + exfalso. apply rem_el in H1. apply H1. reflexivity.
      + reflexivity.
    - apply card_eq. split; intros z H1.
      + destruct H1 as [->|H1%rem_el]. exact H. apply H1.
      + cbn. destruct (X_eqdec x z) as [<-|H2].
        * auto.
        * right. apply rem_el. auto.
  Qed.

  Fixpoint disjoint A B : Prop :=
    match A with
      [] => True
    | x::A' => x nel B /\ disjoint A' B
    end.
  
  Goal forall A B, disjoint A B <-> ~ exists z, z el A /\ z el B.
  Proof.
    intros A B.
    induction A as [|x A IH]; cbn.
    - firstorder.
    - split.
      + intros [H1 H2] [z [H3 H4]].
        apply IH. exact H2. exists z. intuition congruence.
      + intros H. split.
        * eauto 6.
        * apply IH. intros (z&H1&H2). eauto.
  Qed.
End RemovalCard.

(*** Exercises: List Reversal *)

Section Reversal.
  Variable X : Type.
  Implicit Types (x: X) (A B: list X).

  Fact rev_app A B :
    rev (A ++ B) = rev B ++ rev A.
  Proof.
    induction A as [|x A IH]; cbn.
    - symmetry. apply app_nil_r.
    - rewrite IH.  symmetry. apply app_assoc.
  Qed.

  Fact rev_rev A :
    rev (rev A) = A.
  Proof.
    induction A as [|x A IH]; cbn.
    - reflexivity.
    - rewrite rev_app, IH. reflexivity.
  Qed.

  Fact rev_in x A :
    x el A <-> x el rev A.
  Proof.
    induction A as [|y A IH]; cbn.
    - easy.
    - split.
      + intros [->|H]; apply in_or_app.
        * cbn. auto.
        * left. apply IH, H.
      + intros [H|H] %in_app_or.
        * right. apply IH, H.
        * left. destruct H; easy.
  Qed.
  
  Fact nrep_snoc A x :
    nrep A -> x nel A -> nrep (A ++ [x]).
  Proof.
    induction A as [|y A IH]; cbn.
    - easy.
    - intros [H1 H2] H3. split.
      + contradict H1.
        apply in_app_or in H1 as [H1|H1].
        * exact H1.
        * contradict H3. left. destruct H1; easy.
      + apply IH. exact H2. contradict H3. right. exact H3.
  Qed.
  
  Fact rev_nrep A :
    nrep A -> nrep (rev A).
  Proof.
    induction A as [|x A IH]; cbn.
    - reflexivity.
    - intros [H1 H2%IH]. apply nrep_snoc. exact H2.
      contradict H1. apply rev_in, H1.
  Qed.

  Fact list_rec_snoc (p: list X -> Type) :
    p [] ->
    (forall x A, p A -> p (A ++ [x])) ->
    forall A, p A.
  Proof.
    intros e1 e2.
    enough (forall A, p (rev A)) as H.
    { intros A. rewrite <-rev_rev. apply H. }
    induction A as [|x A IH].
    - exact e1.
    - apply e2, IH.
  Qed.

 End Reversal.

(*** Exrcise: seq *)
  
Fixpoint seq n k : list nat :=
  match k with
    0 => []
  | S k' => n :: seq (S n) k'
  end.

Fact seq_length n k :
  length (seq n k) = k.
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Fact seq_in x n k :
  x el seq n k <-> n <= x < n + k.
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - lia.
  - rewrite IH. lia.
Qed.

Fact seq_nrep n k :
  nrep (seq n k).
Proof.
  induction k as [|k IH] in n |-*; cbn.
  - exact I.
  - rewrite seq_in. split. lia. apply IH.
Qed.

Fact nat_list_le (A: list nat) n :
  (Sigma k, k el A /\ k >= n) + forall k, k el A -> k < n.
Proof.
  induction A as [|x A IH].
  - right. easy.
  - destruct (le_lt_dec n x) as [H|H].
    + left. exists x. cbn;auto.
    + destruct IH as [(k&H1&H2)|H1].
      * left. exists k. cbn. auto.
      * right. intros k [<-|H3]; auto.
Qed.

Fact nat_list_nrep (A: list nat) n :
  nrep A -> length A = S n -> Sigma k, k el A /\ k >= n.
Proof.
  intros H1 H2.
  destruct (nat_list_le A n) as [H|H]. exact H.
  exfalso. (* computational exfalso *)
  enough (length A <= n) by lia.
  rewrite <-(seq_length 0 n).
  apply nrep_le. exact nat_eqdec. exact H1.
  intros k H3. apply seq_in. apply H in H3. lia.
Qed.
