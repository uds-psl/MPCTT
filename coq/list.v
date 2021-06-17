From Coq Require Import Arith Lia.
Unset Elimination Schemes.
Definition dec (X: Type) := sum X (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition nat_eqdec : eqdec nat :=
  fun x y => match Nat.eq_dec x y with left H => inl H | right H => inr H end.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Module Scratch.
Section Scratch.
  Variable X: Type.

  Inductive list: Type := nil | cons (x:X) (A: list).

  Implicit Types (x y z: X) (A B C: list).

  Definition list_elim (p: list -> Type)
    : p nil -> (forall x A, p A -> p (cons x A)) -> forall A, p A
    := fun a f => fix F A := match A with nil => a | cons x A' => f x A' (F A') end.

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

  Goal forall x A,
      cons x A <> A.
  Proof.
    intros *; revert A x.
    refine (list_elim _ _ _).
    - intros x. apply cons_nil.
    - intros x A H1 x' H2. eapply H1, cons_injective, H2.
  Qed.
End Scratch.
End Scratch.

(* From now on we use Coq's predefined lists *)
From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).

Section List.
  Variable X : Type.
  Variables X_eqdec: eqdec X.
  Implicit Types (x y z : X) (A B C : list X).

  Goal forall x A,
      x::A <> A.
  Proof.
    induction A as [|y A IH].
    - intros [=].
    - intros [= <- H]. easy. 
  Qed.

  Goal forall A B,
      length (A ++ B) = length A + length B.
  Proof.
    intros A B.
    induction A as [|x A IH]; cbn.
    - reflexivity.
    - f_equal. exact IH.
  Qed.

  Goal eqdec X -> eqdec (list X).
  Proof.
    intros H A B.
    induction A as [|x A IH] in B |-*; destruct B as [|y B].
    - left. reflexivity.
    - right. intros [=].
    - right. intros [=].
    - specialize (H x y) as [<-|H].
      + specialize (IH B) as [<-|IH].
        * left. reflexivity.
        * right. intros [= <-]. easy.
      + right. intros [= <- _]. easy.
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
        * right. cbn.  intuition.
  Qed.

  (*** Inclusion and Equivalence *)
 
  Fact mem_sigma x A :
    x el A -> Sigma A1 A2, A = A1 ++ x::A2.
  Proof.
    intros H.
    induction A as [|y A IH].
    - contradict H.
    - destruct (X_eqdec x y) as [<-|H1].
      + exists [], A. reflexivity.
      + destruct IH as (A1&A2&IH).
        * destruct H as [<-|H]; intuition.
        * exists (y::A1), A2. rewrite IH. reflexivity.
  Qed.

  Definition equi A B := A <<= B /\ B <<= A.
  Notation "A == B" := (equi A B) (at level 70).
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


  (*** Non-Repeating Lists *)
  
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

  Fact rep_sigma A :
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
    nrep A -> length B < length A -> Sigma z, z nel B /\ z el A.
  Proof.
    induction A as [|x A IH] in B |-*; cbn.
    - lia.
    - destruct (mem_dec x B) as [H|H].
      2:{ intros _ _. exists x. auto. }
      intros [H1 H2] H3.
      specialize (IH (rem B x) H2) as (z&H4&H5).
      + apply rem_length_lt in H. lia.
      + exists z. split. 2:{ auto. }
        destruct (X_eqdec z x) as [->|H6]. 1:tauto.
        contradict H4. apply rem_el. easy.
  Qed.
 
  Fact nrep_le A B :
    nrep A -> A <<= B -> length A <= length B.
  Proof.
    intros H1 H2.
    enough (length B < length A -> False) by lia.
    intros H3.
    destruct (nrep_discriminate H1 H3) as (x&H4&H5).
    apply H4, H2, H5.
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

  Fact nrep_incl A B :
    nrep A -> A <<= B -> length B <= length A -> B <<= A.
  Proof.
    intros H1 H2 H3 x H4.
    destruct (mem_dec x A) as [H5|H5]. exact H5. exfalso.
    destruct (@nrep_discriminate (x::A) B) as (z&H6&H7); cbn.
    - easy.
    - lia.
    - destruct H7 as [->|H7]; auto.
  Qed.

  Fact nrep_nrep A B :
    nrep A -> A <<= B -> length B <= length A -> nrep B.
  Proof.
    intros H1 H2 H3.
    apply nrep_not_rep.
    intros (B1&x&B2&->&H5)%rep_sigma.
    assert (H6: length A <= length (B1 ++ B2)).
    {  apply nrep_le. exact H1.
       intros z [H6|[<-|H6]] %H2 %in_app_iff; apply in_app_iff; auto. }
     revert H3 H6. rewrite !app_length. cbn. lia.
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

  (*** Cardinality *)

  Fixpoint card A : nat :=
    match A with
      [] => 0
    | x:: A' => if mem_dec x A' then card A' else S (card A')
    end.

  Fact card_sigma :
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
      destruct (card_sigma A) as (B&H). exists B. exact H.
    - intros (B&H1&H2&<-).
      destruct (card_sigma A) as (C&H4&H5&<-).
      apply nrep_length. 1-2:assumption.
      eapply equi_trans. exact H4. apply equi_symm, H1.
  Qed.
      

  Fact card_length A :
    card A <= length A.
  Proof.
    destruct (card_sigma A) as (A'&H1&H2&<-).
    apply nrep_le. exact H2. apply H1.
  Qed.
 
  Fact card_le A B :
    A <<= B -> card A <= card B.
  Proof.
    destruct (card_sigma A) as (A'&H1&H2&<-).
    destruct (card_sigma B) as (B'&H3&H4&<-).
    intros H5. eapply nrep_le. exact H2.
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
    destruct (card_sigma A) as (A'&H1&H2&<-).
    split.
    - intros H3.
      enough (length A <= length A' -> False) by lia. intros H4.
      eapply rep_not_nrep. exact H3.
      eapply nrep_nrep. exact H2. apply H1. exact H4.
    - apply rep_length_lt, H1.
  Qed.
 
  Fact nrep_card_length A :
    nrep A <-> card A = length A.
  Proof.
    (* Note the use of setoid rewriting *)
    rewrite nrep_not_rep, rep_card_length.
    generalize (card_length A). lia. 
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

  Fixpoint Card A n : Prop :=
    match A, n with
    | nil, 0 => True
    | nil, S n' => False
    | x::A', 0 => False
    | x::A', S n' => if mem_dec x A' then Card A' (S n') else Card A' n'
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

  (*** Sub and Pos *)
  
  Section SubPos.
  Variable X_escape: X.
  
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

  Fact sub_neq A n :
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
      { contradict H1. apply sub_neq. lia. }
      f_equal. apply IH. exact H2. lia.
  Qed.
  End SubPos.

  (*** Disjointness *)

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

End List.
Arguments nrep {X}.
Arguments rep {X}.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Fact nrep_map X Y (f: X -> Y) A :
  injective f -> nrep A -> nrep (map f A).
Proof.
  intros H1.
  induction A as [|x A IH]; cbn.
  - auto.
  - intros [H2 H3].
    split. 2:{ apply IH, H3. }
    intros (x'&H4&H5)%in_map_iff.
    apply H1 in H4 as ->.
    auto.
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
  exfalso.
  enough (length A <= n) by lia.
  rewrite <-(seq_length 0 n).
  apply nrep_le. exact nat_eqdec. exact H1.
  intros k H3. apply seq_in. apply H in H3. lia.
Qed.


(*** Constructive Discrimination Lemma *)

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
  
Section Discrimination.
  Variable X: Type.
  Implicit Types (x: X) (A B: list X).

  Lemma lem1 {x A} :
    x el A -> exists B, A <<= x::B /\ length B < length A.
  Proof.
     induction A as [|a A' IH]; cbn.
    - intros [].
    - intros [->|H].
      + exists A'. split. now intuition. lia.
      + specialize (IH H) as (B&H1&H2).
        exists (a::B). split. now firstorder. cbn; lia.
  Qed.
  
  Fact fac1 A B :
    (forall P, P \/ ~P) -> 
    length B < length A -> nrep A -> exists x, x el A /\ x nel B.
  Proof.
    intros xm.
    induction A as [|a A' IH] in B |-*; cbn; intros H.
    - exfalso. lia.
    - intros [H1 H2].
      destruct (xm (a el B)) as [H3|H3].
      2:{ exists a. auto. }
      destruct (lem1 H3) as (B'&H4&H5).
      specialize (IH B') as (x&H6&H7). lia. exact H2.
      exists x. split. 1:{ auto. }
      intros H8. apply H4 in H8 as [<-|H8]; easy.
  Qed.

  Fact fac2 A B :
    length B < length A -> nrep A -> ~ ~exists x, x el A /\ x nel B.
  Proof.
    induction A as [|a A' IH] in B |-*; cbn; intros H.
    - exfalso. lia.
    - intros [H1 H2].
      apply (neg_xm (a el B)); intros H3.
       2:{ apply neg_skip. exists a. auto. }
       destruct (lem1 H3) as (B'&H4&H5).
       specialize (IH B').
       assert (H6: length B' < length A') by lia.
       specialize (IH H6 H2). revert IH.
       apply neg_skip'. intros (x&H7&H8). apply neg_skip.
       exists x. split. 1:{ auto. } 
       intros H9. apply H4 in H9 as [<-|H9]; easy.
  Qed.
End Discrimination.

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

