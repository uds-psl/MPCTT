From Coq Require Import Arith Lia List.
Implicit Types n k : nat.

Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec P := {P} + {~P}.
Notation decider p := (forall x, dec (p x)).
Definition eqdec X :=
  forall x y: X, dec (x = y).
Fact nat_eqdec : eqdec nat.
Proof.
  exact Nat.eq_dec.
Qed.
Definition option_eqdec X : eqdec X -> eqdec (option X).
Proof.
  intros H [x|] [y|].
  - specialize (H x y) as [<-|H].
    + left. reflexivity.
    + right. intros [= <-]. auto.
  - right. intros [=].
  - right. intros [=].
  - left. reflexivity.
Defined.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H F x x'.
  destruct (F (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. congruence.
Qed.

Notation pi1 := projT1.
Notation pi2 := projT2.

Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).

Fact map_in_ex X Y  (f: X -> Y) y A :
  y el map f A -> exists x, f x = y.
Proof.
  intros (x&H&_)%in_map_iff. eauto.
Qed.

Fixpoint deopt {X} (A: list (option X)) : list X :=
  match A with
  | [] => []
  | Some x::A' => x :: deopt A'
  | None::A' => deopt A'
  end.

Fact deopt_in X (x: X) A :
  x el deopt A <-> Some x el A.
Proof.
  induction A as [|a A IH]; cbn.
  - tauto.
  - destruct a as [y|]; cbn; intuition congruence.
Qed.

Section List.
  Variable X : Type.
  Variables X_eqdec: eqdec X.
  Implicit Types (x y z: X) (A B: list X).
  
  Definition equi A B := A <<= B /\ B <<= A.
  Notation "A == B" := (equi A B) (at level 70).
  Fact equi_refl A :
    A == A.
  Proof.
    unfold equi, incl. auto.
  Qed.

  Fact mem_dec x A :
    dec (x el A).
  Proof.
    apply In_dec, X_eqdec.
  Qed.

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
        intuition; congruence.
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
        * exfalso; auto.
        * apply IH in H2. lia.
  Qed.

  Fixpoint nrep A : Prop :=
    match A with
    | [] => True
    | x::A => x nel A /\ nrep A
    end.
 
  Fact nrep_discriminate A B :
    nrep A -> length B < length A -> { z & z nel B /\ z el A }.
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
        contradict H4. apply rem_el. auto.
  Qed.
 
  Fact nrep_le A B :
    nrep A -> A <<= B -> length A <= length B.
  Proof.
    intros H1 H2.
    enough (length B < length A -> False) by lia.
    intros H3.
    edestruct nrep_discriminate as (x&H4&H5).
    exact H1. exact H3. apply H4, H2, H5.
  Qed.

  Fact nrep_incl A B :
    nrep A -> A <<= B -> length B <= length A -> B <<= A.
  Proof.
    intros H1 H2 H3 x H4.
    destruct (mem_dec x A) as [H5|H5]. exact H5. exfalso.
    destruct (@nrep_discriminate (x::A) B) as (z&H6&H7); cbn.
    - auto.
    - lia.
    - destruct H7 as [->|H7]; auto.
  Qed.
 
  Fixpoint rep A : Prop :=
    match A with
    | [] => False
    | x::A => x el A \/ rep A
    end.

  Fact rep_sigma A :
    rep A -> {A1 &{x &{A2 | A=A1++x::A2 /\ x el A2 }}}.
  Proof.
    induction A as [|x A IH].
    - intros [].
    - destruct (mem_dec x A) as [H|H].
      + intros _. exists [], x, A. auto.
      + intros H1.
        destruct IH as (A1&y&A2&IH1&IH2).
        * revert H H1. cbn. tauto.
        * subst A. exists (x::A1), y, A2. cbn. auto.
  Qed.
   
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

  Fact nrep_not_rep A :
    nrep A <-> ~rep A.
  Proof.
    generalize (rep_plus_nrep A), (rep_nrep_False A).
    tauto.
  Qed.

  Fact nrep_nrep A B :
    nrep A -> A <<= B -> length B <= length A -> nrep B.
  Proof.
    intros H1 H2 H3.
    apply nrep_not_rep.
    intros (B1&x&B2&->&H5)%rep_sigma.
    assert (H6: length A <= length (B1 ++ B2)).
    {  apply nrep_le.  exact H1.
       intros z [H6|[<-|H6]] %H2 %in_app_iff; apply in_app_iff; auto. }
     revert H3 H6. rewrite !app_length. cbn. lia.
  Qed.

  Fact nrep_equiv :
    forall A, { B & B == A /\ nrep B }.
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

  (* Sub and Pos *)

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
    - destruct X_eqdec as [<-|H].
      { auto. }
      intros [->|H1].
      { exfalso; auto. }
      auto.
  Qed.

  Fact pos_bnd A x :
    x el A -> pos A x < length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - intros [].
    - destruct X_eqdec as [->|H].
      + lia.
      + intros [->|H1].
        * exfalso; auto. 
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
      { destruct X_eqdec as [_|H]. reflexivity. exfalso; auto. }
      cbn in H3.
      destruct X_eqdec as [->|_].
      { contradict H1. apply sub_neq. lia. }
      f_equal. apply IH. exact H2. lia.
  Qed.
End List.
Arguments mem_dec {X}.
Arguments sub {X}.
Arguments pos {X}.
Arguments nrep {X}.
Arguments nrep_equiv {X}.
Arguments nrep_discriminate {X}.

Lemma nrep_map X Y (f: X -> Y) A :
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
  nrep (map f A) -> x el A -> x' el A -> f x = f x' -> x = x'.
Proof.
  induction A as [|a A IH]; cbn.
  - intros _ [].
  - intros  [H5 H6] [->|H3] [->|H4] H.
    + reflexivity.
    + eapply IH; try eassumption. contradict H5. apply in_map_iff. eauto.
    + eapply IH; try eassumption. contradict H5. apply in_map_iff. eauto.
    + eauto.
Qed.

Definition inv {X Y} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Definition bijection  X Y :=
  { f: X -> Y & { g & inv g f  /\ inv f g}}.

Fact bijection_refl {X} :
  bijection X X.
Proof.
  exists (fun x => x), (fun x => x). cbv. auto.
Qed.

Fact bijection_sym {X Y} :
  bijection X Y -> bijection Y X.
Proof.
  intros (f&g&H&H'). exists g, f. split; trivial. 
Qed.

Fact bijection_eqdec X Y :
  bijection X Y -> eqdec X -> eqdec Y.
Proof.
  intros (f&g&H). eapply injective_eqdec, inv_injective, H.
Qed.

Definition inv1 {X Y} (f: X -> Y) (g: Y -> option X) :=
  forall x, g (f x) = Some x.
Definition inv2 {X Y} (g: Y -> option X) (f: X -> Y) :=
  forall x y, g y = Some x -> f x = y.
Definition injection X Y :=
  { f & { g & @inv1 X Y f g /\ inv2 g f }}.
Definition dat X :=
  injection X nat.

Fact inv1_injective X Y (f: X -> Y) g :
  inv1 f g -> injective f.
Proof.
  intros H x x'. generalize (H x), (H x'). congruence.
Qed.

Fact injection_injective {X Y} :
  forall C: injection X Y,  injective (pi1 C).
Proof.
  intros (f&g&H1&H2). cbn. eapply inv1_injective, H1.
Qed.

Fact injection_refl {X} :
  injection X X.
Proof.
  exists (fun x => x), (fun x => Some x). cbv.
  split. reflexivity. congruence.
Qed.

Fact injection_eqdec X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros H1 H2.
  eapply injective_eqdec. 2:exact H2.
  exact (injection_injective H1).
Qed.

Fact injection_upgrade X Y :
  eqdec Y -> {f & {g | @inv1 X Y f g}} -> injection X Y.
Proof.
  intros D (f&g&H1).
  exists f.
   exists (fun y => match g y with
           | Some x => if D (f x) y then Some x else None
           | None => None
           end).
  split; hnf.
  - intros x. rewrite (H1 x). destruct D; congruence.
  - intros x y. specialize (H1 x). destruct (g y) as [x'|].
    + destruct D; congruence.
    + intros [=].
Qed.
 
Definition infinite X : Prop := forall A: list X, exists x, x nel A.

Fact nat_infinite :
  infinite nat.
Proof.
  enough (forall A, exists n, forall x, x el A -> x < n) as H.
  { intros A. specialize (H A) as [n H]. exists n. intros H1%H. lia. }
  induction A as [|x A IH]; cbn.
  - exists 0. intros x [].
  - destruct IH as [n IH]. exists (S n + x).
    intros y [<-|H%IH]; lia.
Qed.

Fact injection_infinite_transport X Y :
  injection X Y -> infinite X -> infinite Y.
Proof.
  intros (f&g&E1&E2) F B.
  destruct (F (deopt (map g B))) as [x H].
  exists (f x). contradict H.
  apply deopt_in, in_map_iff. exists (f x). auto.
Qed.

(*** Coverings and Listings *)

Definition covering {X} (A: list X) :=
  forall x, x el A.
Definition listing {X} (A: list X) :=
  nrep A /\ covering A.

Section CoveringListing.
  Variable X: Type.
  Variable X_eqdec: eqdec X.
  Implicit Types A B : list X.

  Fact covering_listing A :
    covering A -> { B: list X | listing B }.
  Proof.
    intros H.
    destruct (nrep_equiv X_eqdec A) as (B&H1&H2).
    exists B. split. exact H2.
    intros x. apply H1, H.
  Qed.
  
  Fact listing_length_unique A B :
    listing A -> listing B -> length A = length B.
  Proof.
    intros [H1 H2] [H3 H4].
    enough (length A <= length B /\ length B <= length A) by lia.
    split; apply nrep_le; try assumption.
    - intros x _. apply H4.
   - intros x _. apply H2.
  Qed.

  Fact nrep_iff_covering A B :
    listing A -> length B = length A -> (nrep B <-> covering B).
  Proof.
    intros [H1 H2] H3.
    split; intros H.
    - intros x.
      eapply nrep_incl. 1,2:assumption. 3:apply H2. 2:lia.
      intros x' _. apply H2.
    - eapply nrep_nrep. 1,2: eassumption. 2:lia.
      intros x _; apply H.
  Qed.
 
End CoveringListing.
Arguments covering_listing {X}.

(*** Finite Types *)

Definition finite X : Type :=
  eqdec X * sigT (@covering X).
Definition fin n X : Type :=
  eqdec X * { A: list X | listing A /\ length A = n }.

Fact finite_fin X :
  finite X <=> { n & fin n X }.
Proof.
  split.
  - intros [D [A H]].
    destruct (covering_listing D A H) as [B H1].
    exists (length B). split. exact D. exists B. auto.
  - intros [_ [D (A&[_ H]&_)]]. hnf. eauto.
Qed.

Fact fin_unique X m n :
  fin m X -> fin n X -> m = n.
Proof.
  intros [D (A&H1&H2)] [_ (B&H3&H4)].
  subst m n. apply listing_length_unique; assumption.
Qed.

Fact fin_dat X :
  finite X -> dat X.
Proof.
  intros (D&A&H1).
  apply injection_upgrade. exact nat_eqdec.
  destruct A as [|a A].
  - exists (fun x => 0), (fun n => None).
    intros x. contradiction (H1 x).
  - exists (pos D (a::A)), (fun n => Some (sub a (a::A) n)).
    intros x. f_equal. rewrite sub_pos; trivial.
Qed.

Fact fin_not_infinite X :
  finite X -> infinite X -> False.
Proof.
  intros (D&A&H) F. destruct (F A) as [x H1]. apply H1, H.
Qed.

Fact injection_nat_not_finite X :
  injection nat X -> finite X -> False.
Proof.
  intros H1 H2.
  eapply fin_not_infinite. exact H2.
  eapply injection_infinite_transport. exact H1.
  exact nat_infinite.
Qed.

Fact fin_fun_injective_surjective X Y n f :
  fin n X -> fin n Y -> @injective X Y f <-> surjective f. 
Proof.
  intros (_&A&[H0 H1]&<-) (E&B&H2&H3).
  assert (H4: nrep (map f A) <-> covering (map f A)).
  { eapply nrep_iff_covering. exact E. exact H2. rewrite H3. apply map_length. }
  split; intros H.
  - enough (covering (map f A)) as H5.
    { intros y. eapply map_in_ex, H5. }
    apply H4. apply nrep_map; assumption.
  - intros x x'. eapply nrep_injective. 2,3:apply H1.
    clear x x'. apply H4. intros y. specialize (H y) as [x H].
    eapply in_map_iff; eauto.
 Qed.
    
(*** Finite Ordinals *)

Fixpoint Fin n : Type :=
  match n with 0 => False | S n' => option (Fin n') end.

Fact fin_eqdec n :
  eqdec (Fin n).
Proof.
  induction n as [|n IH]; cbn.
  - intros [].
  - apply option_eqdec, IH.
Qed.

Fact Fin_listing n :
  { A : list (Fin n) | listing A /\ length A = n }.
Proof.
  induction n as [|n (A&IH1&IH2)].
  - exists nil. split. 2:reflexivity. split. constructor. intros []. 
  - exists (None:: map Some A). cbn. split. 1:split.
    + cbn. split.
      * intros (a&[=]&_)%in_map_iff.
      * apply nrep_map. 2:{ apply IH1. }
        intros k l [= <-]. reflexivity.
    + intros [a|]. 2: now left.
      right. apply in_map, IH1.
    + f_equal. rewrite <- IH2. apply map_length.
Qed.

Fact fin_Fin n :
  fin n (Fin n).
Proof.
  split. apply fin_eqdec. apply Fin_listing.
Qed.  

Fact Fin_forall_dec n X (f: Fin n -> X) (p: X -> Prop) :
  (forall x, dec (p x)) -> dec (forall a, p (f a)).
Proof.
  intros F.
  induction n as [|n IH].
  - left. intros [].
  - specialize (IH (fun a => f (Some a))) as [IH|IH].
    + destruct (F (f None)) as [H|H].
      * left. intros [a|]. exact (IH a). exact H.
      * right. intros H1. contradiction (H (H1 None)).
    + right. contradict IH. intros a. apply IH.
Qed.

Fact Fin_exists_dec n X (f: Fin n -> X) (p: X -> Prop) :
  (forall x, dec (p x)) -> dec (exists a, p (f a)).
Proof.
  intros F.
  induction n as [|n IH].
  - right. intros [[] _].
  - specialize (IH (fun a => f (Some a))) as [IH|IH].
    +  left. destruct IH as [a IH]. eauto.
    + destruct (F (f None)) as [H|H].
      * left. eauto.
      * right. intros [[a|] H1]; eauto.
Qed.

Goal forall m n, m = n -> Fin m = Fin n.
Proof.
  intros m n ->. reflexivity.
Qed.

(*** Bijections *)
  
Fact bijection_fin_fin X Y n :
  bijection X Y -> fin n X -> fin n Y.
Proof.
  intros H (D&A&H2&H3). hnf.
  split.
  { eapply bijection_eqdec; eassumption. }
  destruct H as (f&g&H1).
  exists (map f A). split.
  2:{ rewrite <- H3. apply map_length. }
  split.
  - apply nrep_map.
    + eapply inv_injective, H1.
     + apply H2.
  - intros x. eapply in_map_iff. exists (g x). split.
    + apply H1.
    + apply H2.
Qed.

Fact fin_fin_bijection n X Y:
  fin n X -> fin n Y -> bijection X Y.
Proof.
  (* beautiful proof script *)
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6).
  destruct n as [|n], A as [|a A], B as [|b B];
    try discriminate H3; try discriminate H6.
  - exists (fun x => match (H2 x) with end).
    exists (fun y => match (H5 y) with end).
    split.
    + intros x. destruct (H2 x).
    + intros y. destruct (H5 y).
  - exists (fun x => sub b (b::B) (pos D (a::A) x)).
    exists (fun y => sub a (a::A) (pos E (b::B) y)).
    assert (H: length (a::A) = length (b::B)) by congruence.
    split.
    + intros x. rewrite pos_sub, sub_pos; trivial.
      rewrite <- H. apply pos_bnd, H2.
    + intros y. rewrite pos_sub, sub_pos; trivial.
      rewrite H. apply pos_bnd, H5.
Qed.

Corollary fin_fin_bij_card_eq  X Y m n :
  fin m X -> fin n Y -> (bijection X Y <=> m = n).
Proof.
  intros H1 H2. split.
  - intros H3. eapply fin_unique. exact H1.
    eapply bijection_fin_fin. 2: exact H2.
    apply bijection_sym, H3.
  - intros ->. eapply fin_fin_bijection; eassumption.
Qed.
  
Corollary bijection_Fin m n :
  bijection (Fin m) (Fin n) -> m = n.
Proof.
  intros H. eapply fin_unique.
  - apply fin_Fin.
  - eapply bijection_fin_fin.
    + apply bijection_sym, H.
    + apply fin_Fin.
Qed.

Goal forall m n,
    m = n -> bijection (Fin m) (Fin n).
Proof.
  intros m n ->. apply bijection_refl.
  (* Note the type cast *)
Qed.

(*** Injections *)

Fact injection_covering {X Y} B:
  injection X Y -> @covering Y B -> { A | @covering X A }.
Proof.
  intros (f&g&H1&_) H2.
  exists (deopt (map g B)). intros x.
  specialize (H2 (f x)).
  apply deopt_in, in_map_iff. exists (f x). auto.
Qed.

Fact injection_fin X Y :
  injection X Y -> finite Y -> finite X.
Proof.
  intros H1 (D&B&H2).
  destruct (injection_covering B H1 H2) as [A H3].
  split. 1:eapply injection_eqdec. all:eauto.
Qed.

Fact fin_fin_le_injection X Y m n :
  fin m X -> fin n Y -> m <= n -> injection X Y.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6) H.
  apply injection_upgrade. exact E.
  destruct A as [|a A].
  { exists (fun x => match (H2 x) with end), (fun y => None).
    intros x. contradiction (H2 x). }
  destruct B as [|b B].
  { exfalso. subst m n. cbn in H. lia. }
  exists (fun x => sub b (b::B) (pos D (a::A) x)),
  (fun y => Some (sub a (a::A) (pos E (b::B) y))).
  hnf. intros x. f_equal. rewrite pos_sub, sub_pos; trivial.
  enough (pos D (a::A) x < length (a::A)) by lia.
  apply pos_bnd, H2.
Qed.

Fact fin_fin_injection_le X Y m n :
  fin m X -> fin n Y -> injection X Y -> m <= n.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&H4&H5) H6.
  destruct H6 as (f&g&H6&H8).
  subst n.
  replace m with (length (map f A)).
  2:{ rewrite map_length. exact H3. }
  apply nrep_le. exact E.
  - apply nrep_map. 2:exact H1. eapply inv1_injective, H6.
  - intros y _. apply H4.
Qed.

Theorem fin_fin_inj_card_le  X Y m n :
  fin m X -> fin n Y -> (injection X Y <=> m <= n).
Proof.
  intros H1 H2. split.
  - apply fin_fin_injection_le; assumption.
  - intros H. eapply fin_fin_le_injection; eassumption.
Qed.

Fact injection_fin_sigma X Y n :
  injection X Y -> fin n Y -> { m & prod (fin m X) (m <= n) }.
Proof.
  intros H1 H2.
  assert { m & fin m X } as [m H3].
  { eapply finite_fin, injection_fin. exact H1.
    eapply finite_fin. eauto. }
  exists m. split. exact H3.
  eapply fin_fin_injection_le; eassumption.
Qed.

Fact fin_sandwich X Y n :
  injection X Y -> injection Y X -> fin n X -> fin n Y.
Proof.
  intros H1 H2 H3.
  edestruct injection_fin_sigma as (m&H4&H5). exact H2. exact H3.
  edestruct injection_fin_sigma as (k&H6&H7). exact H1. exact H4.
  assert (k=n) as -> by (eapply fin_unique; eassumption).
  assert (m=n) as -> by lia.
  exact H4.
Qed.

Fact finite_sandwich X Y :
  injection X Y -> injection Y X -> finite X -> bijection X Y.
Proof.
  intros H1 H2 [n H3]%finite_fin.
  eapply fin_fin_bijection. exact H3.
  eapply fin_sandwich; eassumption.
Qed.
