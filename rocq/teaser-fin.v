From Stdlib Require Import Arith Lia List.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Inductive void : Type := .
Definition dec (X: Type) : Type := X + ~X.
Notation decider p := (forall x, dec (p x)).
Definition eqdec X := forall x y: X, dec (x = y).
Fact nat_eqdec : eqdec nat.
Proof.
  intros x y. unfold dec.
  destruct ((x-y)+(y-x)) eqn:?. left;lia. right;lia.
Qed.

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H F x x'.
  destruct (F (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. congruence.
Qed.

Definition inv {X Y} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Fact bijection_sym X Y :
  bijection X Y -> bijection Y X.
Proof.
  intros [f g H1 H2]. econstructor; eassumption. 
Qed.
  
Fact bijection_injection X Y :
  bijection X Y -> injection X Y.
Proof.
  intros [f g H1 H2]. econstructor; eassumption. 
Qed.

Fact injection_eqdec X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H1].
  eapply injective_eqdec, inv_injective, H1.
Qed.

Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A == B" := (A <<= B /\ B <<= A) (at level 70).

Definition covering X (A: list X) :=
  forall x, x el A.

Definition finite X : Type :=
  eqdec X * sig (covering X).
 
Fixpoint nrep {X} (A: list X) : Prop :=
  match A with
  | [] => True
  | x::A => x nel A /\ nrep A
  end.

Definition listing X A :=
  covering X A /\ nrep A.

Definition fin n X : Type :=
  eqdec X * Sigma A, listing X A /\ length A = n.

Fact option_eqdec X :
  eqdec X -> eqdec (option X).
Proof.
  unfold eqdec, dec.
  intros H [x|] [y|].
  - specialize (H x y). intuition congruence.
  - intuition congruence.
  - intuition congruence.
  - intuition congruence.
Qed.

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

Fact listing_option X A :
  listing X A -> listing (option X) (None::map Some A).
Proof.
  intros [H1 H2]. unfold listing. split.
  - intros [x|]; cbn.
    + right. apply in_map_iff. exists x. easy.
    + auto.
  - split.
    + intros H%in_map_iff. destruct H as (x&H&_). easy.
    + apply nrep_map. 2:easy. unfold injective. congruence.
Qed.

Fact fin_option n X :
  fin n X -> fin (S n) (option X).
Proof.
  intros [D (A&H1&H2)].
  split. 
  - apply option_eqdec, D.
  - exists (None:: map Some A). split.
    + apply listing_option, H1.
    + cbn. rewrite length_map. congruence.
Qed.

Fixpoint num n : Type :=
  match n with 0 => void | S n => option (num n) end.

Fact fin_O :
  fin 0 void.
Proof.
  split. easy. exists nil. easy.
Qed.

Theorem fin_num n :
  fin n (num n).
Proof.
  induction n.
  - exact fin_O.
  - apply fin_option, IHn.
Qed.

Fact fin_void X :
  fin 0 X <=> ~X.
Proof.
  split.
  - intros (_&A&[H1 _]&H2) x.
    specialize (H1 x). destruct A; easy.
  - intros H. split. intros x; easy.
    exists nil. easy.
Qed.

Fact nat_not_finite :
  ~finite nat.
Proof.
  intros (_&A&H).
  revert H.
  enough (exists n, forall k, k el A -> n > k) as [n H].
  { intros H2. apply (H n) in H2. lia. }
  induction A as [|a A IH].
  - cbn.  exists 0. easy.
  - destruct IH as [n IH].
    exists (S a + n). intros k [->|H]. lia.
    specialize (IH k H). lia.
Qed.

Section Covering_Listing.
  Variable X : Type.
  Variables X_eqdec: eqdec X.
  Implicit Types (A B: list X).

  Fact mem_dec x A :
    dec (x el A).
  Proof.
    induction A as [|y A IH].
    - right. easy.
    - destruct IH as [IH|IH];cbn; unfold dec.
      + intuition.
      + destruct (X_eqdec x y); intuition congruence.
  Qed.
 
  Fact equi_refl A :
    A == A.
  Proof.
    unfold incl. auto.
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

  Fact covering_listing :
    sig (covering X) -> sig (listing X).
  Proof.
    intros [A H].
    destruct (nrep_equiv A) as (B&H1&H2).
    exists B. split. 2:easy.
    intros x. apply H1, H.
  Qed.
End Covering_Listing.
Arguments mem_dec {X}.

Theorem finite_fin X :
  finite X <=> Sigma n, fin n X.
Proof.
  split.
  - intros (D&A&H).
    destruct (covering_listing X) as [B HB].
    + easy.
    + eauto.
    + exists (length B). split. exact D. exists B. easy.
  - intros (n&D&A&H&_).
    split. exact D. exists A. apply H.
Qed.

Theorem bijection_fin_fin X Y n :
  bijection X Y -> fin n X -> fin n Y.
Proof.
  intros H (D&A&H1&H2). hnf.
  split.
  - eapply injection_eqdec. 2:exact D.
    apply bijection_injection, bijection_sym, H.
 - destruct H as [f g H3 H4].
   exists (map f A). split.
   + split.
     * intros x. eapply in_map_iff. exists (g x). 
       split. apply H4. apply H1.
     * apply nrep_map.
       -- eapply inv_injective, H3.
       -- apply H1.
   + rewrite length_map. exact H2.
Qed.

Fact injection_covering {X Y}:
  injection X Y -> sig (covering Y) -> sig (covering X).
Proof.
  intros [f g H] [A H1].
  exists (map g A). intros x.
  specialize (H1 (f x)).
  apply in_map_iff. exists (f x). auto.
Qed.

Theorem injection_fin X Y :
  injection X Y -> finite Y -> finite X.
Proof.
  intros H1 (D&B&H2).
  destruct (injection_covering H1) as [A H3].
  - eauto.
  - split.
    + revert H1 D. apply injection_eqdec.
    + eauto.
Qed.

(** Construction of injections and bijections *)

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
    - easy.
    - destruct X_eqdec as [<-|H]. easy.
      intros [->|H1]. easy. auto.
  Qed.

  Fact pos_bnd A x :
    x el A -> pos A x < length A.
  Proof.
    induction A as [|y A IH]; cbn.
    - easy.
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
Arguments sub {X}.
Arguments pos {X}.

Theorem fin_fin_bijection n X Y:
  fin n X -> fin n Y -> bijection X Y.
Proof.
  (* beautiful proof script *)
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6).
  destruct n as [|n], A as [|a A], B as [|b B];
    try discriminate H3; try discriminate H6.
  - exists (fun x => match (H1 x) with end)
      (fun y => match (H4 y) with end).
    + intros x. destruct (H1 x).
    + intros y. destruct (H4 y).
  - assert (length (a::A) = length (b::B)) as H  by congruence.
    exists (fun x => sub b (b::B) (pos D (a::A) x))
      (fun y => sub a (a::A) (pos E (b::B) y)).
    + intros x. rewrite pos_sub, sub_pos; trivial.
      rewrite <-H. apply pos_bnd, H1.
    + intros y. rewrite pos_sub, sub_pos; trivial.
      rewrite H. apply pos_bnd, H4.
Qed.

Fact fin_fin_le_injection X Y m n :
  fin m X -> fin n Y -> 1 <= m <= n -> injection X Y.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6) H.
  destruct A as [|a A].
  { exfalso. cbn in H3. lia. }
  destruct B as [|b B].
  { exfalso. cbn in H6. lia. }
  exists (fun x => sub b (b::B) (pos D (a::A) x))
    (fun y => sub a (a::A) (pos E (b::B) y)).
  hnf. intros x. 
  - rewrite pos_sub. apply sub_pos.
    + apply H1.
    + apply H5.
    + enough (pos D (a::A) x < length (a::A)) by lia.
      apply pos_bnd, H1.
Qed.

(** Discriminating elements *)

Section List.
  Variable X : Type.
  Variables X_eqdec: eqdec X.
  Implicit Types (x y z: X) (A B: list X).
 
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
  
  Fact mem_rear_sig {x A} :
    x el A -> Sigma A', A == x::A' /\ length A = S (length A').
  Proof.
    intros (A1&A2&->) %mem_sig.
    exists (A1++A2). cbn. split.
    - split; intros z; cbn; rewrite !in_app_iff; cbn; intuition.
    (* Note the use of setoid rewriting *)
    - rewrite !length_app. cbn. lia.
  Qed.
 
  Fact nrep_discriminate {A B} :
    nrep A -> length B < length A -> Sigma x, x el A /\ x nel B.
  Proof.
    induction A as [|a A IH] in B |-*; cbn.
    - lia.  (* computational falsity elimination *)
    - intros [H1 H2] H3.
      destruct (mem_dec X_eqdec a B) as [H|H].
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

  Fact nrep_incl A B :
    nrep A -> A <<= B -> length B <= length A -> B <<= A.
  Proof.
    intros H1 H2 H3 x H4.
    destruct (mem_dec X_eqdec x A) as [H5|H5]. exact H5. exfalso.
    destruct (@nrep_discriminate (x::A) B) as (z&H6&H7).
    - easy.
    - cbn; lia.
    - destruct H6 as [->|H6]; auto.
  Qed.

  Fact listing_length_unique A B :
    listing X A -> listing X B -> length A = length B.
  Proof.
    intros [H1 H2] [H3 H4].
    enough (length A <= length B /\ length B <= length A) by lia.
    split; apply nrep_le; try assumption.
    - intros x _. apply H3.
   - intros x _. apply H1.
  Qed.
End List.

Fact fin_unique X m n :
  fin m X -> fin n X -> m = n.
Proof.
  intros [D (A&H1&H2)] [_ (B&H3&H4)].
  subst m n. apply listing_length_unique; assumption.
Qed.
 
(** Injections *)

Fact fin_fin_injection_le X Y m n :
  fin m X -> fin n Y -> injection X Y -> m <= n.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&H4&H5) [f g H6].
  subst m n.
  erewrite <-(length_map f).
  apply nrep_le.
  - exact E.
  - apply nrep_map. 2:exact H2. eapply inv_injective, H6.
  - intros y _. apply H4.
Qed.

Fact injection_fin_sigma X Y n :
  injection X Y -> fin n Y -> Sigma m, fin m X * (m <= n).
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

Corollary fin_fin_bij_card_eq  X Y m n :
  fin m X -> fin n Y -> (bijection X Y <=> m = n).
Proof.
  intros H1 H2. split.
  - intros H3. eapply fin_unique. exact H1.
    eapply bijection_fin_fin. 2: exact H2.
    apply bijection_sym, H3.
  - intros ->. eapply fin_fin_bijection; eassumption.
Qed.
  
Corollary bijection_num m n :
  bijection (num m) (num n) -> m = n.
Proof.
  intros H. eapply fin_unique.
  - apply fin_num.
  - eapply bijection_fin_fin.
    + apply bijection_sym, H.
    + apply fin_num.
Qed.

