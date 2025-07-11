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


Fact bijection_refl X :
  bijection X X.
Proof.
  exists (fun x => x) (fun x => x); easy.
Qed.

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

Fact bijection_void X Y :
  ~X -> ~Y -> bijection X Y.
Proof.
  intros H1 H2.
  exists (fun x => match (H1 x) with end)
    (fun y => match (H2 y) with end).
  easy. easy.
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
    forall A, Sigma B, B == A /\ nrep B /\ length B <= length A.
  Proof.
    induction A as [|x A (B&IH1&IH2&IH3)].
    - exists nil. easy. 
    - destruct (mem_dec x A) as [H3|H3].
      + exists B. repeat split; cbn; firstorder (congruence||lia).
      + exists (x::B); repeat split; cbn; firstorder lia.
  Qed.

  Fact covering_listing A :
    covering X A -> Sigma B, listing X B /\ length B <= length A.
  Proof.
    intros H.
    destruct (nrep_equiv A) as (B&H1&H2&H3).
    exists B. split. firstorder. easy.
  Qed.
End Covering_Listing.
Arguments mem_dec {X}.

Theorem finite_fin X :
  finite X <=> Sigma n, fin n X.
Proof.
  split.
  - intros (D&A&H).
    destruct (covering_listing X D A) as (B&H1&H2).
    + exact H.
    + exists (length B). split. exact D. exists B. easy.
  - intros (n&D&A&H&_).
    split. exact D. exists A. apply H.
Qed.

Theorem bijection_fin_trans X Y n :
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

Theorem injection_fin_trans {X Y} n :
  injection X Y -> fin n Y -> Sigma m, (fin m X) * (m <= n).
Proof.
  intros H (H1&B&H2&H3).
  assert (D: eqdec X).
  { eapply injection_eqdec; eauto. }
  destruct H as [f g H].
  destruct (covering_listing X D (map g B)) as (A&H4&H5).
  { intros x.  eapply in_map_iff. exists (f x). split. easy. apply H2. }
  exists (length A). split.
  - split. exact D. eauto.
  - rewrite length_map in H5. lia.
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

Fact fin_injection_nat X n :
  fin (S n) X -> injection X nat.
Proof.
  intros (D&A&(H1&H2)&H3).
  assert (a:X).
  {destruct A as [|a A]; cbn in *. lia. easy. }
  exists (pos D A) (sub a A).
    intros x. apply sub_pos. easy.
Qed.

Fact fin_fin_le_injection X Y m n :
  fin (S m) X -> fin (S n) Y -> m <= n -> injection X Y.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6) H.
  destruct A as [|a A]. easy.
  destruct B as [|b B]. easy.
  exists (fun x => sub b (b::B) (pos D (a::A) x))
    (fun y => sub a (a::A) (pos E (b::B) y)).
  hnf. intros x. 
  rewrite pos_sub, sub_pos; trivial.
  enough (pos D (a::A) x < length (a::A)) by lia. 
  apply pos_bnd. easy.
Qed.

Theorem fin_fin_bijection n X Y:
  fin n X -> fin n Y -> bijection X Y.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6).
  destruct n as [|n], A as [|a A], B as [|b B]; try easy.
  - apply bijection_void; easy.
  - assert (H: length (a::A) = length (b::B))  by congruence.
    exists (fun x => sub b (b::B) (pos D (a::A) x))
      (fun y => sub a (a::A) (pos E (b::B) y)).
    + intros x. rewrite pos_sub, sub_pos; trivial.
      rewrite <-H. apply pos_bnd. easy.
    + intros y. rewrite pos_sub, sub_pos; trivial.
      rewrite H. apply pos_bnd. easy.
Qed.

Theorem fin_num_equiv n X :
  fin n X  <=> bijection X (num n).
Proof.
  split; intros H.
  - eapply fin_fin_bijection. exact H. apply fin_num.
  - eapply bijection_fin_trans.
    + apply bijection_sym. exact H.
    + apply fin_num.
Qed.

(** Injection Lowering *)

Definition lower X Y (f: option X -> option Y) (g: option Y -> option X) y0 x :=
  match f (Some x) with
  | Some y' => y'
  | None => match f None with
           | Some y => y
           | None => y0
           end
  end.

Lemma lower_inv X Y f g x0 y0 :
  inv g f -> inv (lower Y X g f x0) (lower X Y f g y0).
Proof.
  intros H. intros x. unfold lower.
  destruct (f (Some x)) as [y|] eqn:E1.
  - destruct (g (Some y)) as [x'|] eqn:E2.
    + congruence.
    + exfalso. congruence.
  - destruct (f None) as [y|] eqn:E2. 
    + destruct (g (Some y))  as [y'|] eqn:E3.
      * exfalso. congruence.
      * destruct (g None) as [x'|] eqn:E4.
        -- congruence.
        -- exfalso. congruence.
    + exfalso. congruence.
Qed.

Lemma option_lower_injection X Y :
  X -> Y -> injection (option X) (option Y) -> injection X Y.
Proof.
  intros x0 y0 [f g H].
  exists (lower X Y f g y0) (lower Y X g f x0).
  eapply lower_inv, H.
Qed.

(** Cardinality theorems *)

Lemma num_card_le_S m n :
  injection (num (S m)) (num (S n)) -> m <= n.
Proof.
  revert n. induction m. lia.
  intros n H.
  destruct n.
  - exfalso. destruct H as [f g Hfg].
    assert (H: f None <> f (Some None)).
    { intros H %(f_equal g). congruence. }
    destruct (f None) eqn:H1; destruct (f (Some None)) eqn:H2; easy.
  - enough (m <= n) by lia.
    apply IHm, option_lower_injection.
    exact None. exact None. exact H.
Qed.

Lemma num_card_le m n :
  injection (num m) (num n) -> m <= n.
Proof.
  destruct m. lia.
  destruct n.
  { intros [f _ _]. destruct (f None). }
  intros H. enough (m <= n) by lia. apply num_card_le_S, H.
Qed.

Fact injection_trans X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros [f g H] [f' g' H'].
  exists (fun x => f' (f x)) (fun z => g (g' z)).
  intros x. congruence.
Qed.

Theorem fin_card_le X Y m n :
  fin m X -> fin n Y -> injection X Y -> m <= n.
Proof.
  intros H1%fin_num_equiv H2%fin_num_equiv H3.
  apply num_card_le.
  apply bijection_sym, bijection_injection in H1.
  apply  bijection_injection in H2.
    revert H2; apply injection_trans.
    revert H3; apply injection_trans.
    exact H1.
Qed.

Theorem fin_card_eq X Y m n :
  fin m X -> fin n Y -> bijection X Y -> m = n.
Proof.
  intros H1 H2 H3.
  enough (m <= n /\ n <= m) by lia.
  split.
  - apply  bijection_injection in H3.
    eapply fin_card_le; eassumption.
  - apply  bijection_sym, bijection_injection in H3.
    eapply fin_card_le; eassumption.
Qed.

Theorem fin_card_unique X m n :
  fin m X -> fin n X -> m = n.
Proof.
  intros H1 H2.
  eapply fin_card_eq. exact H1. exact H2.
  apply bijection_refl.
Qed.

(** Exercises *)

Fact fin_sandwich X Y n :
  injection X Y -> injection Y X -> fin n X -> fin n Y.
Proof.
  intros H1 H2 H3.
  destruct (injection_fin_trans n H2 H3) as (k&H4&H5).
  edestruct (injection_fin_trans k H1 H4) as (l&H6&H7).
  enough (k=n) by congruence.
  assert (n=l) by (eapply fin_card_unique; eassumption).
  lia.
Qed.

Fact finite_sandwich X Y :
  injection X Y -> injection Y X -> finite X -> bijection X Y.
Proof.
  intros H1 H2 [n H3]%finite_fin.
  eapply fin_fin_bijection. exact H3.
  eapply fin_sandwich; eassumption.
Qed.

Fact fin_fin_bij_card_eq  X Y m n :
  fin m X -> fin n Y -> (bijection X Y <=> m = n).
Proof.
  intros H1 H2. split.
  - intros H3. eapply fin_card_unique. exact H1.
    eapply bijection_fin_trans. 2: exact H2.
    apply bijection_sym, H3.
  - intros ->. eapply fin_fin_bijection; eassumption.
Qed.
  
Fact bijection_num m n :
  bijection (num m) (num n) -> m = n.
Proof.
  intros H.
  eapply fin_card_unique.
  - apply fin_num.
  - eapply bijection_fin_trans.
    + apply bijection_sym, H.
    + apply fin_num.
Qed.

Fact injection_covering {X Y}:
  injection X Y -> sig (covering Y) -> sig (covering X).
Proof.
  intros [f g H] [A H1].
  exists (map g A). intros x.
  specialize (H1 (f x)).
  apply in_map_iff. exists (f x). auto.
Qed.
 
