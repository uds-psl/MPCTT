From Coq Require Import Arith Lia List.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Fixpoint Fin n : Type :=
  match n with 0 => False | S n' => option (Fin n') end.

Definition option_eqdec X : eqdec X -> eqdec (option X).
Proof.
  unfold eqdec, dec; intros H [x|] [y|]; try intuition easy.
  destruct (H x y); intuition congruence.
Qed.

(*** Injection Preliminaries *)

Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H d x x'. specialize (H x x').
  destruct (d (f x) (f x')) as [H1|H1];
    unfold dec in *; intuition  congruence.
Qed.

Definition inv {X Y} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.

Inductive bijection (X Y: Type) : Type :=
| Bijection  {f: X -> Y} {g: Y -> X} (_: inv g f) (_: inv f g).

Fact bijection_sym {X Y} :
  bijection X Y -> bijection Y X.
Proof.
  intros [f g H H']. exists g f; easy. 
Qed.

Fact bijection_empty X Y :
  (X -> False) -> (Y -> False) -> bijection X Y.
Proof.
  intros f g.
  exists (fun x => match f x with end) (fun y => match g y with end).
  - intros x. contradiction (f x).
  - intros y. contradiction (g y).
Qed.  

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).

Fact bijection_injection X Y :
  bijection X Y -> injection X Y.
Proof.
  intros [f g H _]. exists f g. exact H.
Qed.

Fact injection_eqdec X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros [f g H1] H2.
  eapply injective_eqdec. 2:exact H2.
  eapply inv_injective, H1.
Qed.

(*** EWO Preliminaries *)

Definition ewo X :=
  forall (p: X -> Prop), decider p -> ex p -> sig p.

Fact bot_ewo:
  ewo False.
Proof.
  intros p _ [[] _].
Qed.

Definition option_ewo {X} :
  ewo X -> ewo (option X).
Proof.
  intros E p p_dec H.
  destruct (p_dec None) as [H1|H1].
  - eauto.
  - destruct (E (fun x => p (Some x))) as [x H2].
    + easy. 
    + destruct H as [[x|] H].
      * eauto.
      * easy.
    + eauto.
Qed.

Fact Fin_ewo :
  forall n, ewo (Fin n).
Proof.
  induction n as [|n IH]; cbn.
  - apply bot_ewo.
  - apply option_ewo, IH.
Qed.

Fact injection_ewo X Y :
  injection X Y -> ewo Y -> ewo X.
Proof.
  intros [f g H] E p p_dec H1.
  destruct (E (fun y => p (g y))) as [y H2].
  - easy.
  - destruct H1 as [x H1]. exists (f x). congruence.
  - eauto.
Qed.

(*** List Preliminaries *)

Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).

Section List.
  Variable X : Type.
  Variables X_eqdec: eqdec X.
  Implicit Types (x y z: X) (A B: list X).

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
   
  Definition equi A B := A <<= B /\ B <<= A.
  Notation "A == B" := (equi A B) (at level 70).
  
  Fixpoint nrep A : Prop :=
    match A with
    | [] => True
    | x::A => x nel A /\ nrep A
    end.

  Fact nrep_equiv :
    forall A, Sigma B, B == A /\ nrep B /\ length B <= length A.
  Proof.
    induction A as [|x A (B&IH1&IH2&IH3)].
    - exists nil. easy.
    - destruct (mem_dec x A) as [H3|H3].
      + exists B; cbn. repeat split.
        * firstorder.
        * firstorder congruence.
        * easy.
        * lia.
      + exists (x::B); cbn. repeat split.
        * firstorder.
        * firstorder.
        * firstorder.
        * easy.
        * lia.
  Qed.
 
  Fact mem_rearrange {x A} :
    x el A -> Sigma B, A == x::B /\ length A = S (length B).
  Proof.
    intros H.
    induction A as [|a A IH]. easy.
    destruct (X_eqdec a x) as [->|H1].
    - exists A. easy.
    - specialize IH as (B&(IH1&IH2)&IH3).
      + destruct H; congruence.
      + exists (a::B). split. 2:(cbn; lia). split; intros z.
        * intros [-> | H2]. firstorder. specialize (IH1 z). firstorder.
        * intros [-> | [-> |H2]]; intuition.
  Qed.

  Fact nrep_discriminate A B :
    nrep A -> length B < length A -> Sigma x, x el A /\ x nel B.
  Proof.
    induction A as [|a A IH] in B |-*; cbn.
    - lia.  (* computational falsity elimination *)
    - intros [H1 H2] H3.
      destruct (mem_dec a B) as [H|H].
      2: {exists a. intuition. }
      destruct (mem_rearrange H) as (B'&H4&H5).
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
    edestruct nrep_discriminate as (x&H4&H5).
    exact H1. exact H3. apply H5, H2, H4.
  Qed.

  Fact nrep_incl A B :
    nrep A -> A <<= B -> length B <= length A -> B <<= A.
  Proof.
    intros H1 H2 H3 x H4.
    destruct (mem_dec x A) as [H5|H5]. exact H5. exfalso.
    destruct (@nrep_discriminate (x::A) B) as (z&H6&H7); cbn.
    - auto.
    - lia.
    - destruct H6 as [->|H6]; auto.
  Qed.

  Fact nrep_sigma A :
    nrep A + Sigma B, A <<= B /\ length B < length A.
  Proof.
    induction A as [|x A [IH1|(B&IH2&IH3)]]; cbn.
    - auto.
    - destruct (mem_dec x A) as [H|H].
      + right. exists A. split. intuition. cbn. lia.
      + auto.
    - right. exists (x::B). split. intuition. cbn. lia.
  Qed.

  Fact nrep_nrep A B :
    nrep A -> A <<= B -> length B <= length A -> nrep B.
  Proof.
    intros H1 H2 H3.
    destruct (nrep_sigma B) as [H|(C&H4&H5)]. exact H. exfalso.
    destruct (nrep_discriminate A C) as (x&H6&H7).
    exact H1. lia. auto.
  Qed.

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

  Fact sub_in A n :
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
      { contradict H1. apply sub_in. lia. }
      f_equal. apply IH. exact H2. lia.
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

End List.
Arguments mem_dec {X}.
Arguments nrep {X}.
Arguments nrep_equiv {X}.
Arguments sub {X}.
Arguments pos {X}.

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

Fact nrep_injective X Y (f: X -> Y) x x' A :
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

Fact map_in_ex X Y  (f: X -> Y) y A :
  y el map f A -> exists x, f x = y.
Proof.
  induction A as [|a A IH]; cbn. easy.
  intros [<- | [x <- ]%IH]; eauto.
Qed.

(*** Coverings and Listings *)

Definition covering {X} (A: list X) :=
  forall x, x el A.
Definition listing {X} (A: list X) :=
  covering A /\ nrep A.

Section CoveringListing.
  Variable X: Type.
  Variable X_eqdec: eqdec X.
  Implicit Types A B : list X.

  Fact covering_listing A :
    covering A -> Sigma B, (length B <= length A) * listing B.
  Proof.
    intros H.
    destruct (nrep_equiv X_eqdec A) as (B&H1&H2&H3).
    exists B. repeat split. easy. firstorder. easy.
  Qed.
  
  Fact listing_length_unique A B :
    listing A -> listing B -> length A = length B.
  Proof.
    intros [H1 H2] [H3 H4].
    enough (length A <= length B /\ length B <= length A) by lia.
    split; apply nrep_le; firstorder.
  Qed.

  Fact nrep_iff_covering A B :
    listing A -> length B = length A -> nrep B <-> covering B.
  Proof.
    intros [H1 H2] H3. split.
    - intros H x. eapply nrep_incl. 5:apply H1. 4:lia. all: easy.
    - intros H. eapply nrep_nrep; eauto. easy. lia.
  Qed.

End CoveringListing.
Arguments covering_listing {X}.


(*** Finite Types Basics *)

Definition finite X : Type :=
  eqdec X * Sigma A, @covering X A.
Definition fin n X : Type :=
  eqdec X * Sigma A,  @listing X A /\ length A = n.

Fact fin_unique X m n :
  fin m X -> fin n X -> m = n.
Proof.
  intros [D (A&H1&H2)] [_ (B&H3&H4)].
  subst m n. apply listing_length_unique; assumption.
Qed.

Fact finite_fin X :
  finite X <=> Sigma n, fin n X.
Proof.
  split.
  - intros [D [A H]].
    destruct (covering_listing D A H) as (B&H1&H2).
    exists (length B). split. exact D. exists B. easy.
  - intros [_ [D (A&[H _]&_)]]. hnf. eauto.
Qed.

Fact fin_zero X :
  fin 0 X <=> (X -> False).
Proof.
  split.
  - intros [D (A&[H1 _]&H2)] x.
    specialize (H1 x). destruct A; easy.
  - intros H. split.
    + intros x. easy.
    + exists nil. easy.
Qed.

Fact fin_option X n :
  fin n X -> fin (S n) (option X).
Proof.
  intros (d&A&H1&H2).
  split.
  - apply option_eqdec, d.
  - exists (None::map Some A); repeat split; cbn.
    + intros [a|].
      *  right. apply in_map, H1.
      * left. reflexivity.
    + intros [x H]%map_in_ex; easy.
    + apply nrep_map.
      * hnf. congruence.
      * apply H1.
    + rewrite map_length. congruence.
Qed.

Fact fin_Fin n :
  fin n (Fin n).
Proof.
  induction n as [|n IH]; cbn.
  - apply fin_zero. easy.
  - apply fin_option, IH.
Qed.

Fact list_sigma_forall {X} {p: X -> Prop} (p_dec: decider p) :
  forall A, (Sigma x, x el A /\ p x) + (forall x, x el A -> ~p x).
Proof.
  induction A as [|a A IH].
  - right. intros x [].
  - destruct IH as [(b&H1&H2)|H].
    + left. exists b. firstorder.
    + destruct (p_dec a) as [H1|H1].
      * left. exists a. firstorder.
      * right. intros x [->|H2]; auto.
Qed.          

Section Dec.
  Variable (X: Type).
  Variable (X_fin: finite X).
  Variable (p: X -> Prop).
  Variable (p_dec: decider p).
  Implicit Types A B: list X.

  Fact fin_sigma_forall :
    (Sigma x, p x) + (forall x, ~p x).
  Proof.
    destruct X_fin as (_&A&H).
    destruct (list_sigma_forall p_dec A) as [(a&H1&H2)|H1]; eauto.
  Qed.

  Fact fin_dec_exists :
    dec (exists x, p x).
  Proof.
    destruct X_fin as (_&A&H).
    destruct fin_sigma_forall as [(a&H1)|H1].
    - left. eauto.
    - right. intros [a H2]. apply (H1 a H2).
  Qed.

End Dec.

Fact nat_list_next :
  forall A: list nat, Sigma n, forall x, x el A -> x < n.
Proof.
  induction A as [|x A [n IH]].
  - exists 0. easy.
  - exists (S x + n). intros y [-> |H].
    + lia.
    + apply IH in H. lia.
Qed.
 
Fact nat_not_finite :
  finite nat -> False.
Proof.
  intros (_&A&H).
  destruct (nat_list_next A) as [n H1].
  specialize (H (S n)).  apply H1 in H. lia.
Qed.

(*** Finiteness by Injection *)


Fact injection_fin_sigma {X Y n} :
  injection X Y -> fin n Y -> Sigma m, (fin m X) * (m <= n).
Proof.
  intros H (H1&B&H2&H3).
  assert (eqdec X) as H6.
  { eapply injection_eqdec;eauto. }
  destruct H as [f g H].  
  assert (covering (map g B)) as (A&H4&H5)%covering_listing.
  { intros x. eapply in_map_iff. exists (f x). split. easy. apply H2. }
  2: exact H6.
  exists (length A). repeat split.
  + exact H6.
  + exists A. easy.
  + rewrite map_length in H4. lia.
Qed.

Fact fin_fin_injection_le X Y m n :
  injection X Y -> fin m X -> fin n Y -> m <= n.
Proof.
  intros H1 H2 H3.
  destruct (injection_fin_sigma H1 H3) as (m'&H5&H6).
  enough (m=m') by lia.
  eapply fin_unique; eassumption.
Qed.

Fact fin_sandwich X Y n :
  injection X Y -> injection Y X -> fin n X -> fin n Y.
Proof.
  intros H1 H2 H3.
  destruct (injection_fin_sigma H2 H3) as (m&H4&H5).
  enough (H: n <= m).
  { assert (m=n) as -> by lia. trivial. }
  eapply fin_fin_injection_le. exact H1. all: trivial.
Qed.

Fact bijection_fin_fin X Y n :
  bijection X Y -> fin n X -> fin n Y.
Proof.
  intros H. apply fin_sandwich; apply bijection_injection.
  - apply H.
  - apply bijection_sym, H.
Qed.

Fact injection_nat_not_finite X :
  injection nat X -> finite X -> False.
Proof.
  intros H1 [n H2]%finite_fin.
  apply nat_not_finite.
  destruct (injection_fin_sigma H1 H2) as (m&H3&_).
  eapply finite_fin. eauto.
Qed.

(*** Existence of Injections *)
  
Fact fin_fin_le_injection X Y m n :
  fin m X -> fin n Y -> 1 <= m <= n -> injection X Y.
Proof.
  intros (D&A&(H1&H2)&H3) (E&B&(H4&H5)&H6) [H7 H8].
  (* obtain default values *)
  assert (a:X).
  {destruct A as [|a A]; cbn in *. lia. easy. }
  assert (b:Y).
  {destruct B as [|b B]; cbn in *. lia. easy. }
  exists (fun x => sub b B (pos D A x))
    (fun y => sub a A (pos E B y)).
  intros x. rewrite pos_sub, sub_pos; trivial.
  enough (pos D A x < length A) by lia.
   apply pos_bnd, H1.
Qed.

Fact fin_fin_inv_inv X Y n f g :
  fin n X -> fin n Y -> @inv X Y g f -> inv f g.
Proof.
  intros (D&A&(H1&H2)&H3) (H4&B&H7&<-) H5.
  enough (covering (map f A)) as H.
  { intros y. specialize (H y). apply map_in_ex in H as [x H]. congruence. }
  assert (nrep (map f A)) as H6.
  { apply nrep_map. 2:easy. eapply inv_injective; easy. }
  eapply nrep_iff_covering.
  2: exact H7. all: trivial. rewrite map_length. trivial.
Qed.

Fact fin_fin_bij n X Y :
  fin n X -> fin n Y -> bijection X Y.
Proof.
  intros H1 H2.
  destruct n.
  - apply bijection_empty; apply fin_zero; trivial.
  - assert (injection X Y) as [f g H3].
    { eapply fin_fin_le_injection. exact H1. exact H2. lia. }
    exists f g. exact H3.
    eapply fin_fin_inv_inv; eassumption.
Qed.
  
Fact finite_sandwich X Y :
  injection X Y -> injection Y X -> finite X -> bijection X Y.
Proof.
  intros H1 H2 [n H3]%finite_fin.
  assert (fin n Y) as H4 by (eapply fin_sandwich; eassumption).
  eapply fin_fin_bij; eassumption.
Qed.

Fact fin_Fin_bijection X n :
  fin n X <=> bijection X (Fin n).
Proof.
  split; intros H.
  - eapply fin_fin_bij. exact H. apply fin_Fin.
  - eapply bijection_fin_fin.
    + apply bijection_sym, H.
    + apply fin_Fin.
Qed.

Fact fin_ewo X :
  finite X -> ewo X.
Proof.
  intros [n H] %finite_fin.
  generalize (Fin_ewo n).
  apply injection_ewo, bijection_injection, fin_Fin_bijection, H.
Qed.

Fact fin_injection_nat X n :
  fin (S n) X -> injection X nat.
Proof.
  intros (D&A&(H1&H2)&H3).
  assert (a:X).
  {destruct A as [|a A]; cbn in *. lia. easy. }
  exists (pos D A) (sub a A).
    intros x. apply sub_pos. easy.
Qed.

(* Exercise *)
Fact injection_covering {X Y} B: 
  injection X Y -> @covering Y B -> Sigma A, @covering X A.
Proof.
  intros [f g H1] H2.
  exists (map g B). intros x.
  specialize (H2 (f x)).
  apply in_map_iff. exists (f x). auto.
Qed.

(*** Upgrade Theorem *)

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
  - intros x x'. eapply nrep_injective. 2,3:apply H0.
    clear x x'. apply H4. intros y. specialize (H y) as [x H].
    eapply in_map_iff; eauto.
Qed.

Fact surjective_inv X Y f :
  @surjective X Y f -> ewo X -> eqdec Y -> Sigma g, inv f g.
Proof.
  intros H E d.
  enough (G: forall y, Sigma x, f x = y).
  { exists (fun y => pi1 (G y)). intros y. destruct (G y) as [x H1]; easy. }
  intros y. apply E.
  - intros x. apply d.
  - apply H. 
Qed.

Theorem upgrade X Y n f :
  fin n X -> fin n Y -> @surjective X Y f ->
  Sigma g, inv g f /\ inv f g.
Proof.
  intros H1 H2 H3.
  destruct (surjective_inv X Y f H3) as [g H4].
  - apply fin_ewo, finite_fin. eauto.
  - apply H2.
  - exists g. split. 2:exact H4.
    eapply fin_fin_inv_inv; eassumption.
Qed.

Theorem upgrade_inj X Y n f :
  fin n X -> fin n Y -> @injective X Y f ->
  Sigma g, inv g f /\ inv f g.
Proof.
  intros H1 H2 H3.
  eapply upgrade. exact H1. exact H2.
  eapply fin_fun_injective_surjective; eassumption.
Qed.

(*** Listless proofs *)

Definition L {X Y}
  : (option X -> option (option Y)) -> X -> option Y
  := fun f x => match f (Some x) with
             | Some b => b
             | None => match f None with
                      | Some b => b
                      | None => None
                      end
             end.

Lemma lowering {X Y}
  {f: option (option X) -> option (option Y)}
  {g: option (option Y) -> option (option X)} :
  inv g f -> inv (L g) (L f).
Proof.
  intros H a. unfold L.
  destruct (f None) eqn:?, (g None) eqn:?, (f (Some _)) eqn:?, (g (Some _)) eqn:?.
  all: congruence.
Qed.

Fact Fin_inv_inv n f g :
  @inv (Fin n) (Fin n) g f -> inv f g.
Proof.
  revert f g.
  induction n as [|n IH]; cbn.
  { intros f g _ []. }
  destruct n; cbn.
  { intros f g H [[]|]. destruct f as [[]|]. reflexivity. }
  intros f g H.
  specialize (IH _ _ (lowering H)).
  destruct (f (g None)) as [b|] eqn:E.
  - exfalso.
    destruct (f None) as [b'|] eqn:?. 2:congruence.
    specialize (IH b'). revert IH. unfold L.
    destruct  (g (Some b')) eqn:?. 1:congruence.
    destruct (g None) eqn:?.
    + rewrite E. congruence.
    + destruct (f (Some None)) eqn:?; congruence.
  - intros [b|]. 2:exact E.
    specialize (IH b). revert IH. unfold L.
    destruct (g (Some b)) as [a|] eqn:?.
    + destruct (f (Some a)) eqn:?.
      * congruence.
      * destruct (f None) eqn:?; congruence.
    + destruct (g None) as [a|] eqn:?.
      * rewrite E. destruct (f None) eqn:?; congruence.
      * destruct (f (Some None)) eqn:?; congruence.
Qed.


Corollary fin_bijection_fin_fin X Y n f g :
  bijection X (Fin n) ->
  bijection Y (Fin n) ->
  @inv X Y g f -> inv f g.
Proof.
  intros [f1 g1 g1f1 f1g1] [f2 g2 g2f2 f2g2] gf y.
  enough (inv (fun a => f2 (f (g1 a))) (fun a => f1 (g (g2 a)))) as H by congruence.
  apply Fin_inv_inv. congruence.
Qed.

Lemma Fin_Fin_False n :
  injection (Fin (S (S n))) (Fin 1) -> False.
Proof.
  intros [f g H].
  enough (f (Some None) = f None) as E.
  { apply (f_equal g) in E. congruence. }
  destruct f as [a|]. easy.
  destruct f as [a|]; easy.
Qed.
  
Fact Fin_le m n :
  injection (Fin m) (Fin n) -> m <= n.
Proof.
  intros H.
  destruct m. lia.
  destruct H as [f g H].
  destruct n. contradiction (f None).
  induction m as [|m IH] in H, f, g, n |-*.
  - lia.
  - destruct n.
    + exfalso. eapply Fin_Fin_False. exists f g. exact H.
    + enough (S m <= S n) by lia.
      apply (IH n (L f) (L g)), lowering, H.
Qed.

Fact Fin_bijection_card m n :
  bijection (Fin m) (Fin n) -> m = n.
Proof.
  intros H.
  enough (m <= n /\ n <= m) by lia.
  split.
  - apply Fin_le, bijection_injection, H.
  - apply Fin_le, bijection_injection, bijection_sym, H.
Qed.
 
(** Exercises *)

Fact Fin_forall_dec n X (f: Fin n -> X) (p: X -> Prop) :
  (forall x, dec (p x)) -> dec (forall a, p (f a)).
Proof.
  intros F.
  induction n as [|n IH].
  - left. intros [].
  - specialize (IH (fun a => f (Some a))) as [IH|IH].
    + destruct (F (f None)) as [H|H].
      * left. intros [a|]. exact (IH a). exact H.
      * right. intros H1. contradict (H (H1 None)).
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

(* Bijection theorem for option types *)

Fact R {X Y f g} :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with Some y' => y = y' | None => f None = Some y end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:E1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:E2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

Fact R_inv {X Y f g} :
  forall (H1: @inv (option X) (option Y) g f)
    (H2: inv f g),
    inv (fun y => pi1 (R H2 y)) (fun x => pi1 (R H1 x)).
Proof.
  intros H1 H2 x.
  destruct (R H1 x) as [y H3]; cbn.
  destruct (R H2 y) as [x' H4]; cbn.
  revert H3 H4.  
  destruct (f (Some x)) as [y1|] eqn:E.
  - intros <-. rewrite <-E, H1. easy.
  - intros <-.  rewrite H1. rewrite <-E, H1. congruence.
Qed.

Theorem bijection_option X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  exists (fun y => pi1 (R H1 y)) (fun x => pi1 (R H2 x)); apply R_inv.
Qed.

Fact Fin_bijection_card' m n :
  bijection (Fin m ) (Fin n) -> m = n.
Proof.
  induction m as [|m IH] in n |-*;  destruct n; cbn.
  - easy.
  - intros [_ g _ _]. exfalso. apply g. apply None.
  - intros [f _ _ _]. exfalso. apply f. apply None.
  - intros H. f_equal. apply IH. clear IH.
    apply bijection_option, H.
Qed.


