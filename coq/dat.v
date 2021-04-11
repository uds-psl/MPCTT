From Coq Require Import Arith Lia ConstructiveEpsilon List.
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

Section nat_LWO.
  Variable p: nat -> Prop.
  Definition safe  n := forall k, p k -> k >= n.
  Definition least  n := p n /\ safe n.
  Fact nat_LWO :
    decider p -> sig p -> sig least.
  Proof.
    intros D.
    enough (forall n, safe n + sig least) as H.
    { intros [n H1].
      specialize (H n) as [H|H]. 2:exact H.
      exists n. hnf. auto. }
    induction n as [|n [IH|IH]].
    - left. hnf. lia.
    - destruct (D n) as [H1|H1].
      + right. exists n. hnf. auto.
      + left. intros k H2.
        enough (~ k <= n) by lia. intros H.
        specialize (IH k H2). 
        assert (k = n) as -> by lia. auto.
    - right. exact IH.
  Qed.
End nat_LWO.

Definition size_rec {X: Type} (sigma: X -> nat) {p: X -> Type} :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  (forall x, p x).
Proof.
  intros F.
  enough (forall n x, sigma x < n -> p x) as H.
  { intros x. apply (H (S (sigma x))). lia. }
  induction n as [|n IH]; intros x H.
  - exfalso. lia.
  - apply F. intros y H1. apply IH. lia.
Defined.

Notation pi1 := projT1.
Notation pi2 := projT2.

Definition WO X :=
  forall (p: X -> Prop), decider p -> ex p -> sigT p.

Fact nat_wo :
  WO nat.
Proof.
  intros p H1 H2.
  enough (sig p) as [x H].
  { exists x. exact H. }
  apply constructive_indefinite_ground_description_nat; assumption.
Qed.
  
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
End List.
Arguments nrep {X}.

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

    
(*** Inverse functions *)

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.
Definition bijective {X Y} (f: X -> Y) :=
  injective f /\ surjective f.
Definition inv {X Y} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.
Fact inv_injective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> injective f.
Proof.
  intros H x x' H1 %(f_equal g). rewrite !H in H1. exact H1.
Qed.
Fact inv_surjective X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective g.
Proof.
  intros H x. exists (f x). apply H.
Qed.
Fact inv_injective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv f g -> injective f -> inv g f.
Proof.
  intros H1 H2 y. apply H2. rewrite H1. reflexivity.
Qed.
Fact inv_surjective_inv X Y (f: X -> Y) (g: Y -> X) :
  inv g f -> surjective f -> inv f g.
Proof.
  intros H1 H2 y.
  specialize (H2 y) as [x H2]. subst y. rewrite H1. reflexivity.
Qed.
Fact inv_agree X Y (f: X -> Y) (g g': Y -> X) :
  surjective f -> inv g f -> inv g' f -> forall y, g y = g' y.
Proof.
  intros H1 H2 H3 y.
  specialize (H1 y) as [x H1]. subst y. rewrite H2, H3. reflexivity.
Qed.

Fact inv_sigma X Y (f: X -> Y) :
  (forall y, { x & f x = y }) -> { g & inv f g }.
Proof.
  intros G. exists (fun y => pi1 (G y)).
  intros y. apply pi2.
Qed.

Fact injective_eqdec {X Y f} :
  @injective X Y f -> eqdec Y -> eqdec X.
Proof.
  intros H F x x'.
  destruct (F (f x) (f x')) as [H1|H1].
  - left. apply H, H1.
  - right. congruence.
Qed.

(*** Bijections *)

Definition bijection  X Y :=
  { f: X -> Y & { g & inv g f  /\ inv f g}}.

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

(*** Injections *)

Definition inv1 {X Y} (f: X -> Y) (g: Y -> option X) :=
  forall x, g (f x) = Some x.
Definition inv2 {X Y} (g: Y -> option X) (f: X -> Y) :=
  forall x y, g y = Some x -> f x = y.
Definition injection X Y :=
  { f & { g & @inv1 X Y f g /\ inv2 g f}}.

Fact inv1_injective X Y (f: X -> Y) g :
  inv1 f g -> injective f.
Proof.
  intros H x x'. generalize (H x), (H x'). congruence.
Qed.

Fact inv2_quasi_injective X Y (f: X -> Y) g y y' :
  inv2 g f -> g y <> None -> g y = g y' -> y = y'.
Proof.
  intros H1 H2 H3.
  destruct (g y) as [x|] eqn:H4. 2:congruence.
  destruct (g y') as [x'|] eqn:H5. 2:congruence.
  apply H1 in H4. apply H1 in H5. congruence.
Qed.

Fact injection_injective {X Y} :
  forall C: injection X Y,  injective (pi1 C).
Proof.
  intros (f&g&H1&H2). cbn. eapply inv1_injective, H1.
Qed.

Fact injection_refl X :
  injection X X.
Proof.
  exists (fun x => x). exists Some. split; hnf; congruence.
Qed.

Fact injection_trans X Y Z :
  injection X Y -> injection Y Z -> injection X Z.
Proof.
  intros (f&g&H1&H2) (f'&g'&H1'&H2').
  exists (fun x => f' (f x)).
  exists (fun z => match g' z with Some y => g y | None => None end).
  split; hnf.
  - intros x. rewrite H1'. apply H1.
  - intros x y.
    destruct (g' y) as [x'|] eqn:H. 2:{ intros [=]. }
    intros H3%H2. apply H2' in H. congruence.
Qed.

Fact bijection_injection {X Y} :
  bijection X Y -> injection X Y.
Proof.
  intros (f&g&H1&H2). exists f. exists (fun y => Some (g y)). split; hnf.
  - intros x. f_equal. apply H1.
  - intros x y H. generalize (H2 y). congruence.
Qed.

Fact injection_option X :
  injection X (option X).
Proof.
  exists Some. exists (fun a => a). split; hnf; congruence.
Qed.

Fact injection_eqdec X Y :
  injection X Y -> eqdec Y -> eqdec X.
Proof.
  intros H1 H2.
  eapply injective_eqdec. 2:exact H2.
  exact (injection_injective H1).
Qed.

Fact injection_wo X Y :
  injection X Y -> WO Y -> WO X.
Proof.
  intros (f&g&H&_) W p H1 H2.
  destruct (W (fun y => match g y with Some x => p x | None => False end)) as [y H3].
  - intros y. destruct (g y) as [x|]. apply H1. right. auto.
  - destruct H2 as [x H2]. exists (f x). rewrite H. exact H2.
  - destruct (g y) as [x|]. eauto. destruct H3.
Qed.

Fact injection_upgrade' X Y f g :
  eqdec Y -> @inv1 X Y f g -> { g' | inv1 f g' /\ inv2 g' f}.
Proof.
  intros D H.
  exists (fun y => match g y with
           | Some x => if D (f x) y then Some x else None
           | None => None
           end).
  split; hnf.
  - intros x. specialize (H x). rewrite H.
    destruct D; congruence.
  - intros x y. specialize (H x).
    destruct (g y) as [x'|].
    + destruct D; congruence.
    + intros [=].
Qed.

Fact injection_upgrade X Y :
  eqdec Y -> {f & {g | @inv1 X Y f g}} -> injection X Y.
Proof.
  intros H1 (f&g&H2).
  edestruct injection_upgrade' as [g' H].
  exact H1. exact H2. exists f, g'. exact H.
Qed.

(*** Data types *)

Definition dat X :=
  injection X nat.

Fact nat_dat :
  dat nat.
Proof.
  apply injection_refl.
Qed.

Fact dat_eqdec X :
  dat X -> eqdec X.
Proof.
  intros H%injection_eqdec. exact H. exact nat_eqdec.
Qed.

Fact dat_wo {X} :
  dat X -> WO X.
Proof.
  intros H.
  eapply injection_wo. exact H. apply nat_wo.
Qed.

Fact dat_inv_inv {X Y} f :
  @bijective X Y f -> dat X -> eqdec Y -> { g | inv g f /\ inv f g }.
Proof.
  intros [H1 H2] H3 H4.
  enough { g & inv f g } as [g H5].
  { exists g. split. 2:exact H5.
    eapply inv_injective_inv; assumption. }
  apply inv_sigma. intros y.
  apply dat_wo. exact H3.
  - intros x; apply H4.
  - apply H2.
Qed.

Definition enum X := { g: nat -> option X | forall x, exists n, g n = Some x }.

Fact dat_enum X :
  dat X <=> eqdec X * enum X.
Proof.
  split.
  - intros H. split.
    + apply dat_eqdec, H.
    + destruct H as (f&g&H1&_). exists g.
      intros x. exists (f x). apply H1.
  - intros (D&g&H).
    apply injection_upgrade. exact nat_eqdec.
    assert (F: forall x, { n & g n = Some x }).
    { intros x.  apply nat_wo.
      - intros n. apply option_eqdec, D.
      - apply H. }
    exists (fun x => pi1 (F x)), g.
    hnf. intros x. apply (pi2 (F x)).
Qed.

(*** Order on data types *)

Fact tricho :
  forall X (D: dat X) x y,
    {pi1 D x < pi1 D y} + {x = y} + {pi1 D y < pi1 D x}.
Proof.
  intros *.
  edestruct lt_eq_lt_dec as [[H|H]|H].
  - left. left. exact H.
  - left. right. eapply injection_injective; eassumption.
  - right. exact H.
Qed.

Fact dat_LWO {X} (p: X -> Prop) :
  forall D: dat X, decider p -> sig p -> { x | p x /\ forall y, p y -> pi1 D x <= pi1 D y }.
Proof.
  intros D p_dec W.
  destruct D as (f&g&E1&E2). cbn in *.
  destruct (nat_LWO (fun n => match g n with Some x => p x | None => False end))
    as (n&H1&H2).
  - intros n. destruct (g n) as [x'|]. apply p_dec. hnf. auto.
  - destruct W as [x W]. exists (f x). rewrite E1. exact W.
  - hnf in H2.
    destruct (g n) as [x|] eqn:H3. 2:contradiction H1.
    apply E2 in H3 as <-.
    exists x. split. exact H1.
    intros y H4. apply H2. rewrite E1. exact H4.
Qed.

(*** Infinite data types *)

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

Definition generator X := forall A: list X, { x & x nel A }.

Fact generator_infinite X :
  generator X -> infinite X.
Proof.
  intros H A. specialize (H A) as [x H]. exists x. exact H.
Qed.

Fact generator_dat {X} :
  dat X -> infinite X -> generator X.
Proof.
  intros H1 H2 A. apply dat_wo. exact H1.
  - intros x.
    destruct (in_dec (dat_eqdec X H1) x A) as [H3|H3];
      unfold dec; auto.
  - apply H2.
Qed.

Fact generator_injective_nat X f :
  eqdec X -> @injective nat X f -> generator X.
Proof.
  intros H1 H2 B.
  pose (A:= map f (seq 0 (S (length B)))).
  edestruct (nrep_discriminate X H1 A B) as (x&H&_).
  - apply nrep_map. exact H2. apply seq_nrep.
  - subst A. rewrite map_length, seq_length. lia.
  - exists x. exact H. 
Qed.

(*** Infinite data types *)

Section Compression.
  Variable X: Type.
  Variable X_dat: dat X.
  Variable X_infinite: infinite X.
  Implicit Types x y : X.
  Implicit Types A B : list X.

  Let X_eqdec := dat_eqdec X X_dat.
  Let g : nat -> option X := let (_,H) := X_dat in let (g,_) := H in g.
  
  Fact g_surjective x :
    { n | g n = Some x}.
  Proof.
    destruct X_dat as (f&g'&H). exists (f x). apply H.
  Qed.
  
  Fixpoint G n : list X :=
    match n with
      0 => []
    | S n' => match g n' with
               Some x => x :: G n'
             | None => G n'
             end
    end.

  Fact G_inc n :
    G n <<= G (S n).
  Proof.
    intros x. cbn. destruct (g n) as [y|]; cbn; auto.
  Qed.
  
  Fact G_cum m n :
    m <= n -> G m <<= G n.
  Proof.
    induction 1 as [|n _ IH]; intros x.
    - trivial. 
    - intros H %IH %G_inc. exact H.
  Qed.

  Fact G_in n x :
    g n = Some x -> x el G (S n).
  Proof.
    cbn. destruct (g n) as [y|].
    - intros [= ->]. cbn; auto.
    - intros [=].
  Qed.

  Lemma Phi A :
    { x & x nel A /\ exists n, g n = Some x /\ G n <<= A }.
  Proof.
    edestruct (generator_dat X_dat X_infinite A) as [x0 H].
    destruct (g_surjective x0) as [n0 H1].
    enough (forall k, k <= n0 -> G k <<= A ->
                 { x & x nel A /\ exists n, g n = Some x /\ G n <<= A }) as H0.
    { apply (H0 0). lia. intros x []. }
    refine (size_rec (fun k => n0 - k) _). intros k IH H0 H2.
    destruct (g k) as [x|] eqn:H3.
    - destruct (in_dec X_eqdec x A) as [H4|H4].
      + destruct (nat_eqdec k n0) as [->|H5].
        { exfalso. congruence. }
        apply (IH (S k)). lia. lia.
        intros y. cbn. rewrite H3. intros [<-|H6]. exact H4. apply H2, H6.
      + exists x. split. exact H4. exists k. auto.
    - destruct (nat_eqdec k n0) as [->|H5].
      { exfalso. congruence. }
      apply (IH (S k)). lia. lia.
      intros x. cbn. rewrite H3. apply H2.
  Qed.

  Definition phi: list X -> X :=
    fun A => pi1 (Phi A).
  
  Fact phi_new A :
    phi A nel A.
  Proof.
    unfold phi. destruct (Phi A) as (x&H1&H2). exact H1.
  Qed.
  
  Fact phi_min A :
    exists n, g n = Some (phi A) /\ G n <<= A.
  Proof.
    unfold phi. destruct (Phi A) as (x&H1&H2). exact H2.
  Qed.

  Fact phi_neq x A :
    x el A -> x <> phi A.
  Proof.
    intros H ->. eapply phi_new, H.
  Qed.

  Fixpoint H n : list X :=
    match n with
      0 => nil
    | S n' => phi (H n') :: H n'
    end.

  Fact H_inc n :
    H n <<= H (S n).
  Proof.
    intros x. cbn; auto.
  Qed.

  Fact H_cum m n :
    m <= n -> H m <<= H n.
  Proof.
    induction 1 as [|n _ IH]; intros x.
    - trivial. 
    - intros H %IH %H_inc. exact H.
  Qed.

  Definition h n : X := phi (H n).

  Lemma h_in_H n :
    h n el H (S n).
  Proof.
    unfold h. cbn; auto.
  Qed.
  
  Lemma h_injective' m n :
    m < n -> h m <> h n.
  Proof.
    intros H. apply phi_neq. apply (H_cum (S m)). lia. apply h_in_H.
  Qed.

  Fact h_injective :
    injective h.
  Proof.
    intros m n H1. 
    assert (m < n \/ m = n \/ n < m) as [H|[H|H]] by lia.
    - exfalso. eapply h_injective'; eassumption.
    - congruence.
    - exfalso. eapply h_injective'; eauto.
  Qed.

  Fact G_incl_H n :
    G n <<= H n.
  Proof.
    induction n as [|n IH].
    - intros x; auto.
    - cbn. destruct (g n) as [x|] eqn:H0.
      2:{ intros x H1%IH. cbn; auto. }
      intros y [<-|H1]. 2:{ right. apply IH, H1. }
      destruct (in_dec X_eqdec x (H n)) as [H1|H1].
      { right. exact H1. }
      destruct (X_eqdec (phi (H n)) x) as [H'|H'].
      { cbn. auto. }
      exfalso.
      destruct (phi_min (H n)) as (k&H2&H3).
      assert (k < n \/ k = n \/ n < k) as [H4|[H4|H4]] by lia.
      + apply (phi_new (H n)), IH.
        assert (H5: phi (H n) el G (S k)).
        { cbn. rewrite H2. left. reflexivity. }
        apply G_cum in H4. apply H4, H5.
      + congruence.
      + apply H1, H3.
        assert (H5: x el G (S n)).
        { cbn. rewrite H0. left. reflexivity. }
        apply G_cum in H4. apply H4, H5.
  Qed.

  Fact H_in x n :
    x el H n -> exists k, h k = x.
  Proof.
    induction n as [|n IH].
    - intros [].
    - intros [<-|H1].
      + exists n. reflexivity.
      + specialize (IH H1) as (k&<-). eauto.
  Qed.
  
  Fact h_surjective :
    surjective h.
  Proof.
    intros x.
    destruct (g_surjective x) as [n [k <-] %G_in %G_incl_H %H_in].
    eauto.
  Qed.

  Fact compression :
    { h: nat -> X | bijective h }.
  Proof.
    exists h. split. exact h_injective. exact h_surjective.
  Qed.

End Compression.

Theorem dat_infinite_bijection X :
  dat X -> infinite X -> bijection X nat.
Proof.
  intros H1 H2.
  destruct (compression X H1 H2) as [g H].
  destruct (dat_inv_inv g) as [f H3].
  - exact H.
  - apply nat_dat.
  - apply dat_eqdec, H1.
  - exists f, g. split; apply H3.
Qed.

Fact sandwich_nat X :
  injection nat X -> injection X nat -> bijection X nat.
Proof.
  intros H1 H2.
  apply dat_infinite_bijection. exact H2.
  apply generator_infinite.
  eapply generator_injective_nat.
  - eapply dat_eqdec. exact H2.
  - exact (injection_injective H1).
Qed.

  
