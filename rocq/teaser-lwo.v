From Stdlib Require Import Lia.
Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Arguments Nat.sub : simpl nomatch.
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Definition dec (X: Type) : Type := X + ~X.
Notation decider p := (forall x, dec (p x)).
Notation unique p := (forall x x', p x -> p x' -> x = x').

Implicit Types (n k x: nat) (p: nat -> Prop).

Definition safe p n := forall k, k < n -> ~p k.
Definition least p n := p n /\ safe p n.

Fact least_unique p : unique (least p).
Proof.
  intros n n' [H1 H2] [H1' H2'].
  enough (~(n < n') /\ ~(n' < n)) by lia.
  split; intros H.
  - eapply H2'; eassumption.
  - eapply H2; eassumption.
Qed.

Fact safe_O p :
  safe p 0.
Proof.
  hnf. lia.
Qed.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  intros H1 H2 k H3. unfold safe in *.
  assert (k < n \/ k = n) as [H|H] by lia.
  - apply H1. easy.
  - congruence.
Qed.

Section LWO.
  Variable p : nat -> Prop.
  Variable p_dec : decider p.

  (*** Certifying LWO *)

  Lemma lwo_cert :
    forall n, (Sigma k, k < n /\ least p k) + safe p n.
  Proof.
    induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [[k H1]|H1].
      + left. exists k. destruct H1 as [H1 H2]. split. lia. exact H2.
      + destruct (p_dec n).
        * left. exists n. split. lia. easy.
        * right. apply safe_S; assumption.
  Qed.
  
  Fact safe_dec n :
    dec (safe p n).
  Proof.
    destruct (lwo_cert n) as [[k H1]|H1].
    - right. intros H. exfalso.
      destruct H1 as [H1 H2]. apply (H k). exact H1. apply H2.
    - left. exact H1.
  Qed.

  Fact least_dec n :
    dec (least p n).
  Proof.
    unfold least.
    destruct (p_dec n) as [H|H].
    - destruct (safe_dec n) as [H1|H1].
      + left. easy.
      + right. tauto.
    - right. tauto.
  Qed.

  Fact lwo_sig :
    sig p -> sig (least p).
  Proof.
    intros [n H].
    destruct (lwo_cert n) as [(k&H1&H2)|H2].
    - eauto.
    - exists n. easy.
  Qed.

  Fixpoint G n : option nat :=
    match n with
    | 0 => None
    | S n => match G n with
            | None => if p_dec n then Some n else None
            | a => a
            end
    end.
  
  Definition phi n a :=
    match a with
    | Some k => k < n /\ least p k
    | None => safe p n
    end.

  Lemma G_correct n :
    phi n (G n).
  Proof.
    hnf; induction n; cbn.
    - apply safe_O.
    - destruct (G n) as [k|].
      + split. lia. easy.
      + destruct (p_dec n) as [H|H].
        * split. lia. easy.
        * apply safe_S; easy.
  Qed.

  Fact phi_unique n a a' :
    phi n a -> phi n a' -> a = a'.
  Proof.
    destruct a as [k|], a' as [k'|]; cbn.
    - generalize (least_unique p k k').
      intuition congruence.
    - firstorder.
    - firstorder.
    - easy.
  Qed.

  (*** LWO without options *)

  Definition psi n x :=
    (x < n /\ least p x) \/ (x = n /\ safe p n).

  Fixpoint G' n : nat :=
    match n with
    | 0 => 0
    | S n => let x := G' n in
            if S x - n then x
            else if p_dec n then n else S n
    end.

  Lemma G'_correct n :
    psi n (G' n).
  Proof.
    hnf; induction n; cbn.
    - right. easy.
    - specialize (IHn) as [[IH1 IH2]|[IH1 IH2]].
      + replace (S (G' n) - n) with 0 by lia.
        auto.
      + rewrite IH1.
        replace (S n - n) with 1 by lia.
        destruct (p_dec n) as [H|H].
        * left. split. lia. easy.
        * right. split. easy. apply safe_S; easy.
  Qed.

  Fact psi_unique n a a' :
    psi n a -> psi n a' -> a = a'.
  Proof.
    intros [(H1&H2)|(H1&H2)] [(H1'&H2')|(H1'&H2')].
    - eapply least_unique; eassumption.
    - exfalso. firstorder.
    - exfalso. firstorder.
    - congruence.
  Qed.
  
  Lemma G'_agree n :
    G' n = match G n with Some x => x | None => n end.
  Proof.
    apply (psi_unique n).
    - apply G'_correct.
    -  assert (H:= G_correct n).
       unfold phi in H. unfold psi.
      destruct (G n) as [x|]; auto.
  Qed.
    
  (*** Linear Search *)

  Fact ls_cert' :
    forall n k, safe p k -> sig (psi (n + k)).
  Proof.
    induction n; intros k H.
    - exists k. right. easy.
    - destruct (p_dec k) as [H1|H1].
      + exists k. left. split. lia. easy.
      + specialize (IHn (S k)).
        replace (S n + k) with (n + S k) by lia.
        apply IHn. apply safe_S; easy.
  Qed.

  Fixpoint L' n k : nat :=
    match n with
    | 0 => k
    | S n => if p_dec k then k else L' n (S k)
    end.

  Fact L'_correct :
    forall n k, safe p k -> psi (n + k) (L' n k).
  Proof.
    induction n; intros k H; cbn.
    - right. easy.
    - destruct (p_dec k) as [H1|H1]; cbn.
      + left. split. lia. easy.
      + replace (S (n + k)) with (n + S k) by lia.
        apply IHn. apply safe_S; easy.
  Qed.
  
  Fact L'_correct' n :
    psi n (L' n 0).
  Proof.
    replace n with (n + 0) at 1 by lia.
    apply L'_correct. apply safe_O.
  Qed.

  Fact lwo'_agree  n :
    G' n = L' n 0.
  Proof.
    eapply psi_unique.
    - apply G'_correct.
    - apply L'_correct'.
  Qed.
End LWO.

(*** Excluded Middle *)

Definition XM := forall P: Prop, P \/ ~P.
Definition LWE := forall p: nat -> Prop, ex p -> ex (least p).

Fact LWE_XM :
  LWE -> XM.
Proof.
  intros H P.
  specialize (H (fun n => if n then P else True)) as (k&H1&H2).
  - exists 1. exact I.
  - destruct k.
    + left. exact H1.
    + unfold safe in H2. specialize (H2 0); cbn in H2.
      right. apply H2. lia.
Qed.

Section XM.
  Variable xm : XM.
  Variable p : nat -> Prop.
 
  Fact xm_lwo :
    forall n, (exists k, k < n /\ least p k) \/ safe p n.
  Proof.
    induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [(k&H1&H2)|H1].
      + left. exists k. split. lia. exact H2.
      + destruct (xm (p n)).
        * left. exists n. split. lia. easy.
        * right. apply safe_S; assumption.
  Qed.

  Definition xm_least_ex :
    ex p -> ex (least p).
  Proof.
    intros [n H].
    destruct (xm_lwo (S n)) as [(k&H1&H2)|H1].
    - exists k. exact H2.
    - exfalso. apply (H1 n). lia. exact H.
  Qed.
End XM.

Fact XM_LWE :
  XM -> LWE.
Proof.
  intros xm p. apply (xm_least_ex xm).
Qed.
