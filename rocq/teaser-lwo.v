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

Implicit Types (n k: nat) (p: nat -> Prop).

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

  Lemma lwo_cert :
    forall n, (Sigma k, k < n /\ least p k) + safe p n.
  Proof.
    hnf. induction n as [|n IH].
    - right. apply safe_O.
    - destruct IH as [[k H1]|H1].
      + left. exists k. destruct H1 as [H1 H2]. split. lia. exact H2.
      + destruct (p_dec n).
        * left. exists n. split. lia. easy.
        * right. apply safe_S; assumption.
  Qed.

  Fixpoint lwo n : option nat :=
    match n with
    | 0 => None
    | S n => match lwo n with
            | None => if p_dec n then Some n else None
            | a => a
            end
    end.
  
  Definition phi n a :=
    match a with
    | Some k => k < n /\ least p k
    | None => safe p n
    end.

  Lemma lwo_correct n :
    phi n (lwo n).
  Proof.
    unfold phi.
    induction n; cbn.
    - apply safe_O.
    - destruct (lwo n) as [k|].
      + intuition lia.
      + destruct (p_dec n) as [H|H].
        * split. lia. easy.
        * apply safe_S; easy.
  Qed.

  Fixpoint lsearch n k : option nat :=
    match n with
    | 0 => None
    | S n => if p_dec k then Some k else lsearch n (S k)
    end.

  Lemma lsearch_correct n k :
    safe p k -> phi (n + k) (lsearch n k).
  Proof.
    revert k; induction n; intros k H; cbn.
    - exact H.
    - destruct (p_dec k) as [H1|H1]; cbn.
      + split. lia. easy. 
      + specialize (IHn (S k)).
        replace (S(n + k)) with (n + S k) by lia.
        apply IHn. apply safe_S; assumption.
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
  
  Fact lwo_lsearch_agree n :
    lwo n = lsearch n 0.
  Proof.
    apply (phi_unique n).
    - apply lwo_correct.
    - replace n with (n + 0) at 1 by lia.
      apply lsearch_correct.
      easy.
  Qed.

  Fact lsearch_cert' :
    forall n k, safe p k ->
           Sigma a, (a < (n + k)%nat /\ least p a) + (a = (n + k)%nat /\ safe p (n + k)).
  Proof.
    induction n; intros k H.
    - exists k. right. easy.
    - destruct (p_dec k) as [H1|H1].
      + exists k. left. split. lia. easy.
      + specialize (IHn (S k)) as [a IH].
        * apply safe_S; assumption.
        * exists a.
          destruct IH as [[IH1 IH2]|[IH1 IH2]].
          -- left. split. lia. easy.
          -- right. replace (S n + k) with (n + S k) by lia. easy.
  Qed.

  Fixpoint lsearch' n k : nat :=
    match n with
    | 0 => k
    | S n => if p_dec k then k
            else lsearch' n (S k)
    end.

  Definition psi n k a :=
    (a < n + k /\ least p a) \/ (a = n + k /\ safe p (n +k)).

  Fact lsearch'_correct :
    forall n k, safe p k -> psi n k (lsearch' n k).
  Proof.
    induction n; intros k H.
    - right. easy.
    - cbn. destruct (p_dec k) as [H1|H1].
      + left. split. lia. easy.
      + specialize (IHn (S k)) as [[IH1 IH2]|[IH1 IH2]].
        * apply safe_S; assumption.
        * left. split. lia. easy.
        * right. replace (S n + k) with (n + S k) by lia. easy. 
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
