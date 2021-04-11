From Coq Require Import Arith Lia.
Definition dec P := { P } + { ~P }.
Notation decidable p := (forall x, dec (p x)).
Notation unique p := (forall x y, p x -> p y -> x = y).
Definition eqdec X := forall x y: X, dec (x = y).
Definition nat_eqdec : eqdec nat := Nat.eq_dec.

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
  intros ->. auto.
Qed.

Section Least.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.

  Lemma least_sigma_safe :
    forall n, safe p n + { k & least p k }.
  Proof.
    induction n as [|n IH].
    - left. apply safe_O.
    - destruct IH as [IH|IH].
      + destruct (p_dec n) as [H|H].
        * right. exists n. hnf. auto.
        * left. apply safe_S; assumption.
      + right. exact IH.
  Qed.

  Lemma least_sigma :
    sigT p -> sigT (least p).
  Proof.
    intros [n H].
    destruct (least_sigma_safe n) as [H1|H1].
    2:exact H1.
    exists n. hnf. auto.
  Qed.

  Fact least_ex :
    ex p -> ex (least p).
  Proof.
    intros [n H].
    edestruct least_sigma as [k H1].
    - exists n. exact H.
    - exists k. exact H1.
  Qed.

  Fact least_dec :
    decidable (least p).
  Proof.
    intros n.
    destruct (p_dec n) as [H|H].
    2:{ right. contradict H. apply H. }
    edestruct least_sigma as [k H1].
    - exists n. exact H.
    - destruct (nat_eqdec k n) as [->|H2].
      + left. exact H1.
      + right. contradict H2.
        eapply least_unique; eassumption.
  Qed.
End Least.

Section Least_bool.
  Variable f: nat -> bool.

  Fixpoint L' n : option nat :=
    match n with
    | 0 => None
    | S n' => match L' n' with
             | Some x => Some x
             | None => if f n' then Some n' else None
             end
    end.

  Definition L n : nat :=
    match L' n with
    | Some x => x
    | None => n
    end.

  Fact L'_correct n :
    match L' n with
    | Some x => least (fun n => f n = true) x
    | None => safe (fun n => f n = true) n
    end.
  Proof.
    induction n as [|n IH]; cbn.
    - apply safe_O.
    - destruct (L' n) as [x|].
      + exact IH.
      + destruct (f n) eqn:H.
        * split; assumption.
        * apply safe_S. exact IH. congruence.
  Qed.

  Fact L_correct n :
    f n = true -> least (fun n => f n = true) (L n).
  Proof.
    intros H. unfold L. generalize (L'_correct n).
    destruct (L' n) as [x|].
    - auto.
    - intros H1. split; assumption.
  Qed.
End Least_bool.


Section Least_linear_search.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.

  Lemma least_linear_sigma_safe :
    forall n k, p (n + k) -> safe p k -> sigT (least p).
  Proof.
    induction n as [|n IH].
    - intros k H1 H2. exists k. hnf. auto.
    - intros k H1 H2.
      destruct (p_dec k) as [H|H].
      + exists k. hnf. auto.
      + apply (IH (S k)).
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S; assumption.
  Qed.

  Lemma least_linear_sigma :
    sigT p -> sigT (least p).
  Proof.
    intros [n H].
    apply (least_linear_sigma_safe n 0).
    - replace (n + 0) with n by lia. exact H.
    - apply safe_O.
  Qed.
End Least_linear_search.

Module Least_linear_search_bool.
Section S.
  Variable f: nat -> bool.

  Fixpoint L n k : nat :=
    match n with
    | 0 => k
    | S n' => if f k then k else L n' (S k)
    end.

  Lemma L_correct' :
    forall n k, f (n + k) = true -> safe (fun n => f n = true) k -> least (fun n => f n = true) (L n k).
  Proof.
    induction n as [|n IH]; intros k H1 H2; cbn.
    - hnf. auto.
    - destruct (f k) as [H|H] eqn:H3.
      + hnf. auto.
      + apply IH.
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S. exact H2. congruence.
  Qed.

  Lemma L_correct :
    forall n, f n = true -> least (fun n => f n = true) (L n 0).
  Proof.
    intros n H. apply L_correct'.
    - replace (n + 0) with n by lia. exact H.
    - hnf. lia.
  Qed.
End S.
End Least_linear_search_bool.
 
Lemma least_ex_or (p: nat -> Prop):
  (forall x, p x \/ ~p x) -> ex p -> ex (least p).
Proof.
  intros p_dec [k H].
  enough (forall n, safe p n \/ ex (least p)) as H1.
  { specialize (H1 k) as [H1|H1]. 2:exact H1. exists k. hnf. auto. }
  induction n as [|n IH].
  - left. apply safe_O.
  - destruct IH as [IH|IH].
      + destruct (p_dec n) as [H1|H1].
        * right. exists n. hnf. auto.
        * left. apply safe_S; assumption.
      + right. exact IH.
Qed.
  
Definition XM := forall P, P \/ ~P.

Fact least_xm :
  XM <->  (forall p, ex p -> ex (least p)).
Proof.
  split.
  - intros H p. apply least_ex_or. intros x. apply H.
  - intros H P.
    destruct (H (fun x => if x then P else True)) as (n&H1&H2).
    { exists 1. exact I. }
    destruct n.
    { auto. } 
    right. intros H3. hnf in H2. specialize (H2 0). apply H2 in H3. lia.
Qed.

    


