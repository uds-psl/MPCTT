From Coq Require Import Arith Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decidable p := (forall x, dec (p x)).
Notation unique p := (forall x y, p x -> p y -> x = y).

Definition nat_eqdec : eqdec nat.
Proof.
  intros x y.
  destruct (Nat.eq_dec x y) as [H|H].
  - left. exact H.
  - right. exact H.
Defined.

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
  intros ->. easy.
Qed.


(*** Step-Indexed Linear Search *)


Section Step_indexed_linear_search.
  Variable p: nat -> Prop.
  Variable p_dec: decidable p.
  
  Fixpoint L n k : nat :=
    match n with
    | 0 => k
    | S n' => if p_dec k then k else L n' (S k)
    end.

  Lemma L_correct' :
    forall n k, p (n + k) -> safe p k -> least p (L n k).
  Proof.
    induction n as [|n IH]; cbn; intros k H1 H2.
    - easy.
    - destruct (p_dec k) as [H|H].
      + easy.
      + apply IH. 
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S; assumption.
  Qed.

  Lemma L_correct n :
    p n -> least p (L n 0).
  Proof.
    intros H. apply L_correct'.
    - replace (n + 0) with n by lia. exact H.
    - apply safe_O.
  Qed.

  Lemma least_linear_sigma' :
    forall n k, p (n + k) -> safe p k -> sig (least p).
  Proof.
    induction n as [|n IH]; intros k H1 H2.
    - exists k. easy.
    - destruct (p_dec k) as [H|H].
      + exists k. easy.
      + apply (IH (S k)).
        * replace (n + S k) with (S n + k) by lia. exact H1.
        * apply safe_S; assumption.
  Qed.

  Lemma least_linear_sigma :
    sig p -> sig (least p).
  Proof.
    intros [n H].
    apply (least_linear_sigma' n 0).
    - replace (n + 0) with n by lia. exact H.
    - apply safe_O.
  Qed.
End Step_indexed_linear_search.

(*** Direct Search *)

Section Direct_search.
  Variable p: nat -> Prop.

  (** Certifying version *)

  Variable p_dec: decidable p.
  
  Lemma least_direct_sigma' :
    forall n, safe p n + sig (least p).
  Proof.
    induction n as [|n IH].
    - left. apply safe_O.
    - destruct IH as [IH|IH].
      + destruct (p_dec n) as [H|H].
        * right. exists n. easy.
        * left. apply safe_S; assumption.
      + right. exact IH.
  Qed.

  Lemma least_direct_sigma :
    sig p -> sig (least p).
  Proof.
    intros [n H].
    destruct (least_direct_sigma' n) as [H1|H1].
    - exists n. easy.
    - exact H1.
  Qed.

  Fact least_ex :
    ex p -> ex (least p).
  Proof.
    intros [n H].
    edestruct least_direct_sigma as [k H1].
    - exists n. exact H.
    - exists k. exact H1.
  Qed.

  Fact least_dec :
    decidable (least p).
  Proof.
    intros n.
    destruct (p_dec n) as [H|H].
    2:{ right. contradict H. apply H. }
    destruct (least_direct_sigma (Sig _ n H)) as [k H1].
    destruct (nat_eqdec k n) as [->|H2].
    - left. exact H1.
    - right. contradict H2. eapply least_unique; eassumption.
  Qed.

  (** Simply-typed version *)

  Fixpoint D n : option nat :=
    match n with
    | 0 => None
    | S n' => match D n' with
             | Some x => Some x
             | None => if p_dec n' then Some n' else None
             end
    end.

  Definition W n : nat :=
    match D n with
    | Some x => x
    | None => n
    end.

  Fact D_correct n :
    match D n with
    | Some x => least p x
    | None => safe p n
    end.
  Proof.
    induction n as [|n IH]; cbn.
    - apply safe_O.
    - destruct (D n) as [x|].
      + exact IH.
      + destruct (p_dec n) as [H|H].
        * easy.
        * apply safe_S; assumption.
  Qed.

  Fact W_correct n :
    p n -> least p (W n).
  Proof.
    intros H. unfold W. generalize (D_correct n).
    destruct (D n) as [x|]; easy.
  Qed.

  (** Derivation rules *)

  Definition delta n (a: option nat) : Prop :=
    match a with None => safe p n | Some x => least p x end.

  Fact delta1 :
    delta 0 None.
  Proof.
    apply safe_O.
  Qed.
  
  Fact delta2 n x :
    delta n (Some x) -> delta (S n) (Some x).
  Proof.
    easy.
  Qed.
  
  Fact delta3 n :
    delta n None -> p n -> delta (S n) (Some n).
  Proof.
    easy.
  Qed.
  
  Fact delta4 n :
    delta n None -> ~p n -> delta (S n) None.
  Proof.
    intros H1 H2. apply safe_S; assumption.
  Qed.

  Goal forall n, delta n (D n).
  Proof.
    induction n as [|n IH].
    - apply delta1.
    - cbn. destruct (D n) as [x|].
      + apply delta2, IH.
      + destruct (p_dec n) as [H|H].
        * apply delta3; assumption.
        * apply delta4; assumption.
  Qed.
  
  Goal forall n, sig (delta n).
  Proof.
    induction n as [|n IH]; cbn.
    - exists None. apply delta1.
    - destruct IH as [[x|] IH].
      + exists (Some x). apply delta2, IH.
      + destruct (p_dec n) as [H|H].
        * exists (Some n). apply delta3; assumption.
        * exists None. apply delta4; assumption.
  Qed.

  Goal forall n, sig (delta n) <=> safe p n + sig (least p).
  Proof.
    split.
    - intros [[x|] H].
      + right. exists x. exact H.
      + left. exact H.
    - intros [H|[x H]].
      + exists None. exact H.
      + exists (Some x). exact H.
  Qed.
End Direct_search.

(*** XM and Least Elements *)
 
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
        * right. exists n. easy.
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
    + exists 1. exact I.
    + destruct n.
      * left. exact H1. 
      * right. intros H3. specialize (H2 0). hnf in H2. apply H2 in H3. lia.
Qed.

    


