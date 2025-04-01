(*** MPCTT, Chapter Least Witness Operators *)

Arguments Nat.sub : simpl nomatch.
From Stdlib Require Import Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sig (fun x => .. (sig (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation decider p := (forall x, dec (p x)).
Notation unique p := (forall x x', p x -> p x' -> x = x').

Implicit Types (n k: nat) (p: nat -> Prop).

(*** Least Witness Predicate *)

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
  - auto.
  - congruence.
Qed.

Fact safe_char p n :
  safe p n <-> forall k, p k -> k >= n.
Proof.
  split.
  - intros H k H1.
    enough (k < n -> False) by lia.
    intros H2. apply H in H2. auto.
  - intros H k H1 H2. apply H in H2. lia.
Qed.

Fact safe_char_S p n :
  safe p (S n) <-> safe p n /\ ~p n.
Proof.
  split.
  - intros H. split.
    + intros k H1. apply H. lia.
    + apply H. lia.
  - intros [H1 H2]. apply safe_S; assumption.
Qed.

Fact safe_eq p n k :
  safe p n -> k <= n  -> p k -> k = n.
Proof.
  intros H1 H2 H3. unfold safe in *.
  enough (~(k < n)) by lia.
  specialize (H1 k). tauto.
Qed.

Fact E14 x y z :
  x - y = z <-> least (fun k => x <= y + k) z.
Proof.
  assert (H: least (fun k => x <= y + k) (x - y)).
  { split; unfold safe; lia. }
  split. congruence.
  eapply least_unique, H.
Qed.  

(*** Certifying LWOs *)

Section LWO.
  Variable p : nat -> Prop.
  Variable p_dec : decider p.

Definition lwo :
  forall n, (Sigma k, k < n /\ least p k) + safe p n.
Proof.
  induction n as [|n IH].
  - right. apply safe_O.
  - destruct IH as [[k H1]|H1].
    + left. exists k. destruct H1 as [H1 H2]. split. lia. exact H2.
    + destruct (p_dec n).
      * left. exists n. split. lia. easy.
      * right. apply safe_S; assumption.
Defined.

(** Note that the script for "lwo" is closed with "Defined"
    rather than "Qed".  This way "lwo" is transparent 
    rather than abstract and reduces.  To fully reduce, 
    the script must separate the computational level 
    from the propositional level where automation tactics 
    will insert abstract proof functions.  In particular,
    one must be careful to not destructure conjuctions  
    at the computational level.  For this reason the
    "destruct H1" in the above script is placed at the
    propositionsal level rather than the computational level.
    It would be helpful if there was a way to impose the
    discrimination restriction on conjunctions so that a
    misplaced destructuring of a conjunction would not
    type check.             

    Eventually we will arrive at a reducible certifying decider
    deciding primality by computation.   

    If all occurrences of "Defined" in this file are replaced 
    with "Qed", everaything stays intact but the "Compute" commands.    
 *)

Definition lwo' :
  forall n, (Sigma k, k <= n /\ least p k) + safe p (S n).
Proof.
  intros n.
  destruct (lwo (S n)) as [(k&H1&H2)|H].
  - left. exists k. split. lia. exact H2.
  - right.  exact H.
Qed.

Definition least_sig :
  sig p -> sig (least p).
Proof.
  intros [n H].
  destruct (lwo (S n)) as [(k&H1&H2)|H1].
  - exists k. exact H2.
  - exfalso. apply (H1 n). lia. exact H.
Qed.

Definition least_ex :
  ex p -> ex (least p).
Proof.
  intros [n H].
  destruct (lwo (S n)) as [(k&H1&H2)|H1].
  - exists k. exact H2.
  - exfalso. apply (H1 n). lia. exact H.
Qed.

(** Exercise: greatest witness operator *)

Definition greatest n k := p k /\ k < n  /\ forall i, k < i < n -> ~p i.

Definition gwo :
  forall n, sig (greatest n) + (forall k, k < n -> ~p k).
Proof.
  induction n as [|n IH].
  - right. lia.
  - destruct (p_dec n) as [H|H].
    + left. exists n. repeat split. easy. lia. lia.
    + destruct IH as [[k IH]|IH].
      * left. exists k. destruct IH as (IH1&IH2&IH3).
        repeat split. easy. lia.
        intros i H1.
        assert (i = n \/ i < n) as [->|H2] by lia.
        -- easy.
        -- apply IH3. lia.
      * right. intros k H1.
        assert (k = n \/ k < n) as [->|H5] by lia.
        -- easy.
        -- apply IH. easy.
Qed.


(*** Decidability Results *)

Definition safe_dec n :
  dec (safe p n).
Proof.
  destruct (lwo n) as [[k H1]|H1].
  - right. intros H. exfalso.
    destruct H1 as [H1 H2]. apply (H k). exact H1. apply H2.
  - left. exact H1.
Defined.

Definition least_dec n :
  dec (least p n).
Proof.
  unfold least.
  destruct (p_dec n) as [H|H].
  2:{ right. tauto. }
  destruct (safe_dec n) as [H1|H1].
  - left. easy.
  - right. tauto.
Qed.
End LWO.

Fact DM_fin_exists p n :
  ~(exists k, k < n /\ p k) <-> (forall k, k < n -> ~p k).
Proof.
  split.
  - intros H1 k H2. contradict H1. eauto.
  - intros H (k&H1&H2). apply (H k); assumption.
Qed.

Definition neg p n := ~p n.
Definition neg_dec p : decider p -> decider (neg p).
Proof.
  unfold neg. intros H n.
  destruct (H n) as [H1|H1].
  - right. auto.
  - left. easy.
Defined.
Fact neg_equiv p n :
  decider p -> ~neg p n <-> p n.
Proof.
  unfold dec, neg. intros H. specialize (H n). tauto.
Qed.
  

Section Dec.
  Variable p : nat -> Prop.
  Variable p_dec : decider p.
 
  Fact DM_fin_forall n :
    ~(forall k, k < n -> p k) <-> (exists k, k < n /\ ~p k).
  Proof.
    split.
    - intros H.
      destruct (lwo (neg p) (neg_dec p p_dec) n) as [(k&H1&H2)|H1].
      + exists k. split. exact H1. apply H2.
      + exfalso.  apply H. intros k H2.
        apply neg_equiv, H1, H2. exact p_dec.
    - intros (k&H2&H3) H. exfalso. auto.
  Qed.
  
  Definition forall_fin_dec n :
    dec (forall k, k < n -> p k).
  Proof.
    destruct (safe_dec (neg p) (neg_dec p p_dec) n) as [H|H].
    - left. intros k H1. apply neg_equiv, H, H1. exact p_dec.
    - right. contradict H. intros k H1. apply neg_equiv, H, H1. exact p_dec.
  Defined.

  Definition exists_fin_dec n :
    dec (exists k, k < n /\ p k).
  Proof.
    destruct (lwo p p_dec n) as [[k H1]|H1].
    - left. exists k. destruct H1 as [H1 H2]. split. exact H1. apply H2.
    - right. apply DM_fin_exists, H1.
  Defined.
End Dec.

(*** Decidability of Primality *)

Definition divides n x : Prop :=
  x <> 0 -> n <> 1 -> n <> x -> exists k, k < x /\ x = k * n.
Notation "( n | x )" := (divides n x) (at level 0) : nat_scope.
Definition prime x := x >= 2 /\ forall k, k < x -> (k | x) -> k = 1.

Definition nat_eqdec : eqdec nat.
Proof.
  intros x y.
  destruct ((x - y) + (y - x)) eqn:?.
  - left; lia.
  - right; lia.
Defined.

Definition le_lt_dec x y :
  (x <= y) + (x > y).
Proof.
  destruct (x - y) eqn:?.
  - left; lia.
  - right; lia.
Defined.

Fact divides_equiv n x :
  (n | x) <-> exists k, x = k * n.
Proof.
  unfold divides; split.
  - intros H.
    destruct x.
    { exists 0. easy. }
    destruct (nat_eqdec n 1) as [->|H1].
    { exists (S x). lia. }
    destruct (nat_eqdec n (S x)) as [->|H2].
    { exists 1. lia. }
    destruct H as (k&H3&H4). 1-3:easy. eauto.
  - intros [k ->] H1 H2 H3.
    exists k. split. 2:lia.
    destruct n. lia.
    destruct k; lia.
Qed.

Definition divides_dec n x :
  dec (n | x).
Proof.
  unfold divides.
  enough (dec (exists k, k < x /\ x = k * n)) as [H|H].
  - left. auto.
  - destruct x. left; lia.
    destruct (nat_eqdec n 1) as [H1|H1]. left; lia.
    destruct (nat_eqdec n (S x)) as [H2|H2]. left; lia.
    right. contradict H. apply H; easy.
  - apply exists_fin_dec. intros y. apply nat_eqdec.
Defined.

Definition prime_dec x :
  dec (prime x).
Proof.
  unfold prime.
  enough (dec (forall k, k < x -> (k | x) -> k = 1)) as [H|H].
  - destruct (le_lt_dec 2 x) as [H1|H1].
    + left. easy.
    + right. lia.
  - right. tauto.
  - apply forall_fin_dec. intros k.
    destruct (divides_dec k x) as [H|H].
    + destruct (nat_eqdec k 1) as [H1|H1].
      * left. auto.
      * right. auto.
    + left. intros H2. exfalso. auto.
Defined.

Definition prime_hat n : bool :=
  if prime_dec n then true else false.

Compute prime_hat 101.
Compute prime_hat 117.

Fact prime_hat_correct n :
  if prime_hat n then prime n else ~prime n.
Proof.
  unfold prime_hat.
  destruct (prime_dec n) as [H|H]; exact H.
Qed.

(** We get super compact proof terms *)

Goal prime 101.
Proof.
  exact (prime_hat_correct 101).
Qed.

Goal ~prime 117.
Proof.
  exact (prime_hat_correct 117).
Qed.


(*** Reducible LWOs *)

Module RLWO.
Section RLWO.
  Variable p : nat -> Prop.
  Variable p_hat : nat -> bool.
  Variable p_hat_correct : forall n, if p_hat n then p n else ~p n.

  Fixpoint G n : option nat :=
    match n with
    | 0 => None
    | S n => match G n with
            | Some k => Some k
            | None => if p_hat n then Some n else None
            end
    end.

  Definition phi n a :=
    match a with
    | Some k => k < n /\ least p k
    | None => safe p n
    end.

  Fact G_correct n :
    phi n (G n).
  Proof.
    induction n as [|n IH]; cbn.
    - apply safe_O.
    - destruct (G n) as [k|]; cbn in *.
      + split. lia. easy.
      + assert (H:= p_hat_correct n).
        destruct (p_hat n); cbn.
        * split. lia. easy.
        * apply safe_S; assumption.
  Qed.

  (** Step-indexed linear search *)

  Fixpoint L n m : option nat :=
    match n with
    | 0 => None
    | S n => if p_hat m then Some m else L n (S m)
    end.

  Lemma L_correct' n m : 
    safe p m -> phi (n + m) (L n m).
  Proof.
    induction n as [|n IH] in m |-*; intros H; cbn.
    - exact H. 
    - assert (H1:= p_hat_correct m).
      destruct (p_hat m); cbn.
      + split. lia. easy.
      + specialize (IH (S m)).
        replace (S(n + m)) with (n + S m) by lia.
        apply IH. apply safe_S; assumption.
  Qed.
  
  Fact L_correct n :
    phi n (L n 0).
  Proof.
    assert (H:= L_correct' n 0).
    replace (n + 0) with n in H by lia.
    apply H, safe_O.
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
  
  Fact GL_agree n :
    G n = L n 0.
  Proof.
    apply (phi_unique n).
    apply G_correct.
    apply L_correct.
  Qed.

  (** Invariant puzzle *)

  Fixpoint W n :=
    match n with
    | 0 => 0
    | S n => let k:= W n in if p_hat k then k else S n
    end.

  Definition delta n k :=  k <= n /\ safe p k /\ (~p k -> k = n).

  Fact delta_init :
    delta 0 0.
  Proof.
    repeat split. lia. apply safe_O.
  Qed.

  Fact delta_upgrade n k :
    delta n k -> if p_hat k then delta (S n) k else delta (S n) (S n).
  Proof.
    intros (H1&H2&H3).
    assert (H:= p_hat_correct k).
    destruct (p_hat k).
    - repeat split. lia. all:easy.
    - repeat split. lia.
      destruct (H3 H). apply safe_S; easy.
  Qed.

  Fact W_correct n :
    delta n (W n).
  Proof.
    induction n; cbn.
    - apply delta_init.
    - apply delta_upgrade in IHn.
      destruct (p_hat (W n)); exact IHn.
  Qed.


  Definition F n := if n - W n then None else Some (W n).

  Fact W_correct_phi n :
    phi n (F n).
  Proof.
    unfold F.
    destruct (W_correct n) as (H1&H2&H3).
    destruct (n - W n) eqn:H4; cbn.
    - assert (W n = n) as <- by lia. exact H2.
    - assert (H5: W n < n) by lia.
      repeat split. lia. 2:exact H2.
      generalize (p_hat_correct (W n)).
      destruct (p_hat (W n)); intuition lia.
  Qed.

End RLWO.
End RLWO.

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

Definition bool_LWE := forall p: bool -> Prop, ex p -> exists x, p x /\ (p true -> x = true).

Fact bool_XM_LWE:
  XM <-> bool_LWE.
Proof.
  split.
  - intros H p [x H1].
    destruct x eqn:H2.
    + exists true. easy.
    + destruct (H (p true)); eauto.
  - intros H P.
    specialize (H (fun x => if x then P else True)) as (x&H).
    + exists false. exact I.
    + destruct x.
      * left. apply H.
      * right. intros H1%H. easy.
Qed.

Section Extra.
  Variable p: nat -> Prop.
  Variable d: decider p.

  Fact A: forall x, (Sigma y, least p y /\ y < x) + safe p x.
  Proof.
    induction x as [|x [[y IH]|IH]].
    - right. easy.
    - left. exists y. split. easy. lia.
    - destruct (d x) as [Hx|Hx].
      + left. exists x. split. easy. lia.
      + right. apply safe_S; easy.
  Qed.
  
  Fixpoint FA (x: nat) : option nat :=
    match x with
    | 0 => None
    | S x => match FA x with
            | Some y => Some y
            | None => if d x then Some x else None
            end
    end.

    Fact FA_correct x :
      match FA x with
      | Some y => least p y /\ y < x
      | None => safe p x
      end.
    Proof.
    induction x as [|x IH]; cbn.
    - easy. 
    - destruct (FA x) as [y|].
      + split. easy. lia.
      + destruct (d x) as [Hx|Hx].
        * split. easy. lia.
        *  apply safe_S; easy.
    Qed.

    Goal forall x, Sigma y, if S y - x then least p y else safe p x.
    Proof.
      induction x as [|x [y IH]].
      - exists 0. cbn. easy. 
      - destruct (S y - x) as [|a] eqn:E.
        + exists y. replace  (S y - S x) with 0 by lia. exact IH.
        + destruct (d x) as [Hx|Hx].
          * exists x.  cbn. replace  (x - x) with 0 by lia. easy.
          * exists (S x). cbn. replace  (S x - x) with 1 by lia. apply safe_S; easy.
    Qed.
  
  Fact B: forall x, Sigma y, (least p y /\ y < x) \/ (safe p x /\ y = x).
  Proof.
    induction x as [|x [y IH]].
    - exists 0. right. easy. 
    - destruct (x - y) as [|a] eqn:E.
      + assert (safe p x) as H by intuition lia. clear E IH.
        destruct (d x) as [Hx|Hx].
        * exists x. left. split. easy. lia.
        * exists (S x). right. split. 2:easy. apply safe_S; easy.
      + assert (least p y) as H by intuition lia. clear IH.
        exists y. left. split. easy. lia.
  Qed.

  Fixpoint FB (x: nat) : nat :=
    match x with
    | 0 => 0
    | S x => let y := FB x in
            if x - y then if d x then x else S x else y
    end.

  Fact FB_correct x :
    (least p (FB x) /\ FB x < x) \/ (safe p x /\ FB x = x).
  Proof.
    induction x as [|x IH]; cbn.
    - right. easy. 
    - destruct (x - FB x) as [|a] eqn:E.
      + assert (safe p x) as H by intuition lia. clear E IH.
        destruct (d x) as [Hx|Hx].
        * left. split. easy. lia.
        * right. split. 2:easy. apply safe_S; easy.
      + assert (least p (FB x)) as H by intuition lia. clear IH.
        left. split. easy. lia.
  Qed.    
    
End Extra.

Section Extra_prop.
  Variable p: nat -> Prop.
  Variable d: forall n, p n \/ ~p n.

  Fact A': forall x, (exists y, least p y /\ y < x) \/ safe p x.
  Proof.
    induction x as [|x [[y IH]|IH]].
    - right. easy.
    - left. exists y. split. easy. lia.
    - destruct (d x) as [Hx|Hx].
      + left. exists x. split. easy. lia.
      + right. apply safe_S; easy.
  Qed.
  
  Fact B': forall x, exists y, (least p y /\ y < x) \/ (safe p x /\ y = x).
  Proof.
    induction x as [|x IH].
    - exists 0. right. easy. 
    - specialize IH as [y [IH|IH]].
      + exists y. intuition lia.
      + destruct (d x) as [Hx|Hx].
        * exists x. left. split. easy. lia.
        * exists (S x). right. split. 2:lia. apply safe_S; easy.
  Qed.
End Extra_prop.
