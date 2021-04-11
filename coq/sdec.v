(** Preliminaries, have been done before *)

From Coq Require Import Bool.

Definition iffT (X Y: Type) : Type :=
  (X -> Y) * (Y -> X).

Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Notation dec X := ({ X } + { ~X }).

Definition bdec {X} (p: X -> Prop) (f: X -> bool) : Prop :=
  forall x, p x <-> f x = true.

Fact dec_transport X Y :
  (X <-> Y) -> dec X -> dec Y.
Proof.
  intros H1 [H2|H2].
  - left. apply H1, H2.
  - right. contradict H2. apply H1, H2.
Qed.

Lemma cdec_bdec X (p: X -> Prop) :
  sig (bdec p) <=> forall x, dec (p x).
Proof.
  split.
  - intros [f H] x. destruct (f x) eqn:H1.
    + left. apply H, H1.
    + right. intros H2%H. congruence.
  - intros H.
    exists (fun x => if H x then true else false).
    intros x. destruct (H x) as [H1|H1].
    tauto. intuition; discriminate.
Qed.

(** Witness Operator *)

Section WO.
  Variable f: nat -> bool.

  Inductive G (n: nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Lemma G_sig n :
    G n -> { k | f k = true }.
  Proof.
    induction 1 as [n _ IH].
    destruct (f n) eqn:H.
    - exists n. exact H.
    - apply IH. reflexivity.
  Qed.

  Lemma G_zero n :
    G n -> G 0.
  Proof.
    induction n as [|n IH].
    - intros H. exact H.
    - intros H. apply IH. constructor. intros _. exact H.
  Qed.
   
  Theorem wo :
    (exists n, f n = true) -> { n | f n = true }.
  Proof.
    intros H. apply (G_sig 0).
    destruct H as [n H].  (* witness needed *)
    apply (G_zero n).
    constructor. rewrite H. discriminate.
  Qed.
End WO.

(** Now we staert with semi-decidability *)

Definition tsat (f: nat -> bool) : Prop :=
  exists n, f n = true.

Definition sdec (X: Prop) : Type :=
  { f | X <-> tsat f }.

Goal forall X, dec X -> sdec X.
Proof.
  intros X [H|H].
  - exists (fun n => true). intuition. exists 0. reflexivity.
  - exists (fun n => false). split. tauto. intros [_ H1]. discriminate.
Qed.

Fact sdec_transport X Y :
  (X <-> Y) -> sdec X -> sdec Y.
Proof.
  intros H1 [f H2]. exists f. tauto.
Qed.

Goal forall X (p: X -> Prop),
    (forall x, sdec (p x)) <=> { F | forall x, p x <-> tsat (F x) }.
Proof.
  split.
  - intros H.
    exists (fun x => proj1_sig (H x)).
    intros x. destruct (H x) as [f H1]. cbn. exact H1.
  - intros [F H] x. exists (F x). apply H.
Qed.    

(** Semi-decisions closed under conjunction and disjunction *)

Fact sdec_or X Y :
  sdec X -> sdec Y -> sdec (X \/ Y).
Proof.
  intros [f Hf] [g Hg]. exists (fun n => f n || g n).
  split.
  - intros [[n H1]%Hf|[n H1]%Hg]; exists n; rewrite H1.
    + reflexivity.
    + apply orb_true_r.
  - intros [n [H|H]%orb_true_elim].
    + left. apply Hf. exists n. exact H.
    + right. apply Hg. exists n. exact H.
Qed.

Section Sdec_and.
  Variables (F: nat -> nat -> nat) (pi1: nat -> nat) (pi2: nat -> nat).
  Variable pi1_eq : forall x y, pi1 (F x y) = x.
  Variable pi2_eq : forall x y, pi2 (F x y) = y.

  Fact sdec_and X Y :
    sdec X -> sdec Y -> sdec (X /\ Y).
  Proof.
    intros [f Hf] [g Hg]. exists (fun n => f (pi1 n) && g (pi2 n)).
    split.
    - intros [x y].
      apply Hf in x as [nx Hx].
      apply Hg in y as [ny Hy].
      exists (F nx ny). rewrite pi1_eq, pi2_eq. rewrite Hx. exact Hy.
    - intros [n [Hx Hy]%andb_true_iff]. split.
      + apply Hf. exists (pi1 n). exact Hx.
      + apply Hg. exists (pi2 n). exact Hy.
  Qed.
End Sdec_and.  

(** [CO <=> forall X, sdec X -> dec X] *)

Goal  (forall X, sdec X -> dec X) <=> (forall f, dec (tsat f)).
Proof.
  split.
  - intros H f. apply H. exists f. tauto.
  - intros H X [f H1]. specialize (H f) as [H|H].
    + left. apply H1, H.
    + right.  tauto.
Qed.

(** Markov <=> Post *)

Definition Markov: Prop :=
  forall f: nat -> bool, ~(forall x, f x = false) -> tsat f.

Definition Post: Type :=
  forall X: Prop, sdec X -> sdec (~X) -> dec X.

Definition stable (X: Prop) : Prop :=
  ~ ~X -> X.

Lemma dma (f: nat -> bool) :
  ~ (forall n, f n = false) <-> ~ ~tsat f.
Proof.
  split.
  - intros H. contradict H. intros n.
    destruct (f n) eqn:H1. 2:reflexivity.
    contradict H. exists n. exact H1.
  - intros H H1. contradict H. intros [n H].
    revert H. rewrite H1. discriminate.
Qed.

Fact Markov_stable :
  Markov <-> forall f, stable (tsat f).
Proof.
  split.
  - intros M f H. apply M, dma, H.
  - intros H f H1. apply H, dma, H1.
Qed.

Lemma Markov2Post :
  Markov -> Post.
Proof.
  intros M X [f H1] [g H2].
  pose (h n := f n || g n).
  enough ({ n | h n = true }) as [n [H3|H3]%orb_true_elim].
  - left. apply H1. exists n; exact H3.
  - right. apply H2. exists n; exact H3.
  - apply wo, M. subst h. cbn. intros H3.
    enough (~X /\ ~ ~X) by tauto. split.
    + intros [n H4]%H1.
      specialize (H3 n) as [H3 _]%orb_false_iff. congruence.
    + intros [n H4]%H2.
      specialize (H3 n) as [_ H3]%orb_false_iff. congruence.
Qed.

Goal
  Post -> Markov.
Proof.
  intros P f H%dma.
  specialize (P (tsat f)) as [H1|H1].
  - exists f. tauto.
  - exists (fun _ => false). unfold tsat at 2. firstorder congruence.
  - exact H1.
  - contradict (H H1).
Qed.

(** tsat not co-semi-decidable *)

Definition comp {X} (p: X -> Prop) x := ~p x.
Definition CO := ex (bdec tsat).

Goal Markov -> (forall f, sdec (comp tsat f)) -> CO.
Proof.
  intros M H. hnf.
  enough (forall f, dec (tsat f)) as [phi H1]%cdec_bdec by eauto.
  intros f. apply (Markov2Post M).
  - exists f. tauto.
  - apply H.
Qed.

(** Reductions *)

Definition red {X Y} (p: X -> Prop) (q: Y -> Prop) (f : X -> Y) : Prop
  := forall x, p x <-> q (f x).

Goal forall X Y p q (F: X -> Y),
    red p q F -> (forall y, dec (q y)) -> (forall x, dec (p x)).
Proof.
  intros * H1 H2 x.
  specialize (H2 (F x)).
  specialize (H1 x).
  revert H2. apply dec_transport. tauto.
Qed.

Goal forall X Y p q (F: X -> Y),
    red p q F -> (forall y, sdec (q y)) -> (forall x, sdec (p x)).
Proof.
  intros * H1 H2 x.
  specialize (H2 (F x)) as [f H2].
  specialize (H1 x).
  exists f. tauto.
Qed.

Goal forall X (p q: X -> Prop),
    (forall x, p x <-> q x) -> red p q (fun x => x).
Proof.
  intros * H x. apply H.
Qed.

(** Predicate is semi-decidable iff it reduces to tsat *)

Goal forall X (p: X -> Prop),
    (forall x, sdec (p x)) <=> sig (red p tsat).
Proof.
  split.
  - intros H.
    exists (fun x => let (f, _) := H x in f).
    intros x. cbn. destruct (H x) as [f H1]. exact H1.
  - intros [F H] x. specialize (H x). exists (F x). exact H.
Qed.
