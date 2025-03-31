Definition XM: Prop :=
  forall P, P \/ ~P.
Definition DN: Prop :=
  forall P, ~~P -> P.
Definition Contra: Prop :=
  forall P Q, (~Q -> ~P) -> P -> Q.
Definition Peirce: Prop :=
  forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition XM': Prop :=
  forall P, (P <-> True) \/ (P <-> False).

Fact XM_XM' :
  XM <-> XM'.
Proof.
  split.
  - intros H P. specialize (H P). tauto.
  - intros H P. specialize (H P). tauto.
Qed.

Fact XM_DN :
  XM -> DN.
Proof.
  intros H P H1. specialize (H P) as [H|H].
  exact H. contradict (H1 H).
Qed.

Fact DN_Contra :
  DN -> Contra.
Proof.
  intros H P Q H1 x. apply H. clear H.
  intros H2. revert x. apply H1, H2.
Qed.

Fact Contra_Peirce :
  Contra -> Peirce.
Proof.
  intros H P Q. apply H. clear H.
  intros H1 H2. apply H1, H2. intros x.
  contradict (H1 x).
Qed.

Fact Peirce_XM' :
  Peirce -> XM.
Proof.
  intros H P. apply H with (Q:=False). clear H.
  intros H. right. intros x. apply H. left. exact x.
Qed.

Fact counterexample:
  XM <-> forall X (p: X -> Prop), (forall x, p x) \/ (exists x, ~p x).
Proof.
  split.
  - intros H X p.
    destruct (H (exists x, ~p x)) as [H1|H1].
    + right. exact H1.
    + left. intros x.
      specialize (H (p x)) as [H|H]. exact H.
      exfalso. apply H1. exists x. exact H.
  - intros H P.
    specialize (H True (fun _ => P)) as [H|[_ H]].
    + left. apply H, I.
    + right. exact H.
Qed.

(*** Stability *)

Definition stable (P: Prop) := ~~P -> P.

Fact stable_not P :
  stable (~P).
Proof.
  cbv. tauto.
Qed.

Fact stable_invariant P Q :
  (P <-> Q) -> (stable P <-> stable Q).
Proof.
  unfold stable. tauto.
Qed.

Goal forall P Q, stable P -> stable Q -> ~ (P /\ Q) -> ~P \/ ~Q.
Proof.
  unfold stable.
Abort.

Goal forall P Q, stable Q -> stable (P -> Q).
Proof.
  unfold stable. tauto.
Qed.

Goal forall P Q, stable P -> stable Q -> stable (P /\ Q).
Proof.
  unfold stable. tauto.
Qed.

Goal forall A (p: A -> Prop), (forall a, stable (p a)) -> stable (forall a, p a).
Proof.
  unfold stable. intros a p H1 H2 b.
  apply H1; clear H1. intros H1.
  apply H2; clear H2; intros H2.
  apply H1, H2.
Qed.

Goal forall P (p: P -> Prop),
    (forall x, stable (p x)) -> ~(forall x, p x) -> ~~(exists x, ~p x).
Proof.
  intros P p H H1 H2. apply H1. intros x.
  apply H. intros H3.  apply H2. exists x. exact H3.
Qed.


Goal forall P, stable P <-> exists Q, P <-> ~Q.
Proof.
  intros P. 
  split.
  - intros H. exists (~P). split. 2:exact H. tauto.
  - intros [Q  H]. unfold stable. tauto.
Qed.

Goal forall P1 P2 Q, stable Q -> ~(P1 /\ P2) -> (~P1 \/ ~P2 -> Q) -> Q.
Proof.
  intros *. unfold stable. tauto.
Qed.

Goal forall P1 P2 Q, stable Q -> (~P1 -> ~P2) -> ((P2 -> P1) -> Q) -> Q.
Proof.
  intros *. unfold stable. tauto.
Qed.

(*** Definiteness *)

Definition definite (P: Prop) := P \/ ~P.

Goal forall P, definite P -> stable P.
Proof.
  intros P. cbv. tauto.
Qed.

Goal forall P Q, definite P -> definite Q -> definite (P -> Q).
Proof.
  unfold definite. tauto.
Qed.

Goal forall P Q, definite P -> definite Q -> definite (P /\ Q).
Proof.
  unfold definite. tauto.
Qed.

Goal forall P Q, definite P -> definite Q -> definite (P \/ Q).
Proof.
  unfold definite. tauto.
Qed.

Goal forall P, definite P -> definite (~P).
Proof.
  unfold definite. tauto.
Qed.

Goal forall P Q, definite P \/ definite Q -> ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
  unfold definite. tauto.
Qed.

(*** Truth Value Semantics *)

Definition TVS : Prop :=
  forall P: Prop, P = True \/ P = False.
Definition PE : Prop :=
  forall P Q: Prop, P <-> Q -> P = Q.

Fact TVS_XM_PE :
  TVS <-> XM /\ PE.
Proof.
  split.
  - intros H. split.
    + intros P. specialize (H P) as [-> | ->]; tauto.
    + intros P Q.
      destruct (H P) as [-> | ->], (H Q) as [-> | ->]; tauto.
  - intros [H1 H2] P.
    specialize (H1 P) as [H1|H1].
    + left. apply H2. tauto.
    + right. apply H2. tauto.
Qed.
