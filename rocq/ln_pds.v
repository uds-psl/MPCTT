Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + ~X.
From Stdlib Require Import Lia List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Definition incl {X} (A B: list X) := forall x, x el A -> x el B.
Notation "A <<= B" := (incl A B) (at level 70).

(** Formulas *)

Inductive form: Type :=
| var :nat -> form
| bot : form
| imp : form -> form -> form.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).

Implicit Types s t u v: form.
Implicit Types A B C: list form.

(** Intuitionistic ND *)

Reserved Notation "A |- s" (at level 70).
Inductive nd : list form -> form -> Type :=
| ndA A s:                    s el A  ->  A |- s
| ndE A s:                  A |- bot  ->  A |- s
| ndII A s t:              s::A |- t  ->  A |- s ~> t
| ndIE A s t:  A |- s ~> t  ->  A |- s  ->  A |- t
where "A |- s" := (nd A s).

Ltac close := cbn; auto; firstorder; intuition congruence.
Ltac ndA := apply ndA; close.

(** Constructing derivations with tactics is easy.
    One follows the construction of a meta proof *)                          

Fact D1 A s:
  A |- s ~> s.
Proof.
  apply ndII. ndA.
Qed.

Fact D2 s A:
  s::A |- --s.
Proof.
  apply ndII.
  apply ndIE with s.
  all:ndA.
Qed.

Fact D3 A :
  --bot::A |- bot.
Proof.
  apply ndIE with (-bot). 1:ndA.
  apply ndII. ndA.
Qed.

Goal forall A s t, A |- (-t ~> -s) ~> --(s ~> t).
Proof.
  intros *.
  apply ndII, ndII.
  apply ndIE with (s ~> t). 1:ndA.
  apply ndII.
  apply ndE.
  apply ndIE with (s). 2:ndA.
  apply ndIE with (-t). 1:ndA.
  apply ndII.
  apply ndIE with (s ~> t). 1:ndA.
  apply ndII. ndA.
Qed.
  
Fact bot_dn A :
  A |- --bot -> A |- bot.
Proof.
  intros H. eapply ndIE. 1:exact H. apply ndII. ndA.
Qed.

Fact Weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2] in B |-*.
  all:intros H.
  - ndA.
  - apply ndE. apply IH, H.
  - apply ndII. apply IH. close.
  - eapply ndIE. apply IH1, H. apply IH2, H.
Qed.

Fact ImpL A s t :
  A |- s~>t -> s::A |- t.
Proof.
  intros H. eapply ndIE. 2:ndA. eapply Weak. exact H. close.
Qed.

Fact Imp A s t :
  A |- s~>t <=> s::A |- t.
Proof.
  split.
  - apply ImpL.
  - apply ndII.
Qed.

Fixpoint revert A s : form :=
  match A with
  | nil => s
  | u::A' => revert A' (u ~> s)
  end.

Fact reversion A s :
  A |- s <=> [] |- revert A s.
Proof.
  induction A as [|u A IH] in s |-*; cbn.
  - hnf; auto.
  - split.
    + intros H%ndII%IH. exact H.
    + intros H%IH. apply Imp, H.
Qed.

Goal (forall s, dec (nd [] s)) -> (forall A s, dec (nd A s)).
Proof.
  intros d A s.
  destruct (reversion A s) as [H1 H2].
  destruct (d (revert A s)) as [H|H].
  all: unfold dec; auto.
Qed.
  
(** Excluded middle *)

Definition LEM := forall X: Prop, X \/ ~X.
Definition DNL := forall X: Prop, ~ ~X -> X.
Definition Peirce := forall X Y: Prop, ((X -> Y) -> X ) -> X.

Goal DNL <-> LEM.
Proof.
  split.
  all: intros H X. 
  - specialize (H (X \/ ~X)). tauto.
  - specialize (H X). tauto.
Qed.

Goal Peirce <-> DNL.
Proof.
  split.
  - intros H X H1. specialize (H X False). tauto.
  - intros H X Y H1. specialize (H X). tauto.
Qed.

(** Classical ND *)

Reserved Notation "A |-c s" (at level 70).
Inductive ndc A : form -> Type :=
| ndcA s :                    s el A  ->  A |-c s
| ndcC s :             -s::A |-c bot  ->  A |-c s
| ndcII s t :             s::A |-c t  ->  A |-c s ~> t
| ndcIE s t :  A |-c s ~> t -> A |-c s  ->  A |-c t
where "A |-c s" := (ndc A s).

Ltac ndcA := apply ndcA; close.

Fact DN A s :
  A |-c --s ~> s.
Proof.
  apply ndcII, ndcC. eapply ndcIE. all:ndcA.
Qed.

Fact Weakc A B s :
  A |-c s -> A <<= B -> B |-c s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2] in B |-*.
  all:intros H.
  - ndcA.
  - apply ndcC. apply IH. close.
  - apply ndcII. apply IH. close.
  - eapply ndcIE. apply IH1, H. apply IH2, H.
Qed.

Lemma Explosion A s :
  A |-c bot -> A |-c s.
Proof.
  intros H. apply ndcC. eapply Weakc. exact H. close.
Qed.

Fact ndc_refute A s :
  A |-c s <=> -s::A |-c bot.
Proof.
  split.
  - intros H. eapply ndcIE. ndcA. eapply Weakc. exact H. close.
  - apply ndcC.
Qed.

Goal (forall A, dec (ndc A bot)) -> (forall A s, dec (ndc A s)).
Proof.
  intros d A s.
  destruct (ndc_refute A s) as [H1 H2].
  destruct (d (-s :: A)) as [H|H].
  all: unfold dec; auto.
Qed.

Fact Impc A s t :
  A |-c s~>t <=> s::A |-c t.
Proof.
  split.
  - intros H. eapply ndcIE. 2:ndcA. eapply Weakc. exact H. close.
  - apply ndcII.
Qed.

Fact reversionc A s :
  A |-c s <=> [] |-c revert A s.
Proof.
  induction A as [|u A IH] in s |-*; cbn.
  - hnf; auto.
  - split.
    + intros H%ndcII%IH. exact H.
    + intros H%IH. apply Impc, H.
Qed.

Goal (forall s, dec (ndc [] s)) -> (forall A s, dec (ndc A s)).
Proof.
  intros d A s.
  destruct (reversionc A s) as [H1 H2].
  destruct (d (revert A s)) as [H|H].
  all: unfold dec; auto.
Qed.
  
Lemma Translation A s :
  A |- s -> A |-c s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - ndcA.
  - apply Explosion, IH.
  - apply ndcII, IH.
  - eapply ndcIE. 1,2:eassumption.
Qed.

(** Glivenko *)

Lemma Gliv0 A s :
  A |- (-s ~> --bot) ~> --s.
Proof.
  apply ndII, ndII.
  apply ndIE with (-bot).
  - apply ndIE with (-s); ndA.
  - apply ndII; ndA.
Qed.

Lemma Gliv1 A s t :
  A |- (s ~> - - t) ~> - - (s ~> t).
Proof.
  apply ndII, ndII.
  apply ndIE with (s~>t). 1:ndA.
  apply ndII, ndE.
  apply ndIE with (-t).
  - apply ndIE with s; ndA.
  - apply ndII.
    apply ndIE with (s~>t). 1:ndA.
    apply ndII. ndA.
Qed.

Lemma Gliv2 A s t :
  A |- --(s ~> t) ~> --s ~> --t.
Proof.
  apply ndII, ndII, ndII.
  apply ndIE with (-s). 1:ndA.
  apply ndII.
  apply ndIE with (-(s~>t)). 1:ndA.
  apply ndII.
  apply ndIE with t. 1:ndA.
  apply ndIE with s; ndA.
Qed.

Lemma Glivenko' A s :
  A |-c s -> A |- --s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - apply ndII. eapply ndIE. ndA. ndA.
  - eapply ndIE. { apply Gliv0. } apply ndII, IH.
  - apply Imp in IH.
    eapply ndIE. 2:exact IH. apply Gliv1.
  - eapply ndIE. 2:exact IH2.
    eapply ndIE. 2:exact IH1. apply Gliv2.
Qed.

Theorem Glivenko A s :
  A |-c s <=> A |- --s.
Proof.
  split.
  - apply Glivenko'.
  - intros H%Translation.
    eapply ndcIE. 2:exact H. apply DN.
Qed.

Fact refutation_agreement A :
  A |- bot <=> A |-c bot.
Proof.
  split.
  - apply Translation.
  - intros H%Glivenko. apply bot_dn, H.
Qed.

Fact negated_formula_agreement A s :
  A |- -s <=> A |-c -s.
Proof.
  split.
  - apply Translation.
  - intros H%Impc. apply Imp.
    apply refutation_agreement, H.
Qed.

Fact equiconsistency :
  (([] |- bot) -> False) <-> (([] |-c bot) -> False).
Proof.
  split; intros H; contradict H; apply refutation_agreement; assumption.
Qed.


   
(** Intuitionistic Hilbert system *)

Inductive hil A : form -> Type :=
| hilA s :      s el A -> hil A s
| hilMP s t :   hil A (s ~> t) -> hil A s -> hil A t
| hilK s t :    hil A (s ~> t ~> s)
| hilS s t u :  hil A ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u)
| hilE s :      hil A (bot ~> s).

Fact hil_nd A s :
  hil A s -> nd A s.
Proof.
  induction 1 as [s' H |s' t' H1 IH1 H2 IH2 |s' t' |s' t' u |s'].
  - apply ndA, H.
  - eapply ndIE; eassumption.
  - apply ndII, ndII. ndA.
  - apply ndII, ndII, ndII.
    apply ndIE with (s:= t');
      apply ndIE with (s:= s');
      ndA.
  - apply ndII, ndE. ndA.
Qed.

(** ND Completeness of intuitionistic Hilbert system *)

Fact hilAK A s t :
  hil A s -> hil A (t ~> s).
Proof.
  apply hilMP. apply hilK.
Qed.

Fact hilAS A s t u :
  hil A (s ~> t ~> u) -> hil A (s ~> t) -> hil A (s ~> u).
Proof.
  intros H. apply hilMP. revert H. apply hilMP. apply hilS.
Qed.

Fact hilAF A s :
  hil A bot -> hil A s.
Proof.
  apply hilMP, hilE.
Qed.

Fact hilI A s :
  hil A (s ~> s).
Proof.
  apply hilAS with (t:= s~> s).
  all: apply hilK.
Qed.

Definition eqdec X := forall x y: X, dec (x = y).
Definition nat_eqdec: eqdec nat.
Proof.
  intros x y. unfold dec.
  destruct ((x - y) + (y - x)) eqn:?; intuition lia.
Qed.

Lemma form_eqdec :
  eqdec form.
Proof.
  intros s t. unfold dec. revert t.
  induction s as [x| |s1 IH1 s2 IH2];
    destruct t as [y| |t1 t2];
    unfold dec; try intuition congruence.
  - destruct (nat_eqdec x y) as [H|H];
      unfold dec; intuition congruence.
  - destruct (IH1 t1) as [H1|H1],
        (IH2 t2) as [H2|H2];
      unfold dec; intuition congruence.
Qed.

Lemma el_sum s t A :
  s el t::A -> (s = t) + (s el A).
Proof.
  destruct (form_eqdec s t) as [->|H].
  - auto.
  - intros H1. right. close.
Qed.

Fact hilD s A t :
  hil (s::A) t -> hil A (s ~> t).
Proof.
  induction 1 as [s' H |s' t' _ IH1 _ IH2 |s' t' |s' t' u |s'].
  - (* assumption rule *)
    apply el_sum in H as [->|H].
    + apply hilI.
    + apply hilAK. apply hilA, H.
  - (* MP *)
    eapply hilAS. exact IH1. exact IH2.
  - (* K *)
    apply hilAK. apply hilK.
  - (* S *)
    apply hilAK. apply hilS.
  - (* E *)
    apply hilAK. apply hilE.
Qed.

Fact nd_hil {A s} :
  nd A s -> hil A s.
Proof.
  induction 1 as [A s H|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - apply hilA, H.
  - apply hilAF, IH. 
  - apply hilD, IH.
  - eapply hilMP. exact IH1. exact IH2.
Qed.

(** Heyting evaluation *)
           
Module Heyting.
  Inductive tval := ff | uu | tt.
  Implicit Types a b: tval.

  Definition leq a b : bool :=
    match a, b with
    | ff , _ => true
    | uu, uu => true
    | uu, tt => true
    | tt, tt => true
    | _, _ => false
    end.

  Notation "a <= b" := (leq a b).

  Definition impl a b : tval :=
    if a <= b then tt else b.
  
  Compute impl (impl (impl uu ff) ff) uu.
  
  Fixpoint eva s : tval :=
    match s with
    | var _ => uu
    | bot => ff
    | s1~>s2 => impl (eva s1) (eva s2)
    end.

  Fact hil_sound s :
    hil [] s -> eva s = tt.
  Proof.
    induction 1 as [s' H |s' t' _ IH1 _ IH2 |s' t' |s' t' u |s'].
    - exfalso. apply H.
    - cbn in IH1. destruct eva, eva; easy.
    - cbn. destruct eva, eva; easy.
    - cbn. destruct eva, eva, eva; easy.
    - cbn. reflexivity.
  Qed.
  
  Fact hil_DN x :
    ~ hil [] (--var x ~> var x).
  Proof.
    intros [=]%hil_sound.
  Qed.

  Fact nd_DN x :
    ~ [] |- --var x ~> var x.
  Proof.
    intros H %nd_hil %hil_DN. exact H.
  Qed.

  Corollary nd_consistent :
    ~ [] |- bot.
  Proof.
    intros H. apply nd_DN with 0. apply ndE, H.
  Qed.
  
  Corollary ndc_consistent :
    ~ [] |-c bot.
  Proof.
    intros H%refutation_agreement.
    apply nd_consistent, H.
  Qed.

End Heyting.

(* Boolean Entailment *)

Implicit Types alpha : nat -> bool.

Fixpoint eva alpha s : bool :=
  match s with
  | var x => alpha x
  | bot => false
  | s1~>s2 => if eva alpha s1 then eva alpha s2 else true
  end.

Fixpoint evac alpha A : bool :=
  match A with
  | nil => true
  | s::A' => if eva alpha s then evac alpha A' else false
  end.

Definition ben A s : Prop :=
  forall alpha, if evac alpha A then eva alpha s = true else True.
          
Notation "A |= s" := (ben A s) (at level 70).

Fact ben_impl A s t :
  A |= s ~> t  <->  s::A |= t.
Proof.
  split; intros H alpha; generalize (H alpha); cbn; destruct eva, eva, evac; trivial.
Qed.

Fact ben_revert A s :
  A |= s <-> [] |= revert A s.
Proof.
  induction A as [|u A IH] in s |-*; cbn [revert].
  - tauto.
  - split.
    + intros H. apply IH, ben_impl, H.
    + intros H. apply ben_impl, IH, H.
Qed.

(** Left Overs *)

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.


Definition Peirce_ndc :=
  forall A s t, (s ~> t) :: A |-c s -> A |-c s.
Definition Contra_ndc :=
  forall A s , -s :: A |-c bot  -> A |-c s.

Goal Peirce_ndc.
Proof.
  intros A s t.
  intros H %ndcII.
  apply ndcC.
  apply ndcIE with s. ndcA.
  apply ndcIE with (s~>t).
  { eapply Weakc. exact H. close. }
  apply ndcII, Explosion.
  apply ndcIE with s; ndcA.
Qed.

Goal Peirce_ndc -> Contra_ndc.
(* We use Explosion, but not Contra *)
Proof.
  intros H A s H1.
  specialize (H A s bot). apply H. clear H.
  apply Explosion, H1.
Qed.

Lemma form_memdec s A :
  dec (s el A).
Proof.
  unfold dec.
  induction A as [|t A IH]; cbn.
  - auto.
  - destruct (form_eqdec t s) as [->|H]; close.
Qed.
