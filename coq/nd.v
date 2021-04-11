From Coq Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Ltac list := cbn; auto; firstorder.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec P := { P } + { ~P }.
Definition decT (X: Type) : Type :=  X + (X -> False).

(*** Intuitionistic ND *)

Inductive form: Type :=
| var (x: nat)
| bot
| imp (s t: form).

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).

Implicit Types s t u v: form.
Implicit Types A B C: list form.

Reserved Notation "A |- s" (at level 70).
Inductive nd A : form -> Type :=
| ndA s:                    s el A  ->  A |- s
| ndE s:                  A |- bot  ->  A |- s
| ndII s t:              s::A |- t  ->  A |- s ~> t
| ndIE s t:  A |- s ~> t  ->  A |- s  ->  A |- t
where "A |- s" := (nd A s).

Definition  elim_nd
  : forall p: list form -> form -> Type,
    (forall A s, s el A -> p A s) ->
    (forall A s, p A bot -> p A s) ->
    (forall A s t, p (s::A) t -> p A (s ~> t)) ->
    (forall A s t, p A (s ~> t) -> p A s -> p A t) ->
    (forall A s, A |- s -> p A s)
  := fun p f1 f2 f3 f4 => fix F A _ d :=
       match d with
       | ndA _ s h => f1 A s h
       | ndE _ s d' => f2 A s (F A bot d')
       | ndII _ s t d' => f3 A s t (F (s::A) t d')
       | ndIE _ s t d1 d2 => f4 A s t (F A (s ~> t) d1) (F A s d2)
       end.

Ltac ndA := apply ndA; list.

Fact D1 A s:
  A |- s ~> s.
Proof.
  apply ndII. ndA.
Qed.

Fact D2 s A:
  s::A |- --s.
Proof.
  apply ndII. eapply ndIE. all:ndA.
Qed.

Fact D3 A :
  --bot::A |- bot.
Proof.
  eapply ndIE. ndA. apply ndII. ndA.
Qed.

Fact Cut A s t :
  A |- s -> s::A |- t -> A |- t.
Proof.
  intros H1 H2. eapply ndIE. 2:exact H1. apply ndII, H2.
Qed.

Fact bottom A :
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
  - apply ndII. apply IH. list.
  - eapply ndIE. apply IH1, H. apply IH2, H.
Qed.

Fact Imp A s t :
  A |- s~>t <=> s::A |- t.
Proof.
  split.
  - intros H. eapply ndIE. 2:ndA. eapply Weak. exact H. list.
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

Fixpoint ground s : Prop :=
  match s with
  | var _ => False
  | bot => True
  | imp s t => ground s /\ ground t
  end.

Fact ground_proof s :
  ground s -> ([] |- s) + ([] |- -s).
Proof.
  induction s as [x| |s1 IH1 s2 IH2]; cbn.
  - intros [].
  - intros _. right. apply ndII. ndA.
  - intros [[H1|H1]%IH1 [H2|H2]%IH2].
    + left. apply ndII. eapply Weak. exact H2. list.
    + right. apply ndII.
      assert (H3: [] <<= [s1 ~> s2]) by list.
      eapply Weak in H1. 2:exact H3.
      eapply Weak in H2. 2:exact H3.
      eapply ndIE. exact H2.
      eapply ndIE. 2:exact H1. ndA.
    + left. apply ndII. eapply Weak. exact H2. list.
    + left. apply ndII, ndE, Imp, H1.
Qed.


(*** Heyting Entailment *)
           
Module Heyting.
  Inductive tval := ff | nn | tt.
  Implicit Types a b: tval.
  Implicit Type alpha: nat -> tval.

  Definition le a b : bool :=
    match a, b with
    | ff , _ => true
    | _, tt => true
    | nn, nn => true
    | _, _ => false
    end.

  Notation "a <= b" := (le a b).

  Definition impl a b : tval :=
    if a <= b then tt else b.

  Fact impl_tt a :
    impl a tt = tt.
  Proof.
    destruct a; reflexivity.
  Qed.
  
  Fixpoint eva alpha s : tval :=
    match s with
    | var x => alpha x
    | bot => ff
    | s1~>s2 => impl (eva alpha s1) (eva alpha s2)
    end.

  Compute eva (fun _ => nn) bot.
  Compute eva (fun _ => nn) (var 7).
  Compute eva (fun _ => nn) (-var 7).
  Compute eva (fun _ => nn) (--var 7).
  Compute eva (fun _ => nn) (--var 7 ~> var 7).
  
  Fixpoint evac alpha A : tval :=
    match A with
    | nil => tt
    | s::A' => if eva alpha s <= evac alpha A' then eva alpha s else evac alpha A'
    end.

  Definition heyting A s : Prop :=
    forall alpha, (evac alpha A <= eva alpha s) = true.
          
  Notation "A |= s" := (heyting A s) (at level 70).
  
  Lemma evac_in A s :
    s el A -> A |= s.
  Proof.
    induction A as [|u A IH]; cbn.
    + intros [].
    + intros [<-|H] alpha; cbn.
      * destruct eva, evac; cbn; reflexivity.
      * generalize (IH H alpha). destruct evac, eva, eva; cbn; auto.
  Qed.

  Fact soundness A s :
    A |- s -> A |= s.
  Proof.
    induction 1 as [A s H|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
    - apply evac_in, H.
    - intros alpha. generalize (IH alpha). cbn. destruct evac, eva; auto.
    - intros alpha. generalize (IH alpha). cbn. destruct evac, eva, eva; auto.
    - intros alpha. generalize (IH1 alpha) (IH2 alpha). cbn. destruct evac, eva, eva; cbn; auto.
  Qed.

  Corollary double_negation x :
    (nil |- --var x ~> var x) -> False.
  Proof.
    intros H%soundness. generalize (H (fun _ => nn)). cbn. discriminate.
  Qed.

  Corollary consistency :
    (nil |- bot) -> False.
  Proof.
    intros H%soundness. generalize (H (fun _ => nn)). cbn. discriminate.
  Qed.
End Heyting.

(*** Classical ND *)

Reserved Notation "A |-c s" (at level 70).
Inductive ndc A : form -> Type :=
| ndcA s :                    s el A  ->  A |-c s
| ndcC s :             -s::A |-c bot  ->  A |-c s
| ndcII s t :             s::A |-c t  ->  A |-c s ~> t
| ndcIE s t :  A |-c s ~> t -> A |-c s  ->  A |-c t
where "A |-c s" := (ndc A s).

Ltac ndcA := apply ndcA; list.

Fact DN A s :
  A |-c --s ~> s.
Proof.
  apply ndcII, ndcC. eapply ndcIE. all:ndcA.
Qed.

Fact Cutc A s t :
  A |-c s -> s::A |-c t -> A |-c t.
Proof.
  intros H1 H2. eapply ndcIE. 2:exact H1. apply ndcII, H2.
Qed.

Fact Weakc A B s :
  A |-c s -> A <<= B -> B |-c s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2] in B |-*.
  all:intros H.
  - ndcA.
  - apply ndcC. apply IH. list.
  - apply ndcII. apply IH. list.
  - eapply ndcIE. apply IH1, H. apply IH2, H.
Qed.

Lemma Explosion A s :
  A |-c bot -> A |-c s.
Proof.
  intros H. apply ndcC. eapply Weakc. exact H. list.
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

Fact Impc A s t :
  A |-c s~>t <=> s::A |-c t.
Proof.
  split.
  - intros H. eapply ndcIE. 2:ndcA. eapply Weakc. exact H. list.
  - apply ndcII.
Qed.

Fact ndc_refute A s :
  A |-c s <=> -s::A |-c bot.
Proof.
  split.
  - intros H. eapply ndcIE. ndcA. eapply Weakc. exact H. list.
  - apply ndcC.
Qed.

(*** Glivenko *)

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
  - intros H%Glivenko. apply bottom, H.
Qed.

Fact classical_consistency :
  ([] |-c bot) -> False.
Proof.
  intros H % Glivenko % bottom. apply Heyting.consistency, H.
Qed.

(*** Boolean Entailment *)

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
  
Lemma evac_in A s :
  s el A -> A |= s.
Proof.
  induction A as [|u A IH]; cbn.
  + intros [].
  + intros [<-|H] alpha; cbn.
    * destruct eva, evac; cbn; trivial.
    * generalize (IH H alpha). destruct evac, eva, eva; cbn; auto.
Qed.

Fact ben_sound A s :
  A |-c s -> A |= s.
Proof.
  induction 1 as [A s H|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - apply evac_in, H.
  - intros alpha. generalize (IH alpha). cbn. destruct evac, eva; auto.
  - intros alpha. generalize (IH alpha). cbn. destruct evac, eva, eva; auto.
  - intros alpha. generalize (IH1 alpha) (IH2 alpha). cbn. destruct evac, eva, eva; cbn; auto.
Qed.

Corollary consistency :
  (nil |-c bot) -> False.
Proof.
  intros H%ben_sound. generalize (H (fun _ => true)). cbn. discriminate.
Qed.

Fact ben_equiv A s :
  A |= s <-> forall alpha, evac alpha A = true -> eva alpha s = true.
Proof.
  split.
  - intros H alpha H1. generalize (H alpha). rewrite H1. trivial.
  - intros H alpha. generalize (H alpha). destruct evac; auto.
Qed.

Fact ben_bot_equiv A :
  A |= bot <-> forall alpha, evac alpha A = false.
Proof.
  split.
  - intros H alpha. generalize (H alpha). destruct evac; auto.
  - intros H alpha. rewrite H. trivial.
Qed.

Fact evac_true alpha A :
  evac alpha A = true <-> forall s, s el A -> eva alpha s = true.
Proof.
  induction A as [|u A IH]; cbn.
  - intuition.
  - destruct (eva alpha u) eqn:H; split.
    + intros H1 s [->|H2]. exact H. apply IH; assumption.
    + intros H1. apply IH. intros s H2. apply H1. auto.
    + intros [=].
    + intros H1. specialize (H1 u). rewrite <-H. auto.
Qed.

Fact ben_refute A s :
  A |= s <-> -s::A |= bot.
Proof.
  split.
  - intros H alpha. generalize (H alpha). cbn. destruct evac, eva; trivial.
  - intros H alpha. generalize (H alpha). cbn. destruct evac, eva; trivial.
Qed.

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

(*** Certifying Boolean Solver *)

Section CBS.
  Variable CBS: forall A, { alpha | evac alpha A = true } + (A |-c bot).

  Fact ben_complete A s :
    A |= s -> A |-c s.
  Proof.
    intros H %ben_refute. apply ndc_refute.
    destruct (CBS (-s::A)) as [[alpha H1]|H1]. 2:exact H1.
    exfalso. apply ben_bot_equiv with (alpha:= alpha) in H. congruence.
  Qed.

  Fact ndc_dec A s :
    decT (A |-c s).
  Proof.
    destruct (CBS (-s::A)) as [[alpha H1]|H1].
    - right. intros H %ben_sound %ben_refute.
      apply ben_bot_equiv with (alpha:= alpha) in H. congruence.
    - left. apply ndcC, H1.
  Qed.

  Fact ben_agree A s :
    A |-c s <=> A |= s.
  Proof.
    split. apply ben_sound. apply ben_complete.
  Qed.
  
  Fact ben_dec A s :
    dec (A |= s).
  Proof.
    destruct (ndc_dec A s) as [H|H].
    - left. apply ben_sound, H.
    - right. contradict H. apply ben_complete, H.
  Qed.
End CBS.

(*** Substitution *)

Implicit Types  (theta : nat -> form).
  
Fixpoint subst theta s : form :=
  match s with
  | var x => theta x
  | bot => bot
  | s~>t => subst theta s ~> subst theta t
  end.

Fixpoint substC theta A : list form :=
  match A with
  | nil => nil
  | s::A' => subst theta s :: substC theta A'
  end.

Fact substC_in s A theta:
  s el A -> subst theta s el substC theta A.
Proof.
  induction A as [|t A IH]; cbn.
  - intros [].
  - intros [->|H]; auto.
Qed.

Fact nd_subst A s theta :
  A |- s -> substC theta A |- subst theta s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  all: cbn in *.
  - apply ndA, substC_in, H1.
  - apply ndE, IH.
  - apply ndII, IH.
  - eapply ndIE. exact IH1. exact IH2.
Qed. 

(*** Entailment Predicates *)

Section Sandwich.

  Variable E: list form -> form  -> Prop.
  Notation "A ||- s" := (E A s) (at level 70).
  Variable Eassu: forall s A, s el A -> A ||- s.
  Variable Ecut: forall A s t, A ||- s -> s::A ||- t -> A ||- t.
  Variable Eweak: forall A s B, A ||- s -> A <<= B -> B ||- s.
  Variable Esubst: forall A s theta, A ||- s -> substC theta A ||- subst theta s.
  Variable Econs: exists s, ~ nil ||- s.
  Variable Eexfalso : forall A s, A ||- bot -> A ||- s.
  Variable Eimpl: forall A s t, A ||- s ~> t <-> s::A ||- t.

  Fact EIE A s t :
    A ||- s~>t -> A ||- s -> A ||- t.
  Proof.
    intros H1 % Eimpl H2.
    eapply Ecut; eassumption.
  Qed.

  Fact absurd s :
    nil ||- s -> nil ||- -s -> False.
  Proof.
    intros H1 H2. destruct Econs as [t H].
    apply H. apply Eexfalso.
    eapply EIE; eassumption.
  Qed.

  Definition hat alpha n := if alpha n then -bot else bot.

  Lemma Tebbi alpha s :
    if eva alpha s then nil ||- subst (hat alpha) s
    else nil ||- -subst (hat alpha) s.
  Proof.
    induction s as [n| |s1 IH1 s2 IH2]; cbn.
    - unfold hat. destruct alpha.
      + apply Eimpl, Eassu. list.
      + apply Eimpl, Eassu. list.
    - apply Eimpl, Eassu. list.
    - set (sigma := subst (hat alpha)) in *.
      destruct (eva alpha s1).
      + destruct eva.
        * apply Eimpl. eapply Eweak. exact IH2. list.
        * apply Eimpl. apply EIE with (sigma s2).
          -- eapply Eweak. exact IH2. list.
          -- apply EIE with (sigma s1).
             ++ apply Eassu. list.
             ++ eapply Eweak. exact IH1. list.
      + apply Eimpl, Eexfalso, Eimpl. exact IH1.
  Qed.
  
  Lemma E2BE' s :
    nil ||- s -> nil |= s.
  Proof.
    intros H alpha. cbn. generalize (Tebbi alpha s).
    destruct eva.
    - auto.
    - intros H1. exfalso.
      apply Esubst with (theta:= hat alpha) in H. cbn in H.
      eapply absurd. exact H. exact H1.
  Qed.

  Fact ereversion A s :
    A ||- s <-> nil ||- revert A s.
  Proof.
    revert s.
    induction A as [|u A IH]; intros s; cbn [revert].
    - tauto.
    - split.
      + intros H. apply IH, Eimpl, H.
      + intros H. apply Eimpl, IH, H.
  Qed.

  Theorem E2BE A s :
    A ||- s -> A |= s.
  Proof.
    intros H. apply ben_revert, E2BE'.
    apply ereversion with (A:= A), H.
  Qed.
   
End Sandwich.
  
