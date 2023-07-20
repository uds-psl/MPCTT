From Coq Require Import List Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) := sum X (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Lemma nat_eqdec : eqdec nat.
Proof.
  hnf; unfold dec.
  induction x; destruct y; try intuition easy.
  specialize (IHx y). intuition congruence.
Qed.
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
Qed.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Ltac list := cbn; auto; firstorder; fail.

(*** Formulas *)

Inductive form: Type :=
| var (x: nat)
| bot
| imp (s t: form).

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).

Implicit Types s t : form.
Implicit Types A B C: list form.

Lemma form_eqdec :
  eqdec form.
Proof.
  intros s t. revert t.
  induction s as [x| |s1 IH1 s2 IH2];
    destruct t as [y| |t1 t2]; 
    try (unfold dec; intuition congruence).
  - destruct (nat_eqdec x y) as [H|H];
      unfold dec; intuition congruence.
  - destruct (IH1 t1) as [H1|H1],
        (IH2 t2) as [H2|H2];
      unfold dec; intuition congruence.
Qed.

Lemma form_mem_dec s A :
  dec (s el A).
Proof.
  unfold dec.
  induction A as [|t A IH]; cbn.
  - auto.
  - destruct (form_eqdec t s) as [->|H]; intuition.
Qed.

(*** Solved and Clashed Clauses *)

Fixpoint solved A : Prop :=
  match A with
  | [] => True
  | s::A => solved A /\ match s with
                      | var x => -var x nel A
                      | -var x => var x nel A
                      | -bot => True
                      | _ => False
                      end
  end.

Fact solved_forall A :
  solved A ->
  forall s, s el A ->
       match s with
       | var x => -var x nel A
       | -var x => var x nel A
       | -bot  => True
       | _ => False
       end.
Proof.
  induction A as [|u A IH]. easy.
  intros [H1 H2] s [-> |H].
  - destruct s as [x| | s1 s2]; auto.
    + intros [H3|H3]; easy.
    + destruct s1, s2; auto.
      intros [H3|H3]; easy.
  - specialize (IH H1 s H).
    destruct s as [x| | s1 s2] eqn:E.
     + intros [-> |H4]; easy.
     + exact IH.
     + destruct s1, s2; auto.
       intros [-> |H3]; auto.
Qed.

Fixpoint clashed A : Type :=
  match A with
  | [] => False
  | s::A => clashed A + match s with
                       | var x  => -var x el A
                       | -var x => var x el A
                       | bot => True
                       | _ => False
                       end
  end.

Fact clashed_exists A :
  clashed A -> (bot el A) + (Sigma x, var x el A /\ -var x el A).
Proof.
  induction A as [|s A IH]. easy.
  intros [H1|H2].
  - specialize (IH H1) as [IH|(x&IH1&IH2)].
    + intuition.
    + right. exists x; intuition.
  - destruct s  as [x| | s1 s2].
    + right. exists x. intuition.
    + intuition.
    + destruct s1, s2; try easy.
      right. exists x. intuition.
Qed.
  
Definition decomposable s :=
  match s with
  | imp s bot => match s with imp _ _ => True | _ => False end
  | imp _ _ => True
  | _ => False
  end.

Lemma analyze s :
  (s = bot) + (s = -bot) +
    (Sigma x, (s = var x) + (s = -var x))%type +
    decomposable s.
Proof.
  destruct s as [x| |s t]; eauto.
  destruct s, t; cbn;  eauto.
Qed.

Lemma analyze_decomp s :
  decomposable s ->
  Sigma s1 s2, ((s = -(s1 ~> s2)) + (s = s1 ~> s2 /\ s2 <> bot) )%type.
Proof.
  destruct s as [x| |s t]; try easy.
  destruct t as [x| |t1 t2].
  - intros _. exists s, (var x). right. easy.
  - destruct s ; eauto; easy. 
  - intros _. exists s, (t1 ~> t2). right. easy.
Qed.

Definition decomp A := Sigma B s C, A = B++s::C /\ decomposable s.

Lemma pre_solve A :
  decomp A + solved A + clashed A.
Proof.
  induction A as [|s A IH]; cbn.
  - auto.
  - destruct IH as [[IH|IH]|IH].
    + destruct IH as (B&t&C&H).
      left. left. exists (s::B), t, C.
      destruct H as [-> H]. easy.
    + destruct (analyze s) as [[[->| ->]|[x [->| ->]]]|H]; cbn; auto.
      * destruct (form_mem_dec (-var x) A) as [H|H]; auto.
      * destruct (form_mem_dec (var x) A) as [H|H]; auto.
      * left. left. exists [], s, A. easy.
    + auto.
Qed.

(*** Derivation Systems *)

Inductive sigma : list form -> Type :=
| sigma_term A :
  solved A -> sigma A
| sigma_rot s A :
  sigma (A++[s]) -> sigma (s::A)
| sigma_imp_pos1 s t A :
  t <> bot -> sigma (-s::A) -> sigma (s~>t::A)
| sigma_imp_pos2 s t A :
  t <> bot -> sigma (t::A) -> sigma (s~>t::A)
| sigma_imp_neg s t A :
  sigma (s::-t::A) -> sigma (-(s~>t)::A).

Inductive rho : list form -> Type :=
| rho_term A :
  clashed A -> rho A
| rho_rot s A :
  rho (A++[s]) -> rho (s::A) 
| rho_imp_pos s t A :
  t <> bot -> rho (-s::A) -> rho (t::A) -> rho (s~>t::A)
| rho_imp_neg s t A :
  rho (s::-t::A) -> rho (-(s~>t)::A).

Fixpoint gamma' s : nat :=
  match s with
  | var _ => 1
  | bot   => 1
  | imp s t => S (gamma' s + gamma' t)
  end.

Definition gamma'' s : nat :=
  match s with
  | -s => gamma' s
  | s => gamma' s
  end.
Arguments gamma'' : simpl nomatch.

Fixpoint gamma A : nat :=
  match A with
  | [] => 0
  | s::A => gamma'' s + gamma A
  end.

Lemma gamma_app A B :
  gamma (A++B) = gamma A + gamma B.
Proof.
  induction A as [|s A IH]; cbn.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma gamma_imp s t :
   t <> bot -> gamma'' (s ~> t) = S (gamma' s + gamma' t).
Proof.
  destruct t; cbn; intros H.
  reflexivity. easy. reflexivity.
Qed.

Lemma gamma_le s :
  gamma'' s <= gamma' s.
Proof.
  destruct s as [x| |s t]; cbn. lia. lia.
  destruct t as [x| |t1 t2]; cbn; lia.
Qed.

Lemma rotate s A B :
  Sigma C, ( (sigma (s::C) -> sigma (A++s::B)) *
           (rho (s::C) -> rho (A++s::B)) *
           (gamma (s::C) = gamma (A++s::B)) )%type.
Proof.
  induction A as [|t A IH] in B|-*.
  - exists B. easy.
  - destruct (IH (B++[t])) as [C [[IH1 IH2] IH3]].
    exists C. repeat split.
    + intros H. apply sigma_rot.
      rewrite <- app_assoc. apply IH1, H.
    + intros H. apply rho_rot.
      rewrite <- app_assoc. apply IH2, H.
    + rewrite IH3. cbn.
      rewrite !gamma_app. cbn.
      rewrite gamma_app. cbn.
      lia.
Qed.

Lemma solver' :
  forall A, sigma A + rho A.
Proof.
  apply (size_rec gamma).
  intros A IH.
  destruct (pre_solve A) as [[(B&s&C&->&H)|H]|H].
  - destruct (rotate s B C) as (A&(H1&H2)&H3).
    apply (analyze_decomp s) in H as (s1&s2&[->| [-> H]]).
    + destruct (IH (s1::-s2::A)) as [IH1|IH1].
      * rewrite <-H3; cbn. generalize (gamma_le s1); lia.
      * left. apply H1. apply sigma_imp_neg; easy.
      * right. apply H2. apply rho_imp_neg; easy.
    + destruct (IH (-s1::A)) as [IH1|IH1].
      * rewrite <-H3; cbn. rewrite (gamma_imp _ _ H). lia.
      * left. apply H1. apply sigma_imp_pos1; easy.
      * destruct (IH (s2::A)) as [IH2|IH2].
        -- rewrite <-H3; cbn. rewrite (gamma_imp _ _ H).
           generalize (gamma_le s2); lia.           
        -- left. apply H1. apply sigma_imp_pos2; easy.
        -- right. apply H2. apply rho_imp_pos; easy.
  - left. apply sigma_term, H.
  - right. apply rho_term, H.
Qed.

(*** Satisfiability *)

Implicit Types alpha : nat -> bool.

Fixpoint eva alpha s : bool :=
  match s with
  | var x => alpha x
  | bot => false
  | s1~>s2 => if eva alpha s1 then eva alpha s2 else true
  end.

Definition sat A := Sigma alpha, forall s, s el A -> eva alpha s = true.

Fact solved_sat A :
  solved A -> sat A.
Proof.
  intros H.
  exists (fun x => if form_mem_dec (var x) A then true else false).
  intros s H1.
  assert (H2:=solved_forall A H s H1). clear H.
  destruct s as [x| |s1 s2]; cbn.
  - destruct form_mem_dec; easy.
  - easy.
  - destruct s1, s2; cbn; auto.
    destruct form_mem_dec; easy.
Qed.

Fact sigma_sat A :
  sigma A -> sat A.
Proof.
  induction 1 as
    [A H|s A _ [alpha IH]|s t A H _ [alpha IH]|s t A H _ [alpha IH]|s t A _ [alpha IH]].
  - apply solved_sat, H.
  - exists alpha. intros u H1. apply IH.
    apply in_or_app.
    destruct H1 as [<- | H1]; intuition.
   - exists alpha. intros u [<- |H1]; cbn.
    + specialize (IH (-s)). cbn in IH.
      destruct (eva alpha s). 2:reflexivity.
      enough (false = true) by easy.
      auto.
    + intuition.
  - exists alpha. intros u [<- |H1]; cbn.
    + destruct (eva alpha s);intuition.
    + intuition.
  - exists alpha. intros u [<- |H1]; cbn.
    + assert (H1: eva alpha s = true).
      { apply IH. intuition. }
      assert (H2: eva alpha (-t) = true).
      { apply IH. intuition. }
      cbn in H2.
      destruct (eva alpha s), (eva alpha t); easy.
    + apply IH. intuition.
Qed.

(*** Refutation *)

Reserved Notation "A |- s" (at level 70).
Inductive nd A : form -> Type :=
| ndA s:                    s el A  ->  A |- s
| ndE s:                  A |- bot  ->  A |- s
| ndII s t:              s::A |- t  ->  A |- s ~> t
| ndIE s t:  A |- s ~> t  ->  A |- s  ->  A |- t
where "A |- s" := (nd A s).

Ltac ndA := (apply ndA; list).

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

Fact ImpL A s t :
  A |- s~>t -> s::A |- t.
Proof.
  intros H. eapply ndIE. 2:ndA. eapply Weak. exact H. list.
Qed.

Fact rho_refut A :
  rho A -> (A |- bot).
Proof.
  induction 1 as [A H|s A _ IH|s t A H _ IH1 _ IH2|s t A  _ IH1].
  - apply clashed_exists in H as [H|(x&H1&H2)].
    + ndA.
    + eapply ndIE with (s:=var x); ndA.
  - eapply Weak. exact IH. intros u.
    intros [H|H] %in_app_or; list.
  - apply ndII in IH1. apply ndII in IH2. apply ImpL.
    enough (H1: A |- --s ~> -t ~> -(s ~> t)).
    +  eapply ndIE. 2:exact IH2.
       eapply ndIE; eassumption.
    + do 3 apply ndII.
      apply ndIE with (s:=-s). ndA.
      apply ndII. apply ndIE with (s:=t). ndA.
      apply ndIE with (s:=s); ndA.
  - do 2 apply ndII in IH1. apply ImpL.
    enough (H1: A |- (-t ~> -s) ~> --(s ~> t)).
    + eapply ndIE. exact H1. exact IH1.
    + do 2 apply ndII.
      eapply ndIE with (s:=s~>t). ndA.
      apply ndII.  apply ndE.
      apply ndIE with (s:=s). 2:ndA.
      apply ndIE with (s:=-t). ndA.
      apply ndII. apply ndIE with (s:=s~>t). ndA.
      apply ndII. ndA.
Qed.

Fact solver :
  forall A, sat A + (A |- bot).
Proof.
  intros A.
  destruct (solver' A) as [H %sigma_sat| H %rho_refut]; auto.
Qed.

