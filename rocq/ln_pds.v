Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + (~X).
From Stdlib Require Import Lia List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~In x A) (at level 70).
Definition incl {X} (A B: list X) := forall x, x el A -> x el B.
Notation "A <<= B" := (incl A B) (at level 70).

(** Formulas *)

Inductive For: Type :=
| var :nat -> For
| bot : For
| imp : For -> For -> For.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).

Implicit Types s t u v: For.
Implicit Types A B C: list For.

(** Intuitionistic ND *)

Reserved Notation "A |- s" (at level 70).
Inductive nd : list For -> For -> Type :=
| ndA A s:                    s el A  ->  A |- s
| ndE A s:                  A |- bot  ->  A |- s
| ndII A s t:              s::A |- t  ->  A |- s ~> t
| ndIE A s t:  A |- s ~> t  ->  A |- s  ->  A |- t
where "A |- s" := (nd A s).

(* Two defined automation tactics *)
Ltac close := cbn; auto; firstorder; intuition congruence.
Ltac ndA := apply ndA; close.

(** Constructing derivations with tactics is easy.
    One follows the construction of a meta proof *)                          

Goal forall A s, A |- s ~> s.
Proof.
  intros *. apply ndII. ndA.
Qed.

Goal forall A s, s::A |- --s.
Proof.
  intros *. apply ndII.
  apply ndIE with s.
  all:ndA.
Qed.

Goal [] |- --bot ~> bot.
Proof.
  apply ndII. apply ndIE with (-bot). ndA.
  apply ndII. ndA.
Qed.

Fact nd_dn A s :
  A |- s -> A |- --s.
Proof.
  intros H.
  apply ndIE with s. 2:exact H.
  apply ndII, ndII. apply ndIE with s; ndA.
Qed.

Fact nd_dn_bot A :
  A |- --bot -> A |- bot.
Proof.
  intros H.
  apply ndIE with (-bot). exact H.
  apply ndII. ndA.
Qed.

Fact Weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2] in B |-*.
  all:intros H.
  - ndA.
  - apply ndE. close.
  - apply ndII. close.
  - apply ndIE with s. all: close.
Qed.

Goal forall A s, A |- s -> A |- --s.
Proof.
  intros * H. apply ndII.
  apply ndIE with s. ndA.
  apply Weak with A; close.
Qed.
  
Fact ImpL A s t :
  A |- s~>t -> s::A |- t.
Proof.
  intros H.
  apply ndIE with s. 2:ndA.
  apply Weak with A. exact H. close.
Qed.

Fact Imp A s t :
  A |- s~>t <=> s::A |- t.
Proof.
  split.
  - apply ImpL.
  - apply ndII.
Qed.

Fixpoint revert A s : For :=
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
Definition BIL := forall X Y: Prop, (X -> Y) <-> (~X \/ Y).

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

Goal BIL <-> LEM.
Proof.
  split.
  - intros H X.  specialize (H X X). tauto.
  - intros H X Y. split. 2:tauto.
    specialize (H X). tauto.
Qed.

(** Contra and Peirce in nd *)

Definition Peirce_as_nd_rule :=
  forall A s t, (s ~> t) :: A |- s -> A |- s.
Definition Contra_as_nd_rule :=
  forall A s , -s :: A |- bot  -> A |- s.

Goal Peirce_as_nd_rule <=> Contra_as_nd_rule.
Proof.
  split.
  - intros H A s H1.
    specialize (H A s bot).
    apply H. apply ndE. exact H1.
  - intros H A s t.
    intros H1 %ndII.
    apply H. apply ndIE with s. ndA.
    apply ndIE with (s~>t). apply Weak with A; close.
    apply ndII. apply H. apply ndIE with s; ndA.
Qed.

(** Classical ND *)

Reserved Notation "A |-c s" (at level 70).
Inductive ndc : list For -> For -> Type :=
| ndcA A s :                    s el A  ->  A |-c s
| ndcC A s :             -s::A |-c bot  ->  A |-c s
| ndcII A s t :             s::A |-c t  ->  A |-c s ~> t
| ndcIE A s t :  A |-c s ~> t -> A |-c s  ->  A |-c t
where "A |-c s" := (ndc A s).

Ltac ndcA := apply ndcA; close.

Fact ndc_DN A s :
  A |-c --s ~> s.
Proof.
  apply ndcII, ndcC.
  apply ndcIE with (-s). all:ndcA.
Qed.

Fact Weakc A B s :
  A |-c s -> A <<= B -> B |-c s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2] in B |-*.
  all:intros H.
  - ndcA.
  - apply ndcC. close.
  - apply ndcII. close.
  - apply ndcIE with s. all:close. 
Qed.

Lemma Explosion A s :
  A |-c bot -> A |-c s.
Proof.
  intros H. apply ndcC.
  apply Weakc with A; close.
Qed.

Fact ndc_refute A s :
  A |-c s <=> -s::A |-c bot.
Proof.
  split.
  - intros H.
    apply ndcIE with s. ndcA. apply Weakc with A; close.
  - apply ndcC.
Qed.

Fact ndc_cases A s t :
  s::A |-c t -> -s::A |-c t -> A |-c t.
Proof.
  intros H1 H2.
  apply ndcII in H1. apply ndcII in H2.
  apply ndcC.
  apply ndcIE with t. ndcA. 
  apply ndcIE with (-s).
  - apply Weakc with A. all:close.
  - apply ndcII.
    apply ndcIE with t. ndcA.
    apply ndcIE with s. apply Weakc with A; close.
    ndcA.
Qed.
  
Fact ndc_dec_red_bot :
  (forall A, dec (A |-c bot)) -> (forall A s, dec (A |-c s)).
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
  - intros H. apply ndcIE with s. 2:ndcA.
    apply Weakc with A. all: close.
  - apply ndcII.
Qed.

Fact reversionc A s :
  A |-c s <=> [] |-c revert A s.
Proof.
  induction A as [|u A IH] in s |-*; cbn.
  - hnf; auto.
  - split.
    + intros H. apply IH, ndcII, H.
    + intros H. apply Impc, IH, H.
Qed.

Fact ndc_dec_red_empty :
  (forall s, dec ([] |-c s)) -> (forall A s, dec (A |-c s)).
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
  - apply ndcIE with s. all:assumption.
Qed.

(** Glivenko *)

Lemma Glivenko' A s :
  A |-c s -> A |- --s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - apply nd_dn. ndA.
  - apply ndII in IH.
    apply ndIE with (-s ~> --bot). 2:exact IH.
    apply ndII, ndII. apply nd_dn_bot.
    apply ndIE with (-s). all:ndA.
  - apply ndII. apply ndII in IH.
    apply ndIE with (s ~> t). ndA. apply ndII. apply ndE.
    apply ndIE with (-t).
    + apply ndIE with s. 2:ndA.
      apply Weak with A; close.
    + apply ndII. apply ndIE with (s ~> t). ndA.
      apply ndII. ndA.
  - apply ndII. apply ndIE with (-s).
    + apply Weak with A. exact IH2. close.
    + apply ndII. apply ndIE with (-(s~>t)).
      * apply Weak with A; close.
      * apply ndII. apply ndIE with t. ndA.
        apply ndIE with s; ndA.
Qed.

Theorem Glivenko A s :
  A |-c s <=> A |- --s.
Proof.
  split.
  - apply Glivenko'.
  - intros H%Translation. apply ndcC. apply Impc, H. 
 Qed.

Fact refutation_agreement A :
  A |- bot <=> A |-c bot.
Proof.
  split.
  - apply Translation.
  - intros H%Glivenko. apply nd_dn_bot, H.
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
  ~([] |- bot) <-> ~([] |-c bot).
Proof.
  split; intros H; contradict H; apply refutation_agreement; assumption.
Qed.


(** Intuitionistic Hilbert system *)

Inductive hil A : For -> Type :=
| hilA s :      s el A -> hil A s
| hilMP s t :   hil A (s ~> t) -> hil A s -> hil A t
| hilK s t :    hil A (s ~> t ~> s)
| hilS s t u :  hil A ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u)
| hilE s :      hil A (bot ~> s).

Fact hil_nd A s :
  hil A s -> A |- s.
Proof.
  induction 1 as [s' H |s' t' H1 IH1 H2 IH2 |s' t' |s' t' u |s'].
  - apply ndA, H.
  - apply ndIE with s'; assumption.
  - apply ndII, ndII. ndA.
  - apply ndII, ndII, ndII.
    apply ndIE with t'.
    + apply ndIE with s'; ndA.
    + apply ndIE with s'; ndA.
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

Fact hilAE A s :
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

Lemma For_eqdec :
  eqdec For.
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

Lemma mem_sum s t A :
  s el t::A -> (s = t) + (s el A).
Proof.
  destruct (For_eqdec s t) as [->|H].
  - auto.
  - intros H1. right. close.
Qed.

Fact hilD s A t :
  hil (s::A) t -> hil A (s ~> t).
Proof.
  induction 1 as [s' H |s' t' _ IH1 _ IH2 |s' t' |s' t' u |s'].
  - apply mem_sum in H as [->|H].  (* assumption rule *)
    + apply hilI.
    + apply hilAK. apply hilA, H.
  - revert IH1 IH2. apply hilAS.  (* MP *)
  - apply hilAK. apply hilK.  (* K *)
  - apply hilAK. apply hilS.  (* S *)
  - apply hilAK. apply hilE.  (* E *)
Qed.

Fact nd_hil {A s} :
  A |- s -> hil A s.
Proof.
  induction 1 as [A s H|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  - apply hilA, H.
  - apply hilAE, IH. 
  - apply hilD, IH.
  - apply hilMP with s; assumption. 
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

  Fact nd_sound s :
    [] |- s -> eva s = tt.
  Proof.
    intros H. apply hil_sound, nd_hil, H.
  Qed.

  Fact nd_DN x :
    ~ ([] |- --var x ~> var x).
  Proof.
    intros H%nd_sound. cbn in H. easy.
  Qed.

  Fact nd_Var x :
    ~ ([] |- var x).
  Proof.
    intros H%nd_sound. cbn in H. easy.
  Qed.

  Fact nd_negVar x :
    ~ ([] |- -var x).
  Proof.
    intros H%nd_sound. cbn in H. easy.
  Qed.

  Fact nd_consistent :
    ~ [] |-c bot.
  Proof.
    intros H %refutation_agreement %nd_sound. cbn in H. easy.
  Qed.
  
  Fact ndc_unsound :
    ~ (forall s, [] |-c s -> eva s = tt).
  Proof.
    intros H.
    assert (H1:= ndc_DN [] (var 0)).
    specialize (H _ H1).
    cbn in H1. easy.
  Qed.

End Heyting.

(** Boolean Entailment *)

Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.

Implicit Types alpha : nat -> bool.

Fixpoint eva alpha s : bool :=
  match s with
  | var x => alpha x
  | bot => false
  | s1~>s2 => if eva alpha s1 then eva alpha s2 else true
  end.

Abbreviation satF alpha s := (eva alpha s = true).
Abbreviation satL alpha A := (forall s, s el A -> satF alpha s).
Definition ben A s := forall alpha, satL alpha A -> satF alpha s.   
Notation "A |= s" := (ben A s) (at level 70).

Lemma satL_cons alpha s A :
  satL alpha (s::A) <-> satF alpha s /\ satL alpha A.
Proof.
  close.
Qed.

Fact ben_refute A s :
  A |= s <-> -s::A |= bot.
Proof.
  unfold ben.
  split; intros H alpha.
  - rewrite satL_cons. specialize (H alpha).
    cbn. destruct (eva alpha s); close.
  - specialize (H alpha). revert H.
    rewrite satL_cons. cbn. destruct (eva alpha s); close.
Qed.

Fact ndc_sound {A s} :
  A |-c s -> A |= s.
Proof.
  induction 1 as [A s H1|A s _ IH|A s t _ IH|A s t _ IH1 _ IH2].
  all: intros alpha.
  - auto.
  - apply ben_refute, IH.
  - specialize (IH alpha). rewrite satL_cons in IH.
    cbn. destruct (eva alpha s); auto.
  - intros H. specialize (IH1 alpha H). specialize (IH2 alpha H).
    cbn in IH1. rewrite IH2 in IH1. exact IH1.
Qed.

Definition sat A := Sigma alpha, satL alpha A.

Fact ben_unsat_bot A :
  A |= bot <-> ~sat A.
Proof.
  split; intros H.
  - intros [alpha H1]. specialize (H alpha H1). easy.
  - intros alpha H1. exfalso. apply H. exists alpha. exact H1.
Qed.

Section Decidability_Completeness.
  Variable solver : forall A, sat A + (A |-c bot).

  Fact ndc_dec :
    forall A s, dec (A |-c s).
  Proof.
    apply ndc_dec_red_bot.
    intros A.
    destruct (solver A) as [H|H].
    - right. intros H1. revert H.
      apply ben_unsat_bot, ndc_sound, H1.
    - left. easy.
  Qed.

  Fact sat_dec :
    forall A, dec (sat A).
  Proof.
    intros A.
    destruct (solver A) as [H|H].
    - left. easy.
    - right. apply ben_unsat_bot, ndc_sound, H.
  Qed.
  
  Fact ndc_ben A s :
    A |-c s <=> A |= s.
  Proof.
    split.
    - apply ndc_sound.
    - intros H%ben_refute.
      apply ndcC.
      destruct (solver (-s::A)) as [H1|H1].
      + exfalso.
        assert (H2:= ben_unsat_bot (-s::A)).
        tauto.
      + easy.
  Qed.
End Decidability_Completeness.

(** Presolver *)

Definition solved A : Type :=
  forall s, s el A -> Sigma x, (s = var x /\ -var x nel A) +
                      (s = -var x /\ var x nel A).

Definition clashed A : Type :=
  (bot el A) + (Sigma s, s el A /\ -s el A).

Lemma For_memdec s A :
  dec (s el A).
Proof.
  unfold dec.
  induction A as [|t A IH]; cbn.
  - auto.
  - destruct (For_eqdec t s) as [->|H]; close.
Qed.

Fact solved_sat A :
  solved A -> sat A.
Proof.
  intros H.
  exists (fun x => if For_memdec (var x) A then true else false).
  intros s H1.
  specialize (H s H1) as [x [[-> H]|[-> H]]]; cbn;
    destruct For_memdec; easy.
Qed.

Fact clashed_refut A :
  clashed A -> A |-c bot.
Proof.
  intros [H|(s&H1&H2)].
  - ndcA.
  - apply ndcIE with s; ndcA.
Qed.

Fact solved_var_pos A x:
  solved A -> solved (var x :: A) + clashed (var x :: A).
Proof.
  intros H. 
  destruct (For_memdec (-var x) A) as [H1|H1].
  - right. close.
  - left. intros s [->|H2] %mem_sum.
    + exists x. left. close.
    + specialize (H s H2) as [y H]. exists y. close.
Qed.

Fact solved_var_neg A x:
  solved A -> solved (-var x :: A) + clashed (-var x :: A).
Proof.
intros H. 
  destruct (For_memdec (var x) A) as [H1|H1].
  - right. close.
  - left. intros s [->|H2] %mem_sum.
    + exists x. right. close.
    + specialize (H s H2) as [y H]. exists y. close.
Qed.

Inductive decomposable : For -> Type :=
| decomposableFn : decomposable (-bot)
| decomposableIn s t : decomposable (-(s ~> t))
| decomposableIp s t : t <> bot -> decomposable (s ~> t).

Inductive formula : For -> Type :=
| formulaVp x : formula (var x)
| formulaVn x : formula (- var x)
| formulaFp : formula bot
| formulaD s : decomposable s -> formula s.

Fact For_formula :
  forall s, formula s.
Proof.
  destruct s as [x| |s t].
  - constructor.
  - constructor.
  - destruct t as [x| |t1 t2].
    + constructor. constructor. easy.
    + destruct s as [x| |s1 s2].
      * constructor.
      * constructor. constructor.
      * constructor. constructor.
    + constructor. constructor. easy.
Qed.

Fact presolver :
  forall A, (solved A + clashed A) + (Sigma B s C, (A = B ++ s::C) * decomposable s).
Proof.
  induction A as [|s A IH].
  - left. left. easy. (* solved *)
  - destruct IH as [[IH|IH]|IH].
    + destruct (For_formula s) as [x|x| |s H].  (* solved *)
      * left. apply solved_var_pos, IH.
      * left. apply solved_var_neg, IH.
      * left. right. close.
      * right. exists [], s, A. easy.
    + left. right. close.  (* clashed *)
    + right. destruct IH as (B&t&C&IH1&IH2). (* decomposable *)
      rewrite IH1. exists (s::B), t, C. easy.
Qed.

(** Derivation systems [sigma] and [rho] *)

Inductive sigma : list For -> Type :=
| sigma_solved A :
  solved A -> sigma A
| sigma_rot A B :
  sigma (B++A) -> sigma (A++B)
| sigma_bot A :
  sigma A -> sigma (-bot::A) 
| sigma_imp_pos1 s t A :
  t <> bot -> sigma (-s::A) -> sigma (s~>t::A)
| sigma_imp_pos2 s t A :
  t <> bot -> sigma (t::A) -> sigma (s~>t::A)
| sigma_imp_neg s t A :
  sigma (s::-t::A) -> sigma (-(s~>t)::A).

Inductive rho : list For -> Type :=
| rho_clashed A :
  clashed A -> rho A
| rho_rot A B :
  rho (B++A) -> rho (A++B) 
| rho_bot A :
  rho A -> rho (-bot::A) 
| rho_imp_pos s t A :
  t <> bot -> rho (-s::A) -> rho (t::A) -> rho (s~>t::A)
| rho_imp_neg s t A :
  rho (s::-t::A) -> rho (-(s~>t)::A).

Fact sigma_sound A :
  sigma A -> sat A.
Proof.
  induction 1 as
    [A H|A B _ [alpha IH]|A _ [alpha IH]|s t A _ H [alpha IH]|s t A _ H [alpha IH]|s t A _ [alpha IH]].
  - apply solved_sat, H.
  - exists alpha. intros u H%in_app_iff. apply IH. apply in_app_iff. intuition.
  - exists alpha. intros u [<-|H1]; close.
  - exists alpha. intros u [<-|H1]. 2:close.
    specialize (IH (-s)). cbn in *. destruct (eva alpha s); close.
  - exists alpha. intros u [<- |H1]. 2:close.
    specialize (IH t). cbn in *. destruct (eva alpha s); close.
  - exists alpha. intros u [<- |H1]. 2:close.
    assert (IHs:= IH s). specialize (IH (-t)). cbn in *. destruct (eva alpha s); close.
Qed.

Fact rho_sound A :
  rho A -> (A |-c bot).
Proof.
  induction 1 as [A H|A B _ IH|A _ IH|s t A H _ IH1 _ IH2|s t A  _ IH1].
  - apply clashed_refut, H.
  - apply Weakc with (B++A). exact IH.
    intros s. rewrite !in_app_iff. close.
  - apply Weakc with A; close.
  - apply ndcII in IH1. apply ndcII in IH2.
    apply ndcIE with (-s). apply Weakc with A; close.
    apply ndcII.
    apply ndcIE with t. apply Weakc with A; close.
    apply ndcIE with s; ndcA.
  - do 2 apply ndcII in IH1.
    apply ndcIE with (s~>t). ndcA. apply ndcII.
    apply ndcC. apply ndcIE with s. 2:ndcA.
    apply ndcIE with (-t). 2:ndcA.
    apply Weakc with A; close.
Qed.

Fact solver :
  (forall A, sigma A + rho A) -> forall A, sat A + (A |-c bot).
Proof.
  intros H A. specialize (H A) as [H|H].
  - left. apply sigma_sound, H.
  - right. apply rho_sound, H.
Qed.

(** Size induction *)
 
Lemma size_ind {X} (sigma: X -> nat) (p: X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H.
  enough (forall n x, sigma x < n -> p x) by eauto.
  induction n as [|n IH]. lia. (* CFE *)
  intros x H1. apply H. intros y H2.
  apply IH. lia.
Qed.

Fixpoint gammaF s : nat :=
  match s with
  | var _ => 1
  | bot   => 1
  | imp s t => S (gammaF s + gammaF t)
  end.

Definition gamma' s : nat :=
  match s with
  | -s => gammaF s
  | s => gammaF s
  end.

Fixpoint gamma A : nat :=
  match A with
  | [] => 0
  | s::A => gamma' s + gamma A
  end.

Lemma gamma_app A B :
  gamma (A++B) = gamma A + gamma B.
Proof.
  induction A as [|s A IH]; cbn.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma gamma_In s t :
  gamma' s + gamma' (-t) < gamma' (-(s ~>t)).
Proof.
  destruct s; cbn; try lia.
  destruct s2; cbn; lia.
Qed.

Lemma gamma_Ipl s t :
  t <> bot -> gamma' (-s) < gamma' (s ~>t).
Proof.
  destruct t; cbn; (easy||lia).
Qed.

Lemma gamma_Ipr s t :
  t <> bot -> gamma' t < gamma' (s ~>t).
Proof.
  destruct t; cbn; try (easy||lia).
  destruct t2; cbn; (easy||lia).
Qed.

Fact presolver' :
  forall A, (solved A + clashed A)
       + (Sigma s B, decomposable s
                 * (gamma (s::B) = gamma A)
                 * (sigma (s::B) -> sigma A)
                 * (rho (s::B) -> rho A)).
Proof.
  intros A.
  destruct (presolver A) as [H|H].
  - left. exact H.
  - right. destruct H as (B&s&C&->&H).
    exists s, (C++B).
    change (s::C++B) with ((s::C)++B).
    repeat split.
    + exact H.
    + rewrite !gamma_app. lia.
    + apply sigma_rot.
    + apply rho_rot.
Qed.

Theorem abstract_solver :
  forall A, sigma A + rho A.
Proof.
  apply (size_ind gamma).
  intros A IH.
  destruct (presolver' A) as [[H|H]|(s&B&[[H H1] H2]&H3)]. 
  - left. apply sigma_solved, H.
  - right. apply rho_clashed, H.
  - destruct H as [|s t|s t H].
    + specialize (IH B) as [IH|IH].
      * rewrite <-H1. cbn. lia.
      * left. apply H2, sigma_bot, IH.
      * right. apply H3, rho_bot, IH.
    + specialize (IH (s::-t::B)) as [IH|IH].
      * rewrite <-H1. clear.
        generalize (gamma_In s t). cbn; lia.
      * left. apply H2, sigma_imp_neg, IH.
      * right. apply H3, rho_imp_neg, IH.
    + destruct (IH (-s::B)) as [IH1|IH1].
      * rewrite <-H1. revert H. clear.
        generalize (gamma_Ipl s t). cbn; intuition lia.
      * left. apply H2, sigma_imp_pos1, IH1. easy.
      * destruct (IH (t::B)) as [IH2|IH2].
        -- rewrite <-H1. revert H. clear.
           generalize (gamma_Ipr s t). cbn; intuition lia.
        -- left. apply H2, sigma_imp_pos2, IH2. easy.
        -- right. apply H3, rho_imp_pos; assumption.
Qed.

Corollary decidability :
  forall A s, dec (A |-c s).
Proof.
  apply ndc_dec, solver, abstract_solver.
Qed.

Corollary agreement :
  forall A s, A |-c s <=> A |= s.
Proof.
  apply ndc_ben, solver, abstract_solver.
Qed.


