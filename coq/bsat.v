From Coq Require Export Bool Lia List.
From Equations Require Export Equations.
Set Equations Transparent.

Notation "! b" := (negb b) (at level 39).
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "x 'nel' A" := (~In x A) (at level 70).
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (P: Prop) := {P} + {~P}.
Lemma dec_transport (X Y : Prop) : 
  (X <-> Y) -> dec X -> dec Y.
Proof.
  unfold dec; tauto.
Qed.
Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
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
Defined.

(*** Formulas and clauses *)

Definition var := nat.
Inductive form: Type := Var (x: nat) | Fal | Imp (s t : form).
Notation "s ~> t" := (Imp s t) (at level 41, right associativity).
Notation "-- s" := (s ~> Fal) (at level 42, right associativity).
Implicit Types x y : var.
Implicit Types s t : form.
Inductive sform : Type := Pos (s: form) | Neg (s: form).
Notation "+ s" := (Pos s) (at level 43).
Notation "- s" := (Neg s). (* cannot overwrite reserved level for nat *)
Definition clause := list sform.
Implicit Types S T : sform.
Implicit Types C D E : clause.
Implicit Types L : list clause.

Definition sform_eq_dec S T : dec (S = T).
Proof. 
  unfold dec. repeat decide equality. 
Defined.
Definition clause_eq_dec C D : dec (C = D).
Proof. 
  unfold dec. repeat decide equality. 
Defined.
Definition list_clause_eq_dec L L' : dec (L = L').
Proof. 
  unfold dec. repeat decide equality. 
Defined.
Definition clause_in_dec S C : dec (S el C).
Proof. 
  unfold dec. apply in_dec, sform_eq_dec.
Defined.

(** Evaluation *)

Implicit Types alpha beta : var -> bool.

Equations eva alpha s : bool :=
  eva alpha (Var x)  := alpha x ;
  eva alpha Fal      := false ;
  eva alpha (s ~> t) := !eva alpha s || eva alpha t.
Equations evas alpha S : bool :=
  evas alpha (+s) := eva alpha s ;
  evas alpha (-s) := !eva alpha s.
Equations evac alpha C : bool :=
  evac alpha []     := true ;
  evac alpha (T::C) := evas alpha T && evac alpha C.
Equations evad alpha L : bool :=
  evad alpha []     := false ;
  evad alpha (C::L) := evac alpha C || evad alpha L.
Notation "alpha '|=' C" := (evac alpha C = true) (at level 70).
Definition satf s := exists alpha, eva alpha s = true. 
Definition satc C := exists alpha, alpha |= C.

Lemma satfc s :
  satf s <-> satc [+s].
Proof.
  split; intros [alpha H]; exists alpha; cbn in *;
    revert H; rewrite andb_true_r; trivial.
Qed.
Lemma evac_app alpha C D :
  evac alpha (C++D) = evac alpha C && evac alpha D.
Proof.
  induction C as [|S C IH]; cbn. reflexivity.
  rewrite IH. apply andb_assoc.
Qed.
Lemma evad_app alpha L L' :
  evad alpha (L++L') = evad alpha L || evad alpha L'.
Proof.
  induction L as [|C L IH]; cbn. reflexivity.
  rewrite IH. apply orb_assoc.
Qed.
Lemma evac_false S C alpha :
  S el C -> evas alpha S = false -> evac alpha C = false.
Proof.
  intros H1 H2. induction C as [|T C IH]; cbn.
  - destruct H1.
  - destruct H1 as [->|H1]. now rewrite H2.
    rewrite (IH H1). apply andb_false_r.
Qed.

(*** DNF Solver *)

Inductive solved : clause -> Prop :=
| solved_nil :solved []
| solved_pos x C : -Var x nel C -> solved C -> solved (+Var x::C)
| solved_neg x C : +Var x nel C -> solved C -> solved (-Var x::C).

Definition DNF Delta := forall C, C el Delta -> solved C.

Equations sizeF s : nat :=
  sizeF (s1 ~> s2) := 1 + sizeF s1 + sizeF s2 ;
  sizeF _          := 1.     
Equations size C : nat :=
  size nil := 0 ;
  size (+s::C) := sizeF s + size C ;
  size (-s::C) := sizeF s + size C.

Lemma dnf_rec (p: clause -> clause -> Type) :
  (forall C, solved C -> p C []) -> 
  (forall C D x, -Var x el C -> p C (+Var x::D)) -> 
  (forall C D x, -Var x nel C -> p (+Var x::C) D -> p C (+Var x::D)) -> 
  (forall C D x, +Var x el C -> p C (-Var x::D)) -> 
  (forall C D x, +Var x nel C -> p (-Var x::C) D -> p C (-Var x::D)) -> 
  (forall C D, p C (+Fal::D)) ->
  (forall C D, p C D -> p C (-Fal::D)) ->
  (forall C D s t, p C (-s::D) -> p C (+t::D) -> p C (+(s ~> t) :: D)) ->
  (forall C D s t, p C (+s::-t::D) -> p C (-(s ~> t) :: D)) ->
  forall C D, solved C -> p C D.
Proof.
  intros e1 e2 e3 e6 e7 e4  e8 e5 e9.
  intros C D. revert D C.
  refine (size_rec size _).
  intros D IH C H.
  destruct D as [|S D].
  { apply e1, H. }
  destruct S as [[x| | s t]|[x| | s t]].
  - destruct (clause_in_dec (-Var x) C) as [H1|H1].
    + apply e2; easy.
    + apply e3. exact H1. apply IH.
      * cbn; lia.
      * constructor; easy.
  - apply e4; easy.
  - apply e5.
    + apply IH. 2:exact H. cbn. lia.
    + apply IH. 2:exact H. cbn. lia.
  - destruct (clause_in_dec (+Var x) C) as [H1|H1].
    + apply e6; easy.
    + apply e7. exact H1. apply IH.
      * cbn; lia.
      * constructor; easy.
  - apply e8. apply IH. 2:exact H. cbn; lia.
  - apply e9. apply IH. 2:exact H. cbn; lia.
Qed.

Lemma dnf_cla_cla :
  forall C D, solved C -> Sigma Delta, DNF Delta /\ forall alpha, evac alpha (D ++ C) = evad alpha Delta.
Proof.
  apply dnf_rec.
  - intros C H. exists [C]. split.
    + intros D [->|[]]. exact H.
    + intros alpha. cbn. destruct evac; reflexivity.
  - intros C D x H1. exists []. split.
    + intros _ [].
    + intros alpha. rewrite evac_app.
      specialize (evac_false (-Var x) C alpha). cbn.
      destruct alpha, evac, evac; cbn; tauto.
  - intros C D x H (Delta&IH1&IH2).
    exists Delta. split. exact IH1.
    intros alpha. destruct (IH2 alpha).
    do 2 rewrite evac_app. cbn.
    destruct alpha, evac; reflexivity.
  - intros C D x H1. exists []. split.
    + intros _ [].
    + intros alpha. rewrite evac_app.
      specialize (evac_false (+Var x) C alpha). cbn.
      destruct alpha, evac, evac; cbn; tauto.
  - intros C D x H (Delta&IH1&IH2).
    exists Delta. split. exact IH1.
    intros alpha. destruct (IH2 alpha).
    do 2 rewrite evac_app. cbn.
    destruct alpha, evac; reflexivity.
  - intros C D. exists []. split.
    + intros _ [].
    + reflexivity.
  - intros C D (Delta&IH1&IH2).
    exists Delta. split. exact IH1.
    intros alpha. destruct (IH2 alpha). reflexivity.
  - intros C D s t (Delta1&IH11&IH12) (Delta2&IH21&IH22).
    exists (Delta1++Delta2). split.
    + intros E H1%in_app_iff. intuition.
    + intros alpha. rewrite evad_app, <-IH12, <-IH22. cbn.
      destruct eva, eva, evac; reflexivity.
  - intros C D s t (Delta&IH1&IH2).
    exists Delta. split. exact IH1.
    intros alpha. destruct (IH2 alpha). cbn.
    destruct eva, eva; reflexivity.
Qed.

Theorem dnf_cla :
  forall C, Sigma Delta, DNF Delta /\ forall alpha, evac alpha C = evad alpha Delta.
Proof.
  intros C.
  destruct (dnf_cla_cla [] C) as (Delta&H1&H2).
  { constructor. }
  exists Delta. split. exact H1. intros alpha. destruct (H2 alpha).
  rewrite evac_app. cbn. destruct evac; reflexivity.
Qed.

Corollary dnf_for :
  forall s, Sigma Delta, DNF Delta /\ forall alpha, eva alpha s = evad alpha Delta.
Proof.
  intros s.
  destruct (dnf_cla [+s]) as (Delta&H1&H2).
  exists Delta. split. exact H1. intros alpha. destruct (H2 alpha).
  cbn. destruct eva; reflexivity.
Qed.

(*** Solved clauses are satisfiable *)

Definition sol C x := if clause_in_dec (+Var x) C then true else false.

Lemma evac_forall alpha C :
  alpha |= C <-> forall S, S el C -> evas alpha S = true.
Proof.
  induction C as [|T C IH]; cbn.
  - firstorder.
  - rewrite andb_true_iff, IH; clear. firstorder; congruence.
Qed.

Lemma solved_in {S C} :
  solved C -> S el C ->
  exists x, S = + Var x /\ -Var x nel C \/
       S = - Var x /\ +Var x nel C.
Proof.
  induction 1 as [|x C H1 _ IH|x C H1 _ IH]; cbn.
  - tauto.
  - intros [<-|H2].
    + exists x. intuition congruence.
    + destruct (IH  H2) as [x' [[-> H3]|[-> H3]]]; 
        exists x'; intuition congruence.
  - intros [<-|H2].
    + exists x. intuition congruence.
    + destruct (IH  H2) as [x' [[-> H3]|[-> H3]]]; 
        exists x'; intuition congruence.
Qed.

Lemma sol_solved C :
  solved C -> sol C |= C.
Proof.
  intros H. apply evac_forall. intros S H1.
  destruct (solved_in H H1) as [x [[-> H2]|[-> H2]]]; cbn;
    unfold sol; destruct clause_in_dec as [H3|H3]; tauto.
Qed.

(*** Certifying Boolean Solvers *)

Corollary solve_cla :
  forall C, (Sigma alpha, alpha |= C) + ~satc C.
Proof.
  intros C. destruct (dnf_cla C) as (Delta&H1&H2).
  destruct Delta as [|D Delta].
  - right. intros [alpha H]. rewrite H2 in H. discriminate H.
  - left. exists (sol D). rewrite H2. cbn.
    rewrite sol_solved. reflexivity. apply H1. cbn; auto.
Qed.

Corollary satc_dec C :
  dec (satc C).
Proof.
  destruct (solve_cla C) as [[alpha H]|H].
  - left. exists alpha. exact H.
  - right. exact H.
Qed.

Corollary solve_for :
  forall s, (Sigma alpha, eva alpha s = true) + ~satf s.
Proof.
  intros s. destruct (solve_cla [+s]) as [[alpha H]|H].
  - left. exists alpha. cbn in H. destruct eva; easy.
  - right. contradict H. destruct H as [alpha H]. exists alpha.
    cbn. rewrite H. reflexivity.
Qed.

Corollary satf_dec s :
  dec (satf s).
Proof.
  destruct (solve_for s) as [[alpha H]|H].
  - left. exists alpha. exact H.
  - right. exact H.
Qed.

(** Tableau system *)

Inductive tab : list sform -> Type :=
| tabM S C D: tab (S::C++D) -> tab (C++S::D)
| tabF C: tab (+Fal::C)
| tabC x C: tab (+Var x::-Var x::C)
| tabpI s t C: tab (-s::C) -> tab (+t::C) -> tab (+(s~>t)::C)
| tabnI s t C: tab (+s::-t::C) -> tab (-(s~>t)::C).

Lemma tab_sound C alpha :
  tab C -> alpha |= C -> False.
Proof.
  induction 1; cbn in *.
  - contradict IHtab. revert IHtab. cbn.
    do 2 rewrite evac_app. cbn.
    destruct (evac alpha C), (evas alpha S) ; auto.
  - discriminate.
  - destruct (alpha x); cbn; discriminate.
  - revert IHtab1 IHtab2.
    destruct (eva alpha s), (eva alpha t); cbn; auto.
  - revert IHtab. destruct (eva alpha s), (eva alpha t); cbn; auto.
Qed.

Lemma tabW C S:
  tab C -> tab (S::C).
Proof.
  induction 1.
  - apply (tabM S0 (S::C)).
    apply (tabM S [S0]), IHtab.
  - apply (tabM (+Fal) [S]), tabF.
  - apply (tabM (-Var x) [S;+Var x]).
    apply (tabM (+Var x) [-Var x;S]), tabC.
  - apply (tabM (+(s~>t)) [S]), tabpI.
    + apply (tabM S [-s]), IHtab1.
    + apply (tabM S [+t]), IHtab2.
  - apply (tabM (-(s~>t)) [S]), tabnI.
    apply (tabM S [+s;-t]), IHtab.
Qed.

Lemma tabR C D E :
  tab (rev D++C++E) -> tab (C++D++E).
Proof.
  induction D as [|S D IH] in C |-*; cbn; intros H.
  - exact H.
  - apply (tabM S C).
    apply (IH (S::C)).
    change (S::C) with ([S]++C).
    revert H. do 2 rewrite <-app_assoc. trivial.
Qed.
    
Lemma tabL C D E :
  tab (C++D++E) -> tab (D++C++E).
Proof.
  intros H. apply tabR. apply tabR with (C:=[]).
  rewrite rev_involutive. exact H.
Qed.

Lemma tabM' C D S :
  tab (C++S::D) -> tab (S::C++D).
Proof.
  apply tabL with (D:=[S]).
Qed.

Lemma split_cla S C :
  S el C -> Sigma C1 C2, C = C1 ++ S::C2.
Proof.
  induction C as [|T C IH].
  - intros [].
  - intros H. destruct (clause_in_dec S C) as [H1|H1].
    + destruct (IH H1) as (C1&C2&->). exists (T::C1), C2. reflexivity.
    + exists [], C. destruct H as [<-|H2]; easy.
Qed.

Lemma tabC' x C :
  +Var x el C -> -Var x el C -> tab C.
Proof.
  (* Rewriting lists with app_assoc can be terribly painful *)
  intros (C1&C2&->)%split_cla.
  destruct (clause_in_dec (-Var x) C1) as [H|H].
  - intros _. apply split_cla in H as (C3&C4&->).
    cbn.  rewrite <-app_assoc. cbn.
    apply (tabM (-Var x)).
    rewrite app_assoc.
    apply (tabM (+Var x) (-Var x::C3 ++ C4)). cbn.
    constructor.
  - intros H1.
    assert (-Var x el C2) as H2.
    { apply in_app_or in H1 as [H1|[H1|H1]]; easy. }
    apply split_cla in H2 as (C3&C4&->).
    change (tab (C1 ++ (+ Var x :: C3) ++ (- Var x :: C4))).
    rewrite app_assoc.
    apply (tabM (-Var x)).
    rewrite <-app_assoc.
    apply (tabM (+Var x) (-Var x::C1)).
    constructor.
Qed.

Lemma tab_complete:
  forall C D, solved C -> ~ satc (D++C) -> tab (D++C).
Proof.
  refine (dnf_rec _ _ _ _ _ _ _ _ _ _); cbn.
  - intros C H1 H2.
    contradict H2. eexists. apply sol_solved, H1.
  - intros C D x H2 H3. apply (tabC' x); cbn.
    + auto.
    + right. apply in_or_app. auto.
  - intros C D x  H1 IH H2. 
    apply tabM'. apply IH.
    contradict H2. destruct H2 as [alpha H2]. exists alpha.
    revert H2. cbn. rewrite !evac_app. cbn.
    destruct alpha, evac; easy.
  - intros C D x H2 H3. apply (tabC' x); cbn.
    + right. apply in_or_app. auto.
    + auto.
  - intros C D x H1 IH H2.
    apply tabM'. apply IH.
    contradict H2. destruct H2 as [alpha H2]. exists alpha.
    revert H2. cbn. rewrite !evac_app. cbn.
    destruct alpha, evac; easy.
  - intros C D H2. constructor.
  - intros C D IH H.
    apply tabW. apply IH.
    contradict H. destruct H as [alpha H]. exists alpha. exact H.
  -  intros C D s t IH1 IH2 H.
     constructor.
     + apply IH1.
      contradict H. destruct H as [alpha H]. exists alpha.
      cbn. cbn in H. destruct eva, eva, evac; easy.
     + apply IH2.
      contradict H. destruct H as [alpha H]. exists alpha.
      cbn. cbn in H. destruct eva, eva, evac; easy.
  - intros C D s t IH H.
    constructor. apply IH.
    contradict H. destruct H as [alpha H]. exists alpha.
    cbn. cbn in H. destruct eva, eva; easy.
Qed.

Lemma tab_unsat C :
  tab C <=> ~satc C.
Proof.
  split.
  - intros H [alpha H1]. revert H H1. apply tab_sound.
  - rewrite <-(app_nil_r C). apply tab_complete. constructor.
Qed.

Lemma tab_solve C :
  (Sigma alpha, alpha |= C) + tab C.
Proof.
  destruct (solve_cla C) as [H|H]. 
  - left. exact H.
  - right. apply tab_unsat, H.
Qed.

(*** Abstract refutation systems *)

Implicit Types (A B: list form).

Equations eval alpha A : bool :=
eval alpha []     := true ;
eval alpha (s::A) := eva alpha s && eval alpha A.
Notation "alpha |== A" := (eval alpha A = true) (at level 70).
Definition sat A := exists alpha, alpha |== A.

Lemma map_pos alpha A :
  evac alpha (map Pos A) = eval alpha A.
Proof.
  induction A as [|s A IH]; cbn. reflexivity.
  f_equal. exact IH.
Qed.

Definition uns S : form :=
  match S with +s => s | -s => --s end.

Lemma uns_pos A :
  map uns (map Pos A) = A.
Proof.
  induction A as [|s A IH]; cbn. reflexivity.
  f_equal. exact IH.
Qed.

Section Refutation.
  Variables (rho: list form -> Type)
            (Move: forall s A B, rho(s::A++B) -> rho(A++s::B))
            (Clash: forall x A, rho(Var x :: --Var x :: A))
            (Falsity: forall A, rho(Fal::A))
            (Posimp: forall s t A, rho(--s::A) -> rho(t::A) -> rho(s~>t::A))
            (Negimp: forall s t A, rho(s::--t::A) -> rho(--(s~>t)::A)).

  Lemma tab_rho C :
    tab C -> rho(map uns C).
  Proof.
    induction 1; cbn in *.
    - revert IHtab. rewrite !map_app. cbn. apply Move.
    - apply Falsity.
    - apply Clash.
    - now apply Posimp.
    - now apply Negimp.
  Qed.
  
  Theorem rho_solve A :
    (Sigma alpha, alpha |== A) + rho A.
  Proof.
    destruct (tab_solve (map Pos A)) as [[alpha H]|H].
    - left. exists alpha. rewrite map_pos in H. exact H.
    - right. apply tab_rho in H. rewrite uns_pos in H. exact H.
  Qed.
  
  Variable Sound: forall A , rho A -> ~sat A.

  Lemma rho_complete A :
    rho A <=> ~sat A.
  Proof.
    split. { apply Sound. } intros H.
    destruct (rho_solve A) as [[alpha H1]|H1]. 2:exact H1.
    exfalso. apply H. unfold sat; eauto.
  Qed.

  Lemma rho_dec A :
    rho A + (rho A -> False).
  Proof.
    destruct (rho_solve A) as [[alpha H]|H].
    - right. intros H1%Sound. apply H1; unfold sat; eauto.
    - left. exact H.
  Qed.
End Refutation.

(*** Validity *)

Definition valid s := forall alpha, eva alpha s = true.

Fact valid_unsat s :
  valid s <-> ~satf (--s).
Proof.
  split; intros H.
  - intros [alpha H1]. specialize (H alpha).
    revert H1. cbn. rewrite H. cbn. discriminate.
  - intros alpha. destruct (eva alpha s) eqn:H1. reflexivity.
    contradict H. exists alpha. cbn. rewrite H1. trivial.
Qed.

Fact sat_valid s :
  satf s <-> ~valid (--s).
Proof.
  split.
  - intros [alpha H] H1. specialize (H1 alpha).
    revert H1. cbn. rewrite H. cbn.  discriminate.
  - intros H.  apply dec_DN. { apply satf_dec. }
    contradict H. intros alpha. cbn.
    destruct (eva alpha s) eqn:H1. 2:reflexivity.
    contradict H. exists alpha. exact H1.
Qed.

Fact valid_solve :
  forall s, (Sigma alpha, eva alpha s = false) + valid s.
Proof.
  intros s.
  destruct (solve_for (--s)) as [[alpha H]|H].
  - left. exists alpha. revert H. cbn. destruct eva; easy.
  - right. apply valid_unsat, H.
Qed.
