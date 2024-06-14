(*** MPCTT, Chapter EWOs *)
From Coq Require Import Lia.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + (X -> False).
Definition eqdec X := forall x y: X, dec (x = y).
Definition decider {X} (p: X -> Type) := forall x, dec (p x).
Notation sig := sigT.
Notation Sig := existT.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p%type)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.
Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) := forall x, g (f x) = x.
Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (_: inv g f).
Definition injective {X Y} (f: X -> Y) :=
  forall x x', f x = f x' -> x = x'.
Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.
Definition bijective {X Y} (f: X -> Y) :=
  injective f /\ surjective f.


(*** Linear Search Types *)

Section EWO.
  Variable p: nat -> Prop.

  Inductive T | (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Definition T_elim (q: nat -> Type)
    : (forall n, (~p n -> q (S n)) -> q n) ->
      forall n, T n -> q n
    := fun e => fix f n a :=
      let (phi) := a in
      e n (fun h => f (S n) (phi h)).

  (*** EWO for Numbers *)

  Lemma TI n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma TD n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Variable p_dec: decider p.

  Definition TE (q: nat -> Type)
    : (forall n, p n -> q n) ->
      (forall n, ~p n -> q (S n) -> q n) ->
      forall n, T n -> q n.
  Proof.
    intros e1 e2.
    apply T_elim. intros n IH.
    destruct (p_dec n); auto.
  Qed.

  (** From now on T will only be used through TI, TD, and TE *)

  
  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply TD, H.
  Qed.

  Definition ewo_nat :
    ex p -> sig p.
  Proof.
    intros H.
    refine (TE (fun _ => sig p) _ _ 0 _).
    - eauto.
    - auto.
    - destruct H as [n H]. apply (T_zero n), TI, H.
  Qed.

  (* T_zero generalized *)
  
  Fact T_lower n m :
    m <= n -> T n -> T m.
  Proof.
    induction n as [|n IH].
    - intros H1 H2.
      assert (m = 0) as -> by lia.
      exact H2.
    - intros H1 H2.
      assert (m = S n \/ m <= n) as [H|H] by lia.
      + congruence.
      + apply IH. exact H. apply TD, H2.
  Qed.

  Fact T_sig n :
    T n -> Sigma m, m >= n /\ p m.
  Proof.
    revert n.
    refine (TE _ _ _).
    - intros n IH. exists n. split. lia. exact IH.
    - intros n _ (m&IH1&IH2). exists m. split. lia. exact IH2.
  Qed.

  Fact T_equiv n :
    T n <=> Sigma m, m >= n /\ p m.
  Proof.
    split.
    - apply T_sig.
    - intros (m&H1&H2).
      eapply T_lower. exact H1. apply TI, H2.
  Qed.    
End EWO.

(*** General EWOs *)

Definition ewo (X:Type) :=
  forall p: X -> Prop, decider p -> ex p -> sig p.

Fact bot_ewo:
  ewo False.
Proof.
  intros p _ [[] _].
  (* note computational falsity elimination *)
Qed.

Goal ewo True.
Proof.
  intros p d H.
  destruct (d I) as [H1|H1].
  - eauto.
  - exfalso. destruct H as [[] H]. auto.
    (* note computational falsity elimination *)
Qed.

Goal ewo bool.
Proof.
  intros p d H.
  destruct (d true) as [H1|H1].
  - eauto.
  - destruct (d false) as [H2|H2].
    + eauto.
    + exfalso. destruct H as [[|] H]; auto.
      (* note computational falsity elimination *)
Qed.

Goal ewo nat.
Proof.
  exact ewo_nat.
Qed.

Theorem ewo_or X (p q: X -> Prop) :
  ewo X -> decider p -> decider q -> ex p \/ ex q -> sig p + sig q.
Proof.
    intros E dp dq H.
    destruct (E (fun x => p x \/ q x)) as [x H1].
    - intros x. unfold dec.
      destruct (dp x) as [H1|H1]. { auto. }
      destruct (dq x) as [H2|H2]. { auto. }
      tauto.
    - destruct H as  [[x H]|[x H]]; eauto.
    - destruct (dp x) as [H2|H2]. { eauto. }
      destruct (dq x) as [H3|H3]. { eauto. }
      exfalso. tauto.
Qed.

Definition option_ewo {X} :
  ewo X -> ewo (option X).
Proof.
  intros E p p_dec H.
  destruct (p_dec None) as [H1|H1].
  - eauto.
  - destruct (E (fun x => p (Some x))) as [x H2].
    + easy. 
    + destruct H as [[x|] H].
      * eauto.
      * easy.
    + eauto.
Qed.

Definition option_ewo' {X} :
  ewo (option X) -> ewo X.
Proof.
  intros E p p_dec H.
  destruct (E (fun a => match a with Some x => p x | none => False end)) as [[x|] H1].
  - intros [x|].
      + easy.
      + right; easy.
  - destruct H as [x H]. exists (Some x); exact H.
  - eauto.
  - easy.
Qed.

Fixpoint Fin n : Type :=
  match n with 0 => False | S n' => option (Fin n') end.

Fact Fin_ewo :
  forall n, ewo (Fin n).
Proof.
  induction n as [|n IH]; cbn.
  - apply bot_ewo.
  - apply option_ewo, IH.
Qed.

Fact injection_ewo X Y :
  injection X Y -> ewo Y -> ewo X.
Proof.
  intros [f g H] E p p_dec H1.
  destruct (E (fun y => p (g y))) as [y H2].
  - easy.
  - destruct H1 as [x H1]. exists (f x). congruence.
  - eauto.
Qed.

Fact injection_nat_ewo X :
  injection X nat -> ewo X.
Proof.
  intros H.
  eapply injection_ewo. exact H. exact ewo_nat.
Qed.

Fact ewo_binary :
  injection (nat * nat) nat ->
  forall p: nat -> nat -> Prop,
  forall d: forall x y, dec (p x y),
    (exists x y, p x y) -> Sigma x y, p x y.
Proof.
  intros E %injection_ewo. 2:exact ewo_nat.
  intros p d H.
  pose (q a := p (fst a) (snd a)).
  specialize (E (fun a => p (fst a) (snd a))) as [[x y] E].
  - intros [x y]. apply d.
  - destruct H as (x&y&H). exists (x,y). exact H.
  - eauto.
Qed.

(*** EWO Applications *)

Fact surjective_inv {X Y f} :
  @surjective X Y f -> ewo X -> eqdec Y -> Sigma g, inv f g.
Proof.
  intros H e d.
  enough (G: forall y, Sigma x, f x = y).
  { exists (fun y => pi1 (G y)). intros y. apply (pi2 (G y)). }
  intros y. apply e.
  - intros x. apply d.
  - apply H. 
Qed.

Fact bijective_inv X Y f :
  @bijective X Y f -> ewo X -> eqdec Y -> Sigma g, inv g f /\ inv f g.
Proof.
  intros [H1 H2] e d.
  destruct (surjective_inv H2 e d) as [g H3].
  exists g. split. 2:exact H3.
  intros x. apply H1. congruence.
Qed.

Section Step_indexed_eqdec.
  Variable X: Type.
  Variable f: X -> X -> nat -> bool.
  Variable f_prop: forall x y, x = y <-> exists n, f x y n = true.
  Goal eqdec X.
  Proof.
    intros x y.
    enough (Sigma n, f x x n = true) as [n H].
    { destruct (f x y n) eqn:H1.
      - left. apply f_prop. exists n. exact H1.
      - right. intros <-. congruence. }
    apply ewo_nat.
    - intros n.
      destruct (f x x n).
      + left. auto.
      + right. intros [=].
    - apply f_prop. reflexivity.
  Qed.
End Step_indexed_eqdec.

(*** EWO with interface *)

Definition safe p n := forall k, k < n -> ~p k.
Definition least p n := p n /\ safe p n.

Fact safe_S p n :
  safe p n -> ~p n -> safe p (S n).
Proof.
  unfold safe; intros H1 H2 k H3.
  assert (k < n \/ k = n) as [H| ->] by lia; auto.
Qed.

Module EWO_Nat_Inter.

  Section EWO_nat_above.
    Variable p : nat -> Prop.
    Variable T' : nat -> Prop.
    Variable I : forall n, p n -> T' n.
    Variable D : forall n, T' (S n) -> T' n.
    Variable E' :
      decider p ->
      forall q: nat -> Type,
        (forall n, p n -> q n) ->
        (forall n, q (S n) -> q n) ->
        (forall n, T' n -> q n).

    Lemma T'_sig :
      decider p -> forall n, T' n -> sig p.
    Proof.
      intros d. apply (E' d); eauto.
    Qed.

    Lemma T'_zero :
      forall n, T' n -> T' 0.
    Proof.
      induction n as [|n IH]. easy.
      intros H. apply IH, D, H.
    Qed.

    Lemma ex_T'_zero :
      ex p -> T' 0.
    Proof.
      intros [x H]. eapply T'_zero, I, H.
    Qed.

    Fact ewo_nat :
      decider p -> ex p -> sig p.
    Proof.
      intros d H. apply (T'_sig d 0).
      destruct H as [n H].
      apply (T'_zero n), I, H.
    Qed.

    Lemma T'_least :
      decider p -> forall n, T' n -> safe p n -> sig (least p).
    Proof.
      intros d.
      refine (E' d _ _ _).
      - intros n H1 H2. exists n. easy.
      - intros n H1 H2.
        destruct (d n) as [H3|H3].
        + exists n. easy.
        + apply H1, safe_S; easy.
    Qed.

    Fact ewo_nat_least :
      decider p -> ex p -> sig (least p).
    Proof.
      intros d H.
      apply (T'_least d 0). 2:easy.
      apply ex_T'_zero, H.
    Qed.

  End EWO_nat_above.

  Section EWO_nat_below.
    Variable p : nat -> Prop.

    Definition I : forall n, p n -> T p n.
    Proof. intros n H. apply C. easy. Qed.

    Definition D : forall n, T p (S n) -> T p n.
    Proof. intros n H. apply C. easy. Qed.

    Fact E':
      decider p ->
      forall q: nat -> Type,
        (forall n, p n -> q n) ->
        (forall n, q (S n) -> q n) ->
        (forall n, T p n -> q n).
    Proof.
      intros d q e1 e2.
       apply T_elim.
      intros n IH.
      destruct (d n) as [H|H]; auto.
    Qed.
  End EWO_nat_below.
End EWO_Nat_Inter.
