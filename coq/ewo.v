From Coq Require Import Lia.
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

(*** EWO Basics *)

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


(* Injection from surjective function *)

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Fact surjective_inv X Y f :
  @surjective X Y f -> ewo X -> eqdec Y -> Sigma g, inv f g.
Proof.
  intros H E d.
  enough (G: forall y, Sigma x, f x = y).
  { exists (fun y => pi1 (G y)). intros y. destruct (G y) as [x H1]; easy. }
  intros y. apply E.
  - intros x. apply d.
  - apply H. 
Qed.

  
(*** Linear Search Types and EWO for nat *)

Module EWO_nat.
Section EWO_nat.
  Variable p: nat -> Prop.
  Variable p_dec: decider p.

  Inductive T (n: nat) : Prop := C (phi: ~p n -> T (S n)).

  Lemma T_base n :
    p n -> T n.
  Proof.
    intros H. constructor. intros H1. destruct (H1 H).
  Qed.

  Lemma T_step n :
    T (S n) -> T n.
  Proof.
    intros H. constructor. intros _. exact H.
  Qed.

  Lemma T_zero n :
    T n -> T 0.
  Proof.
    induction n as [|n IH].
    - auto.
    - intros H. apply IH. apply T_step, H.
  Qed.

  Lemma V n :
    p n -> T 0.
  Proof.
    intros H. eapply T_zero, T_base, H.
  Qed.

  Definition W'
    : forall n, T n -> sig p
    := fix f n a := let (phi) := a in
                    match p_dec n with
                    | inl h => (Sig p n h)
                    | inr h => f (S n) (phi h)
                    end.

  Theorem W :
    ex p -> sig p.
  Proof.
    intros H. apply (W' 0).
    destruct H as [n H].
    apply (V n), H.
  Qed.

  (* Eliminator generalizing W' *)
  
  Definition elim_T (q: nat -> Type)
    : (forall n, (~p n -> q (S n)) -> q n) ->
      forall n, T n -> q n
    := fun e => fix f n a := let (phi) := a in e n (fun h => f (S n) (phi h)).

  Fact W'_elim_T_agree :
    W' = elim_T (fun _ => sig p)
           (fun n f => match p_dec n with
                    | inl h => (Sig p n h)
                    | inr h => f h
                    end).
  Proof.
    reflexivity.
  Qed.
 
  Fact elim_T_unfold q e n phi :
    elim_T q e n (C n phi) = e n (fun h => elim_T q e (S n) (phi h)).
  Proof.
    reflexivity.
  Qed.
  
  Goal forall n, T n -> sig p.
  Proof.
    refine (elim_T _ (fun n IH => _)). cbn in IH.
    destruct (p_dec n) as [H|H].
    - exists n. exact H.
    - exact (IH H).
  Qed.

  (** Existential characterisation of T *)

  Fact T_step_add k n :
    T (k + n) -> T n.
  Proof.
    induction k as [|k IH].
    - auto. 
    - intros H. apply IH, T_step, H.
  Qed.

  Fact T_p_zero n :
    p n -> T 0.
  Proof.
    intros H%T_base%T_zero. exact H.
  Qed.

  Fact T_ex_ge n :
    T n <-> exists k, k >= n /\ p k.
  Proof.
    split.
    - revert n.
      refine (elim_T _ (fun n IH => _)). cbn in IH.
      destruct (p_dec n) as [H|H].
      + exists n. auto.
      + destruct (IH H) as (k&H1&H2).
        exists k. split. lia. exact H2.
    - intros (k&H1&H2). apply (T_step_add (k - n)).
      replace (k - n + n) with k by lia.
      constructor. easy. 
  Qed.

  (* Padding *)
  
  Definition pad3 n (d: T n) : T n :=
    C n (fun h => C (S n) (fun h1 => C (S (S n)) (fun h2 =>
       let (phi) := d in
       let (phi1) := phi h in
       let (phi2) := phi1 h1 in
       phi2 h2))).

End EWO_nat.
End EWO_nat.

Fact ewo_nat : ewo nat.
Proof.
  exact EWO_nat.W.
Qed.

Fact ewo_injection_nat X :
  injection X nat -> ewo X.
Proof.
  intros H %injection_ewo. apply H. apply ewo_nat.
Qed.
    

(*** More EWOs *)

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
