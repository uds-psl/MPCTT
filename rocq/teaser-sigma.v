From Stdlib Require Import Lia.
Notation pi1 := projT1.
Notation pi2 := projT2.
Notation sig := sigT.
Notation Sig := existT.
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sig (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
    : type_scope.


Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

Fact dependent_eta X p :
  forall a, @Sig X p (pi1 a) (pi2 a) = a.
Proof.
  intros [x y]. cbn. reflexivity.
Qed.

(** Euclidean Division *)

Definition delta x y a b := x = a * S y + b /\ b <= y.

Fact lt_le x y :
  (x < y) + (x >= y). 
Proof.
  destruct (y - x) as [|a] eqn:H.
  - right. lia.
  - left. lia.
Qed.

Definition delta_fun :
  forall x y, Sigma a b, delta x y a b.
Proof.
  intros x y.
  induction x.
  - exists 0, 0. unfold delta; lia.
  - specialize IHx as [a [b IHx]].    
    destruct (lt_le b y) as [H|H].
    + exists a, (S b). unfold delta in *. lia.
    + exists (S a), 0. unfold delta in *. lia.
Qed.

Fact delta_unique x y a b a' b' :
  delta x y a b  -> delta x y a' b' -> a = a' /\ b = b'.
Proof.
  unfold delta. intros [H1 H2] [H3 H4].
  subst x.
  enough (a = a') by lia.
  revert a a' H3. induction a; destruct a'; cbn.
  1-3: lia.
  specialize (IHa a'). lia.
Qed.

Definition D x y := pi1 (delta_fun x y).
Definition M x y := pi1 (pi2 (delta_fun x y)).

Fact DM_delta x y :
  delta x y (D x y) (M x y).
Proof.
  unfold D, M.
  destruct (delta_fun x y) as [a [b H]]. cbn.
  exact H.
Qed.

Fact DM_unique x y a b :
  delta x y a b -> D x y = a /\ M x y = b.
Proof.
  apply delta_unique. apply DM_delta.
Qed.
    
Fact DS x y :
  D (x + S y) y = S (D x y) /\ M (x + S y) y = M x y.
Proof.
  apply DM_unique.
  destruct  (DM_delta x y) as [H1 H2].
  unfold delta in *. lia.
Qed.

Fixpoint ediv (x y: nat) : nat * nat :=
  match x with
  | 0 => (0,0)
  | S x => let (a,b) := ediv x y in
          if S b - y then (a, S b) else (S a, 0)
  end.

Fact ediv_correct x y :
  let (a,b) := ediv x y in delta x y a b.
Proof.
  induction x.
  - cbn. hnf. lia.
  - unfold ediv; fold ediv.
    (* important idiom in Rocq to mimique inductive functions *)
    destruct (ediv x y) as [a b].
    cbn in IHx. destruct IHx as [IH1 IH2].
    destruct (S b - y) eqn:H; cbn; unfold delta; lia.
Qed.
          
Goal bijection (nat + nat) nat.
Proof.
  unshelve eexists.
  - exact (fun a => match a with inl n => 2*n | inr n => 2*n+1 end).
  - exact (fun n => if M n 1 then inl (D n 1) else inr (D n 1)).
  - hnf. intros [n|n].
    + destruct (DM_delta (2*n) 1) as [H1 H2].
      destruct (M (2*n) 1) eqn:H3.
      * f_equal. lia.
      * lia.
    + destruct (DM_delta (2*n+1) 1) as [H1 H2].
      destruct (M (2*n+1) 1) eqn:H3.
      * exfalso. lia. 
      * f_equal. lia.
  - hnf. intros x.
    destruct (DM_delta x 1) as [H1 H2].
    destruct (M x 1) eqn:H3.
      * lia.
      * lia.
Qed.

(** Bijections *)

Fact Sigma_product X Y :
  bijection (X * Y) (Sigma _:X, Y).
Proof.
  unshelve eexists.
  (* yields best type checking and inference *)
  exact (fun a => Sig _ (fst a) (snd a)).
  exact (fun a => (pi1 a, pi2 a)).
  - intros [x y]. cbn. reflexivity.
  - intros [x y]. cbn. reflexivity.
Qed.

(* Note first use of tactic "unshelve eexists" *)
Fact bijection_sum X Y :
  bijection (X + Y) (sig (fun b:bool => if b then X else Y)).
Proof.
  unshelve eexists.
  - exact (fun a => match a with
                 | inl x => Sig _ true x
                 | inr y => Sig _ false y
                 end).
  - exact (fun a => match a with
                 | Sig _ true x => inl x
                 | Sig _ false y => inr y
                 end).
  (* inlined boolean discrimination yields best type checking *)
  - intros [x|y]. all:reflexivity.
  - intros [[|] a]. all:reflexivity.
Qed.

(* Note: First time we construct a reducible function with tactics *)   
Fact bijection_injection X Y :
  bijection (injection X Y) (Sigma f g, @inv X Y g f).
Proof.
  unshelve eexists.
  - intros [f g H]. exists f, g. exact H.
  - intros [f [g H]]. exists f g. exact H.
  - hnf. intros [f g H]. reflexivity.
  - hnf. intros [f [g H]]. reflexivity.
Qed.

(** Translations *)

Notation "~ X" := (X -> False) (at level 75, right associativity) : type_scope.
Definition iffT (X Y: Type) : Type := (X -> Y) * (Y -> X).
Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).
Definition dec (X: Type) : Type := X + ~X.
Definition eqdec X := forall x y: X, dec (x = y).


Fact eqdec_bool X :
  eqdec X <=> Sigma f: X -> X -> bool, forall x y, if f x y then x = y else x <> y.
Proof.
  split.
  - intros D.
    exists (fun x y => if D x y then true else false).
    intros x y.
    destruct (D x y) as [H|H]; easy.
  - intros [f H] x y.
    specialize (H x y).
    destruct (f x y); unfold dec; auto.
Qed.

Definition decider {X} (p: X -> Type) := forall x, dec (p x).

Fact decider_bool X (p: X -> Type) :
  decider p <=> Sigma f:  X -> bool, forall x, if f x then p x else ~ p x.
Proof.
  split.
  - intros D.
    exists (fun x => if D x then true else false).
    intros x.
    destruct (D x) as [H|H]; easy.
  - intros [f H] x.
    specialize (H x).
    destruct (f x); unfold dec; auto.
Qed.

Fact skolem_trans X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) -> Sigma f: X -> Y, forall x, p x (f x).
Proof.
  intros F.
  exists (fun x => pi1 (F x)).
  intros x. destruct (F x) as [y H]. cbn. exact H.
Qed.

Fact skolem_bitrans X Y (p: X -> Y -> Type) :
  (forall x, Sigma y, p x y) <=> Sigma f: X -> Y, forall x, p x (f x).
Proof.
  split.
  - apply skolem_trans.
  - intros [f H] x. exists (f x). apply H.
Qed.


(** Truncation *)

Print nat.

Inductive truncation (X: Type) : Prop := Truncation (_ : X).
Notation "□ X" := (truncation X) (at level 30, right associativity).

Goal forall P Q, P /\ Q <-> □ (P * Q).
Proof.
  intros *; split.
  - intros [H1 H2]. constructor. auto.
  - intros [[H1 H2]]. auto.
Qed.

Goal forall P Q, P \/ Q <-> □ (P + Q).
Proof.
  intros *; split.
  - intros [H1|H2]; constructor; auto.
  - intros [[H1|H2]]; auto.
Qed.

Goal forall X p, @ex X p <-> □ @sig X p.
Proof.
  intros *; split.
  - intros [x H]. constructor. eauto.
  - intros [[x H]]. eauto.
Qed.

Goal forall P: Prop, □ P <-> P.
Proof.
  intros *; split.
  - intros [H]. auto.
  - intros H. constructor. auto.
Qed.
Goal forall P: Prop, □ P <-> P.
Proof.
  intros *; split.
  - intros [H]. auto.
  - intros H. constructor. auto.
Qed.

Goal forall X, □ X <-> forall Z: Prop, (X -> Z) -> Z.
Proof.
  intros *; split.
  - intros [x] Z H. auto.
  - intros F. apply F. apply Truncation.
Qed.

(** Dependent pair injectivity *)

Fact DPI1 X p x y x' y' :
  @Sig X p x y = @Sig X p x' y' -> x = x'.
Proof.
  intros H.
  change x with (pi1 (Sig p x y)).
  rewrite H. reflexivity.
Qed.

(* Dependent pair injectivity in the 2nd component
   can be only be shown  with inductive equality and PI.   
   We will see a proof once we have indexed inductive types. *)        

Definition DPI := forall X p x y y', @Sig X p x y = @Sig X p x y' -> y = y'.

Fact sigma_eqdec X p :
  DPI -> eqdec X -> (forall x, eqdec (p x)) -> eqdec (@sig X p).
Proof.
  intros H D F [x y] [x' y'].
  destruct (D x x') as [H1|H1].
  - subst x'.
    destruct (F x y y') as [H2|H2].
    + subst y'. left. reflexivity.
    + right. intros H3. eapply H2, H, H3.
  - right. intros H2. apply H1.
    eapply DPI1, H2.
Qed.

(*** Lowering theorems for option types *)

(** With escape values *)

Definition lower {X Y} (f: option X -> option Y) y0 x :=
  match f (Some x) with
  | Some y' => y'
  | None => match f None with
           | Some y => y
           | None => y0
           end
  end.

Lemma lower_inv X Y f g x0 y0 :
  @inv (option X) (option Y) g f -> @inv X Y (lower g x0) (lower f y0).
Proof.
  intros H. intros x. unfold lower.
  destruct (f (Some x)) as [y|] eqn:E1.
  - destruct (g (Some y)) as [x'|] eqn:E2.
    + congruence.
    + exfalso. congruence.
  - destruct (f None) as [y|] eqn:E2. 
    + destruct (g (Some y))  as [y'|] eqn:E3.
      * exfalso. congruence.
      * destruct (g None) as [x'|] eqn:E4.
        -- congruence.
        -- exfalso. congruence.
    + exfalso. congruence.
Qed.

Theorem injection_lower_esc X Y (x0: X) (y0: Y) : 
  injection (option X) (option Y) -> injection X Y.
Proof.
  intros [f g H].
  exists (lower f y0) (lower g x0).
  eapply lower_inv, H.
Qed.

Theorem bijection_lower_esc X Y (x0: X) (y0: Y) : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  exists (lower f y0) (lower g x0).
  - eapply lower_inv, H1.
  - eapply lower_inv, H2.
Qed.

Inductive void : Type := .

Fixpoint num n : Type :=
  match n with 0 => void | S n => option (num n) end.

Lemma num_card_le_S m n :
  injection (num (S m)) (num (S n)) -> m <= n.
Proof.
  revert n. induction m. lia.
  intros n H.
  destruct n.
  - exfalso. destruct H as [f g Hfg].
    assert (H: f None <> f (Some None)).
    { intros H %(f_equal g). congruence. }
    destruct (f None); destruct (f (Some None)); easy.
  - enough (m <= n) by lia.
    apply IHm, injection_lower_esc.
    exact None. exact None. exact H.
Qed.

(** Without escape values *)

Definition lower_rel X Y (f: option X -> option Y) x y :=
  match f (Some x) with
  | Some y' => y = y'
  | None => Some y = f None
  end.

Definition lowering X Y f f' :=
  forall x, lower_rel X Y f x (f' x).

Lemma inv_lowering {X Y} f g :
  inv g f -> sig (lowering X Y f).
Proof.
  intros H.
  apply skolem_trans. intros x. unfold lower_rel.
  destruct (f (Some x)) as [y|] eqn:H1.
  - eauto.
  - destruct (f None) as [y|] eqn:H2.
    + eauto.
    + exfalso. congruence.
Qed.

Fact lowering_inv X Y f g f' g'  :
  lowering X Y f f' -> lowering Y X g g' -> inv g f -> inv g' f'.
Proof.
  intros H3 H4 H5 x.
  specialize (H3 x). hnf in H3.
  destruct (f (Some x)) as [y|] eqn:E1.
  - specialize (H4 y). hnf in H4.
    replace (g (Some y)) with (Some x) in H4; congruence.
  - destruct (f None) as [y|] eqn:E2.
    + specialize (H4 y). hnf in H4.
      replace (g (Some y)) with (@None X) in H4; congruence.
    + exfalso. clear H3 H4. congruence.
Qed.

Theorem bijection_lowering X Y : 
  bijection (option X) (option Y) -> bijection X Y.
Proof.
  intros [f g H1 H2].
  destruct (inv_lowering f g H1) as [f' H3].
  destruct (inv_lowering g f H2) as [g' H4].
  - exists f' g'.
    + revert H1. apply lowering_inv; assumption.
    + revert H2. apply lowering_inv; assumption.
Qed.

(** Only left inhabitation needed for injection lowering *)

Lemma lowering_inv' X Y f g f' x0 :
  lowering X Y f  f'-> inv g f -> inv (lower g x0) f'.
Proof.
  intros H1 H x.
  specialize (H1 x). hnf in H1.
  destruct (f (Some x)) as [y|] eqn:E1; unfold lower.
  - replace (g (Some (f' x))) with (Some x); congruence.
  - replace (g (Some (f' x))) with (@None X) by congruence.
    replace (g None) with (Some x); congruence.
Qed.

Theorem injection_lowering X Y : 
  X -> injection (option X) (option Y) -> injection X Y.
Proof.
  intros x0 [f g H].
  destruct (inv_lowering f g H) as [f' H1].
  exists f' (lower g x0).
  eapply lowering_inv'; eassumption.
Qed.






