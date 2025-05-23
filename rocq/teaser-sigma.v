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
  (forall x, Sigma y, p x y) <=> Sigma f: X -> Y, forall x, p x (f x).
Proof.
  split.
  - intros F.
    exists (fun x => pi1 (F x)).
    intros x. destruct (F x) as [y H]. cbn. exact H.
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

(** Bijection theorem for option types *)

Lemma lower_f X Y f g :
  @inv (option X) (option Y) g f ->
  forall x, Sigma y, match f (Some x) with
            | Some y' => y = y'
            | None => Some y = f None
            end.
Proof.
  intros H x.
  destruct (f (Some x)) as [y|] eqn:H1.
  - exists y. reflexivity.
  - destruct (f None) as [y|] eqn:H2.
    + exists y. reflexivity.
    + exfalso. congruence.
Qed.

(** Injection Theorem for option types, under construction 

Lemma lower_g X Y f g x0 :
  @inv (option X) (option Y) g f -> 
  forall y, Sigma x, match g (Some y) with
            | Some x' => x = x'
            | None => match f None with
                     | None => x = x0
                     | Some y' => False end
            end.
Proof.
  intros H y.
  destruct (g (Some y)) as [x|] eqn:H1.
  - exists x. reflexivity.
  - exists x0. destruct (f None) as [y'|] eqn:H2.
    + admit.
    + congruence.
Qed.

Lemma lower X Y (x0: X) f g f' g' :
  @inv (option X) (option Y) g f ->
  (forall x, match f (Some x) with Some y => f' x = y | None => Some (f' x) = f None end) ->
  (forall y, match g (Some y) with Some x => g' y = x | None => g' y = x0 end) ->
  @inv X Y g' f'.
Proof.
  intros H H1 H2 x.
  assert (H1' := H1 x).
  assert (H2' := H2 (f' x)).
   clear H1 H2.
  destruct (f (Some x)) as [y|] eqn:H3.
  - destruct (g (Some (f' x))) as [x'|] eqn:H4; congruence.
  - destruct (g (Some (f' x))) as [x'|] eqn:H4.
    + congruence.
    + destruct (g None) as [x'|] eqn:H5.
      * destruct (f None) as [y'|] eqn:H6.
        -- assert (H7: f' x = y') by congruence. clear H1'.
           rewrite H7 in H4, H2'.
           rewrite H7. clear H7.
           subst (f' x).
           
      * exfalso. congruence.
Qed.

*)

      


