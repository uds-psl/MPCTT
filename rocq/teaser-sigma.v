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
  revert H3. subst x. revert a'.
  induction a; destruct a'; cbn.
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
    
Fact DMS x y :
  D (x + S y) y = S (D x y) /\ M (x + S y) y = M x y.
Proof.
  apply DM_unique.
  generalize (DM_delta x y).
  unfold delta. lia.
Qed.

(** Bijections *)

Definition inv {X Y: Type} (g: Y -> X) (f: X -> Y) :=
  forall x, g (f x) = x.

Inductive bijection (X Y: Type) : Type :=
| Bijection: forall (f: X -> Y) (g: Y -> X), inv g f -> inv f g -> bijection X Y.

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

Inductive injection (X Y: Type) : Type :=
| Injection {f: X -> Y} {g: Y -> X} (H: inv g f).

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

