Check forall X:Prop, X -> X.

Check fun X:Prop  => fun x:X=> x.

Check (fun X x => x)
  : forall X:Prop, X -> X.

Check (fun X Y Z f g x => g (f x)) 
  : forall X Y Z: Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).

Definition F1 (X Y Z : Prop)
  : (X -> Y) -> (Y -> Z) -> (X -> Z)
  := fun f g x => g (f x).
Print F1.

Definition F1' (X Y Z : Prop)
  : (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros f g x. exact (g (f x)).
Qed.
Print F1'.

Definition F2 (X Y Z : Prop)
  : (X -> Y -> Z) -> (X -> Y) -> (X -> Z)
  := fun f g x => f x (g x).
Print F2.

Definition F2' (X Y Z : Prop)
  : (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  intros f g x. exact (f x (g x)).
Qed.
Print F2'.

Definition F2'' (X Y Z : Prop)
  : (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  refine (fun f g x => _).
  Show Proof.
  exact (f x (g x)).
Qed.
Print F2''.

(* We may write [Fact] in place of [Definition]
   if we want to comit to using  tactic mode.
   We may  also use the  command [Goal]
   if we don't need a name. *)

Goal forall (X Y Z : Prop), (X -> Y -> Z) -> (X -> Y) -> (X -> Z).     
Proof.
  intros X Y Z f g x.
  Show Proof.
  exact (f x (g x)).
Qed.
(* We loose the ability to display the final proof term *)

(** Falsity and Negation *)

(* We define a constant for falsity and a notation for negation.
   We do this in a module to preserve the predefined versions *)        
Module Falsity.
  Notation False := (forall X: Prop, X).
  Notation "~ X" := (X -> False) : type_scope.

  Fact N1 (X: Prop) :
    X -> ~ ~ X.
  Proof.
    intros x f. exact (f x).
  Qed.
  Print N1.

  Fact N2 (X Y: Prop) :
    X -> ~ X -> Y.
  Proof.
    intros x f. exact (f x Y).
  Qed.
  Print N2.

  Fact N3 (X Y: Prop) :
    (X -> Y) -> (~Y -> ~X).
  Proof.
    intros f g x. exact (g (f x)).
  Qed.
  Print N3.

  Fact N4 (X: Prop) :
    (X -> ~X) -> (~X -> X) -> False.
  Proof.
    intros f g.
    assert (h : ~X).
    - exact ((fun x => f x x)).
    - exact (h (g h)).
  Qed.
  Print N4.

  Fact N4' (X: Prop) :
    (X -> ~X) -> (~X -> X) -> False.
  Proof.
    intros f g.
    exact (let h x := f x x in h (g h)).
  Qed.
  Print N4'.

  Fact N4'' (X: Prop) :
    (X -> ~X) -> (~X -> X) -> False.
  Proof.
    intros f g.
    apply f.
    - exact (g (fun x => f x x)).
    - exact (g (fun x => f x x)).
  Qed.
  Print N4''.
End Falsity.

(** Abstract conjunction and disjunction *)

Module Abstract_and_or.
  Section Abstract_and_or.
    
  Variable and : Prop -> Prop -> Prop.
  Variable and_intro : forall X Y, X -> Y -> and X Y.
  Variable and_elim : forall X Y, and X Y -> forall Z: Prop, (X -> Y -> Z) -> Z.

  Fact and_comm X Y :
    and X Y -> and Y X.
  Proof.
    intros a.
    apply (and_elim _ _ a).
    intros x y.
    apply (and_intro _ _ y x).
  Qed.
  Print and_comm.

  Fact and_elim_intro X Y :
    (forall Z, (X -> Y -> Z) -> Z) -> and X Y.
  Proof.
    intros F. apply F. apply and_intro.
  Qed.

  Variable or : Prop -> Prop -> Prop.
  Variable or_intro_l : forall X Y, X -> or X Y.
  Variable or_intro_r : forall X Y, Y -> or X Y.
  Variable or_elim : forall X Y, or X Y -> forall Z:Prop, (X -> Z) -> (Y -> Z) -> Z.

  
  Fact or_comm X Y :
    or X Y -> or Y X.
  Proof.
    intros a.
    apply (or_elim _ _ a).
    - apply or_intro_r.
    - apply or_intro_l.
  Qed.
  Print or_comm.

  Fact or_elim_intro X Y :
    (forall Z, (X -> Z) -> (Y -> Z) -> Z) -> or X Y.
  Proof.
    intros H. apply H.
    - apply or_intro_l.
    - apply or_intro_r.
  Qed.
End Abstract_and_or.
End Abstract_and_or.

Module Functional_and_or.
  Definition and
    : Prop -> Prop -> Prop
    := fun X Y => forall Z: Prop, (X -> Y -> Z) -> Z.
  
  Definition  and_intro
    : forall X Y, X -> Y -> and X Y
    := fun X Y x y => fun Z f  => f x y.
  
  Definition and_elim
    : forall X Y, and X Y -> forall Z: Prop, (X -> Y -> Z) -> Z
    := fun X Y a => a.

  Definition or
    : Prop -> Prop -> Prop
    := fun X Y => forall Z, (X -> Z) -> (Y -> Z) -> Z.
  
  Definition or_intro_l
    : forall X Y, X -> or X Y
    := fun X Y x => fun Z f g => f x.
 
  Definition or_intro_r
    : forall X Y, Y -> or X Y
    := fun X Y y => fun Z f g => g y.

  Definition or_elim 
    : forall X Y, or X Y -> forall Z:Prop, (X -> Z) -> (Y -> Z) -> Z
    := fun X Y a => a.
End Functional_and_or.

Module Inductive_and_or.
  Inductive and (X Y: Prop) : Prop := 
  | and_intro (x:X) (y:Y).

  Definition and_elim (X Y: Prop) (a: and X Y) (Z: Prop) (f: X -> Y -> Z) : Z :=
    match a with and_intro _ _ x y => f x y end.
  
  Inductive or (X Y: Prop) : Prop :=
  | or_intro_l (x:X)
  | or_intro_r (y:Y).

  Definition or_elim (X Y: Prop) (a: or X Y) (Z: Prop) (f: X -> Z) (g: Y -> Z) : Z :=
    match a with
    | or_intro_l _ _ x => f x
    | or_intro_r _ _ y => g y
    end.

  Inductive False : Prop := .
  Definition False_elim (a: False) (Z: Prop) : Z :=
    match a with end.
End Inductive_and_or.

(** Using Rocq's inductive definitions *)

(* Notations
   - [s \/ t] expands to [or s t]
   - [s /\ t] expands to [and s t]
   - [s <-> t] expands to [(s -> t) /\ (t -> s) ]
 *)

(* Tactics
   - application of introduction constructors:
     [split], [left], [right]
   - application of eliminators:
     [destruct], [intros] with destructuring pattterns, [exfalso]     
 *)

Fact and_char' (X Y: Prop) :
  X /\ Y <-> forall Z: Prop, (X -> Y -> Z) -> Z.
Proof.
  split.
  - intros a Z f. destruct a as [x y]. exact (f x y).
  - intros f. apply f. intros x y.
    split. exact x. exact y.
Qed.
Print and_char'.

Fact and_char (X Y: Prop) :
  X /\ Y <-> forall Z: Prop, (X -> Y -> Z) -> Z.
Proof.
  split.
  - intros [x y] Z f. exact (f x y).
  - intros f. apply f. intros x y.
    split. exact x. exact y.
Qed.

Fact or_char (X Y: Prop) :
  X \/ Y <-> forall Z: Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  split.
  - intros [x|y] Z f g.
    + exact (f x).
    + exact (g y).
  - intros f. apply f.
    + intros x. left. exact x.
    + intros y. right. exact y.
Qed.

Fact False_char :
  False <-> forall Z:Prop, Z.
Proof.
  split.
  - intros [].
  - intros f. apply f.
Qed.
Print False_char.

Fact Russell X :
  ~ (X <-> ~X).
Proof.
  intros [f g].
  assert (h: ~X).
  - exact (fun x => f x x).
  - exact (h (g h)).
Qed.

Goal forall X Y: Prop, X -> ~X -> Y.
  intros X Y x f.
  exfalso. Show Proof.
  exact (f x).
Qed.

(* Typing rules *)

Check nat -> Prop.
Check forall (p: nat -> Prop) (x:nat), p x.

Goal Type.
  exact (nat -> Prop).
Qed.

Goal Prop.
  exact (forall (p: nat -> Prop) (x:nat), p x).
Qed.


(** assert / let as abstract function *)

Lemma Assert (X Z: Prop) :
  X -> (X -> Z) -> Z.
Proof.
  exact (fun x f => f x).
Qed.

Goal forall X: Prop, (X -> ~X) -> ~(~X -> X).
Proof.
  intros X f g.
  apply (Assert (~X)).
  - exact (fun x => f x x).
  - intros h. exact (h (g h)).
Qed.

(** abstract constants *)

Definition a : nat.
  exact 0.
Qed.
 
Definition b : nat.
  exact 0.
Qed.

Print a.
Print b.

Goal a = b.
  Fail reflexivity.
Abort.

Module And_fun_mixed.
  
  Definition and (X Y : Prop) : Prop
    := forall Z, (X -> Y -> Z) -> Z.

  Print and.
 
  Definition and_intro (X Y : Prop) 
    : X -> Y -> and X Y
    := fun x y => fun Z f => f x y.
 
  Definition and_elim (X Y : Prop) 
    : and X Y -> forall Z: Prop, (X -> Y -> Z) -> Z
    := fun a => a.
  
End And_fun_mixed.

(** Excluded Middle *)

Goal (forall X, X \/ ~X) <-> (forall X, ~(~X) -> X).
  split; intros H X.
  - specialize (H X). tauto.
  - apply H. tauto.
Qed.
