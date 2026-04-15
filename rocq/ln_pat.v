Check forall X:Prop, X -> X.
Check fun X:Prop  => fun x:X=> x.

Check (fun X x => x)
  : forall X:Prop, X -> X.

Check forall X Y Z: Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
Check (fun X Y Z f g x => g (f x)) 
  : forall X Y Z: Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).

Definition F1 (X Y Z : Prop) (f: X -> Y) (g: Y -> Z) (x: X) : Z
  := g (f x).
Print F1.

Fact F2 (X Y Z : Prop) :
  (X -> Y) -> (Y -> Z) -> (X -> Z).
Proof.
  intros f g x. exact (g (f x)).
Qed.
Print F2.

Fact F3 (X Y Z : Prop) :
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  intros f g x. exact (f x (g x)).
Qed.
Print F3.

Fact F3' (X Y Z : Prop) :
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  exact (fun f g x => f x (g x)).
Qed.
Print F3'.

Fact F3'' (X Y Z : Prop) :
  (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  refine (fun f g x => _).
  Show Proof.
  exact (f x (g x)).
Qed.
Print F3''.

(* We can also use the  command [Goal] *)

Goal forall (X Y Z : Prop), (X -> Y -> Z) -> (X -> Y) -> (X -> Z).
Proof.
  intros X Y Z f g x.
  Show Proof.
  exact (f x (g x)).
Qed.
(* We loose the ability to display the final proof term *)

(** Falsity and Negation *)

(* We define falsity and negation and in a module
   to preserve the predefined versions *)  
Module Falsity.
Notation "'False'" := (forall X: Prop, X) : type_scope. (* False prints [False] *)
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
  assert (f': ~X).
  - exact (f (g (fun x => f x x))).
  - exact (f' (g f')).
Qed.
Print N4.

Fact N4' (X: Prop) :
  (X -> ~X) -> (~X -> X) -> False.
Proof.
  intros f g.
  apply f.
  - apply g. intros x. exact (f x x).
  - apply g. intros x. exact (f x x).
Qed.
Print N4'.
End Falsity.
