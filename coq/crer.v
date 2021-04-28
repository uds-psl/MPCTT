Locate "~".
Print not.
Locate "<->".
Print iff.

Fact Leibniz_symmetry X (x y: X) :
  (forall p: X -> Prop, p x -> p y) -> (forall p: X -> Prop, p y -> p x).
Proof.
  intros f p.
  refine (f _ (fun a => a)).
  Show Proof.
Abort.

Fact Leibniz_symmetry X (x y: X) :
  (forall p: X -> Prop, p x -> p y) -> (forall p: X -> Prop, p y -> p x).
Proof.
  intros f p.
  change ((fun z => p z -> p x) y).
  apply f.
  intros a. exact a.
  Show Proof.
Qed.

Locate "/\".
Print and.

Definition match_and (X Y: Prop) (Z: Type) (a: X /\ Y) (f: X -> Y -> Z) : Z :=
  match a with conj x y => f x y end.

Locate "\/".
Print or.

Definition match_or (X Y: Prop) (Z: Prop) (a: X \/ Y) (f: X -> Z) (g: Y -> Z) : Z :=
  match a with or_introl x => f x | or_intror y => g y end.

Fail
  Definition match_or (X Y: Prop) (Z: Type) (a: X \/ Y) (f: X -> Z) (g: Y -> Z) : Z :=
  match a with or_introl x => f x | or_intror y => g y end.

