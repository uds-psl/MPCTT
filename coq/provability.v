Section Provable.
  Implicit Types X Y Z: Prop.
  Variable provable : Prop -> Prop.
  Definition disprovable X := provable(~X).
  Definition consistent X := ~provable(~X).
  Definition independent X := ~provable X /\ ~provable (~X).

  Variable MP : forall X Y, provable (X -> Y) -> provable X -> provable Y.
  Variable PK : forall X Y, provable (Y -> X -> Y).
  Variable PS : forall X Y Z, provable ((X -> Y -> Z) -> (X -> Y) -> X -> Z).

  Fact LK X Y :
    provable X -> provable (Y -> X).
  Proof.
    intros H. eapply MP. apply PK. exact H.
   Qed.

  Fact LS X Y Z :
    provable (X -> Y -> Z) -> provable (X -> Y) -> provable (X -> Z).
  Proof.
    intros H1 H2. eapply MP. 2:exact H2.
    eapply MP. 2:exact H1. apply PS.
  Qed.

  Fact LI X :
    provable (X -> X).
  Proof.
    apply LS with (X -> X); apply PK.
  Qed.

  Fact LC X Y Z :
    provable (X -> Y) -> provable ((Y -> Z) -> X -> Z).
  Proof.
    intros H.
    eapply LS.
    - eapply LS.
      + apply LK, PS.
      + eapply LS.
        * apply LK, PK.
        * apply LI.
    - apply LK, H.
  Qed.
  
  Fact transport1 X Y :
    provable (X -> Y) -> ~provable Y -> ~provable X.
  Proof.
    intros H H1. contradict H1. revert H H1. apply MP.
  Qed.
 
  Fact transport2 X Y :
    provable (X -> Y) -> consistent X -> consistent Y.
  Proof.
    intros H. apply transport1. apply LC, H.
  Qed.

  Fact transport3 X Y :
    provable (X -> Y) -> provable (Y -> X) ->
    independent X -> independent Y.
  Proof.
    intros H1 H2 [H3 H4]. split.
    - revert H3. apply transport1. exact H2.
    - revert H4. apply transport2. exact H1.
  Qed.
  
  Fact sandwich X Y Z :
    provable (X -> Y) -> provable (Y -> Z) ->
    consistent X -> ~provable Z ->
    independent Y.
  Proof.
    intros H1 H2 H3 H4. split.
    - revert H2 H4. apply transport1.
    - revert H1 H3. apply transport2.
  Qed.

  Fact sandwich' Y :
    independent Y <-> exists X Z,
      provable (X -> Y) /\ provable (Y -> Z) /\
      consistent X /\ ~provable Z.
  Proof.
    split.
    - intros H. exists Y, Y.
      split. apply LI. split. apply LI. split; apply H.
    - intros (X&Z&H1&H2&H3&H4). eapply sandwich; eassumption.
  Qed.

  Fact cons1 :
    ~provable False -> consistent (~False).
  Proof.
    cbv. intros H. contradict H.
    eapply MP. exact H. apply LI.
  Qed.
 
  Fact cons2 X Y :
    consistent X -> ~ provable False.
  Proof.
    cbv. intros H. contradict H. apply LK, H.
  Qed.

  Fact cons3 :
    ~provable False <-> forall X, provable X -> consistent X.
  Proof.
    cbv. split.
    - intros H X H1. contradict H.
      eapply MP. exact H. exact H1.
    - intros H H1.  eapply H. exact H1. apply LI.
  Qed.

  Fact cons4 :
    ~provable False <-> forall P, disprovable P -> ~provable P.
  Proof.
    unfold disprovable. split.
    - intros H1 P H2. contradict H1. apply (MP _ _ H2 H1).
    - intros H. specialize (H False). apply H. apply LI.
  Qed.

End Provable.
