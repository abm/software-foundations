Require Export MoreCoq.

Check (3 = 3).
Check (forall n : nat, n = 2).

Lemma silly: 0 * 3 = 0.
Proof. reflexivity. Qed.

Print silly.

Lemma silly_implication: (1 + 1) = 2 -> 0 * 3 = 0.
Proof. intros H. reflexivity. Qed.

Print silly_implication.

Inductive and (P Q : Prop) : Prop :=
  conj: P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example:
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.

Theorem and_example':
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity.
Qed.

Theorem proj1:
  forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.

Theorem proj2:
  forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut:
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
    apply HQ.
    apply HP.
Qed.

Theorem and_assoc:
  forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
    Case "left1".
      split.
      SCase "left2".
        apply HP.
      SCase "right2".
        apply HQ.
    Case "right1".
      apply HR.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                    (at level 95, no associativity)
                    : type_scope.
        
Theorem iff_implies:
  forall P Q : Prop,
    (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
    Case "left". apply HP.
Qed.

Theorem iff_sym:
  forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split.
    Case "left". apply HQ.
    Case "right". apply HP.
Qed.

Theorem iff_refl:
  forall P : Prop,
    P <-> P.
Proof.
  intros P.
  split.
    intros H. apply H.
    intros H. apply H.
Qed.

Theorem iff_trans:
  forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H I.
  inversion H as [HQ HR].
  inversion I as [IQ IR].
  split.
    Case "left".
      intros J.
      apply IQ.
      apply HQ.
      apply J.
    Case "right".
      intros J.
      apply HR.
      apply IR.
      apply J.
Qed.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut:
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  Case "left".
    apply or_intror.
    apply HP.
  Case "right".
    apply or_introl.
    apply HQ.
Qed.

Theorem or_commut':
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
  Case "left".
    right. apply HP.
  Case "right".
    left. apply HQ.
Qed.

Theorem or_distributes_over_and_1:
  forall P Q R : Prop,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion H as [HP | [HQ HR]].
  Case "left".
    split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
  Case "right".
    split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.
Qed.

Theorem or_distributes_over_and_2:
  forall P Q R : Prop,
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R.
  intros H.
  inversion H as [[HP1 | HQ] [HP2 | HR]].
  left. apply HP1.
  left. apply HP1.
  left. apply HP2.
  right.
    split. apply HQ. apply HR.
Qed.

Theorem or_distributes_over_and:
  forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
    apply or_distributes_over_and_1.
    apply or_distributes_over_and_2.
Qed.

Theorem andb_prop:
  forall b c,
    andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    split.
      SCase "left". reflexivity.
      SCase "right". apply H.
  Case "b = false".
    split.
      SCase "left". inversion H.
      SCase "right". inversion H.
Qed.

Theorem andb_true_intro:
  forall b c,
    b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H as [HB HC].
  rewrite HB.
  rewrite HC.
  simpl.
  reflexivity.
Qed.

Theorem andb_false:
  forall b c,
    andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    simpl in H.
    rewrite H.
    right. reflexivity.
  Case "b = false".
    left. reflexivity.
Qed.

Theorem orb_prop:
  forall b c,
    orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    left. reflexivity.
  Case "b = right".
    simpl in H.
    rewrite H.
    right. reflexivity.
Qed.

Theorem orb_false_elim:
  forall b c,
    orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    simpl in H.
    inversion H.
  Case "b = false".
    split.
      reflexivity.
      simpl in H. rewrite H. reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense:
  False -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
Qed.

Theorem nonsense_implies_False:
  2 + 2 = 5 -> False.
Proof.
  intros H.
  inversion H.
Qed.

Theorem ex_falso_quodlibet:
  forall P : Prop,
    False -> P.
Proof.
  intros P H.
  inversion H.
Qed.

Definition True : Prop :=
  forall P : Prop,
    P -> P.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False:
  ~ False.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem contradiction_implies_anything:
  forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  inversion HP.
Qed.

Theorem double_neg:
  forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros I.
  apply I in H.
  inversion H.
Qed.

Theorem contrapositive:
  forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H I.
  unfold not.
  intros J.
  unfold not in I.
  apply H in J.
  apply I in J.
  apply J.
Qed.

Theorem not_both_true_and_false:
  forall P : Prop,
    ~(P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  inversion H as [HP HPF].
  apply HPF in HP.
  apply HP.
Qed.

Print not_both_true_and_false.

Theorem classic_double_neg:
  forall P : Prop,
    ~~P -> P.
Proof.
  intros P H.
  unfold not in H.
Abort.

Definition peirce :=
  forall P Q : Prop, 
  ((P -> Q) -> P) -> P.
Definition classic :=
  forall P : Prop, 
  ~~P -> P.
Definition excluded_middle :=
  forall P : Prop, 
    P \/ ~P.
Definition de_morgan_not_and_not :=
  forall P Q : Prop, 
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or :=
  forall P Q : Prop, 
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_irrefutable:
  forall P : Prop,
    ~~(P \/ ~P).
Proof.
  intros P.
  unfold not.
  apply ex_falso_quodlibet.
Abort.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true:
  forall b : bool,
    b <> false -> b = true.
Proof.
  intros b H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
Qed.

Theorem false_beq_nat:
  forall n m : nat,
    n <> m -> beq_nat n m = false.
Proof.
  intros n m H.
  unfold not in H.
  generalize dependent n.
  induction m as [| m'].
  Case "n = 0".
    intros n H.
    destruct n.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.

      simpl. reflexivity.
  Case "n = S n'".
    intros n H.
    destruct n.
      simpl.
      reflexivity.

      simpl.
      apply IHm'.
      intros I.
      apply H.
      apply eq_S.
      apply I.
Qed.

Theorem beq_nat_false:
  forall n m : nat,
    beq_nat n m = false -> n <> m.
Proof.
  intros n m.
  unfold not.
  intros.
  rewrite H0 in H.
  induction m in H.
    simpl in H.
    inversion H.

    simpl in H.
    apply IHn0 in H.
    inversion H.
Qed.
