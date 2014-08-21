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
  intros P Q R H.
