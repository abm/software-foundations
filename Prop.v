Require Export Logic.

Definition even (n:nat) : Prop :=
  evenb n = true.

Print even.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem double_even:
  forall n : nat,
    ev (double n).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    simpl. apply ev_0.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

Theorem ev__even:
  forall n,
    ev n -> even n.
Proof.
  intros n H.
  induction H as [| n' H'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' H'".
    unfold even.
    apply IHH'.
Qed.

Theorem l:
  forall n,
    ev n.
Proof.
  intros n.
  induction n.
  Case "0".
    simpl. apply ev_0.
  Case "S n".
    simpl.
Abort.

Theorem ev_sum:
  forall n m,
    ev n -> ev m -> ev (n+m).
Proof.
  intros n m H.
  induction H as [| n' H'].
  Case "ev_0".
    intros H.
    simpl. apply H.
  Case "ev_SS n' H'".
    intros H.
    simpl.
    apply ev_SS.
    apply IHH'.
    apply H.
Qed.

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
  apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  apply b_sum with (n:=3) (m:=5).
  apply b_3.
  apply b_5.
Qed.

Theorem beautiful_plus_eight:
  forall n,
    beautiful n -> beautiful (8+n).
Proof.
  intros n H.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply H.
Qed.

Theorem beautiful_plus_zero:
  forall n,
    beautiful n -> beautiful (n + 0).
Proof.
  intros n H.
  apply b_sum with (n:=n) (m:=0).
  apply H.
  apply b_0.
Qed.

Theorem b_times2:
  forall n,
    beautiful n -> beautiful (2 * n).
Proof.
  intros n H.
  simpl.
  apply b_sum with (n:=n) (m:=n+0).
  apply H.
  apply beautiful_plus_zero.
  apply H.
Qed.

Theorem beautiful_times_zero:
  forall n,
    beautiful 0 -> beautiful (n * 0).
Proof.
  intros n H.
  induction n as [| n].
    simpl.
    apply b_0.

    simpl.
    apply IHn.
Qed.

Theorem b_timesm:
  forall n m,
    beautiful n -> beautiful (m * n).
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [| m'].
  Case "m = 0".
    intros n H.
    simpl.
    apply b_0.
  Case "m = S m'".
    intros n H.
    simpl.

    apply b_sum with (n:=n) (m:=m' * n).
      apply H.

      apply IHm'. apply H.
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_plus13:
  forall n,
    gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    apply g_plus5 with (n:=8).
    apply g_plus5 with (n:=3).
    apply g_plus3 with (n:=0).
    apply H.
  Case "n = S n'".
    apply g_plus5 with (n:=8 + S n').
    apply g_plus5 with (n:=3 + S n').
    apply g_plus3 with (n:=S n').
    apply H.
Qed.
