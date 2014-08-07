Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2 :
  forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
  reflexivity.
  Case "c = false".
  rewrite <- H.
  destruct b.
  SCase "b = true".
  reflexivity.
  SCase "b = false".
  reflexivity.
Qed.

Theorem plus_O_r_firsttry:
  forall n : nat,
    n + O = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_O_r_secondtry:
  forall n : nat,
    n + O = n.
Proof.
  intros n.
  destruct n as [| n'].
  Case "n = O".
  reflexivity.
  Case "n = S n'".
  simpl.
Abort.

Theorem plus_O_r:
  forall n : nat,
    n + O = n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem minus_diag:
  forall n : nat,
    minus n n = O.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_O_r:
  forall n : nat,
    n * O = O.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm:
  forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = O".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_comm:
  forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = O".
  simpl.
  rewrite -> plus_O_r.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Theorem plus_assoc:
  forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  Case "n = O".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus:
  forall n,
    double n = n + n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
  simpl.
  reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Theorem mult_O_plus':
  forall n m : nat,
    (O + n) * m = n * m.
Proof.
  intros n m.
  assert (H: O + n = n).
  Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry:
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange_secondtry:
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_swap:
  forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_elim:
  forall m n : nat,
    n + n * m = n * S m.
Proof.
  intros m n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> plus_swap.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_comm:
  forall m n : nat,
    m * n = n * m.
Proof.
  intros m n.
  induction m as [| m'].
  Case "m = O".
    simpl.
    rewrite -> mult_O_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_elim.
    reflexivity.
Qed.

Theorem evenb_n__oddb_Sn:
  forall n : nat,
    evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
    simpl. reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    destruct n'.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem ble_nat_refl:
  forall n : nat,
    true = ble_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
  simpl. reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem zero_nbeq_S:
  forall n : nat,
    beq_nat O (S n) = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.

Theorem andb_false_r:
  forall b : bool,
    andb b false = false.
Proof.
  intros b.
  destruct b.
  Case "b = true".
  simpl. reflexivity.
  Case "b = false".
  simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l:
  forall n m p : nat,
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p'].
  Case "p = O".
  simpl.
  rewrite -> H.
  reflexivity.
  Case "p = S p'".
  simpl.
  rewrite -> IHp'.
  reflexivity.
Qed.

Theorem S_nbeq_O:
  forall n : nat,
    beq_nat (S n) O = false.
Proof.
  intros n.
  simpl. reflexivity.
Qed.

Theorem mult_1_l:
  forall n : nat,
    1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plus_O_r.
  reflexivity.
Qed.

Theorem all3_spec:
  forall b c : bool,
    orb
      (andb b c)
      (orb
         (negb b)
         (negb c))
      = true.
Proof.
  intros b c.
  destruct b as [| b].
  Case "b = true".
  simpl.
  destruct c as [| c].
  simpl. reflexivity.
  simpl. reflexivity.
  Case "b = false".
  simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p'].
  Case "p = O".
  rewrite -> mult_O_r.
  rewrite -> mult_O_r.
  simpl.
  rewrite -> mult_O_r.
  reflexivity.
  Case "p = S p'".
  rewrite <- plus_elim.
  rewrite -> IHp'.
  assert (H: n * S p' = n + n * p').
  rewrite <- plus_elim. reflexivity.
  rewrite -> H.
  assert (H': m * S p' = m + m * p').
  rewrite <- plus_elim. reflexivity.
  rewrite -> H'.
Abort.
