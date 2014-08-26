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
