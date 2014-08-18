Require Export Poly.

Theorem silly1:
  forall (n m o p : nat),
    n = m -> [n;o] = [n;p] -> [m;o] = [m;p].
Proof.
  intros n m o p.
  intros eq1.
  intros eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2:
  forall (n m o p : nat),
    n = m ->
    (forall (q r :nat), q = r -> [q;o] = [r;p]) ->
    [n;o] = [m;p].
Proof.
  intros m n o p.
  intros eq1.
  intros eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a:
  forall n m : nat,
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m.
  intros eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex:
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros eq1.
  intros eq2.
  apply eq1.
  apply eq2.
Qed.

Theorem silly3_firsttry:
  forall (n : nat),
    true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use apply directly *)
Abort.

Theorem silly3_firsttry:
  forall (n : nat),
    true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1:
  forall l l' : list nat,
    l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  intros H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example:
  forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq:
  forall (X : Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intros eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example':
  forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
  intros a b c d e f.
  intros eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise:
  forall (m n o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros m n o p.
  intros eq1 eq2.
  apply trans_eq with (m := (n + p)).
  reflexivity.
  rewrite -> eq2.
  apply eq1.
Qed.

Theorem eq_add_S:
  forall n m : nat,
    S n = S m -> n = m.
Proof.
  intros n m.
  intros eq.
  inversion eq.
  reflexivity.
Qed.

Theorem silly4:
  forall n m : nat,
    [n] = [m] -> n = m.
Proof.
  intros n m.
  intros H.
  inversion H.
  reflexivity.
Qed.

Theorem silly5:
  forall n m o : nat,
    [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o.
  intros H.
  inversion H.
  reflexivity.
Qed.

Theorem sillyex1:
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
  intros X x y z l j.
  intros eq1 eq2.
  inversion eq2.
  reflexivity.
Qed.

Theorem silly6:
  forall n : nat,
    S n = O -> 2 + 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Theorem silly7:
  forall n m : nat,
    false = true -> [n] = [m].
Proof.
  intros n m H.
  inversion H.
Qed.

Example sillyex2:
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
  intros X x y z l j.
  intros eq1 eq2.
  inversion eq1.
Qed.

Theorem f_equal:
  forall (A B : Type) (f : A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
  intros A B f x y.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Theorem beq_nat_0_l:
  forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
  intros n H.
  induction n as [| n'].
  reflexivity.
  inversion H.
Qed.

Theorem beq_nat_0_r:
  forall n,
    beq_nat n 0 = true -> n = 0.
Proof.
  intros n H.
  induction n as [| n'].
  reflexivity.
  inversion H.
Qed.

Theorem S_inj:
  forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b.
  intros H.
  simpl in H.
  apply H.
Qed.

Theorem silly3':
  forall n : nat,
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n.
  intros eq1 eq2.
  symmetry in eq2.
  apply eq1 in eq2.
  symmetry in eq2.
  apply eq2.
Qed.

Theorem plus_n_n_O:
  forall n,
    n + n = 0 -> n = 0.
Proof.
  intros n.
  induction n as [| n'].
  simpl. reflexivity.
  intros H.
  inversion H.
Qed.

Theorem plus_n_n_injective:
  forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n' = O".
    simpl.
    intros m H.
    symmetry in H.
    apply plus_n_n_O in H.
    symmetry.
    apply H.
  Case "n' = S n'".
    intros m.
    destruct m.
      SCase "m = O".
      intros H.
      inversion H.
      SCase "m = S m".
      simpl.
      intros H.
      inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn' in H2.
      rewrite -> H2.
      reflexivity.
Qed.

Theorem double_injective:
  forall n m,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
    simpl.
    intros m H.
    destruct m as [| m'].
    SCase "m = O".
      reflexivity.
    SCase "m = S m'".
      inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [| m'].
      SCase "m = O".
        inversion H.
      SCase "m = S m'".
        apply f_equal.
        apply IHn'.
        inversion H.
        reflexivity.
Qed.

Theorem beq_nat_true:
  forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = O".
    intros m H.
    destruct m as [| m'].
    SCase "m = O".
      reflexivity.
    SCase "m = S m'".
      inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [| m'].
    SCase "m = O".
      inversion H.
    SCase "m = S m'".
      apply f_equal.
      apply IHn'.
      inversion H.
      reflexivity.
Qed.

Theorem double_injective_take2_FAILED:
  forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2:
  forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  Case "m = O".
    intros n H.
    destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion H.
  Case "m = S m'".
    intros n H.
    destruct n as [| n'].
    SCase "n = O". inversion H.
    SCase "n = S n'".
      apply f_equal.
      apply IHm'.
      inversion H.
      reflexivity.
Qed.
    
Theorem length_snoc':
  forall (X : Type) (v : X) (l : list X) (n : nat),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l as [| v' l'].
  Case "l = []".
    intros n H.
    rewrite <- H.
    reflexivity.
  Case "l = v' :: l'".
    intros n H.
    simpl.
    destruct n as [| n'].
    SCase "n = O".
      inversion H.
    SCase "n = S n'".
      apply f_equal.
      apply IHl'.
      inversion H.
      reflexivity.
Qed.

Theorem index_after_last:
  forall (n : nat) (X : Type) (l : list X),
    length l = n -> index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| v' l'].
  Case "l = []".
    intros n H.
    simpl. reflexivity.
  Case "l = v' :: l'".
    intros n H.
    destruct n.
    SCase "n = O".
      inversion H.
    SCase "n = S n".
      simpl.
      apply IHl'.
      inversion H.
      reflexivity.
Qed.

Theorem length_snoc''':
  forall (n : nat) (X : Type) (v : X) (l : list X),
    length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [| v' l'].
  Case "l = []".
    intros n H.
    simpl. 
    destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". 
      inversion H.
  Case "l = v' :: l'".
    intros n H.
    simpl.
    destruct n as [| n'].
    SCase "n = O".
      inversion H.
    SCase "n = S n'".
      apply f_equal.
      apply IHl'.
      inversion H.
      reflexivity.
Qed.

Theorem app_length_cons:
  forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n ->
    S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1 as [| v' l1'].
  Case "l1 = []".
    intros n H.
    destruct n as [| n'].
    SCase "n' = O".
      inversion H.
    SCase "n' = S n'".
      simpl in H.
      simpl.
      apply H.
  Case "l1 = v' :: l1'".
    intros n H.
    destruct n as [| n'].
    SCase "n' = O".
      inversion H.
    SCase "n' = S n'".
      simpl.
      apply f_equal.
      apply IHl1'.
      inversion H.
      reflexivity.
Qed.

Theorem app_length_twice:
  forall (X : Type) (n : nat) (l : list X),
    length l = n -> length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [| v' l'].
  Case "l = []".
    intros n H.
    destruct n as [| n'].
    SCase "n = O".
      simpl. reflexivity.
    SCase "n = S n'".
      inversion H.
  Case "l = v' :: l'".
    intros n H.
    destruct n as [| n'].
    SCase "n = O".
      inversion H.
    SCase "n = S n'".
      simpl in H.
      simpl.
      apply f_equal.