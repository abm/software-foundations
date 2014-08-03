Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true => andb b2 b3
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Module Playground1.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Definition pred (n:nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.
  
End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Check (S (S (S (S O)))).
Eval compute in (minustwo 4).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.
  Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
      | O => m
      | (S n') => S (plus n' m)
    end.

  Eval compute in (plus (S (S (S O))) (S (S O))).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O , _ => O
      | S _ , O => n
      | S n' , S m' => minus n' m'
    end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Theorem plus_0_n: forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_1 : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  andb (negb (beq_nat n m)) (ble_nat n m).
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n: forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l: forall n : nat, 0 * n = 0.
Proof.
    intros n.
    reflexivity.
Qed.

Theorem plus_id_example :
  forall (n m : nat),
    n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise :
  forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  rewrite -> H.
  intros H'.
  rewrite -> H'.
  reflexivity.
Qed.

Theorem mult_0_plus :
  forall n m : nat,
    (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.
                 
Theorem mult_S_1 :
  forall n m : nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  rewrite -> plus_1_l.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_1_neg_0 :
  forall n : nat,
    beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [ | n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive :
  forall b : bool,
    negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_negb_plus_1 :
  forall n : nat,
    beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [ | n'].
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall x : bool, f x = x) -> (forall b : bool, f (f b) = b).
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall x : bool, f x = negb x) -> (forall b : bool, f (f b) = b).
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
  destruct c.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Inductive bin : Type :=
  | Zero : bin
  | Odd : bin -> bin
  | Even : bin -> bin.

Definition inc_bin (n : bin) : bin :=
  match n with
    | Zero => Odd Zero
    | Odd _ => Even n
    | Even _ => Odd n
  end.

Example inc_bin1: inc_bin Zero = Odd Zero.
Proof. reflexivity. Qed.
Example inc_bin2: inc_bin (inc_bin Zero) = Even (Odd Zero).
Proof. reflexivity. Qed.
Example inc_bin4: inc_bin (inc_bin (inc_bin Zero)) = Odd (Even (Odd Zero)).
Proof. reflexivity. Qed.
Example inc_bin5: inc_bin (Even (Odd Zero)) = Odd (Even (Odd Zero)).
Proof. reflexivity. Qed. 

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
    | Zero => O
    | Odd n' => S (bin_to_nat n')
    | Even n' => S (bin_to_nat n')
  end.

Example bin_to_nat1: bin_to_nat Zero = 0.
Proof. reflexivity. Qed.
Example bin_to_nat2: bin_to_nat (Odd Zero) = 1.
Proof. reflexivity. Qed.
Example bin_to_nat5: bin_to_nat (Odd (Even (Odd (Even (Odd Zero))))) = 5.
Proof. reflexivity. Qed.
