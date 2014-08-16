Require Export Lists.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length X t)
  end.

Example test_length1: length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2: length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : (list X) :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X : Type) (l : list X) : (list X) :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1: rev nat (cons nat 1 (cons nat 2 (nil nat))) =
                   (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.
Example test_rev2: rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.

  Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble.
  Inductive grumble (X : Type) :=
    | d : mumble -> grumble X
    | e : X -> grumble X.

  Inductive baz : Type :=
    | x : baz -> baz
    | y : baz -> bool -> baz.

End MumbleBaz.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

Fixpoint length' (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length' _ t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X : Type} (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length'' t)
  end.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1;2;3].
Check ([3 + 4] ++ nil).

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | O => []
    | S n' => n :: repeat n n'
  end.

Example test_repeat1: repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem rev_snoc:
  forall X : Type, forall v : X, forall s : list X,
    rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s as [| n s'].
  Case "s = nil".
  simpl. reflexivity.
  Case "s = cons".
  simpl.
  rewrite -> IHs'.
  simpl.
  reflexivity.
Qed.

Theorem rev_involutive:
  forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| n l'].
  Case "l = nil".
  simpl. reflexivity.
  Case "l = cons".
  simpl.
  rewrite -> rev_snoc.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem snoc_with_append:
  forall X : Type, forall l1 l2 : list X, forall v : X,
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1 as [| n l1'].
  Case "l1 = nil".
  simpl.  reflexivity.
  Case "l1 = cons".
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Check @combine.

Eval compute in (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : list (X) * list (Y) :=
  match l with
    | [] => ([], [])
    | (x,y) :: t => (x :: fst (split t), y :: snd (split t))
  end.
Example test_split:
  split [(1, false);(2, false)] = ([1;2], [false;false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
  | None : option X
  | Some : X -> option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1: index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2: index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3: index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | nil => None
    | x :: t => Some x
  end.

Check hd_opt.
Check @hd_opt.

Example test_hd_opt1: hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2: hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f: X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'': doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f: X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f: X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry:
  forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.
