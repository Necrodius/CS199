From LF Require Export Basics.

Theorem add_0_r_firsttry : forall n:nat, n + 0 = n.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat, n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mul_0_r : forall n:nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem eqb_refl : forall n : nat, (n =? n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity. Qed.

Theorem mult_0_plus' : forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> add_assoc. rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem helper : forall m n : nat, m + (m * n) = m * (1 + n).
Proof.
  intros m n. induction m as [ | m' IHm'].
  - simpl. reflexivity.
  - simpl. 
    assert (h1 : n + m'*n = m'*n + n).
    { rewrite add_comm. reflexivity. }
    rewrite h1. 
    assert (h2 : m' + (m' * n + n) = m' + m' * n + n).
    { rewrite add_assoc. reflexivity. }
    rewrite h2. 
    rewrite -> IHm'. rewrite add_comm.
    assert (h3 : S n = 1 + n).
    { rewrite <- plus_1_l. reflexivity. }
    rewrite h3. reflexivity. Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  intros n m. induction n as [ | n' IHn'].
  - simpl. rewrite <- mult_n_O. reflexivity.
  - simpl. rewrite <- plus_1_l. rewrite -> IHn'. rewrite -> helper.
    reflexivity. Qed.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p h. induction p as [| p' IHp' ]. 
  - simpl. rewrite h. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem leb_refl : forall n:nat, (n <=? n) = true.
Proof.
  intros n. induction n as [ | n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat, 0 =? (S n) = false.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat, (S n) =? 0 = false.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> add_0_r. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [ | p' IHp' ].
  - simpl. rewrite -> mul_0_r. rewrite -> mul_0_r. rewrite -> mul_0_r.
    simpl. reflexivity.
  - rewrite <- plus_1_l. 
    rewrite <- helper. rewrite <- helper. rewrite <- helper.
    rewrite -> IHp'. 
    assert (h1 : m + n * p' = n * p' + m).
    { rewrite add_comm. reflexivity. }
    assert (h2 : m + (n * p' + m * p') = n * p' + (m + m * p')).
    { simpl. rewrite add_assoc. rewrite add_assoc. rewrite h1. reflexivity. }
    assert (h3 : n + m + (n * p' + m * p') = n + (m + (n * p' + m * p'))).
    { simpl. rewrite <- add_assoc. reflexivity. }
    rewrite h3. rewrite h2. rewrite add_assoc. reflexivity. Qed.

Theorem mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [ | n' IHn' ].
  - simpl. reflexivity.
  - rewrite <- plus_1_l. rewrite mult_plus_distr_r. 
    rewrite mult_plus_distr_r. rewrite mult_plus_distr_r. 
    rewrite IHn'. simpl. rewrite mult_plus_distr_r. reflexivity. Qed.









