From LF Require Export Logic.

Inductive job : Type :=
  taskj (id : nat) (burst_time : nat).

Notation "job( i , b )" := (taskj i b) (at level 60, right associativity).

Inductive process : Type :=
  taskp (id : nat) (start_time : nat) (end_time : nat).

Notation "proc( i , s , e )" := (taskp i s e) (at level 60, right associativity).
  
Inductive joblist : Type :=
  | empty
  | tcons (t : job) (l : joblist).

Notation "t ;; l" := (tcons t l) (at level 60, right associativity).

Definition fetch (j : job) (t : nat) : process :=
  match j with
  | job(id,burst) => proc(id,t,(t+burst))
  end.

Fixpoint fifo (l : joblist) (t : nat) : list process :=
  match l with
  | empty => nil
  | (taskj id burst) ;; l => (fetch (job(id, burst)) t) :: (fifo l (t + burst))
  end.

Definition get_burst (j : job) : nat :=
  match j with
  | job(id,burst_time) => burst_time
  end.

Definition get_processing_time (p : process) : nat :=
  match p with
  | proc(id,start_time,end_time) => end_time - start_time
  end.

Inductive sound : job -> process -> Prop :=
  | sound_procedure : forall j p, (get_burst j) = (get_processing_time p) -> sound j p.

Theorem helper_0 : forall (n : nat), n + 0 - n = 0.
Proof.
  intros. induction n as [ | n' IHn'].
  - simpl. reflexivity.
  - simpl. apply IHn'. 
Qed.

Theorem helper_1 : forall (a b : nat), a + b - a = b.
Proof.
  intros. induction a as [ | a' IHa'].
  - simpl. 
    assert (H: b - 0 = b).
    {
      induction b as [ | b' IHb'].
      + simpl. reflexivity.
      + simpl. reflexivity. 
    }
    apply H.
  - simpl. rewrite IHa'. reflexivity.
Qed.

Theorem fetch_is_sound : forall (j : job) (t : nat), sound j (fetch j t).
Proof.
  intros j t. induction t as [ | t' IHt].
  - simpl. apply sound_procedure. destruct j. induction burst_time as [ | b' IHb'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. apply sound_procedure. destruct j. induction burst_time as [ | b' IHb'].
    + simpl. rewrite helper_0. reflexivity.
    + simpl. rewrite helper_1. reflexivity.
Qed.

(*
Input:
job(1, 3) ;; job(2, 4) ;; job(3, 6);; job(4,9),  0
Output:
[proc (1,0,3); proc(2,3,7), proc(3,7,13), proc(4,13,22)]
*)

Compute job(1, 3) ;; job(2, 4) ;; job(3, 6);; job(4,9);; empty.
Compute fifo (job(1, 3) ;; job(2, 4) ;; job(3, 6);; job(4,9);; empty) 0.