From LF Require Export Induction.

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if eqb h O then
              nonzeros t else
              h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if even h then
              oddmembers t else
              h :: (oddmembers t)
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 , l2 with
  | nil , nil => nil
  | h :: t , nil => l1
  | nil , h :: t => l2
  | h :: t , h' :: t' => h :: h' :: (alternate t t')
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | h :: t => if eqb h v then S (count v t)
              else (count v t)
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.

Definition sum (b1 b2 : bag) : bag :=
  b1 ++ b2.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  [v] ++ s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | h :: t => if eqb h v then true
              else (member v t)
  end.

Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if eqb v h then t
              else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if eqb v h then (remove_all v t)
              else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. simpl. reflexivity. Qed.


Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => if ltb (length (remove_one h s2)) (length s2) then
              (included t (remove_one h s2))
              else false
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
  Proof. simpl. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
  Proof. simpl. reflexivity. Qed.

Lemma helper : forall v : nat, v =? v = true.
Proof.
  intros v. induction v as [ | v' IHv'' ].
  - simpl. reflexivity.
  - simpl. rewrite IHv''. reflexivity.
Qed.

Theorem add_inc_count : forall (v : nat) (s : bag), (count v (add v s)) = S (count v s). 
Proof.
  intros v s. induction v as [ | v' IHv' ].
  - simpl. reflexivity.
  - simpl. rewrite helper. reflexivity. Qed.

Theorem nil_app : forall l : 
  natlist,[ ] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [ | n l' IHl' ].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl'. rewrite app_assoc. reflexivity. Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite IHl'. 
    reflexivity. Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite app_assoc. rewrite app_assoc.
  reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. destruct n. 
    + simpl. reflexivity.
    + simpl. reflexivity. Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 , l2 with
  | nil , nil => true
  | h :: _ , nil => false
  | nil , h :: _ => false
  | h1 :: t1 , h2 :: t2 =>  if eqb h1 h2 then eqblist t1 t2
                            else false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
  Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.


Theorem eqblist_refl : forall l:natlist, true = eqblist l l.
Proof.
  intros l. induction l as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. rewrite IHl'.
    assert (h1 : n =? n = true).
    { 
      induction n as [ | n' IHn' ].
      - simpl. reflexivity.
      - simpl. rewrite IHn'. reflexivity.
    }
    rewrite h1. reflexivity. Qed.
      
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. simpl. reflexivity. Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count : forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [ | n s' IHs' ].
  - simpl. reflexivity.
  - simpl. destruct n. 
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite IHs'. reflexivity. Qed.

Theorem bag_count_sum : forall (l1 l2 : bag) (v : nat) , 
  count v (sum l1 l2) = count v l1 + count v l2.
Proof.
  intros l1 l2 v. induction l1 as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. destruct (n =? v).
    + simpl. rewrite IHl'. reflexivity.
    + simpl. rewrite IHl'. reflexivity. Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f h1 n1 n2 h2.
  assert ( h3 : f (f n1) = n1 ).
  { rewrite h1. reflexivity. }
  assert ( h4 : f (f n2) = n2 ).
  { rewrite h1. reflexivity. }
  rewrite <- h3. rewrite <- h4. 
  rewrite h2. reflexivity. Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 h.
  assert ( h1 : rev (rev l1) = l1 ).
  { rewrite <- rev_involutive. reflexivity. }
  assert ( h2 : rev (rev l2) = l2 ).
  { rewrite <- rev_involutive. reflexivity. }
  rewrite <- h1. rewrite <- h2. rewrite h. reflexivity. Qed.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [ | n l' IHl' ].
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  destruct x. simpl. induction n as [ | n' IHn' ].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. simpl. rewrite eqb_id_refl. reflexivity. Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o h. simpl. rewrite h. reflexivity. Qed.






