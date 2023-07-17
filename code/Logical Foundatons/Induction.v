From LF Require Export Basics.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  (* n = O *)
  - reflexivity.
  (* n = S n' *)
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n : nat,
  minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  (* n = O *)
  - reflexivity.
  (* n = S n' *)
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Exercise: basic induction (2 stars) *)
Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite -> add_0_r. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. 
Qed.
(* Exercise Ends. *)

Fixpoint double (n : nat) :=
  match n with
  | O => O 
  | S n' => S (S (double n'))
  end.

(* Exercise: double_plus (2 stars) *)
Lemma double_plus : forall n,
  double n = n + n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. 
    rewrite <- plus_n_Sm. 
    rewrite -> IHn'.
    reflexivity.
Qed.
(* Exercise Ends. *)

(* Exercise: eqb_refl (2 stars) *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.
(* Exercise Ends. *)

(* Exercise: even_S (2 star) *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. simpl.
    rewrite -> negb_involutive.
    reflexivity.
Qed.
(* Exercise Ends. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { rewrite add_comm. simpl. 
    rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* More Exercises *)
(* Exercise: mul_comm (3 stars) *)
Theorem add_shuffle3 : forall n m p,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H.
  rewrite add_assoc.
  reflexivity.
Qed.

Theorem mult_n_Sm : forall n m,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'.
    rewrite add_shuffle3.
    reflexivity.
Qed.


Theorem mul_comm : forall n m : nat,
  m * n = n * m.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite mul_0_r. reflexivity.
  - simpl. rewrite mult_n_Sm. 
    rewrite IHn'. reflexivity.  
Qed.
(* Exercise Ends. *)

(* Exercise: plus_leb_compat_l (2 stars) *)
Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  induction p as [|p' IHp'].
  - simpl. intros H. rewrite H. reflexivity.
  - intros H. simpl. 
    rewrite IHp'.
    + reflexivity.
    + rewrite H. reflexivity.
Qed. 
(* Exercise Ends. *)

(* Exercise: more exercises (3 stars) *)
Theorem leb_refl : forall n : nat,
  (n <=? n) = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem zero_neqb_S: forall n : nat,
  0 =? (S n) = false.
Proof.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite add_0_r.
  reflexivity.
Qed.
  
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction p as [|p' IHp'].
  - rewrite mul_0_r.
    rewrite mul_0_r.
    rewrite mul_0_r.
    reflexivity.
  - rewrite mult_n_Sm.
    rewrite mult_n_Sm.
    rewrite mult_n_Sm.
    rewrite IHp'.
    assert (H:m + (n * p' + m * p') = n * p' + (m + m * p')).
    { rewrite add_shuffle3. reflexivity. }
    rewrite <- add_assoc.
    rewrite H. 
    rewrite -> add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite mult_plus_distr_r.
    rewrite IHn'. reflexivity.
Qed.  
(* Exercises End. *)

(* Exercise: add_shuffle3' (2 stars) *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite add_comm. reflexivity.
Qed.
(* Exercise Ends. *)

(* Exercise: bin_to_nat_pres_incr (3 stars) *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b. induction b as [|b' IHb'|b' IHb'].
  - reflexivity.
  - reflexivity.
  - simpl. 
    rewrite <- plus_n_O.
    rewrite <- plus_n_O.
    rewrite IHb'. simpl.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.
(* Exercise Ends. *)

(* Exercise: nat_bin_nat (3 stars) *)
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z 
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : forall n,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr.
    rewrite IHn'. reflexivity.
Qed.

(* Exercise Ends. *)

(* Exercise: double_bin (2 stars) *)
Lemma double_incr : forall n : nat,
  double (S n) = S (S (double n)).
Proof.
  intros n. reflexivity. 
Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z 
  | _ => B0 b
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity. Qed.

Lemma double_incr_bin : forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. destruct b as [|b' |b'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* Exercise Ends. *)

(* Exercise: bin_nat_bin (4 stars) *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z 
  | B0 b' => match (normalize b') with
             | Z => Z 
             | nb' => B0 nb' 
             end
  | B1 b' => B1 (normalize b')
  end. 

Lemma nat_to_bin_double : forall n : nat,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite double_incr_bin.
    rewrite IHn'. reflexivity.
Qed.

Theorem bin_nat_bin : forall b, 
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b. induction b as [|b' IHb'|b' IHb'].
  - reflexivity.
  - simpl. rewrite <- IHb'.
    destruct (bin_to_nat b') as [|n'].
    + reflexivity.
    + rewrite <- plus_n_O.
      rewrite <- double_plus.
      rewrite nat_to_bin_double.
      simpl. destruct (nat_to_bin n').
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
  - simpl. rewrite <- IHb'.
    destruct (bin_to_nat b') as [|n'].
    + reflexivity.
    + rewrite <- plus_n_O.
      rewrite <- double_plus.
      rewrite nat_to_bin_double.
      simpl. destruct (nat_to_bin n').
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
Qed.
(* Exercise Ends. *)