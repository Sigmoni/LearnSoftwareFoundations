From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. 
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. 
Qed.

(* Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p H1 H2 H3.
  apply H2.
  apply H1.
  apply H3.
Qed.
(* Exercise ends *)

Theorem silly3 : forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m H.
  (* Fail apply H. *)
  symmetry. apply H.
Qed.

(* Exercise: 2 stars, standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. 
  rewrite -> eq2. 
  reflexivity. 
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m p eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),  
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1.
  apply eq2.
Qed.

(* Exercise: 3 stars, standard, optional (trans_eq_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m.
  apply eq2. apply eq1.
Qed.
(* Exercisse ends *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)).
  { reflexivity. }
  rewrite H2. rewrite H1. simpl.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* Exercise: 3 stars, standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  injection eq1 as H1 H2.
  assert(eq3: y::l = z::l).
  { transitivity j.
    apply H2.
    apply eq2. }
  injection eq3 as H3.
  rewrite H1. rewrite H3.
  reflexivity.
Qed.
(* Exercise ends *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. 
Qed.

(* Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 : 
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.
(* Exercise ends *)

Theorem eqb_0_l : forall n,
  0 =? n = true ->
  n = 0.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.
  
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.
  apply H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m H. destruct m as [|m'].
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [|m'].
    + discriminate H.
    + f_equal. apply IHn'.
      simpl in H. injection H as H'.
      apply H'.
Qed.

(* Exercise: 2 stars, standard (eqb_true) *)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m H. destruct m as [|m'].
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [|m'].
    + discriminate.
    + f_equal. simpl in H.
      apply IHn'. apply H. 
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, especially useful (plus_n_n_injective) *)
Theorem f: .
Proof.
  
Qed.