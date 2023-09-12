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
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m H. simpl in H.
    destruct m as [|m'].
    + reflexivity.
    + discriminate.
  - intros m H. destruct m as [|m'].
    + discriminate.
    + simpl in H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H.
      apply eq_implies_succ_equal.
      apply IHn'. apply H.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, especially useful (gen_dep_practice) *)
Theorem nth_error_after_last : 
  forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [|h l' IHl'].
  - intros n H. destruct n as [|n'].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros n H. destruct n as [|n'].
    + discriminate H.
    + simpl in H. injection H as H.
      simpl. apply IHl'. apply H. 
Qed.
(* Exercise ends *)

Definition square n := n * n.

Lemma square_mult : forall n m, 
  square (n * m) = square n * square m.
Proof.
  intros n m. unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc.
  reflexivity.
Qed.

(* Exercise: 3 stars, standard (combine_split) *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([],  [])
  | (x, y) :: t => 
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h l' IHl'].
  - intros l1 l2 H. simpl in H.
    injection H as eq1 eq2.
    rewrite <- eq1. rewrite <- eq2.
    reflexivity.
  - intros l1 l2 H. destruct h. 
    simpl in H. destruct (split l') as [lx ly] eqn:E.
    injection H as Ex Ey. rewrite <- Ex. rewrite <- Ey.
    simpl. assert (H: combine lx ly = l').
    { apply IHl'. reflexivity. }
    rewrite H. reflexivity.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn:Eb.
  - destruct (f true) eqn:Eft.
    + rewrite Eft. apply Eft.
    + destruct (f false) eqn:Eff.
      { apply Eft. }
      { apply Eff. }
  - destruct (f false) eqn:Eff.
    + destruct (f true) eqn:Eft.
      { apply Eft. }
      { apply Eff. }
    + rewrite Eff. apply Eff.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard (eqb_sym) *)
Theorem eqb_sym : forall n m,
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m. destruct m as [|m'].
    + reflexivity.
    + reflexivity.
  - intros m. destruct m as [|m'].
    + reflexivity.
    + simpl. apply IHn'.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (eqb_trans) *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H1 H2.
  assert (Eq1: n = m).
  { apply eqb_true. apply H1. }
  assert (Eq2: m = p).
  { apply eqb_true. apply H2. }
  assert (Eq3: n = p).
  { rewrite Eq1. apply Eq2. }
  rewrite Eq3. apply eqb_refl.  
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, advanced (split_combine) *)
Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) (lx : list X) (ly : list Y),
  length lx = length ly -> 
  combine lx ly = l ->
  split l = (lx, ly).

Theorem split_combine: split_combine_statement.
Proof.
  intros X Y l. induction l as [|h l' IHl'].
  - intros lx ly H1 H2. destruct lx as [|x lx'].
    + destruct ly as [|y ly'].
      { reflexivity. }
      { simpl in H1. discriminate H1. }
    + destruct ly as [|y ly'].
      { simpl in H1. discriminate H1. }
      { simpl in H2. discriminate H2. }
  - intros lx ly H1 H2. destruct lx as [|x lx'].
    + simpl in H2. discriminate H2.
    + destruct ly as [|y ly'].
      { simpl in H2. discriminate H2. }
      { simpl in H2. injection H2 as Eqh Eql'.
        simpl in H1. injection H1 as Eqlen.
        assert (Eq: split l' = (lx', ly')).
        { apply IHl'. apply Eqlen. apply Eql'. }
        rewrite <- Eqh. simpl. rewrite Eq. reflexivity. } 
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, advanced (filter_exercise) *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l. induction l as [|h l' IHl'].
  - intros lf H. simpl in H. discriminate H.
  - intros lf H. simpl in H. destruct (test h) eqn:Eth.
    + injection H as eq1 eq2.
      rewrite <- eq1. apply Eth.
    + apply IHl' with (lf := lf).
      apply H. 
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced, especially useful (forall_exists_challenge) *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if (test h)
              then forallb test t
              else false
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
  

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => if (test h)
              then true
              else existsb test t 
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Example test_existsb'_1 : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb'_2 : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb'_3 : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb'_4 : existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb'_existsb : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l. induction l as [|h l' IHl'].
  - reflexivity.
  - unfold existsb'. simpl. destruct (test h) eqn:E.
    + reflexivity.
    + simpl. rewrite IHl'. unfold existsb'. reflexivity.
Qed.
(* Exercise ends *)