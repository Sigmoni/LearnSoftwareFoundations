Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n 
  else (3 * n) + 1.

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1 
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Conjecture collatz : forall n, reaches_1 n.

Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n 
  | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) : 
      R x y -> 
      clos_trans R x y 
  | t_trans (x y z : X) : 
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b] 
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.
(* Exercise ends *)

Theorem ev_inversion : forall (n : nat),
  ev n -> 
  (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [|n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split.
    + reflexivity.
    + apply E'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H. destruct H as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [|n' E' Heq].
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H. destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H.
Qed.

(* Exercise: 1 star, standard (inversion_practice) *)
Theorem SSSSev_even : forall n, 
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [ | n' E' Heq].
  inversion E' as [ | n'' E'' Heq''].
  apply E''.
Qed.
(* Exercise ends *)

(* Exercise: 1 star, standard (ev5_nonsense) *)
Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H as [ | n' E' eq1].
  inversion E' as [ | n'' E'' eq2].
  inversion E''.
Qed.
(* Exercise ends *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H. inversion H.
Qed.

Lemma ev_Even : forall n, 
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH. 
    destruct IH as [k Hk].
    rewrite Hk. 
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even. intros [k Hk].
    rewrite Hk. apply ev_double.
Qed.

(* Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [|n' E' H].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply H.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced, optional (ev'_ev) *)
Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0 
  | ev'_2 : ev' 2 
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply (ev_sum n m IHev'1 IHev'2).
  - intros H. induction H.
    + apply ev'_0.
    + assert (HFoo: S (S n) = 2 + n).
      { simpl. reflexivity. }
      rewrite HFoo. 
      apply (ev'_sum 2 n ev'_2 IHev).
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn.
  induction Hn.
  - simpl in Hnm. apply Hnm.
  - apply IHHn. simpl in Hnm. 
    inversion Hnm. apply H0.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (ev_plus_plus) *)
Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  assert (H1 : forall x, ev (x + x + m + p) -> ev (m + p)).
  { intros H. induction H as [|x' E'].
    - simpl. intros H'. apply H'.
    - simpl. rewrite (add_comm x' (S x')). simpl.
      intros H'. apply E'. 
      inversion H'. apply H0. }
  apply (H1 n).
  assert (H2 : n + n + m + p = (n + m) + (n + p)).
  { rewrite <- (add_assoc n n m).
    rewrite (add_comm n (n + m)).
    rewrite <- add_assoc.
    reflexivity. }
  rewrite H2.
  apply ev_sum.
  - apply Hnm.
  - apply Hnp.
Qed.
(* Exercise ends *)

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n 
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

Theorem test_le1 : 
  3 <= 3.
Proof.
  apply le_n. 
Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S.
  apply le_n.
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H.
  inversion H2.
Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "n < m" := (lt n m).

End Playground.

(* Exercise: 2 stars, standard, optional (total_relation) *)
Inductive total_relation : nat -> nat -> Prop :=
  | ge0_n (n : nat) : total_relation n n 
  | ge0_n_plus_m (n m : nat) (Hn : total_relation n n) (Hm : total_relation m m) : total_relation n m.

Theorem total_relation_is_total : forall n m, total_relation n m.
Proof.
  intros n m. apply ge0_n_plus_m.
  - apply (ge0_n n).
  - apply (ge0_n m).
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (empty_relation) *)
Inductive empty_relation : nat -> nat -> Prop :=
  | lt0_n_plus_m (n m : nat) (Hn : n < 0) (Hm : m < 0) : empty_relation n m.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof.
  intros n m H. inversion H.
  inversion Hn.
Qed.
(* Exercise ends *)

(* Exercise: 5 stars, standard, optional (le_and_lt_facts) *)
Lemma le_prop1 : forall x y, S x <= y -> x <= y.
Proof.
  intros x y H. induction H.
  - apply le_S. apply le_n.
  - apply le_S in IHle. apply IHle.
Qed.

Lemma le_prop2 : forall x y, S x <= S y -> x <= y.
Proof.
  intros x y H. inversion H.
  - apply le_n.
  - apply le_prop1. apply H1.
Qed.

Lemma le_trans : forall n m o, m <= n -> n <= o -> m <= o.
Proof.
  intros n m o Hmn Hno.
  induction Hmn.
  - apply Hno.
  - apply IHHmn. apply le_prop1. apply Hno.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm.
  - apply le_n.
  - apply le_S. apply IHHnm. 
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  apply le_prop2.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n. induction n.
  - intros m. induction m. 
    + right. apply le_n.
    + destruct IHm as [H | H].
      { left. unfold lt in H.
        unfold lt. apply le_S. apply H. }
      { left. inversion H. unfold lt. apply le_n. }
  - intros m. destruct m.
    + right. apply O_le_n.
    + destruct (IHn m) as [H | H].
      { left. apply n_le_m__Sn_le_Sm. apply H. }
      { right. apply n_le_m__Sn_le_Sm. apply H. }
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a. induction a.
  - induction b.
    + simpl. apply le_n.
    + simpl in IHb. simpl. 
      apply le_S. apply IHb.
  - destruct b.
    + rewrite add_comm. simpl. apply le_n.
    + simpl. apply n_le_m__Sn_le_Sm.
      apply (IHa (S b)).
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H. split.
  - apply le_trans with (n := n1 + n2).
    + apply le_plus_l.
    + apply H.
  - apply le_trans with (n := n1 + n2).
    + rewrite add_comm. apply le_plus_l.
    + apply H.
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  induction n.
  - simpl. intros m p q H.
    left. apply O_le_n.
  - simpl. destruct m.
    + intros p q H. right.
      apply O_le_n.
    + destruct p.
      { simpl. intros q H. right.
        apply le_prop1 in H. 
        apply le_trans with (n := n + S m).
        - rewrite add_comm. apply le_plus_l.
        - apply H. }
      { destruct q.
        - intros H. rewrite (add_comm (S p) 0) in H.
          simpl in H. apply Sn_le_Sm__n_le_m in H.
          left. apply n_le_m__Sn_le_Sm. 
          apply le_trans with (n := n + S m).
          + apply le_plus_l.
          + apply H.
        - intros H. simpl in H.
          rewrite (add_comm n (S m)) in H.
          rewrite (add_comm p (S q)) in H.
          simpl in H. 
          apply Sn_le_Sm__n_le_m in H.
          apply Sn_le_Sm__n_le_m in H.
          destruct (IHn m p q) as [H' | H'].
          + rewrite (add_comm n m).
            rewrite (add_comm p q).
            apply H.
          + left. apply n_le_m__Sn_le_Sm. apply H'.
          + right. apply n_le_m__Sn_le_Sm. apply H'. }
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m -> p + n <= p + m.
Proof.
  intros n m p H. induction p.
  - simpl. apply H.
  - simpl. apply n_le_m__Sn_le_Sm.
    apply IHp.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  intros n m p.
  rewrite (add_comm n p).
  rewrite (add_comm m p).
  apply plus_le_compat_l.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m -> n <= m + p.
Proof.
  intros n m p H.
  apply le_trans with (n := m).
  - apply H.
  - apply le_plus_l.
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m -> n <= m.
Proof.
  intros n m. apply le_prop1.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H. unfold lt in H. split.
  - rewrite <- plus_Sn_m in H.
    apply plus_le in H. 
    apply H.
  - rewrite plus_n_Sm in H.
    apply plus_le in H.
    apply H.
Qed.
(* Exercises fucking end *)