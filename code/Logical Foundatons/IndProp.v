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

(* Exercise: 4 stars, standard, optional (more_le_exercises) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m. generalize dependent n. 
  induction m as [|m' IHm'].
  - intros n H. destruct n as [|n'].
    + apply le_n.
    + simpl in H. discriminate H.
  - intros n H. destruct n as [|n'].
    + apply O_le_n.
    + simpl in H. 
      apply n_le_m__Sn_le_Sm.
      apply IHm'. apply H.
Qed.

Lemma leb_ind : forall n m,
  n <=? m = true -> n <=? (S m) = true.
Proof.
  intros n m H. generalize dependent n. 
  induction m as [|m' IHm'].
  - intros n H. destruct n as [|n'].
    + reflexivity.
    + discriminate H.
  - intros n H. destruct n as [|n'].
    + reflexivity.
    + simpl. simpl in H. 
      apply IHm'. apply H.
Qed.

Lemma leb_inv_l : forall n m,
  S n <=? m = true -> n <=? m = true.
Proof.
  intros n m H. destruct m as [|m'].
  - discriminate H.
  - simpl in H. apply leb_ind. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> n <=? m = true.
Proof.
  intros n m H. induction H.
  - apply leb_refl.
  - destruct n as [|n'].
    + reflexivity.
    + simpl. apply leb_inv_l. apply IHle.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2.
  apply leb_iff in H1.
  apply leb_iff in H2.
  apply leb_iff.
  apply le_trans with (n := m).
  - apply H1.
  - apply H2.
Qed.
(* Exercise ends *)

Module R.

(* Exercise: 3 stars, standard, especially useful (R_provability) *)
Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o ) : R n m o. 
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (R_fact) *)
Definition fR : nat -> nat -> nat := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR. split.
  - intros H. induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. f_equal. apply IHR.
    + simpl in IHR. rewrite <- plus_n_Sm in IHR. 
      injection IHR as IHR. apply IHR. 
    + rewrite add_comm. apply IHR. 
  - intros H. rewrite <- H.
    assert (H' : forall m n, R m n (m + n)).
    { intros x y. induction x.
      - simpl. induction y.
        + apply c1.
        + apply c3. apply IHy.
      - simpl. apply c2. apply IHx. }
    apply H'.
Qed.

End R.
(* Exercise ends *)

(* Exercise: 3 stars, advanced (subsequence) *)
Inductive subseq : list nat -> list nat -> Prop :=
  | sub0 (l1 l2 : list nat) (H : l1 = []) : subseq l1 l2
  | sub1 (l1 l2 : list nat) (n : nat) (H : subseq l1 l2) : subseq l1 (n::l2)
  | sub2 (l1 l2 : list nat) (n m : nat) (H : subseq l1 l2) (E : n = m) : subseq (n :: l1) (m :: l2).

Theorem subseq_refl : forall l : list nat, 
  subseq l l.
Proof.
  intros l. induction l.
  - apply sub0. reflexivity.
  - apply sub2.
    + apply IHl.
    + reflexivity.
Qed.

Theorem subseq_app : forall l1 l2 l3 : list nat,
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H.
  - rewrite H. apply sub0. reflexivity.
  - simpl. apply sub1. apply IHsubseq.
  - simpl. apply sub2.
    + apply IHsubseq.
    + apply E.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 -> 
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. generalize dependent l1.
  induction H2.
  - intros l0 H'.
    rewrite H in H'. inversion H'.
    rewrite H0. apply sub0. reflexivity.
  - intros l0 H'. apply sub1.
    apply IHsubseq. apply H'.
  - assert (Hlem : forall l x, (subseq l l1 -> subseq l l2) -> (subseq l (x :: l1) -> subseq l (x :: l2))).
    { intros l x Ha Hb. destruct l.
      - apply sub0. reflexivity.
      - inversion Hb.
        + discriminate H.
        + apply sub1. apply Ha. apply H1.
        + apply sub2. 
          { apply IHsubseq. apply H0. }
          { apply E0. } }
    intros l. rewrite E. apply Hlem.
    apply IHsubseq.
Qed.
(* Exercise ends *)

Module bin1.

Inductive bin : Type :=
  | Z 
  | B0 (n : bin)
  | B1 (n : bin).

End bin1.

Module bin2.

Inductive bin : Type :=
  | Z : bin 
  | B0 (n : bin) : bin 
  | B1 (n : bin) : bin.

End bin2.

Module bin3.

Inductive bin : Type :=
  | Z : bin 
  | B0 : bin -> bin 
  | B1 : bin -> bin.

End bin3.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet 
  | EmptyStr 
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2 
         (H1 : s1 =~ re1) 
         (H2 : s2 =~ re2) 
    : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2 
            (H1 : s1 =~ re1) 
    : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2 
            (H2 : s2 =~ re2) 
    : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re 
             (H1 : s1 =~ re)
             (H2 : s2 =~ (Star re))
    : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar. 
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  apply (MApp [1]). apply MChar.
  apply (MApp [2]). apply MChar.
  apply (MApp [3]). apply MChar.
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T),
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp. 
  - apply H.
  - apply MStar0.
Qed.

(* Exercise: 3 stars, standard (exp_match_ex1) *)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp. 
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s Hs. 
      apply H. simpl. right. apply Hs.
Qed.
(* Exercise ends *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2 
  | Union re1 re2 => re_chars re1 ++ re_chars re2 
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch 
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2 
        | s1 re1 re2 Hmatch IH 
        | re1 s2 re2 Hmatch IH
        | re 
        | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl in Hin. destruct Hin. 
  - simpl. simpl in Hin. apply Hin. 
  - simpl. 
    rewrite In_app_iff in Hin.
    rewrite In_app_iff.
    destruct Hin as [Hin | Hin]. 
    + left. apply IH1. apply Hin.
    + right. apply IH2. apply Hin. 
  - simpl. apply In_app_iff. 
    left. apply (IH Hin). 
  - simpl. apply In_app_iff. 
    right. apply (IH Hin). 
  - simpl in Hin. destruct Hin. 
  - simpl. rewrite In_app_iff in Hin. 
    destruct Hin as [Hin | Hin]. 
    + apply (IH1 Hin). 
    + simpl in IH2. apply (IH2 Hin). 
Qed.

(* Exercise: 4 stars, standard (re_not_empty) *)
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true 
  | Char _ => true
  | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star _ => true 
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s Hmatch]. induction Hmatch.
    + reflexivity.
    + reflexivity. 
    + simpl. rewrite IHHmatch1. 
      rewrite IHHmatch2. reflexivity.
    + simpl. rewrite IHHmatch. reflexivity.
    + simpl. rewrite IHHmatch. destruct (re_not_empty re1).
      { reflexivity. }
      { reflexivity. }
    + reflexivity.
    + reflexivity. 
  - intros H. induction re. 
    + simpl in H. discriminate H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar. 
    + simpl in H. apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply IHre1 in H1. 
      apply IHre2 in H2.
      destruct H1 as [s1 H1].
      destruct H2 as [s2 H2].
      exists (s1 ++ s2).
      apply MApp. 
      { apply H1. }
      { apply H2. }
    + simpl in H. apply orb_true_iff in H.
      destruct H as [H | H].
      { apply IHre1 in H. destruct H as [s' H].
        exists s'. apply MUnionL. apply H. }
      { apply IHre2 in H. destruct H as [s' H].
        exists s'. apply MUnionR. apply H. }
    + exists []. apply MStar0. 
Qed.

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2. 
  induction H1 
    as [| x'
        | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2 
        | s1 re1 re2 Hmatch IH 
        | re1 s2' re2 Hmatch IH 
        | re'' 
        | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2]. 
  - discriminate Heqre'. 
  - discriminate Heqre'.
  - discriminate Heqre'. 
  - discriminate Heqre'.
  - discriminate Heqre'.
  - intros s2 H. simpl. apply H.
  - intros s2 H1. rewrite <- app_assoc. 
    apply MStarApp. 
    + apply Hmatch1.
    + apply IH2.
      { apply Heqre'. }
      { apply H1. }
Qed.

(* Exercise: 4 stars, standard, optional (exp_match_ex2) *)
Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss [] /\
    forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re Hmatch. 
  remember (Star re) as re'.
  induction Hmatch.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. simpl. split.
    + reflexivity.
    + intros s' H. destruct H.
  - destruct (IHHmatch2 Heqre') as [ss' [H1 H2]].
    injection Heqre' as Eq. destruct Eq.
    exists (s1 :: ss'). split.
    + simpl. rewrite <- H1. reflexivity.
    + intros s'. simpl. intros [H | H].
      { rewrite <- H. apply Hmatch1. }
      { apply H2. apply H. }
Qed.
(* Exercise ends *)

(* Exercise: 5 stars, advanced (weak_pumping) *)
Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with 
  | EmptySet => 1 
  | EmptyStr => 1 
  | Char _ => 2 
  | App re1 re2 => 
      pumping_constant re1 + pumping_constant re2 
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2 
  | Star r => pumping_constant r 
  end.

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - simpl. apply le_n.
  - simpl. apply le_n.
  - simpl. apply le_S. apply le_n.
  - simpl. apply le_trans with (n := pumping_constant re1).
    + apply IHre1.
    + apply le_plus_l.
  - simpl. apply le_trans with (n := pumping_constant re1).
    + apply IHre1.
    + apply le_plus_l.
  - simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H. assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  rewrite H in Hp1. 
  inversion Hp1.
Qed.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | O => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- app_assoc.
    rewrite IHn. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re H1 H2. induction m.
  - simpl. apply H2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp. 
    + apply H1.
    + apply IHm.
Qed.

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch 
    as [| x 
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH 
        | re1 s2 re2 Hmatch IH 
        | re 
        | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - simpl. intros H.
    rewrite app_length in H.
    apply add_le_cases in H.
    destruct H as [H | H].
    + apply IH1 in H. 
      destruct H as [x [y [z [H1 [H2 H3]]]]].
      exists x, y, (z ++ s2).
      split.
      { rewrite H1. rewrite <- app_assoc.
        rewrite <- app_assoc. reflexivity. }
      { split.
        - apply H2.
        - intros m. rewrite app_assoc. 
          rewrite app_assoc. apply MApp.
          + rewrite <- app_assoc. apply H3.
          + apply Hmatch2. }
    + apply IH2 in H.
      destruct H as [x [y [z [H1 [H2 H3]]]]].
      exists (s1 ++ x), y, z.
      split.
      { rewrite H1. rewrite app_assoc. reflexivity. }
      { split.
        - apply H2.
        - intros m. rewrite <- app_assoc.
          apply MApp.
          + apply Hmatch1.
          + apply H3. }
  - simpl. intros H. apply plus_le in H. destruct H as [H H'].
    apply IH in H. 
    destruct H as [x [y [z [H1 [H2 H3]]]]].
    exists x, y, z. split.
    + apply H1.
    + split.
      { apply H2. }
      { intros m. apply MUnionL. apply H3. }
  - simpl. intros H. apply plus_le in H. destruct H as [H' H].
    apply IH in H. 
    destruct H as [x [y [z [H1 [H2 H3]]]]].
    exists x, y, z. split.
    + apply H1.
    + split.
      { apply H2. }
      { intros m. apply MUnionR. apply H3. }
  - simpl. intros contra. inversion contra.
    exfalso. apply pumping_constant_0_false in H0. 
    apply H0.
  - destruct s1 eqn:E1.
    + simpl. simpl in IH2. apply IH2. 
    + destruct s2 eqn:E2.
      { simpl. rewrite app_nil_r. simpl in IH1.
        intros H. apply IH1 in H. 
        destruct H as [sx [sy [sz [H1 [H2 H3]]]]].
        exists sx, sy, sz. split.
        - apply H1.
        - split.
          + apply H2.
          + intros m. apply MStar1. apply H3. }
      { simpl. intros H. 
        exists [], s1, s2. split.
        - rewrite E1. rewrite E2. reflexivity.
        - split.
          + rewrite E1. intros contra. 
            discriminate contra.
          + intros m. simpl. apply napp_star.
            { rewrite E1. apply Hmatch1. }
            { rewrite E2. apply Hmatch2. } }
Qed.
(* Exercise ends *)

(* Exercise: 5 stars, advanced, optional (pumping) *)
Lemma plus_le_compat : forall n m p q, 
  n <= p ->
  m <= q ->
  n + m <= p + q.
Proof.
  intros n m p q H1 H2.
  apply le_trans with (n := p + m).
  - apply plus_le_compat_r. apply H1. 
  - apply plus_le_compat_l. apply H2.
Qed.

Lemma le_derives_eq : forall n m,
  n <= m ->
  m <= n ->
  n = m.
Proof.
  intros n. induction n as [|n' IHn']. 
  - intros m H1 H2. inversion H2. reflexivity. 
  - intros m H1 H2. destruct m as [|m']. 
    + inversion H1. 
    + apply le_prop2 in H1. 
      apply le_prop2 in H2. 
      f_equal. apply IHn'. 
      { apply H1. }
      { apply H2. }
Qed.

Lemma n_plus_m_eq_n_indicates_m_is_0 : 
  forall n m,
  n + m = n -> m = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m H. simpl in H. apply H.
  - intros m H. simpl in H. injection H as H. 
    apply IHn'. apply H. 
Qed.

Lemma le_derives_eq_comp : forall n m p q,
  n <= p ->
  m <= q ->
  m + n = p + q ->
  n = p /\ m = q.
Proof.
  intros n. induction n as [|n' IHn']. 
  - intros m p q H1 H2 Heq. 
    rewrite add_0_r in Heq. 
    rewrite Heq in H2.
    assert (H': p + q = q).
    { apply le_derives_eq. 
      - apply H2.
      - rewrite add_comm. apply le_plus_l. }
    split.
    + symmetry. 
      apply n_plus_m_eq_n_indicates_m_is_0 with (n := q).
      rewrite add_comm. apply H'.
    + rewrite <- Heq in H'. apply H'.
  - intros m p. induction p as [|p' IHp'].
    + intros q contra. 
      inversion contra.
    + intros q H1 H2 Heq.
      apply Sn_le_Sm__n_le_m in H1. 
      simpl in Heq. 
      rewrite <- plus_n_Sm in Heq. 
      injection Heq as Heq. 
      destruct (IHn' m p' q H1 H2 Heq) as [H1' H2'].
      split. 
      { f_equal. apply H1'. }
      { apply H2'. }
Qed.

Lemma n_plus_m_le_p_indicates_n_le_p : forall n m p,
  n + m <= p -> n <= p.
Proof.
  intros n m. induction m as [|m' IHm'].
  - intros p H. rewrite add_0_r in H. apply H.
  - intros p H. rewrite <- plus_n_Sm in H.
    apply le_prop1 in H.
    apply IHm'. apply H.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3, 
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [| x 
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH 
        | re1 s2 re2 Hmatch IH 
        | re 
        | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - simpl. rewrite app_length. intros H.
    destruct (lt_ge_cases (pumping_constant re1) (length s1)) as [H1 | H1]. 
    + apply n_lt_m__n_le_m in H1.
      apply IH1 in H1.
      destruct H1 as [sx [sy [sz [Happ [Hnemp [Hcond Hmatch]]]]]].
      exists sx, sy, (sz ++ s2). split.
      { rewrite Happ. 
        rewrite app_assoc. 
        rewrite app_assoc. 
        rewrite app_assoc. 
        reflexivity. }
      { split. 
        - apply Hnemp.
        - split.
          + apply le_trans with (n := pumping_constant re1). 
            { apply Hcond. }
            { apply le_plus_l. } 
          + intros m. rewrite app_assoc. rewrite app_assoc.
            apply MApp. 
            { rewrite <- app_assoc. 
              apply Hmatch. }
            { apply Hmatch2. } }
    + destruct (lt_ge_cases (pumping_constant re2) (length s2)) as [H2 | H2].
      { apply n_lt_m__n_le_m in H2.
        apply IH2 in H2.
        destruct H2 as [sx [sy [sz [Happ [Hnemp [Hcond Hmatch]]]]]].
        exists (s1 ++ sx), sy, sz. split.
        - rewrite Happ.
          rewrite app_assoc. 
          reflexivity.
        - split.
          + apply Hnemp.
          + split. 
            { rewrite app_length. rewrite <- add_assoc.
              apply plus_le_compat.
              - apply H1. 
              - apply Hcond. }
            { intros m. rewrite <- app_assoc. apply MApp.
              - apply Hmatch1.
              - apply Hmatch. } }
      { assert (Heq: length s1 = pumping_constant re1 /\ length s2 = pumping_constant re2).
        { apply le_derives_eq_comp. 
          - apply H1. 
          - apply H2.
          - apply le_derives_eq. 
            + rewrite (add_comm (length s2) (length s1)).
              apply plus_le_compat.
              { apply H1. }
              { apply H2. }
            + rewrite (add_comm (length s2) (length s1)).
              apply H. }
        destruct Heq as [E1 E2].
        assert (H1': pumping_constant re1 <= length s1).
        { rewrite E1. apply le_n. }
        apply IH1 in H1'. 
        destruct H1' as [sx [sy [sz [Happ [Hnemp [Hcond Hmatch]]]]]].
        exists sx, sy, (sz ++ s2). split.
        { rewrite Happ. 
          rewrite app_assoc. 
          rewrite app_assoc. 
          rewrite app_assoc. 
          reflexivity. }
        { split. 
          - apply Hnemp.
          - split.
            + apply le_trans with (n := pumping_constant re1). 
              { apply Hcond. }
              { apply le_plus_l. } 
            + intros m. rewrite app_assoc. rewrite app_assoc.
              apply MApp. 
              { rewrite <- app_assoc. 
                apply Hmatch. }
              { apply Hmatch2. } } }
  - simpl. intros H. 
    apply n_plus_m_le_p_indicates_n_le_p in H.
    apply IH in H. destruct H as [sx [sy [sz [Happ [Hnemp [Hcond H]]]]]].
    exists sx, sy, sz. split.
    { rewrite Happ. 
      rewrite app_assoc. 
      reflexivity. }
    { split. 
      - apply Hnemp.
      - split.
        + apply le_trans with (n := pumping_constant re1). 
          { apply Hcond. }
          { apply le_plus_l. } 
        + intros m. apply MUnionL. apply H. }
  - simpl. intros H.
    rewrite add_comm in H.
    apply n_plus_m_le_p_indicates_n_le_p in H.
    apply IH in H. destruct H as [sx [sy [sz [Happ [Hnemp [Hcond H]]]]]]. 
    exists sx, sy, sz. split.
    { rewrite Happ. 
      rewrite app_assoc. 
      reflexivity. }
    { split. 
      - apply Hnemp.
      - split.
        + apply le_trans with (n := pumping_constant re2). 
          { apply Hcond. }
          { rewrite add_comm. apply le_plus_l. }
        + intros m. apply MUnionR. apply H. } 
  - simpl. intros H. 
    assert (contra: 1 <= 0).
    { apply le_trans with (n := pumping_constant re).
      - apply pumping_constant_ge_1.
      - apply H.  }
    inversion contra.
  - simpl. intros H.
    destruct (lt_ge_cases (pumping_constant re) (length s1)) as [H1 | H1].
    + apply n_lt_m__n_le_m in H1.
      apply IH1 in H1.
      destruct H1 as [sx [sy [sz [Happ [Hnemp [Hcond Hmatch]]]]]].
      exists sx, sy, (sz ++ s2). split.
      { rewrite Happ. rewrite app_assoc. 
        rewrite app_assoc. rewrite app_assoc.
        reflexivity. }
      { split.
        - apply Hnemp.
        - split. 
          + apply Hcond.
          + intros m. 
            rewrite app_assoc. rewrite app_assoc.
            apply MStarApp. 
            { rewrite <- app_assoc. apply Hmatch. }
            { apply Hmatch2. } }
    + destruct s1 as [|h1 s1'] eqn:E.
      { simpl. simpl in H. apply (IH2 H). }
      { exists [], s1, s2. split.
        - rewrite <- E. simpl. reflexivity.
        - split.
          + rewrite E. intros contra. discriminate contra.
          + split. 
            { simpl. rewrite E. apply H1. }
            { intros m. simpl. apply napp_star.
              - rewrite E. apply Hmatch1.
              - apply Hmatch2. } }
Qed.
(* Exercise ends *)

End Pumping.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n  =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (n =? m) eqn:H.
    + intros _. rewrite eqb_eq in H. left.
      rewrite H. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P: Prop) : bool -> Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ~P) : reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b eqn:E.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(* Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intros HP. inversion H.
    + reflexivity.
    + exfalso. apply H0. apply HP.
  - intros Hb. inversion H.
    + apply H0.
    + rewrite Hb in H1. discriminate.
Qed.
(* Exercise ends *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect.
  rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (eqbP n m) as [H | H].
    + intros _. left. rewrite H. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

(* Exercise: 3 stars, standard, especially useful (eqbP_practice) *)
Fixpoint count n l :=
  match l with 
  | [] => 0
  |  m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice: forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [|m l' IHl'].
  - intros H. inversion H.
  - simpl in Hcount. destruct (eqbP n m). 
    + discriminate Hcount. 
    + simpl in Hcount.  intros [Heq | Hin]. 
      { rewrite Heq in H. apply H. reflexivity. }
      { apply IHl'. 
        - apply Hcount.
        - apply Hin. }
Qed.

(* Exercise: 3 stars, standard, especially useful (nostutter_defn) *)
Inductive nostutter {X : Type} : list X -> Prop :=
  | EmptyNoStutter : nostutter []
  | SingleNoStutter (x : X) : nostutter [x]
  | IndNoStutter (x1 x2 : X) (xl : list X) (H: x1 <> x2) (IH: nostutter (x2::xl)) : nostutter (x1::x2::xl).

Example test_nostutter_1 : nostutter [3; 1; 4; 1; 5; 6].
Proof.
  apply IndNoStutter. 
  - intros H. inversion H. 
  - apply IndNoStutter.
    + intros H. inversion H. 
    + apply IndNoStutter.
      * intros H. inversion H. 
      * apply IndNoStutter. 
        { intros H. inversion H. }
        { apply IndNoStutter. 
          - intros H. inversion H. 
          - apply SingleNoStutter. }
Qed. 

Example test_nostutter_2: nostutter (@nil nat).
Proof.
  apply EmptyNoStutter. 
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  apply SingleNoStutter. 
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]). 
Proof. 
  intros H. inversion H. 
  inversion IH. apply H5. reflexivity.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced (filter_challenge) *)
Inductive merge {X : Type} : list X -> list X -> list X -> Prop :=
  | EmptyMergeL (l : list X) : merge [] l l 
  | EmptyMergeR (l : list X) : merge l [] l 
  | IndMergeL (x : X) (l1 l2 l : list X) (H : merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | IndMergeR (x : X) (l1 l2 l : list X) (H : merge l1 l2 l) : merge l1 (x :: l2) (x :: l).

Theorem merge_filter : forall (X : Set) (test : X -> bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l. induction l. 
  - intros l1 l2 Hmerge H1 H2.
    inversion Hmerge. 
    + reflexivity. 
    + reflexivity.
  - intros l1 l2 Hmerge H1 H2. 
    inversion Hmerge. 
    + rewrite H3 in H2. 
      simpl in H2. 
      destruct H2 as [Htest H2].
      simpl. rewrite Htest. 
      apply (IHl [] l). 
      * rewrite <- H in Hmerge.
        rewrite H3 in Hmerge.
        apply EmptyMergeL. 
      * simpl. reflexivity. 
      * apply H2. 
    + rewrite H3 in H1. simpl in H1.
      destruct H1 as [E H1]. 
      simpl. rewrite E. f_equal.
      apply (IHl l []).
      * apply EmptyMergeR. 
      * apply H1. 
      * rewrite <- H0 in H2. 
        apply H2.
    + rewrite H in H0. 
      rewrite <- H0 in H1. 
      simpl in H1. destruct H1 as [E H1].
      simpl. rewrite E. f_equal.
      apply (IHl l0 l2).
      * apply H4.
      * apply H1. 
      * apply H2.
    + rewrite H in H3.
      rewrite <- H3 in H2.
      simpl in H2. destruct H2 as [NE H2].
      simpl. rewrite NE. apply (IHl l1 l3).
      * apply H4.
      * apply H1.
      * apply H2.
Qed.
(* End of exercise *)

(* Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
Theorem merge_filter2 : forall (X : Set) (test : X -> bool) (l l1 l2 : list X), 
  merge l1 l2 l ->
  All (fun x => test x = true) l1 ->
  length l1 <= length (filter test l).
Proof.
  intros X test l. 
  induction l as [|h l' IHl'].
  - intros l1 l2 Hmerge H1.
    destruct l1 as [|h1 l1'].
    + simpl. apply le_n.
    + inversion Hmerge.
  - intros l1 l2 Hmerge H1. 
    inversion Hmerge.
    + simpl. apply O_le_n.
    + rewrite H2 in H1. destruct H1 as [E H1].
      simpl. rewrite E. simpl.
      apply n_le_m__Sn_le_Sm.
      apply (IHl' l' []).
      * apply EmptyMergeR. 
      * apply H1.
    + rewrite <- H0 in H1.
      destruct H1 as [E H1].
      rewrite H in E. simpl.
      rewrite E. simpl. 
      apply n_le_m__Sn_le_Sm.
      apply (IHl' l0 l2).
      * apply H3.
      * apply H1.
    + destruct (test h) eqn:E.
      * simpl. rewrite E. simpl.
        apply le_S. 
        apply (IHl' l1 l3).
        { apply H3. }
        { apply H1. }
      * simpl. rewrite E.
        apply (IHl' l1 l3).
        { apply H3. }
        { apply H1. }
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, standard, optional (palindromes) *)
Inductive pal {X : Type} : list X -> Prop :=
  | EmptyPal : pal [] 
  | SinglePal (x : X) : pal [x]
  | IndPal (x : X) (l : list X) (H : pal l) : pal ([x] ++ l ++ [x]).

Theorem pal_app_rev : 
  forall (X : Type) (l : list X), pal (l ++ rev l).
Proof.
  intros X l. induction l as [|h l' IHl'].
  - simpl. apply EmptyPal. 
  - simpl. rewrite app_assoc. 
    apply IndPal. apply IHl'. 
Qed.

Theorem pal_rev : 
  forall (X : Type) (l : list X),
  pal l -> l = rev l.
Proof.
  intros X l Hpal.
  induction Hpal.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. 
    rewrite <- IHHpal. 
    rewrite <- app_assoc. 
    simpl. reflexivity.
Qed.
(* Exercise ends *)

(* Exercise: 5 stars, standard, optional (palindrome_converse) *)
Theorem rev_length: forall {X: Type} (l : list X),
  length l = length (rev l).
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite app_length. 
    simpl. rewrite <- plus_n_Sm.
    rewrite add_0_r. f_equal.
    apply IHl.
Qed.

Theorem list_app_subtract: forall {X: Type} (l1 l2 l:list X),
  length l1 = length l2 -> l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
  intros X l1. induction l1.
  - intros l2 l H1 H2.
    simpl in H1. destruct l2.
    + reflexivity.
    + simpl in H1. discriminate H1.
  - intros l2 l H1 H2.
    destruct l2.
    + simpl in H1. discriminate H1.
    + simpl in H1. injection H1 as H1.
      simpl in H2. injection H2 as H2.
      apply (IHl1 l2 l H1) in H.
      rewrite H2. rewrite H.
      reflexivity.
Qed.

Lemma list_eq_length_eq: forall {X : Type} (l1 l2 : list X),
  l1 = l2 -> length l1 = length l2.
Proof.
  intros X l1 l2 H. 
  rewrite H. 
  reflexivity.
Qed.

Lemma add_r_subtract: forall (n m o : nat),
  n + o = m + o -> n = m.
Proof.
  intros n m o. induction o.
  - rewrite add_0_r. rewrite add_0_r. 
    intros H. apply H.
  - intros H. 
    rewrite <- plus_n_Sm in H.
    rewrite <- plus_n_Sm in H.
    injection H as H.
    apply IHo in H.
    apply H.
Qed.

Theorem app_subtract: forall {X: Type} (l1 l2 l : list X),
  l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
  intros X l1 l2 l H.
  apply list_app_subtract with (l := l).
  - apply list_eq_length_eq in H.
    rewrite app_length in H.
    rewrite app_length in H.
    apply add_r_subtract in H.
    apply H.
  - apply H.
Qed.

Lemma palindrome_converse_wrapper: forall {X:Type} (n : nat) (l: list X),
  length l <= n -> l = rev l -> pal l.
Proof.
  intros X n. induction n as [|n' IHn'].
  - assert (H': forall {X: Type} (l: list X), length l <= 0 -> l = []).
    { intros X0 l H. destruct l.
      - reflexivity.
      - simpl in H. inversion H. }
    intros l H. apply H' in H. rewrite H.
    intros Eq. apply EmptyPal.
  - intros l H Hrev. destruct l eqn:Eql.
    + apply EmptyPal.
    + simpl in Hrev. destruct (rev l0) eqn:Eqrev.
      { simpl in Hrev. rewrite Hrev. apply SinglePal. }
      { rewrite <- (rev_involutive X l0) in Hrev.
        rewrite Eqrev in Hrev.
        simpl in Hrev. injection Hrev as Hinj.
        rewrite Hinj in H0.
        apply app_subtract in H0.
        rewrite <- (rev_involutive X l0).
        rewrite Eqrev. simpl. 
        simpl in H. apply le_S_n in H.
        rewrite <- (rev_involutive X l0) in H.
        rewrite Eqrev in H.
        simpl in H. rewrite app_length in H.
        simpl in H. rewrite <- plus_n_Sm in H.
        rewrite add_0_r in H.  
        apply le_prop1 in H. 
        rewrite <- rev_length in H.
        rewrite H0. rewrite <- Hinj.
        symmetry in H0.
        apply (IHn' l1 H) in H0.
        replace (x :: l1 ++ [x]) with ([x] ++ l1 ++ [x]).
        + apply IndPal. apply H0.
        + reflexivity. }
Qed.

Theorem palindrome_converse: forall {X : Type} (l : list X),
  l = rev l -> pal l.
Proof.
  intros X l.
  apply palindrome_converse_wrapper with (n := length l).
  apply le_n.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced, optional (NoDup) *)
Definition disjoint {X: Type} (l1 l2 : list X) : Prop :=
  forall x, In x l1 -> ~(In x l2).

Inductive NoDup {X : Type} : list X -> Prop :=
  | EmptyNoDup : NoDup []
  | IndNoDup (x : X) (l : list X) (Hnd : NoDup l) (Hnin : ~(In x l)) : NoDup (x :: l).

Theorem disjoint_app_nodup: forall {X : Type} (l1 l2 : list X),
  NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros X l1. induction l1.
  - intros l2 H. unfold disjoint. 
    intros x H'. inversion H'. 
  - intros l2. simpl. intros H. inversion H.
    apply IHl1 in Hnd. 
    unfold disjoint. simpl. 
    intros y H'. destruct H' as [H' | H'].
    + rewrite <- H'. intros Hin2. 
      apply Hnin. 
      apply In_app_iff.
      right. apply Hin2.
    + apply Hnd. apply H'.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced, optional (pigeonhole_principle) *)
Lemma in_split: forall {X : Type} (x : X) (l : list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l. induction l.
  - intros H. inversion H.
  - simpl. intros H. destruct H as [H | H].
    + exists [], l.
      simpl. rewrite H.
      reflexivity.
    + apply IHl in H.
      destruct H as [l1 [l2 H]].
      exists (x0 :: l1), l2.
      simpl. rewrite H. reflexivity.
Qed.

Inductive repeat {X : Type} : list X -> Prop :=
  | NewRepeat (x : X) (l : list X) (Hl : NoDup l) (Hin : In x l) : repeat (x :: l) 
  | ContRepeat (x : X) (l : list X) (Hl : repeat l) : repeat (x :: l).

Lemma list_is_nodup_or_repeat: excluded_middle ->
  forall {X : Type} (l : list X),
  NoDup l \/ repeat l.
Proof.
  intros exm X l. induction l.
  - left. apply EmptyNoDup.
  - destruct IHl as [IHl | IHl].
    + destruct (exm (In x l)).
      { right. apply NewRepeat.
        + apply IHl.
        + apply H. }
      { left. apply IndNoDup.
        + apply IHl.
        + apply H. }
    + right. apply ContRepeat. 
      apply IHl.
Qed.

Theorem pigeonhole_principle: excluded_middle ->
  forall (X : Type) (l1 l2 : list X),
  (forall x, In x l1 -> In x l2) -> 
  length l2 < length l1 ->
  repeat l1.
Proof.
  intros EM X l1. induction l1.
  - intros. simpl in H0. inversion H0.
  - intros. destruct (EM (In x l1)) as [Hin | Hnin].
    + destruct (list_is_nodup_or_repeat EM l1).
      { apply NewRepeat.
        - apply H1.
        - apply Hin. }
      { apply ContRepeat. apply H1. }
    + apply ContRepeat.
      destruct (in_split x l2) as [ll [lr Hisl2]].
      { apply H. simpl. left. reflexivity. }
      apply IHl1 with (ll ++ lr).
      * intros. apply In_app_iff. 
        assert(Hinxl2: In x0 l2).
        { apply H. simpl. right. apply H1. }
        rewrite Hisl2 in Hinxl2.
        rewrite In_app_iff in Hinxl2.
        simpl in Hinxl2. destruct Hinxl2 as [H' | [H' | H']].
        { left. apply H'. }
        { rewrite <- H' in H1. exfalso. apply Hnin. apply H1. }
        { right. apply H'. }
      * rewrite Hisl2 in H0.
        simpl in H0. rewrite app_length in H0. 
        simpl in H0. rewrite <- plus_n_Sm in H0.
        apply Sn_le_Sm__n_le_m in H0. 
        rewrite app_length. unfold lt.
        apply H0.
Qed.
(* Exercise ends *)

Require Import Coq.Strings.Ascii.

Definition string := list ascii.

Lemma provable_equiv_true : forall (P : Prop), P <-> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
    + intros. reflexivity.
    + intros. apply H.
  - intros. apply H. reflexivity.
Qed.

Lemma not_equiv_false: forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

Lemma null_matches_none: forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros.
  inversion H.
Qed.

Lemma empty_matches_eps: forall (s : string), s =~ EmptyStr <-> s = [].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

Lemma char_nomatch_char:
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

Lemma char_eps_suffix: forall (a : ascii) s, a :: s =~ Char a <-> s = [].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

Lemma app_exists: forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    + reflexivity.
    + split.
      * apply H3.
      * apply H4.
  - intros [s0 [s1 [Happ [Hmat0 Hmat1]]]].
    rewrite Happ.
    apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(* Exercise: 3 stars, standard, optional (app_ne) *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([] =~ re0 /\ a :: s =~ re1) \/ 
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split.
  - intros H. inversion H.
    destruct s1.
    + left. split.
      * apply H3.
      * simpl. apply H4.
    + right. simpl in H1. 
      injection H1 as Eqx.
      exists s1, s2. split.
      * symmetry. apply H1.
      * split. 
        { rewrite Eqx in H3.
          apply H3. }
        { apply H4. }
  - intros H. destruct H as [H | H].
    + destruct H as [H1 H2].
      replace (a :: s) with ([] ++ (a :: s)).
      * apply MApp.
        { apply H1. }
        { apply H2. }
      * reflexivity.
    + destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1. replace (a :: s0 ++ s1) with ((a :: s0) ++ s1).
      * apply MApp.
        { apply H2. }
        { apply H3. }
      * reflexivity.
Qed.

Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <->
  s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros H. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros H. destruct H as [H | H].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (star_ne) *)
Lemma star_ne : forall (a :ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros. split.
  - intros H. 
    remember (a :: s) as s'.
    remember (Star re) as re'. 
    induction H.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct s1.
      * simpl in Heqs'.
        apply IHexp_match2 in Heqs'. 
        { destruct Heqs' as [s0 [s1 [H1 [H2 H3]]]].
          exists s0, s1.
          split. 
          - apply H1.
          - split.
            + apply H2.
            + apply H3. }
        { apply Heqre'. }
      * simpl in Heqs'. 
        injection Heqs' as Heqxa.
        injection Heqre' as Heqre'.
        exists s1, s2. split.
        { symmetry. apply H1. }
        { split.
          - rewrite Heqxa in H. 
            rewrite Heqre' in H.
            apply H. 
          - apply H0. }
  - intros H. destruct H as [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1. replace (a :: s0 ++ s1) with ((a :: s0) ++ s1).
    + apply MStarApp.
      * apply H2.
      * apply H3.
    + reflexivity.
Qed.

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([] =~ re) (m re).
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (match_eps) *)
Fixpoint match_eps (re : reg_exp ascii) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => false
    | App re0 re1 => (match_eps re0) && (match_eps re1)
    | Union re0 re1 => (match_eps re0) || (match_eps re1)
    | Star _ => true
  end.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (match_eps_refl) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros re. induction re.
  - apply ReflectF.
    intros H. inversion H.
  - apply ReflectT.
    apply MEmpty.
  - apply ReflectF.
    intros H. inversion H.
  - simpl. inversion IHre1.
    + inversion IHre2.
      * apply ReflectT.
        apply (MApp [] re1 [] re2 H0 H2).
      * apply ReflectF.
        intros H'. inversion H'.
        destruct s2.
        { apply H2. apply H7. }
        { destruct s1.
          - simpl in H3. discriminate H3.
          - simpl in H3. discriminate H3. }
    + apply ReflectF.
      intros H'. inversion H'.
      destruct s1.
      * apply H0. apply H4.
      * simpl in H1. discriminate H1.
  - simpl. inversion IHre1.
    + apply ReflectT.
      apply MUnionL. apply H0.
    + inversion IHre2.
      * apply ReflectT.
        apply MUnionR.
        apply H2.
      * apply ReflectF.
        intros H'. inversion H'.
        { apply H0. apply H5. }
        { apply H2. apply H5. }
  - apply ReflectT.
    apply MStar0.
Qed.
(* Exercise ends *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

Definition derives d := forall a re, is_der re a (d a re).

(* Exercise: 3 stars, standard, optional (derive) *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
    | EmptySet => EmptySet
    | EmptyStr => EmptySet
    | Char x => if eqb x a then EmptyStr else EmptySet
    | App re0 re1 => if match_eps re0
                     then Union (derive a re1) (App (derive a re0) re1)
                     else App (derive a re0) re1
    | Union re0 re1 => Union (derive a re0) (derive a re1)
    | Star re => App (derive a re) (Star re)
  end.
(* Exercise ends *)

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der6 : 
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(* Exercise: 4 stars, standard, optional (derive_corr) *)
Lemma derive_corr : derives derive.
Proof.
  unfold derives. unfold is_der.
  intros. split. 
  - generalize dependent s. induction re.
    + intros s H. inversion H.
    + intros s H. inversion H.
    + intros s H. inversion H.
      simpl. rewrite eqb_refl.
      apply MEmpty.
    + intros s H. simpl.
      destruct (match_eps_refl re1).
      * apply app_ne in H.
        destruct H as [[H1 H2] | [s0 [s1 [H1 [H2 H3]]]]].
        { apply MUnionL.
          apply IHre2.
          apply H2. }
        { apply MUnionR.
          rewrite H1. 
          apply MApp.
          - apply IHre1. apply H2.
          - apply H3. }
      * apply app_ne in H.
        destruct H as [[H1 H2] | [s0 [s1 [H1 [H2 H3]]]]].
        { exfalso. apply H0. apply H1. }
        { rewrite H1. apply MApp.
          - apply IHre1.
            apply H2.
          - apply H3. }
    + intros s H. simpl.
      apply union_disj.
      apply union_disj in H.
      destruct H.
      * left. apply IHre1. apply H.
      * right. apply IHre2. apply H.
    + intros s H. simpl.
      apply star_ne in H.
      destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1. apply MApp.
      * apply IHre. apply H2.
      * apply H3.
  - generalize dependent s. induction re.
    + simpl. intros s H. inversion H.
    + simpl. intros s H. inversion H.
    + simpl. intros s H. destruct (eqb t a) eqn:E.
      * inversion H. 
        apply eqb_eq in E.
        rewrite E.
        apply MChar.
      * inversion H.
    + simpl. intros s H. destruct (match_eps_refl re1).
      * apply app_ne.
        apply union_disj in H.
        destruct H as [H | H].
        { left. split.
          - apply H0.
          - apply IHre2. 
            apply H. }
        { inversion H.
          right. exists s1, s2. split.
          - reflexivity.
          - split.
            + apply IHre1.
              apply H4.
            + apply H5. }
      * apply app_ne. inversion H.
        right. exists s1, s2. split.
        { reflexivity. }
        { split.
          - apply IHre1. apply H4.
          - apply H5. }
    + simpl. intros s H. 
      apply union_disj in H.
      apply union_disj.
      destruct H as [H | H].
      * left. apply IHre1. apply H.
      * right. apply IHre2. apply H.
    + simpl. intros s H.
      inversion H. apply star_ne.
      exists s1, s2. split.
      * reflexivity.
      * split.
        { apply IHre. apply H3. }
        { apply H4. }
Qed.
(* Exercise ends *)

Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(* Exercise: 2 stars, standard, optional (regex_match) *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
    | [] => match_eps re 
    | x :: s' => regex_match s' (derive x re)
  end.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (regex_match_correct) *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex. intros s.
  induction s.
  - intros re. unfold regex_match.
    destruct (match_eps_refl re).
    + apply ReflectT. apply H.
    + apply ReflectF. apply H.
  - intros re. simpl.
    destruct (IHs (derive x re)).
    + apply ReflectT.
      apply derive_corr. apply H.
    + apply ReflectF. intros H'.
      apply H. apply derive_corr.
      apply H'.
Qed.
(* Exercise ends *)
