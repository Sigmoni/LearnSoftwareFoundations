Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Definition relation (X : Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
  inversion H2.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold partial_function.
  unfold not. 
  intros Hc. 
  assert (0 = 1) as Nonsense. 
  { apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.
Qed.

(* Exercise: 2 stars, standard, optional (total_relation_not_partial_function) *)
Inductive total_relation : nat -> nat -> Prop :=
  | ge0_n (n : nat) : total_relation n n 
  | ge0_n_plus_m (n m : nat) (Hn : total_relation n n) (Hm : total_relation m m) : total_relation n m.

Theorem total_relation_not_partial_function :
  ~(partial_function total_relation).
Proof.
  unfold not. unfold partial_function.
  intros Hc. 
  assert (0 = 1) as Nonsense.
  { apply Hc with (x := 0).
    - apply ge0_n.
    - apply ge0_n_plus_m.
      + apply ge0_n.
      + apply ge0_n. }
  discriminate Nonsense.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (empty_relation_partial_function) *)
Inductive empty_relation : nat -> nat -> Prop :=
  | lt0_n_plus_m (n m : nat) (Hn : n < 0) (Hm : m < 0) : empty_relation n m.

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
  inversion Hn.
Qed.
(* Exercise ends *)

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros a.
  apply le_n.
Qed.

Definition transitive {X : Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans:
  transitive le.
Proof.
  unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  - apply Hnm.
  - apply Hmo.
Qed.

(* Exercise: 2 stars, standard, optional (le_trans_hard_way) *)
Theorem lt_trans' : 
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [|m' Hm'o].
  - apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (lt_trans'') *)
Theorem lt_trans'' : 
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [|o'].
  - inversion Hmo.
  - apply le_S in Hnm. 
    apply le_trans with (b := (S m)).
    + apply Hnm.
    + apply Hmo.
Qed.
(* End of the exercise *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  apply le_trans with (b := (S n)).
  - apply le_S. apply le_n.
  - apply H.
Qed.

(* Exercise: 1 star, standard, optional (le_S_n) *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m HSnm.
  inversion HSnm. 
  - apply le_n.
  - apply le_Sn_le. apply H0.
Qed.
(* Exercise ends *)

(* Exercise: 1 star, standard, optional (le_Sn_n) *)
Theorem le_Sn_n : forall n, 
  ~(S n <= n).
Proof.
  intros n. induction n.
  - intros contra. inversion contra.
  - intros contra. apply le_S_n in contra.
    apply (IHn contra).
Qed.
(* Exercise ends *)

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* Exercise: 2 stars, standard, optional (le_not_symmetric) *)
Theorem le_not_symmetric:
  ~(symmetric le).
Proof.
  unfold symmetric. 
  intros H.
  assert (Nonsense: 1 <= 0).
  { apply H. apply le_S. apply le_n. }
  inversion Nonsense.
Qed.
(* Exercise ends *)

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* Exercise: 2 stars, standard, optional (le_antisymmetric) *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros n m Hnm Hmn.
  inversion Hnm.
  - reflexivity.
  - assert (contra: S m0 <= m0).
    { apply le_trans with (b := n).
      - rewrite H0. apply Hmn.
      - apply H. }
    apply le_Sn_n in contra.
    destruct contra.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (le_step) *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  intros n m p Hnm Hmp.
  unfold lt in Hnm.
  apply le_S_n.
  apply le_trans with (b := m).
  - apply Hnm.
  - apply Hmp.
Qed.
(* Exercise ends *)

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
  | rt_step x y (H: R x y) : clos_refl_trans R x y 
  | rt_refl x : clos_refl_trans R x x
  | rt_trans x y z 
      (Hxy : clos_refl_trans R x y)
      (Hyz : clos_refl_trans R y z) :
      clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with m.
      * apply IHle.
      * apply rt_step.
        apply nn.
  - intros H. induction H.
    + inversion H. apply le_S. apply le_n.
    + apply le_n.
    + apply le_trans with y.
      * apply IHclos_refl_trans1.
      * apply IHclos_refl_trans2.
Qed.

Inductive clos_refl_trans_1n {A : Type} 
                             (R : relation A) (x : A) 
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) 
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y Hxy.
  apply rt1n_trans with y.
  - apply Hxy.
  - apply rt1n_refl.
Qed.

(* Exercise: 2 stars, standard, optional (rsc_trans) *)
Lemma rsc_trans : 
  forall (X : Type) (R : relation X) (x y z : X),
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy.
  - apply Hyz.
  - apply IHHxy in Hyz. 
    apply rt1n_trans with y.
    + apply Hxy.
    + apply Hyz.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
  forall (X : Type) (R : relation X) (x y : X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros X R x y. split.
  - intros H. induction H.
    + apply rsc_R. apply H.
    + apply rt1n_refl.
    + apply rsc_trans with y.
      * apply IHclos_refl_trans1.
      * apply IHclos_refl_trans2.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with y.
      * apply rt_step. apply Hxy.
      * apply IHclos_refl_trans_1n.
Qed.
(* Exercise ends *)