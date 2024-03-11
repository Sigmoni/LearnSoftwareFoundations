Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

Theorem mul_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n IHn. 
    rewrite IHn. reflexivity.
Qed.

(* Exercise: 2 stars, standard (plus_one_r') *)
Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n IHn.
    rewrite IHn. reflexivity.
Qed.
(* Exericse ends *)

(* Exercise: 2 stars, standard (booltree_ind) *)
Inductive booltree : Type :=
  | bt_empty 
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

(* Check booltree_ind :
  forall P : booltree -> Prop,
  P bt_empty ->
  (forall b : bool, P (bt_leaf b)) ->
  (forall (b : bool) (t1 : booltree), P t1 ->(forall t2 : booltree, P t2 -> P (bt_branch b t1 t2))) ->
  forall t : booltree, P t. *)

Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop :=
  P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop :=
  forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop :=
  forall (b : bool) (t1 : booltree), P t1 -> (forall t2 : booltree, P t2 -> P (bt_branch b t1 t2)).

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
  base_case P ->
  leaf_case P ->
  branch_case P ->
  forall (b : booltree), P b.

Theorem booltree_ind_type_correct : booltree_ind_type.
Proof.
  unfold booltree_ind_type.
  apply booltree_ind.
Qed.

(* Exercise: 2 stars, standard (toy_ind) *)
Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).
(* Exercise ends *)

(* Exercise: 1 star, standard, optional (tree) *)
Inductive tree (X : Type) : Type :=
  | leaf (x : X) 
  | node (t1 t2 : tree X).

(* Check tree_ind : 
  forall (X : Type) (P : tree X -> Prop),
  (forall x : X, P (leaf X x)) ->
  (forall t1 : tree X, P t1 -> 
  (forall t2 : tree X, P t2 ->
   P (node X t1 t2)))->
  forall t : tree X, P t. *)
(* Exercise ends *)

(* Exercise: 1 star, standard, optional (mytype) *)
Inductive mytype (X : Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).

(* Check mytype_ind. *)
(* Exercise ends *)

(* Exercise: 1 star, standard, optional (foo) *)
Inductive foo (X Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f : nat -> foo X Y).

(* Check foo_ind. *)
(* Exercise ends *)

Definition P_m0r (n : nat) : Prop := n * 0 = 0.
Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mul_0_r'' : forall n : nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn.
    unfold P_m0r. simpl.
    apply IHn. 
Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0 
  | ev'_2 : ev' 2 
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - apply ev'_0.
  - intros n Hn IHn. 
    apply (ev'_sum 2 n).
    + apply ev'_2.
    + apply IHn.
Qed.

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n 
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

Inductive le2 (n : nat) : nat -> Prop :=
  | le2_n : le2 n n 
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).