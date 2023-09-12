From LF Require Export Tactics.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Theorem plus_claim_is_true : 
  plus_claim.
Proof.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H'. apply H'.
Qed.

Check @eq : forall A : Type, A -> A -> Prop.

Example addd_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(* Exercise: 2 stars, standard (and_exercise) *)
Example and_exercise:
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. split.
  - destruct n as [|n'].
    + reflexivity.
    + discriminate H.
  - destruct m as [|m'].
    + reflexivity.
    + rewrite add_comm in H. discriminate H.
Qed.
(* Exercise ends *)

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' : forall n m : nat,
  n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H. destruct H as [HP HQ].
  apply HP.
Qed.

(* Exercise: 1 star, standard, optional (proj2) *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H. destruct H as [_ HQ].
  apply HQ.
Qed.
(* Exercise ends *)

Theorem add_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - apply HQ.
  - apply HP.
Qed.

(* Exercise: 2 stars, standard (and_assoc) *)
Theorem add_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.
(* Exercise ends *)

Lemma factor_is_0 :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite mul_comm. reflexivity.
Qed.

Lemma or_intro_1 : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA.
Qed.

Lemma zero_or_succ:
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Exercise: 1 star, standard (mult_is_O) *)
Lemma mult_is_O : 
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. destruct n as [|n'].
  - left. reflexivity.
  - destruct m as [|m'].
    + right. reflexivity.
    + discriminate H. 
Qed.
(* Exercise ends *)

(* Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.
(* Exercise ends *)

Module NotPlayground.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

(* Exercise: 2 stars, standard, optional (not_implies_our_not) *)
Theorem not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  unfold not.
  intros P H Q HP.
  apply ex_falso_quodlibet. 
  apply H. apply HP.
Qed.
(* Exercises ends *)

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intros contra.
  discriminate contra.
Qed.

Theorem not_false : 
  ~ False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not.
  intros G. apply G. apply H.
Qed.

(* Exercise: 2 stars, standard, especially useful (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HNQ HP.
  apply HNQ. apply HPQ. apply HP.
Qed.
(* Exercise ends *)

(* Exercise: 1 star, standard (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P [HP HNP].
  apply HNP. apply HP.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard (de_morgan_not_or) *)
Theorem de_morgan_not_or : forall (P Q : Prop),
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q HNPorQ. split.
  - intros HP. apply HNPorQ. left. apply HP.
  - intros HQ. apply HNPorQ. right. apply HQ.
Qed.
(* Exxercise ends *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.  
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.  
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.



