Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
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

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~(0 = S n).
Proof.
  intros n H. 
  assert (H2: disc_fn 0).
  { simpl. reflexivity. }
  rewrite H in H2. simpl in H2. apply H2.
Qed.

Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
  (at level 95, no associativity)
  : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros p Q [HPQ HQP]. split.
  - apply HQP.
  - apply HPQ.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros contra. discriminate contra.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP.
  apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ.
  apply H. apply Hiff. apply HQ.
Qed.

(* Exercise: 3 stars, standard (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | HQR].
    + split.
      { left. apply HP. }
      { left. apply HP. }
    + split.
      { right. apply HQR. }
      { right. apply HQR. }
  - intros [HPoQ HPoR].
    destruct HPoQ as [HP | HQ].
    + left. apply HP.
    + destruct HPoR as [HP | HR].
      { left. apply HP. }
      { right. split.
        - apply HQ.
        - apply HR. }
Qed.
(* Exercise ends *)

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_0.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR.
Qed.

Lemma mul_eq_0_ternary : 
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n, 
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(* Exercise: 1 star, standard, especially useful (dist_not_exists) *)
Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H [x H'].
  unfold not in H'. apply H'.
  apply H.
Qed.
(* Exericse ends *)

(* Exercise: 2 stars, standard (dist_exists_or) *)
Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  induction n as [|n' IHn'].
  - intros m H. exists m. reflexivity.
  - intros [|m'].
    + intros H. simpl in H. discriminate H.
    + simpl. intros H.
      apply IHn' in H.
      destruct H as [x0 H].
      exists x0. rewrite H. reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m H. reflexivity.
  - intros m [x H]. destruct m as [|m'].
    + discriminate H.
    + injection H as H.
      simpl. apply IHn'.
      exists x. apply H.
Qed.
(* Exercise ends *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n' = 2 * n.
Proof.
  simpl. intros n [H | [H | []]].
  - exists 4. rewrite <- H. reflexivity.
  - exists 8. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + left. rewrite H. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* Exercise: 3 stars, standard (In_map_iff) *)
Theorem In_map_iff:
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|h l' IHl'].
    + simpl. intros [].
    + simpl. intros [H | H].
      { exists h. split.
        - apply H.
        - left. reflexivity. }
      { apply IHl' in H.
        destruct H as [x H].
        exists x. split.
        - apply H.
        - right. apply H. }
  - induction l as [|h l' IHl'].
    + simpl. intros [x H]. apply H.
    + simpl. intros [x [H1 [H2 | H3]]].
      { left. rewrite <- H1. rewrite H2. reflexivity. }
      { right. apply IHl'. exists x. split.
        - apply H1.
        - apply H3. } 
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  - induction l as [|lh lt IHlh].
    + simpl. intros H. right. apply H.
    + simpl. intros [H | H].
      { left. left. apply H. }
      { rewrite <- or_assoc. right.
        apply IHlh. apply H. }
  - induction l as [|lh lt IHlh].
    + simpl. intros [H | H].
      { destruct H. }
      { apply H. }
    + simpl. intros H. apply or_assoc in H.
      destruct H as [H | H].
      { left. apply H. }
      { right. apply IHlh. apply H. }
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, especially useful (All) *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ (All P t)
  end.

Theorem All_in :
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l. split.
  - induction l as [|h l' IHl'].
    + simpl. intros H. reflexivity.
    + simpl. intros H. split.
      { apply H. left. reflexivity. }
      { apply IHl'. intros x H'. apply H. right. apply H'. }
  - induction l as [|h l' IHl'].
    + simpl. intros H1 x H2. destruct H2.
    + simpl. intros [H1 H2] x [H3 | H3].
      { rewrite <- H3. apply H1. }
      { apply IHl'. 
        - apply H2.
        - apply H3. }
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard, optional (combine_odd_even) *)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if (odd n) then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2. unfold combine_odd_even. destruct (odd n) eqn:E.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  destruct (odd n) eqn:E.
  - apply H1.
  - discriminate H2.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  destruct (odd n) eqn:E.
  - apply H1.
  - discriminate H2.
Qed.
(* Exercise ends *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intros Hl.
  rewrite Hl in H. simpl in H. apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mul_0_r in Hm. symmetry. apply Hm.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  reflexivity.
Qed.

Axiom functional_extensionality : forall {X Y : Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x. apply add_comm.
Qed.

(* Print Assumptions function_equality_ex2. *)

(* Exercise: 4 stars, standard (tr_rev_correct) *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2 
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_append_is_rev_and_append : forall X (l1 l2 : list X),
  rev_append l1 l2 = (rev_append l1 []) ++ l2.
Proof.
  intros X l1. induction l1 as [|h1 l1' IHl1'].
  - intros l2. simpl. reflexivity.
  - intros l2. simpl.
    rewrite IHl1'.
    rewrite IHl1' with (l2 := [h1]).
    rewrite <- app_assoc. 
    simpl. reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality.
  intros l. induction l as [|h l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'.
    unfold tr_rev. simpl.
    apply rev_append_is_rev_and_append.
Qed.

Example even_42_bool : even 42 = true.
Proof.
  reflexivity.
Qed.

Example even_42_prop : Even 42.
Proof.
  unfold Even. 
  exists 21. reflexivity.
Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(* Exercise: 3 stars, standard (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. exists 0. reflexivity.
  - rewrite even_S.
    destruct (even n') eqn:E.
    + simpl. destruct IHn' as [k IHn'].
      exists k. rewrite IHn'. reflexivity.
    + simpl. destruct IHn' as [k IHn'].
      exists (S k). rewrite IHn'. reflexivity.
Qed.
(* End of the exercise *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. apply eqb_refl.
Qed.

Example even_1000 : Even 1000.
Proof. 
  exists 500. reflexivity. 
Qed.

Example even_1000' : even 1000 = true.
Proof.
  reflexivity.
Qed.

Example even_1000'' : Even 1000.
Proof.
  apply even_bool_prop. reflexivity.
Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  rewrite <- even_bool_prop.
  unfold not. simpl.
  intros H. discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  intros n m p H.
  rewrite eqb_eq in H.
  rewrite H. 
  rewrite eqb_eq. 
  reflexivity.
Qed.

(* Exercise: 2 stars, standard (logical_connectives) *)
Theorem andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. split.
    + destruct b1 eqn:E.
      { reflexivity. }
      { discriminate H. }
    + apply andb_true_elim2 in H.
      apply H.
  - intros [H1 H2].
    rewrite H1. rewrite H2.
    reflexivity.
Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + destruct b2.
      { right. reflexivity. }
      { discriminate H. }
  - intros [H | H].
    + rewrite H. reflexivity.
    + rewrite H. destruct b1.
      { reflexivity. }
      { reflexivity. }
Qed.
(* Exercise ends *)

(* Exercise: 1 star, standard (eqb_neq) *)
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H. apply not_true_iff_false in H.
    unfold not. intros Eq. apply H.
    rewrite Eq. apply eqb_refl.
  - intros H. apply not_true_iff_false.
    intros Heq. apply H. apply eqb_eq.
    apply Heq.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard (eqb_list) *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | _ , [] => false
  | [], _ => false
  | h1 :: t1, h2 :: t2 => if (eqb h1 h2) 
                          then eqb_list eqb t1 t2 
                          else false
  end.

Theorem eqb_list_true_iff:
  forall A (eqb : A -> A -> bool),
  (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb eqb_eq_iff l1. split.
  - generalize dependent l2. induction l1 as [|h1 l1' IHl1'].
    + intros l2 H. destruct l2 as [|h2 l2'].
      { reflexivity. }
      { simpl in H. discriminate H. }
    + intros l2 H. destruct l2 as [|h2 l2'].
      { simpl in H. discriminate H. }
      { destruct (eqb h1 h2) eqn:Eq.
        - simpl in H. rewrite Eq in H.
          apply eqb_eq_iff in Eq. rewrite Eq. f_equal.
          apply IHl1'. apply H.
        - simpl in H. rewrite Eq in H.
          discriminate H. }
  - generalize dependent l2. induction l1 as [|h1 l1' IHl1'].
    + intros l2 H. rewrite <- H. reflexivity.
    + intros l2 H. rewrite <- H.
      simpl. assert(Hrefl: eqb h1 h1 = true).
      { apply eqb_eq_iff. reflexivity. }
      rewrite Hrefl. apply IHl1'. reflexivity.
Qed.

(* Exercise: 2 stars, standard, especially useful (All_forallb) *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if (test h)
              then forallb test t
              else false
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
  - intros H. induction l as [|h l' IHl'].
    + simpl. reflexivity. 
    + simpl in H. assert (H': test h = true).
      { destruct (test h) eqn:E.
        - reflexivity.
        - apply H. }
      rewrite H' in H. simpl. split.
      { apply H'. }
      { apply IHl'. apply H. }
  - intros H. induction l as [|h l' IHl'].
    + simpl. reflexivity.
    + simpl in H. destruct H as [H1 H2]. 
      simpl. rewrite H1. apply IHl'. apply H2.
Qed.
(* Exercise ends *)

Definition excluded_middle := forall P : Prop, P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(* Exercise: 3 stars, standard (excluded_middle_irrefutable) *)
Theorem excluded_middle_irrefutable : forall P : Prop,
  ~~(P \/ ~P).
Proof.
  intros P. unfold not.
  intros H. apply H.
  right. intros HP.
  apply H. 
  left. apply HP.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, advanced (not_exists_dist) *)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X : Type) (P : X -> Prop),
  ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros exm X P H. unfold excluded_middle in exm. 
  intros x. destruct (exm (P x)) as [HP | HnP].
  - apply HP.
  - apply ex_falso_quodlibet.
    apply H. exists x. apply HnP.
Qed.
(* Exercise ends *)

(* Exercise: 5 stars, standard, optional (classical_axioms) *)
Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P : Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_to_perice :
  excluded_middle -> peirce.
Proof.
  unfold excluded_middle. unfold peirce.
  intros Hex P Q H.
  destruct (Hex P) as [HP | HnP].
  - apply HP.
  - apply H. intros HP.
    exfalso. apply HnP. apply HP. 
Qed.

Theorem peirce_to_double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
  unfold peirce. unfold double_negation_elimination.
  intros Hpei P HnnP. apply (Hpei P False).
  intros HnP. exfalso. apply HnnP.
  intros HP. apply HnP. apply HP.
Qed.

Theorem double_negation_elimination_to_de_morgan_not_and_not :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elimination. 
  unfold de_morgan_not_and_not.
  intros Hdne P Q H1. apply Hdne. intros H2. 
  apply de_morgan_not_or in H2. 
  apply H1. apply H2.
Qed.

Theorem de_morgan_not_and_not_to_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. unfold implies_to_or.
  intros Hdm P Q HPtoQ. apply Hdm. 
  intros [HnnP HnQ]. apply HnnP. intros HP.
  apply HnQ. apply HPtoQ. apply HP.
Qed.

Theorem implies_to_or_to_excluded_middle : 
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. unfold excluded_middle.
  intros Hion P. apply or_commut. apply Hion.
  intros HP. apply HP.
Qed.
(* Exercise ends *)