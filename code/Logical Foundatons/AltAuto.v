Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality,-deprecated-syntactic-definition,-deprecated]".
From Coq Require Import Arith List.
From LF Require Import IndProp.

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. apply MEmpty.
  - simpl. apply MChar.
  - simpl. destruct re1.
    + apply MApp; assumption.
    + inversion Hmatch1. simpl. assumption.
    + apply MApp; assumption.
    + apply MApp; assumption.
    + apply MApp; assumption.
    + apply MApp; assumption.
  - simpl. apply MUnionL. assumption.
  - simpl. apply MUnionR. assumption.
  - simpl. apply MStar0.
  - simpl. apply MStarApp; assumption.
Qed.

(* Exercise: 3 stars, standard (try_sequence) *)
Theorem andb_eq_ord:
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros.
  destruct b; 
  destruct c; 
  try reflexivity; 
  try discriminate.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n;
  simpl;
  try rewrite IHn;
  reflexivity.
Qed.

Fixpoint nonzeros (lst : list nat) :=
  match lst with 
  | [] => []
  | 0 :: t => nonzeros t 
  | h :: t => h :: nonzeros t 
  end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof.
  intros.
  induction lst1;
  try (destruct x; simpl; rewrite IHlst1);
  reflexivity.
Qed.
(* End of the exercise *)

Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2]; simpl.
  - apply MEmpty.
  - apply MChar.
  - destruct re1; try (apply MApp; assumption); 
    try (inversion Hmatch1; simpl; assumption).
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
  - apply MStar0.
  - apply MStarApp; assumption.
Qed.

Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [reflexivity | simpl; rewrite IHlst1; reflexivity].
Qed.

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [idtac | simpl; rewrite IHlst1];
    reflexivity.
Qed.

(* Exercise: 1 star, standard (notry_sequence) *)
Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros; induction n; simpl;
  [idtac | rewrite IHn];
  reflexivity.
Qed.
(* End of the exercise *)

Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2]; simpl.
  - apply MEmpty.
  - apply MChar.
  - destruct re1; 
    try (apply MApp; [apply IH1 | apply IH2]).
    inversion Hmatch1. simpl. assumption.
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
  - apply MStar0.
  - apply MStarApp; assumption.
Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.


Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(* Exercise: 1 star, standard (ev100) *)
Theorem ev100 : ev 100.
Proof.
  repeat (right; try apply ev_0).
Qed.
(* End of the exericse *)

(* Exercise: 4 stars, standard (re_opt) *)
Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.

Lemma re_opt_match: forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2]; simpl.
  - apply MEmpty.
  - apply MChar.
  - destruct re1; 
    try (inversion IH1; simpl; destruct re2; assumption);
    destruct re2;
    try (inversion IH2; rewrite app_nil_r; assumption);
    apply MApp; assumption.
  - destruct re1; inversion IH;
    destruct re2; try apply MUnionL;
    subst; assumption.
  - destruct re1; try assumption;
    destruct re2; 
    try (apply MUnionR; assumption);
    inversion IH.
  - destruct re; 
    try apply MEmpty; 
    try apply MStar0.
  - destruct re; 
    try (apply star_app; [apply MStar1; apply IH1 | apply IH2]);
    inversion IH1; inversion IH2; apply MEmpty.
Qed.
    
From Coq Require Import Lia.

Theorem lia_succeed1 : forall (n : nat),
  n > 0 -> n * 2 > n.
Proof.
  lia.
Qed.

Theorem lia_succeed2 : forall (n m : nat),
  n * m = m * n.
Proof.
  lia.
Qed.

Theorem lia_fail1 : 0 = 1.
Proof. 
  Fail lia.
Abort.

Theorem lia_fail2 : forall (n : nat),
  n >= 1 -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof.
  Fail lia.
Abort.

Require Import Ring.

Theorem mult_comm : forall (n m : nat),
  n * m = m * n.
Proof.
  intros. ring.
Qed.

Theorem eq_example1:
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem eq_example1':
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.

Theorem eq_example2 : forall (n m o p : nat),
  n = m -> 
  o = p ->
  (n , o) = (m, p).
Proof.
  congruence.
Qed.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
  [] <> h :: t.
Proof.
  congruence.
Qed.

Theorem intuition_succeed1 : forall (P : Prop),
  P -> P.
Proof. intuition. Qed.

Theorem intuition_succeed2 : forall (P Q : Prop),
  ~ (P \/ Q) -> ~P /\ ~Q.
Proof. intuition. Qed.

Theorem intuition_simplify1 : forall (P : Prop),
  ~~P -> P.
Proof. intuition. Abort.

Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  Fail congruence.
  intuition.
  congruence.
Qed.

Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  intuition congruence.
Qed.

(* Exercise: 2 stars, standard (automatic_solvers) *)
Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. 
  congruence.
Qed.

Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. 
  lia.
Qed.

Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof. 
  intuition.
Qed.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. 
  intuition.
Qed.

Example auto_example_1 : forall (P Q R : Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3. 
  apply H2. apply H1. apply H3.
Qed.

Example auto_example_1' : forall (P Q R : Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof. auto. Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

