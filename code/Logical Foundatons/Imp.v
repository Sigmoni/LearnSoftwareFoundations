Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
Set Default Goal Selector "!".

Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat) 
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTure
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b1 : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n 
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTure => true
  | BFalse => false 
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n 
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - reflexivity.
  - destruct a1 eqn:Ea1.
    + destruct n eqn:En.
      * simpl. apply IHa2.
      * simpl. rewrite IHa2. reflexivity.
    + simpl. simpl in IHa1. 
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1. 
      rewrite IHa2.
      reflexivity.
    + simpl. simpl in IHa1.
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem silly1 : forall (P : Prop),  P -> P.
Proof.
  intros P HP.
  try reflexivity.
  apply HP.
Qed.

Theorem silly2 : forall ae, aeval ae = aeval ae.
Proof.
  try reflexivity.
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n; 
  simpl; 
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1 eqn:Ea1;
      try (simpl; simpl in IHa1; rewrite IHa1; 
           rewrite IHa2; reflexivity).
    + destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.
Qed. 

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - destruct a1 eqn:Ea1;
      try (simpl; simpl in IHa1; rewrite IHa1; 
           rewrite IHa2; reflexivity).
    + destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.
Qed. 

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(* Exercise: 3 stars, standard (optimize_0plus_b_sound) *)
Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTure => BTure
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b, 
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b. 
  induction b;
    try reflexivity;
    try (simpl; repeat rewrite optimize_0plus_sound; reflexivity).
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
(* Exercise ends *)

Ltac invert H :=
  inversion H; subst; clear H.

Lemma invert_example1 : forall {a b c : nat}, [a;b] = [a;c] -> b = c.
Proof.
  intros. 
  invert H.
  reflexivity.
Qed.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
  m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
  m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : aevalR (ANum n) n 
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End HypothesisNames.

Notation "e '==>' n" 
         := (aevalR e n) 
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - intros H. 
    induction H; simpl.
    + reflexivity.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
    + rewrite IHaevalR1.
      rewrite IHaevalR2.
      reflexivity.
  - generalize dependent n.
    induction a; simpl; intros; subst.
    + apply E_ANum.
    + apply E_APlus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + apply E_AMinus.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
    + apply E_AMult.
      * apply IHa1. reflexivity.
      * apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  - intros H. induction H; subst; reflexivity.
  - generalize dependent n. induction a; 
    simpl; intros; subst; constructor; 
    try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* Exercise: 3 stars, standard (bevalR) *)
Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTure ==>b true
  | E_BFalse : BFalse ==>b false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) ->
    (e2 ==> n2) ->
    (BEq e1 e2) ==>b (n1 =? n2)
  | E_BNeq (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) ->
    (e2 ==> n2) ->
    (BNeq e1 e2) ==>b (negb (n1 =? n2))
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) ->
    (e2 ==> n2) ->
    (BLe e1 e2) ==>b (n1 <=? n2)
  | E_BGt (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) ->
    (e2 ==> n2) ->
    (BGt e1 e2) ==>b (negb(n1 <=? n2))
  | E_BNot (e1 : bexp) (b1 : bool) :
    (e1 ==>b b1) ->
    (BNot e1) ==>b (negb b1)
  | E_BAnd (e1 e2 : bexp) (b1 b2 : bool) :
    (e1 ==>b b1) ->
    (e2 ==>b b2) ->
    (BAnd e1 e2) ==>b (b1 && b2)
where "e '==>b' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.
Proof.
  intros. split.
  - intros H. induction H;
      try reflexivity;
      try (simpl; apply aeval_iff_aevalR in H; rewrite H;
      apply aeval_iff_aevalR in H0; rewrite H0; reflexivity).
    + simpl. rewrite IHbevalR. reflexivity.
    + simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
  - generalize dependent bv. induction b;
    simpl; intros; subst; constructor;
    try (apply aeval_iff_aevalR);
    try (apply IHb);
    try (apply IHb1);
    try (apply IHb2);
    reflexivity.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat) 
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Reserved Notation "e '==>' n" 
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)
  | E_ADiv (e1 e2 : aexp) (n1 n2 n3 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (n2 > 0) ->
      (mult n2 n3 = n1) ->
      (ADiv e1 e2) ==> n3  
  where "e '==>' n" := (aevalR e n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny 
  | ANum (n : nat) 
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_AAny (n : nat) :
      AAny ==> n
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.

End aevalR_extended.


Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) 
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n 
  | AId x => st x 
  | <{ a1 + a2 }> => (aeval st a1) + (aeval st a2)
  | <{ a1 - a2 }> => (aeval st a1) - (aeval st a2)
  | <{ a1 * a2 }> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *)
               (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

Example aexp1 : 
  aeval (X !-> 5) <{ 3 + (X * 2) }> 
  = 13.
Proof. reflexivity. Qed.

Example aexp2 : 
  aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }> 
  = 20.
Proof. reflexivity. Qed.

Example bexp1 : 
  beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof. reflexivity. Qed.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do 
       Y := Y * Z;
       Z := Z - 1
     end }>.

(* Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.

Print example_bexp.

Set Printing Coercions.
Print example_bexp.

Print fact_in_coq.
Unset Printing Coercions. *)

(* Locate aexp.
Locate "&&".
Locate ";".
Locate "while". *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.
     
Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

Definition loop : com :=
  <{ while true do 
       skip 
     end }>.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> => st 
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st) 
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in 
        ceval_fun_no_while st' c2 
    | <{ if b then c1 else c2 end }> =>
        if (beval st b) 
          then ceval_fun_no_while st c1 
          else ceval_fun_no_while st c2 
    | <{ while b do c end }> =>
        st 
  end.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st 
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st'' 
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st' 
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' -> 
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st 
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st =[ while b do c end ]=> st'' 
  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1 : 
  empty_st =[
    X := 2;
    if (X <= 1) 
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* Exercise: 2 stars, standard (ceval_example2) *)
Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2; Y !-> 1; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Asgn. reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0).
    + apply E_Asgn. reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* Set Printing Implicit.
Check @ceval_example2. *)

(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (pup_to_n) *)
Definition pup_to_n : com :=
  <{ Y := 0;
     while X <> 0 do 
       Y := Y + X;
       X := X - 1
     end }>.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3; X !-> 1; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0; X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_WhileTrue with (st' := (X !-> 1; Y !-> 2 ; Y !-> 0 ; X !-> 2)).
    + reflexivity.
    + apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
      * apply E_Asgn. reflexivity.
      * apply E_Asgn. reflexivity.
    + apply E_WhileTrue with (st' := (X !-> 0 ; Y !-> 3; X !-> 1; Y !-> 2 ; Y !-> 0 ; X !-> 2)).
      * reflexivity.
      * apply E_Seq with (Y !-> 3; X !-> 1; Y !-> 2 ; Y !-> 0 ; X !-> 2); apply E_Asgn; reflexivity.
      * apply E_WhileFalse. reflexivity.
Qed.
(* End of exercise *)
        
Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption. 
Qed.

Theorem plus2_spec: forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. 
  clear Heval. simpl. 
  apply t_update_eq. 
Qed.

(* Exercise: 3 stars, standard, especially useful (loop_never_stops) *)
Theorem loop_never_stops: forall st st',
  ~(st =[loop]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef eqn:Heqloopdef.
  induction contra; try discriminate.
  - inversion Heqloopdef. subst b. discriminate.
  - inversion Heqloopdef. subst b. subst c.
    apply IHcontra2. reflexivity.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard (no_whiles_eqv) *)
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> => true
  | <{ _ := _ }> => true
  | <{ c1 ; c2 }> => 
      (no_whiles c1) && (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      (no_whiles ct) && (no_whiles cf)
  | <{ while _ do _ end }> => false
  end.

Inductive no_whilesR : com -> Prop :=
  | no_whiles_Skip : no_whilesR <{ skip }>
  | no_whiles_Asgn : forall x a, no_whilesR <{ x := a }>
  | no_whiles_Seq : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR <{ c1 ; c2 }>
  | no_whiles_If : forall b ct cf, no_whilesR ct -> no_whilesR cf -> no_whilesR <{ if b then ct else cf end }>.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intros c. split.
  - intros H. induction c.
    + apply no_whiles_Skip.
    + apply no_whiles_Asgn.
    + simpl in H. rewrite andb_true_iff in H.
      destruct H as [H1 H2].
      apply no_whiles_Seq.
      * apply IHc1. apply H1.
      * apply IHc2. apply H2.
    + simpl in H. rewrite andb_true_iff in H.
      destruct H as [H1 H2].
      apply no_whiles_If.
      * apply IHc1. apply H1.
      * apply IHc2. apply H2.
    + discriminate.
  - intros H. induction c.
    + reflexivity.
    + reflexivity.
    + simpl. apply andb_true_iff.
      inversion H. split.
      * apply IHc1. apply H2.
      * apply IHc2. apply H3.
    + simpl. apply andb_true_iff.
      inversion H. split.
      * apply IHc1. apply H2.
      * apply IHc2. apply H4.
    + inversion H.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, standard (no_whiles_terminating) *)
Theorem no_whiles_terminating:
  forall c, no_whilesR c -> forall st, exists st', st =[ c ]=> st'.
Proof.
  intros c H. 
  induction c.
  - intros st. exists st. constructor.
  - intros st. exists (x !-> (aeval st a) ; st). 
    constructor. reflexivity.
  - intros st. inversion H. subst. clear H.
    assert (H : exists st', st =[ c1 ]=> st').
    { apply IHc1. assumption. }
    destruct H as [st' H'].
    assert (H: exists st'', st' =[ c2 ]=> st'').
    { apply IHc2. assumption. }
    destruct H as [st'' H''].
    exists st''.
    apply E_Seq with st'.
    + apply H'.
    + apply H''.
  - intros st. inversion H. subst. clear H.
    destruct (beval st b) eqn:E.
    + assert (H: exists st', st =[ c1 ]=> st').
      { apply IHc1. apply H2. }
      destruct H as [st' H].
      exists st'. apply E_IfTrue.
      * apply E.
      * apply H.
    + assert (H: exists st', st =[ c2 ]=> st').
      { apply IHc2. apply H4. }
      destruct H as [st' H].
      exists st'. apply E_IfFalse.
      * apply E.
      * apply H.
  - intros st. inversion H.
Qed.

(* Exercise: 3 stars, standard (stack_compiler) *)
Inductive sinstr : Type :=
  | SPush (n : nat)
  | SLoad (x : string)
  | SPlus 
  | SMinus 
  | SMult.

Fixpoint s_execute (st : state) (stack : list nat) 
                   (prog : list sinstr)
                  : list nat :=
  match prog with
  | sym :: prog => match sym with
                   | SPush n => s_execute st (n :: stack) prog 
                   | SLoad x => s_execute st (st x :: stack) prog
                   | SPlus => match stack with
                              | a :: b :: stack => s_execute st (b + a :: stack) prog
                              | _ => s_execute st stack prog 
                              end   
                   | SMinus => match stack with
                               | a :: b :: stack => s_execute st (b - a :: stack) prog
                               | _ => s_execute st stack prog 
                               end   
                   | SMult => match stack with
                              | a :: b :: stack => s_execute st (b * a :: stack) prog
                              | _ => s_execute st stack prog 
                              end   
                   end
  | [] => stack
  end.

Example s_execute1 :
    s_execute empty_st []
      [SPush 5; SPush 3; SPush 1; SMinus]
    = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
    s_execute (X !-> 3) [3;4]
      [SPush 4; SLoad X; SMult; SPlus]
    = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard (execute_app) *)
Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  intros st p1 p2.
  induction p1 as [| s p1].
  - simpl. reflexivity.
  - intros stack. destruct s; try simpl; try apply IHp1; 
      (destruct stack; [apply IHp1 | destruct stack; try apply IHp1]).
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard (stack_compiler_correct) *)
Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros st e. induction e; try reflexivity;
  intros stack; simpl; rewrite app_assoc;
  rewrite execute_app; rewrite execute_app;
  rewrite IHe1; rewrite IHe2; reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. apply s_compile_correct_aux.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (short_circuit) *)
Fixpoint beval_short_circuit (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval_short_circuit st b1)
  | <{b1 && b2}>  => match beval_short_circuit st b1 with
                     | false => false
                     | true => beval_short_circuit st b2
                     end
  end.
(* Exercise ends *)

Module BreakImp.

(* Exercise: 4 stars, advanced (break_imp) *)
Inductive com : Type :=
  | CSkip
  | CBreak (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).
Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue 
  | E_Break : forall st,
      st =[ break ]=> st / SBreak 
  | E_Asgn : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SContinue
  | E_Seq1 : forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak ->
      st =[ c1; c2 ]=> st' / SBreak
  | E_Seq2 : forall c1 c2 st st' st'' s,
      st =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s ->
      st =[ c1; c2 ]=> st'' / s 
  | E_IfTrue : forall c1 c2 b st st' s,
      beval st b = true ->
      st =[ c1 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s 
  | E_IfFalse : forall c1 c2 b st st' s,
      beval st b = false ->
      st =[ c2 ]=> st' / s ->
      st =[ if b then c1 else c2 end ]=> st' / s 
  | E_WhileTrue1 : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
      st =[ while b do c end ]=> st' / SContinue
  | E_WhileTrue2 : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' / SContinue ->
      st' =[ while b do c end ]=> st'' / SContinue ->
      st =[ while b do c end ]=> st'' / SContinue
  | E_WhileFalse : forall st b c,
      beval st b = false ->
      st =[ while b do c end ]=> st / SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').  

Theorem break_ignore : forall c st st' s,
  st =[ break; c ]=> st' / s ->
  st = st'.
Proof.
  intros. inversion H.
  - subst. inversion H5. subst. reflexivity.
  - subst. inversion H2. 
Qed.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros. inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros b c st st' H0 H1.
  apply E_WhileTrue1.
  - apply H0.
  - apply H1.
Qed.

Theorem seq_continue: forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1; c2 ]=> st'' / SContinue.
Proof.
  intros. apply E_Seq2 with st'.
  - apply H.
  - apply H0.
Qed.

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1; c2 ]=> st' / SBreak.
Proof.
  intros. apply E_Seq1. apply H.
Qed.
(* End of exercise *)

(* Exercise: 3 stars, advanced, optional (while_break_true) *)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros. remember <{ while b do c end }> as whiledef.
  induction H; 
    try discriminate; 
    try injection Heqwhiledef as Hb Hc; 
    try subst.
  - exists st. apply H1.
  - apply IHceval2.
    + reflexivity.
    + apply H0.
  - rewrite H in H0. discriminate.
Qed.
(* Exercise ends *)

(* Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c : com) st st1 st2 s1 s2,
  st =[ c ]=> st1 / s1 ->
  st =[ c ]=> st2 / s2 ->
  st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent st2.
  generalize dependent s2.
  induction E1;
    intros s2 st2 E2;
    inversion E2;
    subst;
    try (split; reflexivity);
    try (apply IHE1; assumption);
    try (rewrite H in H0; discriminate).
  - apply IHE1 in H1. destruct H1 as [H1 Contra]. discriminate.
  - apply IHE1_1 in H4. destruct H4 as [H4 Contra]. discriminate.
  - apply IHE1_1 in H1. destruct H1 as [H1 Fact]. 
    symmetry in H1. subst. apply IHE1_2. apply H5.
  - rewrite H in H6. discriminate.
  - rewrite H in H6. discriminate.
  - apply IHE1 in H6. destruct H6 as [H6 Fact]. split.
    + apply H6.
    + reflexivity.
  - apply IHE1 in H3. destruct H3 as [H3 Contra]. discriminate.
  - rewrite H in H5. discriminate.
  - apply IHE1_1 in H6. destruct H6 as [H6 Contra]. discriminate.
  - apply IHE1_1 in H3. destruct H3 as [H3 Fact]. 
    clear Fact. symmetry in H3. subst. 
    apply IHE1_2 in H7. destruct H7 as [H7 Fact].
    clear Fact. split.
    + apply H7.
    + reflexivity.
  - rewrite H in H5. discriminate.
  - rewrite H in H2. discriminate.
  - rewrite H in H2. discriminate.
Qed.
(* End of exercise *)
End BreakImp.