From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
  | <{ skip }> => st 
  | <{ l := a1 }> => 
      (l !-> aeval st a1; st)
  | <{ c1; c2 }> =>
      let st' := ceval_step1 st c1 in 
      ceval_step1 st' c2
  | <{ if b then c1 else c2 end }> =>
      if (beval st b) 
        then ceval_step1 st c1 
        else ceval_step1 st c2 
  | <{ while b1 do c1 end }> =>
      st (* bogus *)
  end.

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
    | <{ skip }> => st 
    | <{ l := a1 }> => 
        (l !-> aeval st a1; st)
    | <{ c1; c2 }> =>
        let st' := ceval_step2 st c1 i' in 
        ceval_step2 st' c2 i'
    | <{ if b then c1 else c2 end }> =>
        if (beval st b) 
          then ceval_step2 st c1 i'
          else ceval_step2 st c2 i'
    | <{ while b1 do c1 end }> =>
        if (beval st b1) 
        then let st' := ceval_step2 st c1 i' in 
             ceval_step2 st' c i'
        else st 
    end
  end.

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | <{ skip }> => Some st 
    | <{ l := a1 }> => 
        Some (l !-> aeval st a1; st)
    | <{ c1; c2 }> =>
        match (ceval_step3 st c1 i') with
        | Some st' => ceval_step3 st' c2 i' 
        | None => None 
        end
    | <{ if b then c1 else c2 end }> =>
        if (beval st b) 
          then ceval_step3 st c1 i'
          else ceval_step3 st c2 i'
    | <{ while b1 do c1 end }> =>
        if (beval st b1) 
        then match (ceval_step3 st c1 i') with
             | Some st' => ceval_step3 st' c i' 
             | None => None
             end
        else Some st
    end
  end.

Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
        | Some x => e2 
        | None => None
      end)
  (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
    | <{ skip }> => Some st
    | <{ l := a1 }> => Some (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> => LETOPT st' <== ceval_step st c1 i' IN
                       ceval_step st' c2 i'
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step st c1 i'
          else ceval_step st c2 i'
    | <{ while b1 do c1 end }> =>
        if (beval st b1)
        then LETOPT st' <== ceval_step st c1 i' IN
             ceval_step st' c i'
        else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
  test_ceval empty_st 
  <{ X := 2;
     if (X <= 1)
     then Y := 3
     else Z := 4
     end }>
  = Some(2, 0, 4).
Proof. reflexivity. Qed.

(* Exercise: 1 star, standard, optional (pup_to_n) *)
Definition pup_to_n : com :=
  <{  Y := 0;
      while (X > 0) do
        Y := Y + X;
        X := X - 1
      end }>.

Example pup_to_n_1:
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
(* End of the exercise *)

(* Exercise: 2 stars, standard, optional (peven) *)
Definition peven : com :=
  <{  Y := 0;
      while (X > Y) do
        Y := Y + 2
      end;
      if (X = Y)
      then Z := 0
      else Z := 1
      end }>.

Example peven_1:
  test_ceval (X !-> 5) peven
  = Some (5, 6, 1).
Proof. reflexivity. Qed.

Example peven_2:
  test_ceval (X !-> 6) peven
  = Some (6, 6, 0).
Proof. reflexivity. Qed.
(* End of the exercise *)

Theorem ceval_step__ceval : forall c st st',
  (exists i, ceval_step st c i = Some st') ->
  st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i'].
  - intros c st st' H. discriminate H.
  - intros c st st' H. 
    destruct c; simpl in H; inversion H; subst; clear H.
    + apply E_Skip.
    + apply E_Asgn. reflexivity.
    + destruct (ceval_step st c1 i') eqn:Heqr1.
      * apply E_Seq with s; apply IHi'; assumption.
      * discriminate.
    + destruct (beval st b) eqn:Heqr.
      * apply E_IfTrue; try apply IHi'; assumption.
      * apply E_IfFalse; try apply IHi'; assumption.
    + destruct (beval st b) eqn:Heqr.
      * destruct (ceval_step st c i') eqn:Heqr1.
        { apply E_WhileTrue with s; try apply IHi'; assumption. }
        { discriminate. }
      * injection H1 as H2. rewrite <- H2.
        apply E_WhileFalse. assumption.
Qed.

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - simpl in Hceval. discriminate.
  - destruct i2 as [|i2']. 
    + inversion Hle.
    + assert (Hle': i1' <= i2') by lia.
      destruct c.
      * simpl in Hceval. inversion Hceval. reflexivity.
      * simpl in Hceval. inversion Hceval. reflexivity.
      * simpl in Hceval. simpl.
        destruct (ceval_step st c1 i1') eqn:Heqr1.
        { apply (IHi1' i2') in Heqr1; try assumption.
          rewrite Heqr1. 
          apply (IHi1' i2') in Hceval; assumption. }
        { discriminate. }
      * simpl in Hceval. simpl. 
        destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.
      * simpl in Hceval. simpl.
        destruct (beval st b); try assumption.
        destruct (ceval_step st c i1') eqn:Heqr1.
        { apply (IHi1' i2') in Heqr1; try assumption.
          rewrite -> Heqr1.
          apply (IHi1' i2') in Hceval; try assumption. }
        { discriminate. }
Qed.