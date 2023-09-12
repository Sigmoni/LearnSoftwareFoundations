# Chapter 5: More Basic Tatics

## The `apply` tatic

The `apply` tatic can prove the goal using existing theorems or hypothesis.

```coq
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  (* eq: n = m *)
  intros n m eq.
  (* rewrite eq. reflexitivity. *)
  apply eq.
Qed.
```

The `apply` tatic matches every token strictly thus in certain occations we need to manually assign variables to each token using `apply with` tatic.

```coq
Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2.
  reflexivity. 
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* CoQ cannot resolve the token 'm' from context *)
  (* We should manually assign one *)
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2. 
Qed.
```

## The `transitivity` tatic

There is a built-in tatic `transitivity` which performs exactly like `apply trans_eq with`.

```coq
Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c; d].
  apply eq1. apply eq2. 
Qed.
```
## The `injection` and `discriminate` tatic

Due to the type system of `Coq`, value constructors are "injective", thus we have:

```coq
S n = S m -> n = m
```

On the other hand, this also means that `S n` can never be equal to `O`。

We can use `injection` to subtract such equality.

```coq
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* H: S n = S m *)
  (* Hnm : N = m *)
  injection H as Hnm. apply Hnm.
Qed.
```

Aslo, we can use `discriminate` to reject contradict hypothesis.

```coq
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. 
Qed.
```

## The `f_equal` tatic

Functions are injective by nature:

```coq
Theorem f_equal: forall X Y (n m : X) (f : X -> Y),
  n = m -> f n = f m.
```

We can make use of such theorem by using `f_equal` tatic:

```coq
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
  intros n m H. 
  f_equal. apply H. 
Qed.
```

