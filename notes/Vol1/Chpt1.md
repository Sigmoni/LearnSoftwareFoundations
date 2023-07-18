# Chapter 1: Functional Programming in Coq

## Types and Functions

Enumerated types are built using multiple value constructors:

```coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```
A function can be defined using either `Definiton` :

```coq
Definition minustwo (n :nat) : nat :=
  match n with
  | O => O 
  | S O => O 
  | S (S n') => n'
  end.
```

rr recursively defined using `Fixpoint` :

```coq
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n' 
  end.
```
## Pattern Matching

As seen above, pattern matching is useful to break down situations. It can be used on any expression:

```coq
match (a =? b) with
| true => false 
| false => true
```
## Notation

Notations make expressions easier to read and write.

```coq
Notation "x + y" := 
  (plus x y)
  (at level 50, left associativity)
  : nat_scope.
```
Some notes:

* Level : the precedence level
* Associativity : options are `left`, `right` and `no` 
* Scope : which scope it shall apply to.

## Theorems and Proof

Theorems are defined straight forward :
```coq
Theorem plus_O_n : forall n : nat, 0 + n = n.
```
And it allways followed by its proof. A proof always starts with `Proof` and end up with `Qed`. 

```coq
Proof.
  intros n. 
  simpl.
  reflexivity.
Qed.
```
### Tactics 

What in between the `Proof` and `Qed` are tactics. I'll explain their usage using informal proof.

```coq
(* Proof of ∀ n : nat, 0 + n = n *)
Proof.
  (* Assume that n is some natural number *)
  intros n. 
  (* n is now in context, the goal becomes 0 + n = n *)

  (* According to definition of '+', we simplify 0 + n to n *)
  simpl.
  (* The goal becomes n = n *)

  (* Since both sides of the equation are the same, 
  thus the equation holds.
  And our goal is proved *)
  reflexivity.
Qed.
```
#### Rewrite

We can use `rewrite` to make use of some known equations (hypothesis or proofed theorems).

```coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.

  (* move the hypothesis into the context: *)
  intros H.

  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  (* the '->' replace all 'n' with 'm' *)

  reflexivity. 
Qed.
```
The arrow decides with side to be replaced.

#### Destruct

We can use `destruct` for case analysis. 

```coq
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = O *)
    reflexivity.
  - (* n = S n' *)
    reflexivity. 
Qed.
```
Without case analysis, the form of `n` is ambiguous, and the goal cannot be further simplfied.