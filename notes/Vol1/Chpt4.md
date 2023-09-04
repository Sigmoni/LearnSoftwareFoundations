# Chapter 4: Ploymorphism and Higher-Order Functions

## Declare a type to be polymorhic

Simply adding a type argument should help:

```coq
Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
```
The `Arguments` directive specifies the name of the function and then lists the argument names to be treated as implicit.

```coq
Arguments nil {X}.
Arguments cons {X}.
``` 

Using curly braces in declarations can also make the type implicit.

```coq
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
```

## Higher Functions

Declare an anonymous function by using `fun`

```coq
fun x => x * x
```

We can pass function like other arguments:

```coq
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
```

## Church Numerals

We discover that the times a fuction is applied to some element has the dual form with natural numbers. (Since natural numbers is defined by how many times constructor `S()` is applied.)

```coq
Definition cnat := forall X : Type, (X -> X) -> X -> X.
```

Thus natural numbers can be describes as below for any `fun X f x`

```coq
Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
```

We can define some basic computation:

```coq
Definition scc (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (f x).

Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
```

Furthermore, the form of `n : cnat` can be seen as some projection from function `f : X -> X` to `fn : X -> X` which performs the original function `n` times.

If we consider the type of `cnat` to be `X -> X`, we get the exponential function:

```coq
Definition exp (n m : cnat) : cnat :=
  fun (X : Type) => m (X -> X) (n X).
```