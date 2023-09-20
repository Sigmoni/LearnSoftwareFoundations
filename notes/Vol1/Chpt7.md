# Chapter 7: Inductively Defined Propositions

## Inductively defined proposition

Take a closer look at the proposition claiming that `n` is even:

1. $\exists x, n = 2 x$
2. $\mathrm{even}(n - 2) \to \mathrm{even}(n)$

For the second definition, we can define:

```coq
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
```

Note that we use `ev : nat -> Prop` instead using `ev (n : nat) : Prop`. This suggests that `ev : nat -> Prop` is a CoQ proposition with "evidence constructors" `ev_0 : ev 0` and `ev_SS : forall n, ev n -> ev (S (S n))`.

