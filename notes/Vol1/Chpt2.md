# Chapter 2: Proof by Induction

## Induction

Recall the principle of induction over natural numbers. To proof $P(n)$ holds for all $n \in \mathbb N$. We can :

* Proof that $P(0)$ holds.
* Proof for any $n'$, if $P(n')$ holds, then $P(n'+1)$ holds.
* Conclude that $P(n)$ holds for all $n \in \mathbb N$

The `induction` tactic seems just like `destruct`:

```coq
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) 
    reflexivity.
  - (* n = S n' *) 
    (* IHn': n' + 0 = n' *)
    simpl. rewrite → IHn'. reflexivity. 
Qed.
```
The `IHn'` records the hypothesis that the theorem holds for `n'`.

## Assert & Replace

Some times, we need some simple lemma, we can use `assert` tactic to create a sub-theorem. 

```coq
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) × m = n × m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { rewrite add_comm. simpl. 
    rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.
```

Simply use `rewrite` tactic may cause unexpected behaviour. We can use `assert` for precise manipulation.

```coq
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. 
Qed.
```

For such propose, we can also use `replace` tactic. Doing so will add a sub-goal after the current goal.

```coq
Theorem plus_rearrange' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  replace (n + m) with (m + n).
  reflexivity.
  
  (* To proof n + m = m + n *)
  rewrite add_comm. reflexivity.
Qed.
```