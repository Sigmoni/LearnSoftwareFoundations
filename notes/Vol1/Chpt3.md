# Chapter 3: Working with Structured Data

## Pair

Also known as product type

```coq
Inductive natprod : Type :=
  | pair (n1 n2 : nat)
```

## List

```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

## Option

```coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

## Partial Map

The `id` type serves as a wrapper.

```coq
Inductive id : Type :=
  | Id (n : nat).
```

And our `partial_map` use `id` as the key.

```coq
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
```