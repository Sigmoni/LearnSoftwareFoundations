Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.

(* Exercise: 2 stars, standard (eight_is_even) *)
Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).
(* Exercise ends *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Definition add1 : nat -> nat.
intro n.
apply S.
apply n.
Defined.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros. destruct H as [HP HQ].
  apply HP.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* Exercise: 2 stars, standard (conj_fact) *)
Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R HPQ HQR => conj (proj1 P Q HPQ) (proj2 Q R HQR).
(* Exercise ends *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q 
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP.
  left. apply HP.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP 
    | or_intror HQ => HQR HQ 
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(* Exercise: 2 stars, standard (or_commut') *)
Definition or_commut' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q HPQ => 
    match HPQ with
    | or_introl HP => or_intror HP 
    | or_intror HQ => or_introl HQ
    end.
(* Exercise ends *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" := 
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise: 2 stars, standard (ex_ev_Sn) *)
Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 3 (ev_SS 2 (ev_SS 0 ev_0)).
(* Exercise ends *)

Inductive True : Prop :=
  | I : True.

(* Exercise: 1 star, standard (p_implies_true) *)
Definition p_implies_true : forall P, P -> True :=
  fun P HP => I.
(* Exercise ends *)

Inductive False : Prop := .

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(* Exercise: 1 star, standard (ex_falso_quodlibet') *)
Definition ex_falso_quodlibet' : forall P, False -> P :=
  fun P contra => match contra with end.
(* Exercise ends *)

End Props.

Module EqualityPlayground.

Inductive eq {X : Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
  (at level 70, no associativity)
  : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=  
  eq_refl 4.

Definition singleton : forall (X : Type) (x : X), [] ++ [x] == x :: [] :=
  fun (X : Type) (x : X) => eq_refl [x].

Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(* Exercise: 2 stars, standard (eq_cons) *)
Definition eq_cons : forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
  h1 == h2 -> t1 == t2 -> h1 :: t1 == h2 :: t2 :=
  fun X h1 h2 t1 t2 Hh Ht =>
    match Hh with
    | eq_refl h => 
        match Ht with
        | eq_refl t => eq_refl (h :: t)
        end 
    end.
(* Exercise ends *)

(* Exercise: 2 stars, standard (equality__leibniz_equality) *)
Lemma equality__leibniz_equality : forall (X : Type) (x y : X),
  x == y -> forall (P : X -> Prop), P x -> P y.
Proof.
  intros. destruct H. apply H0.
Qed.
(* Exercise ends *)

(* Exercise: 2 stars, standard (equality__leibniz_equality_term) *)
Definition equality__leibniz_equality_term : forall (X : Type) (x y : X),
  x == y -> forall P : (X -> Prop), P x -> P y :=
  fun (X : Type) (x y : X) Heq =>
    match Heq with
    | eq_refl n => fun P H => H 
    end.
(* Exercise ends *)

(* Exercise: 3 stars, standard, optional (leibniz_equality__equality) *)
Lemma leibniz_equality__equality : forall (X : Type) (x y : X),
  (forall P : X -> Prop, P x -> P y) -> x == y.
Proof.
  intros. 
  apply H. apply eq_refl.
Qed.
(* Exercise ends *)

End EqualityPlayground.

(* Exercise: 2 stars, standard (and_assoc) *)
Definition and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R 
  :=
  fun P Q R H =>
    match H with 
    | conj HP HQR => match HQR with
                     | conj HQ HR => conj (conj HP HQ) HR 
                     end
    end.
(* Exercise ends *)

(* Exercise: 3 stars, standard (or_distributes_over_and) *)
Definition or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R) 
  :=
  fun P Q R =>
    conj (fun H => 
            match H with
            | or_introl HP => conj (or_introl HP) (or_introl HP)
            | or_intror HQR =>
              match HQR with
              | conj HQ HR => conj (or_intror HQ) (or_intror HR)
              end
            end)
         (fun H => 
            match H with
            | conj HPnQ HPnR => 
              match HPnQ with
              | or_introl HP => or_introl HP 
              | or_intror HQ => 
                match HPnR with
                | or_introl HP => or_introl HP 
                | or_intror HR => or_intror (conj HQ HR) 
                end 
              end 
            end).
(* Exercise ends *)

(* Exercise: 3 stars, standard (negations) *)
Definition double_neg : forall P : Prop,
  P -> ~~P := fun P HP H => H HP.

Definition contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q 
  :=
  fun P Q H =>
    match H with
    | conj HP HnP => match HnP HP with end 
    end. 

Definition de_morgan_not_or : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q 
  :=
  fun P Q H => 
    conj (fun HP => H (or_introl HP)) 
         (fun HQ => H (or_intror HQ)).
(* Exercise ends *)

(* Exercise: 2 stars, standard (currying) *)
Definition curry : forall P Q R : Prop,
  ((P /\ Q) -> R) -> (P -> (Q -> R))
  :=
  fun P Q R H HP HQ => H (conj HP HQ).

Definition uncurry : forall P Q R : Prop,
  (P -> (Q -> R)) -> ((P /\ Q) -> R) 
  := 
  fun P Q R H HPQ => 
    match HPQ with
    | conj HP HQ => H HP HQ 
    end.
(* Exercise ends *)

Definition propositional_extensionality : Prop :=
  forall (P Q : Prop), (P <-> Q) -> P = Q.

(* Exercise: 1 star, advanced (pe_implies_or_eq) *)
Theorem pe_implies_or_eq : 
  propositional_extensionality -> 
  forall (P Q : Prop), (P \/ Q) = (Q \/ P).
Proof.
  intros. apply H. split.
  - intro HPQ. destruct HPQ as [HP | HQ].
    + right. apply HP.
    + left. apply HQ.
  - intro HQP. destruct HQP as [HQ | HP].
    + right. apply HQ.
    + left. apply HP.
Qed.
(* Exercise ends *)

(* Exercise: 1 star, advanced (pe_implies_true_eq) *)
Lemma pe_implies_true_eq : 
  propositional_extensionality ->
  forall (P : Prop), P -> True = P.
Proof.
  intros HPE P HP.
  apply HPE. split.
  - intros HT. apply HP.
  - intros HP'. reflexivity.
Qed.
(* Exercise ends *)

(* Exercise: 3 stars, advanced (pe_implies_pi) *)
Definition proof_irrelevance : Prop :=
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality -> proof_irrelevance.
Proof.
  intros HPE P pf1 pf2.
  remember (pe_implies_true_eq HPE P pf1) as HPT.
  destruct HPT.
  destruct pf1.
  destruct pf2.
  reflexivity.
Qed.
(* Exercise ends *)