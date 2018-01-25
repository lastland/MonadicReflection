From mathcomp Require Import ssreflect ssrnat ssrbool.
From MonadicEffect Require Import Trees.

Require Import Program.

Module Pure.

  Program Definition Pure A (wp : (A -> Prop) -> Prop) :=
     forall p, { a : A | wp p -> p a }.

  Program Definition ret { A } (a : A) :
    Pure A (fun p => p a) :=
    fun _ => a.
  
  Program Definition bind : forall A wp1 B wp2,
      Pure A wp1 -> (forall a : A, Pure B (wp2 a)) ->
      Pure B (fun p => wp1 (fun a => wp2 a p)) :=
    fun A wp1 B wp2 c1 c2 p =>
      let: a := c1 (fun x => wp2 x p) in c2 a p.
  Next Obligation.
    elim: c1 H => a' H' /= H.
    elim: c2 H => a'' H'' /= H.
    apply H''. by apply H'.
  Defined.
End Pure.

Program Definition sqr (x : nat) : Pure.Pure nat (fun p => forall y, p y) :=
  Pure.ret (x * x).

Module DST.

  Section DST.
  Variables S : Set.

  Definition WP {A} : Type := S -> ((A * S) -> Prop) -> Prop.

  Program Definition DST A (wp : WP) :=
    forall p s, { t : A * S | wp s p -> p t }.

  Program Definition ret { A } (a : A) :
    DST A (fun s p => p (a, s)) :=
    fun p s => (a, s).

  Program Definition bind : forall A wp1 B wp2,
      DST A wp1 -> (forall a : A, DST B (wp2 a)) ->
      DST B (fun s p => wp1 s (fun t => let: (a', s') := t in wp2 a' s' p)) :=
    fun A wp1 B wp2 c1 c2 p s1 =>
      let: (a, s2) := c1 (fun x => let: (a, s) := x in wp2 a s p) s1 in
      c2 a p s2.
  Next Obligation.
    elim: c1 Heq_anonymous => a' /= H' Heq_anonymous.
    subst. elim: c2 => a''/= H''. auto.
  Defined.

  Program Definition reflect { A } { wp : WP } :
    (forall s, Pure.Pure (A * S) (wp s)) -> DST A wp :=
    fun P p s => P s p.

  Program Definition reify { A } { wp : WP } :
    DST A wp -> forall s, Pure.Pure (A * S) (fun p => wp s p) :=
    fun m s p => m p s.
  
  Program Definition get : DST S (fun s p => p (s, s)) :=
    reflect (fun s => Pure.ret (s, s)).

  Program Definition put : forall s, DST unit (fun _ p => p (tt, s)) :=
    fun s => reflect (fun _ => Pure.ret (tt, s)).
  End DST.
End DST.

Arguments DST.ret {S} {A}.
Arguments DST.bind {S} {A} {wp1} {B} {wp2}.
Arguments DST.get {S}.
Arguments DST.put {S}.

Notation "c >>= f" := (DST.bind c f) (at level 50, left associativity).
Notation "f =<< c" := (DST.bind c f) (at level 51, right associativity).
Notation "x <- c1 ;; c2" := (DST.bind c1 (fun x => c2)) (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

Notation "'ST' s 'return' a 'requires' [ P ] 'ensures' [ Q ]" :=
  (DST.DST s a (fun s1 p => P /\ (forall c s2, Q s1 c s2 -> p (c, s2))))
    (at level 99, P at next level, Q at next level).

Check (ST nat return (Tree nat) requires [True] ensures [fun _ _ _ => True]).

Import DST.

Program Fixpoint relabel {A : Set} (t : Tree A) :
  ST nat return Tree nat
       requires [True]
       ensures [fun i t f => f = i + size t /\ flatten t = seq i (size t)] :=
  match t with
  | Leaf x =>
    n <- get ;;
    put (n + 1) ;;
    ret (Leaf n)
  | Node l r =>
    l' <- relabel l ;;
    r' <- relabel r ;;
    ret (Node l' r')
  end.
Next Obligation.
  case (l' <- relabel A l;; _) => [[a s] H1] /=.
  apply H1. repeat split => //. intros.
  destruct H2; destruct H3; subst.
  apply H0. split => /=.
  - by rewrite addnA.
  - by rewrite H4 H5 seq_split.
Defined.
