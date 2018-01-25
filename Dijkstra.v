From mathcomp Require Import ssreflect ssrnat.
From MonadicEffect Require Import Trees.

Require Import Program.

Section Dijkstra.

  Variables S : Set.

  Definition WP {A} : Type := (A -> S -> Prop) -> S -> Prop.

  Program Definition DST A (wp : WP) :=
    forall p, { s : S | wp p s } -> { (a, s') : A * S | p a s' }.

  Program Definition ret { A } (a : A) :
    DST A (fun p => p a) :=
    fun _ s => (a, s).

  Program Definition bind : forall A wp1 B wp2,
      DST A wp1 -> (forall a : A, DST B (wp2 a)) ->
      DST B (fun p => wp1 (fun a => wp2 a p)) :=
    fun A wp1 B wp2 c1 c2 _ s1 =>
      let: (a, s2) := c1 _ s1 in c2 a _ s2.
  Next Obligation.
    elim: c1 Heq_anonymous => a' H' /= Heq_anonymous.
    subst; done.
  Defined.

  Program Definition get : DST S (fun p s => p s s) :=
    fun _ s => (s, s).

  Program Definition put : forall s, DST unit (fun p _ => p tt s) :=
    fun s _ _ => (tt, s).
End Dijkstra.

Arguments ret {S} {A}.
Arguments bind {S} {A} {wp1} {B} {wp2}.
Arguments get {S}.
Arguments put {S}.

Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

Program Fixpoint relabel {A : Set} (t : Tree A) :
  DST nat (Tree nat) (fun p i =>
                    forall t f, f = i + size t /\ flatten t = seq i (size t) ->
                    p t f ) :=
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
  apply H3. split => /=.
  - by rewrite addnA.
  - by rewrite H2 H1 seq_split.
Defined.

Reset relabel.

Notation "'ST' s 'return' a 'requires' [ P ] 'ensures' [ Q ]" :=
  (DST s a (fun p s1 => P /\ (forall c s2, Q s1 c s2 -> p c s2)))
    (at level 99, P at next level, Q at next level).

Check (ST nat return (Tree nat) requires [True] ensures [fun _ _ _ => True]).

Program Fixpoint relabel {A : Set} (t : Tree A) :
  ST nat return (Tree nat)
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
  repeat split => //.
  intros; destruct H0; destruct H; subst.
  apply x1. split => /=. 
  - by rewrite addnA.
  - by rewrite H2 H1 seq_split.
Defined.
