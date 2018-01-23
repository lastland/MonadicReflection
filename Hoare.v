From mathcomp Require Import ssreflect ssrnat.
From MonadicEffect Require Import Trees.

Require Import Program.

Section Hoare.

  Variable s : Set.
  
  Definition Pre : Type := s -> Prop.
  Definition Post (a : Set) : Type := s -> a -> s -> Prop.
  Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set :=
    forall i: { t : s | pre t }, { (x, f) : a * s | post i x f }.

  Definition top : Pre := fun s => True.
  Program Definition ret (a : Set) :
    forall x, HoareState top a (fun i y f => i = f /\ y = x) :=
    fun x s => (x, s).

  Program Definition bind : forall a b P1 P2 Q1 Q2,
      HoareState P1 a Q1 ->
      (forall (x : a), HoareState (P2 x) b (Q2 x)) ->
      HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
                  b
                  (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3) :=
    fun a b P1 P2 Q1 Q2 c1 c2 s1 =>
      match c1 s1 with (x, s2) => c2 x s2 end.
  Next Obligation.
    elim: c1 Heq_anonymous => x0 H0 /= Heq_anonymous.
    rewrite <- Heq_anonymous in H0. apply /p0 /H0.
  Qed.
  Next Obligation.
    elim (c2 x) => /=. elim => a0 s0 H.
    exists x. exists s2. split; auto.
    elim: c1 Heq_anonymous => x0 H0 /= Heq_anonymous.
    rewrite <- Heq_anonymous in H0. apply H0.
  Qed.

  Program Definition get : @HoareState top s (fun i y f => i = f /\ y = i) :=
    fun s => (s, s).
  Program Definition put (x : s) : @HoareState top unit (fun _ _ f => f = x) :=
    fun _ => (tt, x).
End Hoare.

Arguments ret {s} {a}.
Arguments bind {s} {a} {b} {P1} {P2} {Q1} {Q2}.
Arguments get {s}.
Arguments put {s}.

Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

Program Fixpoint relabel {A : Set} (t : Tree A) :
  HoareState nat
             (@top nat)
             (Tree nat) 
             (fun i t f => f = i + size t /\ flatten t = seq i (size t)) :=
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
  case (relabel A l >>= _) => /=.
  case=> x' n [t1] [n2] [[H0 H1] H2].
  case: H2 => t2 [n3] [[H3 H4] [H5 H6]].  
  rewrite H6. split => /=.
  - rewrite -H5 H3 H0 addnA //.
  - rewrite H1 H4 seq_split H0 //.
Defined.

Definition DST s a wp := forall p, HoareState s (fun h => wp p h) a (fun h x h' => p x h').

Reset DST.
