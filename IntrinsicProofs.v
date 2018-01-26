From mathcomp Require Import ssreflect ssrnat ssrbool.
Set Bullet Behavior "Strict Subproofs".

From MonadicEffect Require Import Trees.

(** * Extrinsic and Intrinsic Proofs

    There are two types of proofs: _extrinsic_ ones and _intrisic_
    ones. An extrinsic proof is what most people familiar with in Coq:
    you write down a function, and then prove some properties about
    it. In a intrinsic proof, however, you write the properties in the
    type of the function.

    Let's just jump into an example to show what they look like. We
    start with the more familiar extrinsic approach. *)

Section ExtrinsicProof.

  Variable A : Set.

  (** We import state monads from coq-ext-lib. *)
  From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
  Import MonadNotation.
  Local Open Scope monad_scope.

  (** Consider the following [relabel] function. It labels all leaves
      in a tree in with [nat]s in an increasing order. It maintains a
      counter using the state monad. *)
  Fixpoint relabel (t : Tree A) : state nat (Tree nat) :=
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

  (** Now we can write down a specification of this function and prove
      it. *)
  Theorem relabel_spec : forall t s,
      let: (t', s') := runState (relabel t) s in
      s' = s + size t' /\ flatten t' = seq s (size t').
  Proof.
    (** The proof starts by doing induction on the tree. The [Leaf]
        case is trivial, and can be dischagred automatically. *)
    elim => // => l IHt1 r IHt2 s.
    (** In the [Node] case, we do some rewriting to expose the
        computation on left and right children, so we can use our
        induction hypotheses. *)
    rewrite /relabel /= -/relabel.
    (** Now we need a bit boilerplates to destruct the [let]s
        generated from [bind]s, and pass the states through. *)
    specialize (IHt1 s). 
    destruct (runState (relabel l) s) as [t' s'].
    specialize (IHt2 s').
    destruct (runState (relabel r) s') as [t'' s''].
    split => /=; intuition; subst.
    - by rewrite addnA.
    - by rewrite H0 H2 seq_split.
  Qed.
End ExtrinsicProof.
  (** The proof is quite standard. There are a bit boilerplates with
      [bind]s. Can we make use of the monadic structure to propagate
      the proof?

      The intrinsic approach offers one solution to that. Let's see
      how we prove the same thing in that style. *)

(* begin hide *)
Reset ExtrinsicProof.
(* end hide *)
Section IntrinsicProof.

  Variable A : Set.

  (** Here we use something called [Dijkstra] monads we have already
      defined. We will show to define it later. *)
  From MonadicEffect Require Import Dijkstra.

  (** This time, we enhance the type of the [relabel] function, by
      putting a pre- and post-condition in its type. By using the
      [Program] feature provided by Coq, we can define this function
      with the function body exactly the same as before. One
      difference is that now Coq will ask us to prove that the result
      of this function indeed satisfies the post-condition. *)
  Program Fixpoint relabel {A : Set} (t : Tree A) :
    ST nat return (Tree nat)
         requires [fun _ => True]
         ensures  [fun s t s' => s' = s + size t /\ flatten t = seq s (size t)] :=
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
  (** Coq will try to automatically prove some simple proof
      obligations for us. For this function, the case when [t] is a
      [Leaf] is trivial, so Coq has already proved it for us.
      
      We only need to consider the case when [t] is a [Node]. The
      proof is quite similar to the last part of the extrinsic
      proof. *)
  Next Obligation.
    repeat split => //.
    intros; destruct H0; destruct H; subst.
    apply x1. split => /=. 
    - by rewrite addnA.
    - by rewrite H2 H1 seq_split.
  Defined.
End IntrinsicProof.

(* begin hide *)
Reset IntrinsicProof.
(* end hide *)
(** * Intrinsic Proofs in Coq

    Before we jump into the details how the above example is
    implemented in Coq, let's check a little bit technical details in
    Coq. *)
Section IntrinsicProof.

  Fail Definition sqr (x : nat) : { s : nat | s = x * x } :=
    x * x.

  Print sig.

(** The signature of subset types:
<<
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x : A | P x}

For sig: Argument A is implicit
For exist: Argument A is implicit
For sig: Argument scopes are [type_scope type_scope]
For exist: Argument scopes are [type_scope function_scope _ _] 
>> *)

  Definition sqr (x : nat) : { s : nat | s = x * x } :=
    exist (fun s => s = x * x) (x * x) eq_refl.

  Reset sqr.

  Definition sqr (x : nat) : { s : nat | s = x * x }.
    refine (exist _ (x * x) _).
    reflexivity.
  Defined.

  Reset sqr.

  (** Coq's [Program] feature allows us to program with subset types
      without worrying about passing the proof objects. *)
  Program Definition sqr (x : nat) : { s : nat | s = x * x } := x * x.

End IntrinsicProof.

(* begin hide *)
Reset IntrinsicProof.
(* end hide *)
Require Import Program.

(** * The Hoare State Monad

    Most of this section is based on [Swierstra, W. (2009). A Hoare
    Logic for the State Monad]. *)

Section HoareStateMonads.

  Variable S : Set.
  
  Definition Pre : Type := S -> Prop.
  Definition Post (A : Set) : Type := S -> A -> S -> Prop.
  
  Program Definition HoareState (pre : Pre) (A : Set) (post : Post A) : Set :=
    forall s: { s : S | pre s }, { (a, s') : A * S | post s a s' }.

  Definition top : Pre := fun _ => True.

  (** Recall the type of [ret] for an ordinary state monad is

      <<
      A -> state S A
      >> *)
  Program Definition ret (A : Set) :
    forall a, HoareState top A (fun s a' s' => s = s' /\ a = a') :=
    fun a s => (a, s).

  (** Recall the type of [bind] for an ordinary state monad is

      << state S A -> (A -> state S B) -> state S B >>
      
      Note the use of dependent type in our second parameter
      below. The reason is that we would like to refer to [a] in the
      pre- and post-conditions of the second parametr!  *)
  Program Definition bind : forall A B P1 P2 Q1 Q2,
      HoareState P1 A Q1 ->
      (forall (a : A), HoareState (P2 a) B (Q2 a)) ->
      HoareState (fun s1 => P1 s1 /\ forall a s2, Q1 s1 a s2 -> P2 a s2)
                  B
                  (fun s1 a' s3 => exists a, exists s2, Q1 s1 a s2 /\ Q2 a s2 a' s3) :=
    fun A B P1 P2 Q1 Q2 m1 m2 s1 =>
      let: (a, s2) := m1 s1 in m2 a s2.
  Next Obligation.
    (** The first obligation is proving that [a] and [s2] satisfies
        the precontion of [m2]. *)
    elim: m1 Heq_anonymous => t /= H0 Heq_anonymous.
    subst. by apply p0.
  Defined.
  Next Obligation.
    (** The second obligation is proving that [m2 a s2] satisfies the
        post condition of [bind]. *)
    elim (m2 a) => /=. elim => a' s3 H.
    exists a. exists s2. split; auto.
    elim: m1 Heq_anonymous => t /= H0 Heq_anonymous.
    subst. by apply H0.
  Defined.

  (** [get] and [put] are straightforward. *)
  Program Definition get : HoareState top S (fun s a s' => s = s' /\ a = s) :=
    fun s => (s, s).
  Program Definition put (x : S) : HoareState top unit (fun _ _ s' => x = s') :=
    fun _ => (tt, x).
End HoareStateMonads.

(* begin hide *)
Arguments ret {S} {A}.
Arguments bind {S} {A} {B} {P1} {P2} {Q1} {Q2}.
Arguments get {S}.
Arguments put {S}.
(* end hide *)
(** We define some notations to use this monad more easily. *)
Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

(** Now we can do an intrinsic proof to show that our [relabel]
    function is correct with respect to its specification again. *)
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
  case=> a s' [a1] [s1] [[H0 H1] H2].
  case: H2 => a2 [s2] [[H3 H4] [H5 H6]].  
  subst. split => /=.
  - by rewrite addnA.
  - by rewrite H1 H4 seq_split.
Defined.

(** * Dijkstra Monads

    The Hoare state monad we have implemented have a few
    disadvantages, according to [Swamy, N., Weinberger, J.,
    Schlesinger, C., Chen, J., & Livshits, B. (2013). Verifying
    higher-order programs with the dijkstra monad]:

    - There are some existential quantifiers in it. Reasoning with
      these quantifiers, particularly using automated SMT solvers, can
      be problematic.

    - It requires the post-condition to be a two-state relation,
      though sometimes it is not necessary to compare the two states
      in the specification.

    Therefore, they propose another monad called "Dijkstra monad" to
    resolve the above issues (name after Edsger W. Dijkstra, for his
    discoveries in his paper [Dijkstra, E. W. (1975). Guarded
    Commands, Nondeterminacy and Formal Derivation of Programs].

    A Dijkstra monad is parameterized over a weakest precondition
    transformer. It can be seen as a Hoare state monad: *)

Definition DST S A wp :=
  forall p, HoareState S (fun h => wp p h) A (fun h x h' => p x h').

(** But let's define it properly. *)
Reset HoareStateMonads.

Section DijkstraMonads.

  Variables S : Set.

  (** The weakest precondition transformer. As its name suggested, it
      takes a post-condition and transform it into the weakest
      precondition. *)
  Definition WP {A} : Type := (A -> S -> Prop) -> S -> Prop.

  Program Definition DST A (wp : WP) :=
    forall p, { s : S | wp p s } -> { (a, s') : A * S | p a s' }.

  Program Definition ret { A } (a : A) :
    DST A (fun p => p a) :=
    fun _ s => (a, s).

  Program Definition bind : forall A wp1 B wp2,
      DST A wp1 -> (forall a : A, DST B (wp2 a)) ->
      DST B (fun p => wp1 (fun a => wp2 a p)) :=
    fun A wp1 B wp2 c1 c2 p s1 =>
      (** The function body should be

          <<
          let: (a, s2) := c1 (fun a => wp2 a p) s1 in c2 a p s2.
          >>
          But we can also just write this: *)
  let: (a, s2) := c1 _ s1 in c2 a _ s2.
  Next Obligation.
    elim: c1 Heq_anonymous => a' H' /= Heq_anonymous.
    subst; done.
  Defined.

  Program Definition get : DST S (fun p s => p s s) :=
    fun _ s => (s, s).

  Program Definition put : forall s, DST unit (fun p _ => p tt s) :=
    fun s _ _ => (tt, s).
  
End DijkstraMonads.

Arguments ret {S} {A}.
Arguments bind {S} {A} {wp1} {B} {wp2}.
Arguments get {S}.
Arguments put {S}.

Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "f =<< c" := (bind c f) (at level 51, right associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) (at level 100, c1 at next level, right associativity).
Notation "e1 ;; e2" := (_ <- e1 ;; e2) (at level 100, right associativity).

(** Let's see how it works with our [relabel] function: *)
Program Fixpoint relabel {A : Set} (t : Tree A) :
  DST nat (Tree nat) (fun p s =>
                    forall t s', s' = s + size t /\ flatten t = seq s (size t) ->
                    p t s' ) :=
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
  (** We show the function satisfies the post-condition. To do that,
      we show that it satisfies the weakest precondition. *)
  apply H3. split => /=.
  - by rewrite addnA.
  - by rewrite H2 H1 seq_split.
Defined.

(** Writing with weakest precondition transformer can sometimes be
    hard. We can define some notations to make it more intuitive. *)
Reset relabel.

Notation "'ST' s 'return' a 'requires' [ P ] 'ensures' [ Q ]" :=
  (DST s a (fun p s1 => P s1 /\ (forall c s2, Q s1 c s2 -> p c s2)))
    (at level 99, P at next level, Q at next level).

Notation "'ST' s 'return' a 'ensures' [ Q ]" :=
  (DST s a (fun p s1 => forall c s2, Q s1 c s2 -> p c s2))
    (at level 99, Q at next level).

Check (ST nat return (Tree nat) requires [fun _ => True] ensures [fun _ _ _ => True]).

(** Now the specification for [relabel] looks quite similar to that in
    the form of a Hoare state monad, but notice that the proof is
    simpler than that for a Hoare state monad. *)
Program Fixpoint relabel {A : Set} (t : Tree A) :
  ST nat return (Tree nat)
       ensures  [fun i t f => f = i + size t /\ flatten t = seq i (size t)] :=
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
