From mathcomp Require Import ssrbool ssrnat ssreflect eqtype.
From CoqUtils Require Import ord fmap.

From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
Import MonadNotation.
Open Scope monad_scope.

From MonadicEffect Require Import Typ.

Set Implicit Arguments.

Section Heap.
  Import FMap.

  Inductive heap_cell :=
  | HeapCell (a : Typ) (v : const a).

  Record heap :=
    { next_addr : nat; 
      memory : { fmap nat_ordType -> heap_cell } }.

  Variable a : Typ.
  Definition Heap := state heap.

  Definition contains (r : ref a) : Heap bool :=
    h <- get ;;
    ret (match getm (memory h) (addr r) with
         | Some (HeapCell b v) =>
           match dec_eq_typ a b with
           | left _ => true
           | _ => false
           end
         | _ => false
         end).

  Definition unused (r : ref a) : Heap bool :=
    h <- get ;;
    ret (match getm (memory h) (addr r) with
         | None => true
         | _ => false
         end).

  Definition sel (r : ref a) : Heap (const a) :=
    h <- get ;;
    ret (match getm (memory h) (addr r) with
         | Some (HeapCell b v) =>
           match dec_eq_typ a b with
           | left e => eq_rect_r (fun a : Typ => const a) v e
           | _ => init r
           end
         | _ => init r
         end).

  Definition upd (r : ref a) (v : const a) : Heap unit :=
    h <- get ;;
    b <- contains r ;;
    if b then
      put {| next_addr := next_addr h;
             memory := setm (memory h) (addr r) (HeapCell a v) |} ;;
          ret tt
    else
      if (addr r) >= (next_addr h) then
        put {| next_addr := (addr r) .+1;
               memory := setm (memory h) (addr r) (HeapCell a v) |} ;;
       ret tt 
      else
        put {| next_addr := next_addr h;
               memory := setm (memory h) (addr r) (HeapCell a v) |} ;;
        ret tt.

  Definition alloc (x : const a) : Heap (ref a) :=
    h <- get ;;
    let r := {| addr := next_addr h; init := x |} in
      put {| next_addr := (addr r) .+1;
             memory := setm (memory h) (addr r) (HeapCell a x) |} ;;
      ret r.

  Definition free (r : ref a) : Heap unit :=
    h <- get ;;
    put {| next_addr := next_addr h;
           memory := remm (memory h) (addr r) |} ;;
    ret tt.
End Heap.

Notation "x ::= y" := (upd x y) (at level 99).
Notation "# x" := (sel x) (at level 20).

Lemma upd_contains : forall (a : Typ) h0 (r : ref a) x,
    evalState (contains r) h0 ->
    let h1 := execState (upd r x) h0 in
     (forall r',
         evalState (contains r') h0 ->
         addr r' = addr r -> evalState (sel r') h1 = x) /\
     (forall (b : Typ) (r' : ref b),
         evalState (contains r') h0 ->
         addr r' <> addr r -> evalState (sel r') h0 = evalState (sel r') h1) /\
     (forall (b : Typ) (r' : ref b),
         evalState (contains r') h0 <-> evalState (contains r') h1) /\
     (forall (b : Typ) (r' : ref b),
         evalState (unused r') h0 <-> evalState (unused r') h1).
Proof.
  move=>a h0 r x H h1. split; [ | split; [ | split ]].
  - move=>r' H1. rewrite /sel /h1 /upd.
    move: H. rewrite /evalState /execState /runState /=.
    move ->. rewrite /= setmE /eq_op /=. move /eqnP ->.
    destruct a; vm_compute; reflexivity.
  - move=>b r' H1. rewrite /sel /h1 /upd.
    move: H. rewrite /evalState /execState /runState /=.
    move ->. rewrite /= setmE /eq_op /=. 
    case /eqnP. rewrite /is_true Bool.negb_true_iff. move -> =>//.
  - move=>b r'. rewrite /h1.
    move: H. rewrite /evalState /execState /runState /=.
    move=>H. rewrite H /= setmE.
    destruct (addr r' == addr r) eqn:Heqr; rewrite Heqr.
    + move: Heqr. move /eqnP ->. move: H.
      destruct ((memory h0) (addr r)) eqn:Hma; rewrite Hma.
      * destruct h. destruct b; destruct a; destruct a0; vm_compute; auto.
      * discriminate.
    + reflexivity.
  - move=>b r'. rewrite /h1.
    move: H. rewrite /evalState /execState /runState /=.
    move=>H. rewrite H /= setmE.
    destruct (addr r' == addr r) eqn:Heqr; rewrite Heqr.
    + move: Heqr. move /eqnP ->. move: H.
      destruct ((memory h0) (addr r)) eqn:Hma; rewrite Hma.
      * destruct h. destruct b; destruct a; destruct a0; vm_compute; auto.
      * discriminate.
    + reflexivity.
Qed.
