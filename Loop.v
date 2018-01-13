From MonadicEffect Require Import Typ Heap.
From mathcomp Require Import ssrbool ssrnat eqtype ssreflect.

From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
Import MonadNotation.
Open Scope monad_scope.

Require Coq.Program.Wf.

Program Fixpoint sum_up (r : ref Int)
         (from : const Int)
         (to : {t : const Int | from <= t})
         { measure (to - from) } : Heap (const Int) :=
  match from < to with
  | true =>
    v <- #r;;
    r ::= v + from;;
    sum_up r from.+1 to
  | _ => #r
  end.
Next Obligation.
  apply /ltP. apply ltn_sub2l =>//.
Qed.

Program Fixpoint sum_dn (r : ref Int)
         (from : const Int)
         (to : {t : const Int | from <= t})
         { measure (to - from) } : Heap (const Int) :=
  match from < to with
  | true =>
    v <- #r;;
    r ::= v + to;;
    sum_up r from to.-1
  | _ => #r
  end.
Next Obligation.
  rewrite -ltnS /= prednK =>//.
  induction to. discriminate. auto.
Qed.
