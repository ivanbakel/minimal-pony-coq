From Pony Require Import Axioms Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Progress (Map : WSfun) (SetM : WSetsOn).

Module Sem := Semantics Map SetM.
Import Sem.

Theorem result3 :
  forall P : program,
  forall chi : heap,
  forall R : regPart chi,
  @well_formed_heap P chi R
    ->  { forall iota : actorAddr,
          forall actorInstance : actor,
          HeapMapsTo actor (someActorAddr iota) actorInstance chi
            -> messageQueue actorInstance = None
                /\ frameStack actorInstance = None
        } +
        { exists iota : someAddr,
          exists chi' : heap,
          @advancesTo P chi iota chi'
        }.
Proof.
  Admitted.

End Progress.
