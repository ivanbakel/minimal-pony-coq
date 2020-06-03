From Pony Require Import Axioms Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Preservation (Map : WSfun) (SetM : WSetsOn).

Module Sem := Semantics Map SetM.
Import Sem.

Theorem result4 :
  forall P : program,
  forall chi chi' : heap,
  forall R : regPart chi,
  forall iota : someAddr,
  @well_formed_heap P chi R
  -> @advancesTo P chi iota chi'
  -> exists R' : regPart chi', @well_formed_heap P chi' R'. 
Proof.
  Admitted.

End Preservation.
