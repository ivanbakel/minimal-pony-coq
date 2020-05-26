From Pony Require Import Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Result1 (Map : WSfun) (SetM : WSetsOn).

Module Sem := Semantics Map SetM.

Theorem result1 :
  forall P : Sem.WFExpr.Program.program,
  forall gamma gamma' : Sem.WFExpr.context,
  forall e : Syntax.expression,
  forall E : Syntax.expressionSeq,
  forall S : Syntax.typeId,
  forall k : Syntax.capability,
  forall T : Syntax.ponyType,
  forall L L' : Sem.localVars,
  forall chi chi' : Sem.heap,
  forall v : Sem.value,
    @Sem.WFExpr.typing P Syntax.expression gamma e (Syntax.type S k) gamma'
    -> @Sem.WFExpr.well_formed_expr P gamma (Syntax.seq e E) T
    -> (forall x : Syntax.var, 
        forall S' : Syntax.typeId,
        forall b : Syntax.baseCapability,
        forall v' : Sem.value,
          Sem.WFExpr.VarMapsTo x (Syntax.aType S' b) gamma
          -> Sem.LocalMap.VarMapsTo x v' L
          -> Sem.heapTyping v' S' chi)
    -> @Sem.evaluatesTo P Syntax.expression chi L e chi' L' v
    -> Sem.heapTyping v S chi'
        /\ @Sem.WFExpr.well_formed_expr P gamma' E T.
Proof.
  Admitted.

End Result1.
