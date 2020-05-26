From Pony Require Import Language Typing Heap.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.

Module Semantics (Map : WSfun) (SetM : WSetsOn).

(* Here only to have a single chain of module inclusions *)
Module WFExpr := WFExpressions Map SetM.

Module Heap := Heap Map.
Include Heap.

Inductive evaluatesTo { P : WFExpr.Program.program } : forall (X : Type), heap -> localVars -> X -> heap -> localVars -> value -> Prop :=
  | eval_local (chi : heap) (L : localVars) (x : Syntax.var) (v : value)
  : LocalMap.VarMapsTo x v L
    -> evaluatesTo Syntax.path chi L (Syntax.use x) chi L v
  | eval_consume (chi : heap) (L : localVars) (x : Syntax.var) (v : value)
  : LocalMap.VarMapsTo x v L
    -> evaluatesTo Syntax.path chi L (Syntax.consume x) chi (LocalMap.removeVar x L) v
  | eval_field (chi chi' : heap) (L L' : localVars) (p : Syntax.path) (f : Syntax.fieldId) (v v' : value)
  : evaluatesTo Syntax.path chi L p chi' L' v
    -> HeapFieldLookup v f v' chi'
    -> evaluatesTo Syntax.fieldOfPath chi L (p, f) chi' L' v'
  | eval_alias (chi chi' : heap) (L L' : localVars) (X : Type) (x : X) (v : value)
  : evaluatesTo X chi L x chi' L' v
    -> evaluatesTo (@Syntax.aliased X) chi L (Syntax.aliasOf x) chi' L' v
  | eval_vardecl (chi : heap) (L : localVars) (x : Syntax.var)
  : evaluatesTo Syntax.expression chi L (Syntax.varDecl x) chi (LocalMap.addVar x None L) None
  | eval_localassign (chi chi' : heap) (L L' : localVars) (x : Syntax.var) (arhs : @Syntax.aliased Syntax.rhs) (v v' : value)
  : evaluatesTo Syntax.aliased chi L arhs chi' L' v
    -> LocalMap.VarMapsTo x v' L'
    -> evaluatesTo Syntax.expression chi L (Syntax.assign x arhs) chi' (LocalMap.addVar x v L') v'
  | eval_fieldassign (chi chi' chi'' chi''' : heap) (L L' L'' : localVars) (p : Syntax.path) (f : Syntax.fieldId)
    (ap : @Syntax.aliased Syntax.path) (u v v' : value)
  : evaluatesTo Syntax.aliased chi L ap chi' L' v
    -> evaluatesTo Syntax.path chi' L' p chi'' L'' u
    -> HeapFieldLookup u f v' chi''
    -> HeapFieldAdd u f v chi'' chi'''
    -> evaluatesTo Syntax.rhs chi L (Syntax.fieldAssign (p, f) ap) chi''' L'' v'
  | eval_becall (chi chi' chi'' chi''' : heap) (L L' L'' : localVars) (rcvr : @Syntax.aliased Syntax.path) (args : list (@Syntax.aliased Syntax.path))
    (b : Syntax.behaviourId) (rcvrVal : value) (argVals : list value)
  : evaluatesTo_list Syntax.aliased chi L args chi' L' argVals
    -> evaluatesTo Syntax.aliased chi' L' rcvr chi'' L'' rcvrVal
    -> False (*TODO: receiver is actor in the heap - is this necessary? *)
    -> HeapMessageAppend rcvrVal b argVals chi'' chi'''
    -> evaluatesTo Syntax.rhs chi L (Syntax.behaviourCall rcvr b args) chi''' L'' rcvrVal
with
evaluatesTo_list { P : WFExpr.Program.program } : forall (X : Type), heap -> localVars -> list X -> heap -> localVars -> list value -> Prop :=
  | evaluatesTo_list_nil (X : Type) (chi : heap) (L : localVars)
  : evaluatesTo_list X chi L nil chi L nil
  | evaluatesTo_list_cons (X: Type) (chi chi' chi'' : heap) (L L' L'' : localVars) (x : X) (lx : list X) (v : value) (lv : list value)
  : evaluatesTo X chi L x chi' L' v
    -> evaluatesTo_list X chi' L' lx chi'' L'' lv
    -> evaluatesTo_list X chi L (x :: lx) chi'' L'' (v :: lv).

(* TODO: get axioms for these inequalities *)
(* The antivalence axiom is not complete, but should eventually generate these *)
Axiom fieldOfPath_ne_path : Syntax.fieldOfPath <> Syntax.path.
Axiom aliased_ne_path : forall X : Type, @Syntax.aliased X <> Syntax.path.
Axiom expr_ne_path : Syntax.expression <> Syntax.path. 
Axiom rhs_ne_path : Syntax.rhs <> Syntax.path. 

Lemma paths_dont_change_heap { P : WFExpr.Program.program } : forall chi chi' L L' p v, @evaluatesTo P Syntax.path chi L p chi' L' v -> chi = chi'.
Proof.
  intros.
  inversion H; try reflexivity.
  contradict H0; apply fieldOfPath_ne_path.
  contradict H0; apply aliased_ne_path.
  contradict H0; apply expr_ne_path.
  contradict H0; apply rhs_ne_path.
  contradict H0; apply rhs_ne_path.
  Qed.

End Semantics.
