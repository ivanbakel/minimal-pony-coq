From Pony Require Import Language Typing Heap Regions.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.

Module Semantics (Map : WSfun) (SetM : WSetsOn).

Module WFExpr := WFExpressions Map SetM.
Export WFExpr.

Module Heap := Heap Map.
Export Heap.

Inductive evaluatesTo { P : program } : heap -> localVars -> Syntax.cw_encoding -> heap -> localVars -> value -> Prop :=
  | eval_local (chi : heap) (L : localVars) (x : Syntax.var) (v : value)
  : LocalMap.VarMapsTo x v L
    -> evaluatesTo chi L (Syntax.ePath (Syntax.use x)) chi L v
  | eval_temp (chi : heap) (L : localVars) (t : Syntax.temp) (v : value)
  : LocalMap.TempMapsTo t v L
    -> evaluatesTo chi L (Syntax.ePath (Syntax.useTemp t)) chi (LocalMap.removeTemp t L) v
  | eval_consume (chi : heap) (L : localVars) (x : Syntax.var) (v : value)
  : LocalMap.VarMapsTo x v L
    -> evaluatesTo chi L (Syntax.ePath (Syntax.consume x)) chi (LocalMap.removeVar x L) v
  | eval_field (chi chi' : heap) (L L' : localVars) (p : Syntax.path) (f : Syntax.fieldId) (v v' : value)
  : evaluatesTo chi L (Syntax.ePath p) chi' L' v
    -> HeapFieldLookup v f v' chi'
    -> evaluatesTo chi L (Syntax.eFieldOfPath (p, f)) chi' L' v'
  | eval_alias (chi chi' : heap) (L L' : localVars) (x : Syntax.cw_encoding) (v : value)
  : evaluatesTo chi L x chi' L' v
    -> evaluatesTo chi L (Syntax.eAlias x) chi' L' v
  | eval_vardecl (chi : heap) (L : localVars) (x : Syntax.var)
  : evaluatesTo chi L (Syntax.eExpr (Syntax.varDecl x)) chi (LocalMap.addVar x None L) None
  | eval_localassign (chi chi' : heap) (L L' : localVars) (x : Syntax.var) (rhs : Syntax.rhs) (v v' : value)
  : evaluatesTo chi L (Syntax.eAlias (Syntax.eRhs rhs)) chi' L' v
    -> LocalMap.VarMapsTo x v' L'
    -> evaluatesTo chi L (Syntax.eExpr (Syntax.assign x (Syntax.aliasOf rhs))) chi' (LocalMap.addVar x v L') v'
  | eval_fieldassign (chi chi' chi'' chi''' : heap) (L L' L'' : localVars) (p p' : Syntax.path) (f : Syntax.fieldId)
    (u v v' : value)
  : evaluatesTo chi L (Syntax.eAlias (Syntax.ePath p')) chi' L' v
    -> evaluatesTo chi' L' (Syntax.ePath p) chi'' L'' u
    -> HeapFieldLookup u f v' chi''
    -> HeapFieldAdd u f v chi'' chi'''
    -> evaluatesTo chi L (Syntax.eRhs (Syntax.fieldAssign (p, f) (Syntax.aliasOf p'))) chi''' L'' v'
  | eval_becall (chi chi' chi'' chi''' : heap) (L L' L'' : localVars) (rcvr : Syntax.path) (args : list (@Syntax.aliased Syntax.path))
    (b : Syntax.behaviourId) (rcvrVal : value) (argVals : list value)
  : evaluatesTo_list chi L (Syntax.eAPaths args) chi' L' argVals
    -> evaluatesTo chi' L' (Syntax.eAlias (Syntax.ePath rcvr)) chi'' L'' rcvrVal
    -> False (*TODO: receiver is actor in the heap - is this necessary? *)
    -> HeapMessageAppend rcvrVal b argVals chi'' chi'''
    -> evaluatesTo chi L (Syntax.eRhs (Syntax.behaviourCall (Syntax.aliasOf rcvr) b args)) chi''' L'' rcvrVal
with
evaluatesTo_list { P : program } : heap -> localVars -> list Syntax.cw_encoding -> heap -> localVars -> list value -> Prop :=
  | evaluatesTo_list_nil (chi : heap) (L : localVars)
  : evaluatesTo_list chi L nil chi L nil
  | evaluatesTo_list_cons (chi chi' chi'' : heap) (L L' L'' : localVars) (x : Syntax.cw_encoding)
    (lx : list Syntax.cw_encoding) (v : value) (lv : list value)
  : evaluatesTo chi L x chi' L' v
    -> evaluatesTo_list chi' L' lx chi'' L'' lv
    -> evaluatesTo_list chi L (x :: lx) chi'' L'' (v :: lv).

Lemma paths_dont_change_heap { P : program } : forall chi chi' L L' p v, @evaluatesTo P chi L (Syntax.ePath p) chi' L' v -> chi = chi'.
Proof.
  intros.
  (* This is true by construction, so just invert and say so *)
  inversion H; reflexivity.
  Qed.

End Semantics.
