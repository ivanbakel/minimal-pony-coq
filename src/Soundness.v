From Pony Require Import Axioms Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Soundness (Map : WSfun) (SetM : WSetsOn).

Module Sem := Semantics Map SetM.
    

Definition wellTypedLocals (gamma : Sem.WFExpr.context) (L : Sem.localVars) (chi : Sem.heap) : Prop :=
  ( forall x : Syntax.var, 
    forall S : Syntax.typeId,
    forall b : Syntax.baseCapability,
    forall v : Sem.value,
      Sem.WFExpr.VarMapsTo x (Syntax.aType S b) gamma
      -> Sem.LocalMap.VarMapsTo x v L
      -> Sem.heapTyping v S chi)
  /\ 
  ( forall t : Syntax.temp,
    forall S : Syntax.typeId,
    forall k : Syntax.capability,
    forall v : Sem.value,
      Sem.WFExpr.TempMapsTo t (Syntax.type S k) gamma
      -> Sem.LocalMap.TempMapsTo t v L
      -> Sem.heapTyping v S chi).

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
    @Sem.WFExpr.typing P gamma (Syntax.eExpr e) (Syntax.type S k) gamma'
    -> @Sem.WFExpr.well_formed_expr P gamma (Syntax.seq e E) T
    -> wellTypedLocals gamma L chi
    -> @Sem.evaluatesTo P chi L (Syntax.eExpr e) chi' L' v
    -> Sem.heapTyping v S chi'
        /\ @Sem.WFExpr.well_formed_expr P gamma' E T.
Proof.
  intros P gamma gamma' e E S k T L L' chi chi' v.

  intros e_has_type_S_k e_seq_E_wf frame_well_typed e_evaluates_v.
  
  split.
  (*Show that the evaluated value has the expected type.
  *
  * This depends on the form of the expression.
  *)
  { destruct e as [ newVar | var arhs | temp pf ].
    { assert (v = None) as v_is_none.
      { inversion e_evaluates_v.
        reflexivity.
      }
      rewrite -> v_is_none.
      apply Sem.heaptyp_null.
    }
    { admit. (* TODO *)
    }
    { admit. (* TODO *) 
    }
  }
  (*Show the remaining expression is well-formed
  *
  * These are largely trivial, since a proof of the appropriate
  * form is part of the inductive definition. The main work in each
  * case requires arguing that the typing judgement is deterministic
  * w.r.t. the output context, so that gamma' = gamma'0.
  *)
  { inversion e_seq_E_wf.
    { assert (Syntax.type S k = t' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (Sem.WFExpr.varDecl x)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = t' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (Sem.WFExpr.assign x arhs)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (Sem.WFExpr.tempAssign t pf)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr e).
        assumption.
        rewrite <- H.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
  }
  Admitted.

Theorem result2 :
  forall P : Sem.WFExpr.Program.program,
  forall gamma : Sem.WFExpr.context,
  forall p : Syntax.path,
  forall S : Syntax.typeId,
  forall k : Syntax.capability,
  forall L L' : Sem.localVars,
  forall chi chi' : Sem.heap,
  forall v : Sem.value,
    @Sem.WFExpr.well_formed_expr P gamma (Syntax.final p) (Syntax.type S k)
    -> wellTypedLocals gamma L chi
    -> @Sem.evaluatesTo P chi L (Syntax.ePath p) chi' L' v
    -> Sem.heapTyping v S chi'.
Proof.
  intros P gamma p S k L L' chi chi' v.

  intros path_well_formed locals_well_typed p_evaluates_to_v.
  
  assert (chi = chi') as heaps_equal.
  { apply (@Sem.paths_dont_change_heap P) with (L:=L) (L':=L') (p:=p) (v:=v); assumption. 
  } 
  rewrite <- heaps_equal. 
  
  destruct locals_well_typed as [ vars_well_typed temps_well_typed ].
 
  inversion path_well_formed as
    [ _gamma0 gamma' p0 T p_typed_s_k
    | | | |
    ].

  destruct p as [ x | x | t ] eqn:e.
  { inversion p_typed_s_k as
      [ _gamma1 _x0 [S' b] x_mapsto_Sb
      | | | | | | | | | | | |
      ].

    assert (gamma = gamma') as ctxt_same by assumption.

    apply vars_well_typed with (x:=x) (b:=b).
    rewrite ctxt_same.
    assumption.

    inversion p_evaluates_to_v as
      [ _chi0 _L0 _x1 _v0 x_mapsto_v
      | | | | | | | |
      ].
    assumption.
  }
  { inversion p_typed_s_k as 
      [ |
      | _gamma1 _x0 [S' b] x_mapsto_unhat_Sk
      | | | | | | | | | | ].

    assert (S' = S) as typeids_same.
    { apply Syntax.hat_preserves_type_id with (b:=b) (k:=k).
      unfold Syntax.hat.
      assumption.
    }

    apply vars_well_typed with (x:=x) (b:=b).
    rewrite <- typeids_same.
    assumption.

    inversion p_evaluates_to_v as
      [ |
      | _chi0 _L0 _x1 _v0 x_mapsto_v
      | | | | | |
      ].
    assumption.
  }
  { inversion p_typed_s_k as
      [ 
      | _gamma1 _t0 [ S' k' ] t_mapsto_Sk
      | | | | | | | | | | |
      ].

    assert (gamma = gamma') as ctxt_same by assumption.

    apply temps_well_typed with (t:=t) (k:=k).
    rewrite ctxt_same.
    assumption.

    inversion p_evaluates_to_v as
      [
      | _chi0 _L0 _t1 _v0 t_mapsto_v
      | | | | | | | ].
    assumption.
  }
  Qed.

End Soundness.
