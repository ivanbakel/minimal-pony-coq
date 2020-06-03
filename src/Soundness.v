From Pony Require Import Axioms Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Soundness (Map : WSfun) (SetM : WSetsOn).

Module Sem := Semantics Map SetM.
Import Sem. 

Theorem result1 :
  forall P : Program.program,
  forall gamma gamma' : Typing.Context.context,
  forall e : Syntax.expression,
  forall E : Syntax.expressionSeq,
  forall S : Syntax.typeId,
  forall k : Syntax.capability,
  forall T : Syntax.ponyType,
  forall L L' : localVars,
  forall chi chi' : heap,
  forall iota : frameAddr,
  forall R : regPart chi,
  forall v : value,
    @typing P gamma (Syntax.eExpr e) (Syntax.type S k) gamma'
    -> @well_formed_expr P gamma (Syntax.seq e E) T
    -> (exists f : frame, HeapMapsTo frame (someFrameAddr iota) f chi /\ lVars f = L /\ toExecute f = (Syntax.seq e E) /\ returnVar f = None)
    -> well_typed_locals chi R (someFrameAddr iota) L gamma
    -> @evaluatesTo P chi L (Syntax.eExpr e) chi' L' v
    -> heapTyping v S chi'
        /\ @well_formed_expr P gamma' E T.
Proof.
  intros P gamma gamma' e E S k T L L' chi chi' iota R v.

  intros e_has_type_S_k e_seq_E_wf frame_in_heap locals_well_regioned e_evaluates_v.
  
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
      apply heaptyp_null.
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
  * w.r.t. the output Typing.Context.context, so that gamma' = gamma'0.
  *)
  { inversion e_seq_E_wf.
    { assert (Syntax.type S k = t' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (varDecl x)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = t' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (assign x arhs)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr (tempAssign t pf)).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply typing_func_on_type_and_outcome with (P:=P) (gamma:=gamma) (x:=Syntax.eExpr e).
        assumption.
        rewrite <- H.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
  }
  Admitted.

Theorem result2 :
  forall P : Program.program,
  forall gamma : Typing.Context.context,
  forall p : Syntax.path,
  forall S : Syntax.typeId,
  forall k : Syntax.capability,
  forall L L' : localVars,
  forall chi chi' : heap,
  forall iota : frameAddr,
  forall R : regPart chi,
  forall v : value,
    @well_formed_expr P gamma (Syntax.final p) (Syntax.type S k)
    -> (exists f : frame, HeapMapsTo frame (someFrameAddr iota) f chi /\ lVars f = L /\ toExecute f = (Syntax.final p) /\ returnVar f = None)
    -> well_typed_locals chi R (someFrameAddr iota) L gamma
    -> @evaluatesTo P chi L (Syntax.ePath p) chi' L' v
    -> heapTyping v S chi'.
Proof.
  intros P gamma p S k L L' chi chi' iota R v.

  intros path_well_formed frame_in_heap locals_well_typed p_evaluates_to_v.
  
  assert (chi = chi') as heaps_equal.
  { apply (@paths_dont_change_heap P) with (L:=L) (L':=L') (p:=p) (v:=v); assumption. 
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

    apply temps_well_typed with (t:=t) (k:=k).
    assumption.

    inversion p_evaluates_to_v as
      [
      | _chi0 _L0 _t1 _v0 t_mapsto_v
      | | | | | | | ].
    assumption.
  }
  Qed.

End Soundness.
