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
    @Sem.WFExpr.typing P Syntax.expression gamma e (Syntax.type S k) gamma'
    -> @Sem.WFExpr.well_formed_expr P gamma (Syntax.seq e E) T
    -> wellTypedLocals gamma L chi
    -> @Sem.evaluatesTo P Syntax.expression chi L e chi' L' v
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
        contradict H; auto.
        contradict H; auto.
        contradict H; auto.
        contradict H; auto.
        contradict H; auto.
        reflexivity.
        { apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H4.
          contradict H4.
          discriminate.
          apply Axioms.type_decidability.
        }
        contradict H; auto.
        contradict H; auto. 
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
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (X:=Syntax.expression) (gamma:=gamma) (x:=Sem.WFExpr.varDecl x).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = t' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (X:=Syntax.expression) (gamma:=gamma) (x:=Sem.WFExpr.assign x arhs).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (X:=Syntax.expression) (gamma:=gamma) (x:=Sem.WFExpr.tempAssign t pf).
        rewrite -> H.
        assumption.
        assumption.
      }
      rewrite -> gamma_eq; assumption.
    }
    { assert (Syntax.type S k = T' /\ gamma' = gamma'0) as [ _ gamma_eq ].
      { apply Sem.WFExpr.typing_func_on_type_and_outcome with (P:=P) (X:=Syntax.expression) (gamma:=gamma) (x:=e).
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
  forall gamma gamma' : Sem.WFExpr.context,
  forall p : Syntax.path,
  forall S : Syntax.typeId,
  forall k : Syntax.capability,
  forall L L' : Sem.localVars,
  forall chi chi' : Sem.heap,
  forall v : Sem.value,
    @Sem.WFExpr.well_formed_expr P gamma (Syntax.final p) (Syntax.type S k)
    -> wellTypedLocals gamma L chi
    -> @Sem.evaluatesTo P Syntax.path chi L p chi' L' v
    -> Sem.heapTyping v S chi'.
Proof.
  intros P gamma gamma' p S k L L' chi chi' v.

  intros path_well_formed locals_well_typed p_evaluates_to_v.
  
  assert (chi = chi') as heaps_equal.
  { apply (@Sem.paths_dont_change_heap P) with (L:=L) (L':=L') (p:=p) (v:=v); assumption. 
  } 
  rewrite <- heaps_equal. 
  
  destruct locals_well_typed as [ vars_well_typed temps_well_typed ].

  inversion path_well_formed.
  inversion H1.
  { destruct aT as [ S' b ].

    assert (Sem.WFExpr.VarMapsTo x (Syntax.aType S b) gamma) as x_typed_b.
    enough (S = S') as types_same.
    rewrite types_same.
    rewrite H8.
    assumption.
    (* Prove S = S' *)
    simpl in H4.
    inversion H4. 
    reflexivity.

    apply vars_well_typed with (x:=x) (b:=b).
    assumption.

    inversion p_evaluates_to_v.
    
    apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H3; try apply Axioms.type_decidability.
    
    assert (x = x0) as vars_same.
    { apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H7.
      rewrite <- H3 in H7.
      inversion H7.
      reflexivity.
      apply Axioms.type_decidability.
    }

    rewrite vars_same.
    assumption.

    apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H3; try apply Axioms.type_decidability.
    apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H7; try apply Axioms.type_decidability.
    rewrite <- H3 in H7.
    contradict H7.
    discriminate.

    apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H3; try apply Axioms.type_decidability.
    apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H7; try apply Axioms.type_decidability.
    rewrite <- H3 in H7.
    contradict H7.
    discriminate.

    contradict H9; auto.
    contradict H9; auto.
    contradict H9; auto.
    contradict H9; auto.
    contradict H9; auto.
    contradict H9; auto.
  }
  {
    { apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H6.
      contradict H6.
      discriminate.
      apply Axioms.type_decidability.
    }
    { apply Coq.Logic.Eqdep_dec.inj_pair2_eq_dec in H6.
      contradict H6.
      discriminate.
      apply Axioms.type_decidability.
    }
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
    contradict H3; auto. 
  }
  Admitted.

End Soundness.
