From Pony Require Import Axioms Language Typing Heap Semantics.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.Equalities.

Module Result1 (Map : WSfun) (SetM : WSetsOn).

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

End Result1.
