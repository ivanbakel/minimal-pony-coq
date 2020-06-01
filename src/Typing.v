From Pony Require Import Language LocalMap.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.

Module Context (Map : WSfun).

Include Syntax.

Module LocalMap := LocalMap Map.
Include LocalMap.

Definition context : Type := (LocalMap.t aliasedType ponyType).

Definition sendableCtxt (gamma : context) : context :=
  LocalMap.fold_var
    (fun var varType sendableMap =>
      match varType with
      | aType _ b =>
          if isSendable b
            then LocalMap.addVar var varType sendableMap
            else sendableMap
      end)
    gamma
    (LocalMap.empty aliasedType ponyType).

End Context.

Module Typing (Map : WSfun).

Module Program := Program Map.
Include Program.

Module Context := Context Map.
Include Context.

(* Partial function - not defined for @tag@ *)
Definition viewAdapt
  (objCap : capability)
  (fieldCap : baseCapability) 
  : option capability :=
  match objCap with
  | base iso =>
      match fieldCap with
      | iso => Some (base iso)
      | trn => Some (base iso)
      | ref => Some (base iso)
      | val => Some (base val)
      | box => Some (base tag)
      | tag => Some (base tag)
      end
  | base trn => 
      match fieldCap with
      | iso => Some (base iso)
      | trn => Some (base trn)
      | ref => Some (base trn)
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  | base ref =>
      match fieldCap with
      | iso => Some (base iso)
      | trn => Some (base trn)
      | ref => Some (base ref)
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  | base val =>
      match fieldCap with
      | iso => Some (base val)
      | trn => Some (base val)
      | ref => Some (base val)
      | val => Some (base val)
      | box => Some (base val)
      | tag => Some (base val)
      end
  | base box =>
      match fieldCap with
      | iso => Some (base tag)
      | trn => Some (base box)
      | ref => Some (base box)
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  | base tag => None
  | isohat =>
      match fieldCap with
      | iso => Some isohat
      | trn => Some isohat
      | ref => Some isohat
      | val => Some (base val)
      | box => Some (base val)
      | tag => Some (base tag)
      end
  | trnhat => 
      match fieldCap with
      | iso => Some isohat
      | trn => Some trnhat
      | ref => Some trnhat
      | val => Some (base val)
      | box => Some (base val)
      | tag => Some (base tag)
      end
  end.

(* Partial function - not defined for @val@, @box@, @tag@ *)
Definition writeAdapt
  (objCap : capability)
  (fieldCap : baseCapability) 
  : option capability :=
  match objCap with
  | base iso =>
      match fieldCap with
      | iso => Some isohat
      | trn => Some (base val)
      | ref => Some (base tag)
      | val => Some (base val)
      | box => Some (base tag)
      | tag => Some (base tag)
      end
  | base trn => 
      match fieldCap with
      | iso => Some isohat
      | trn => Some (base val)
      | ref => Some (base box)
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  | base ref =>
      match fieldCap with
      | iso => Some isohat
      | trn => Some trnhat
      | ref => Some (base ref)
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  | base val => None
  | base box => None
  | base tag => None
  | isohat =>
      match fieldCap with
      | iso => Some isohat
      | trn => Some isohat
      | ref => Some isohat
      | val => Some (base val)
      | box => Some (base val)
      | tag => Some (base tag)
      end
  | trnhat => 
      match fieldCap with
      | iso => Some isohat
      | trn => Some trnhat
      | ref => Some trnhat
      | val => Some (base val)
      | box => Some (base box)
      | tag => Some (base tag)
      end
  end.

Inductive safeToWrite : capability -> baseCapability -> Prop :=
  (* Write to an @iso@ *)
  | safeToWrite_iso_iso : safeToWrite (base iso) iso
  | safeToWrite_iso_val : safeToWrite (base iso) val
  | safeToWrite_iso_tag : safeToWrite (base iso) tag
  (* Write to a @trn@ *)
  | safeToWrite_trn_iso : safeToWrite (base trn) iso
  | safeToWrite_trn_trn : safeToWrite (base trn) trn
  | safeToWrite_trn_val : safeToWrite (base trn) val
  | safeToWrite_trn_tag : safeToWrite (base trn) tag
  (* Write to a @ref@ *)
  | safeToWrite_ref (b : baseCapability) : safeToWrite (base ref) b
  (* Write to an @iso^@ *)
  | safeToWrite_isohat (b : baseCapability) : safeToWrite isohat b
  (* Write to a @trn^@ *)
  | safeToWrite_trnhat (b : baseCapability) : safeToWrite trnhat b.

Example safeToWrite_implies_writeAdapt_defined : forall k b, safeToWrite k b -> exists k', writeAdapt k b = Some k'.
Proof.
  intros k b stw_k_b.
  induction stw_k_b; try (compute; eauto).
  (* Solve the three "general" cases, which take any value of b *)
  induction b; try (compute; eauto).
  induction b; try (compute; eauto).
  induction b; try (compute; eauto).
  Qed.
 
Reserved Notation "g |- x : T ==> g'" (at level 9, x at level 50, T at level 50).

Inductive typing { P : Program.program } : context -> cw_encoding -> ponyType -> context -> Prop :=
  (* Path rules *)
  | path_var (gamma : context) (x : var) (aT : aliasedType) 
  : VarMapsTo x aT gamma 
      -> gamma |- (ePath (use x)) : asPonyType aT ==> gamma
  | path_temp (gamma : context) (t : temp) (T : ponyType)
  : TempMapsTo t T gamma
      -> gamma |- (ePath (useTemp t)) : T ==> (removeTemp t gamma)
  | path_consume (gamma : context) (x : var) (aT : aliasedType)
  : VarMapsTo x aT gamma
      -> gamma |- (ePath (consume x)) : hat aT ==> (removeVar x gamma)
  | path_field (gamma gamma' : context) (p : path) (s s' : typeId) (k k'' : capability) (k' : baseCapability) (f : fieldId)
  : gamma |- (ePath p) : (type s k) ==> gamma'
      -> @Program.fieldLookup P s f (aType s' k')
      -> viewAdapt k k' = Some k''
      -> gamma |- (eFieldOfPath (p, f)) : (type s' k'') ==> gamma'
  (* The alias rule *)
  | expr_alias (gamma gamma': context) (x : cw_encoding) (s : typeId) (k : capability) (b : baseCapability)
  : gamma |- x : (type s k) ==> gamma'
    -> (alias k <; base b)
    -> gamma |- (eAlias x) : (type s (base b)) ==> gamma'
  | expr_vardecl (gamma : context) (x : var) (aT : aliasedType)
  : ~ VarIn x gamma
      -> gamma |- (eExpr (varDecl x)) : asPonyType aT ==> (addVar x aT gamma)
  | expr_localassign (gamma gamma' : context) (x : var) (r : rhs) (aT : aliasedType)
  : gamma |- (eAlias (eRhs r)) : asPonyType aT ==> gamma
    -> VarMapsTo x aT gamma'
    -> gamma |- (eExpr (assign x (aliasOf r))) : hat aT ==> gamma'
  | expr_tempassign (gamma gamma' : context) (t : temp) (pf : fieldOfPath) (T : ponyType)
  : gamma |- (eFieldOfPath pf) : T ==> gamma'
    -> gamma |- (eExpr (tempAssign t pf)) : T ==> (LocalMap.addTemp t T gamma')
  | expr_fieldassign (gamma gamma' gamma'' : context) (p p' : path) (f : fieldId) (s s' : typeId) (k k' : capability) (b b' : baseCapability)
  : gamma |- (eAlias (ePath p')) : (type s' (base b)) ==> gamma'
      -> gamma' |- (ePath p) : (type s k) ==> gamma''
      -> @Program.fieldLookup P s f (aType s' b')
      -> safeToWrite k b
      -> (base b) <; (base b')
      -> writeAdapt k b' = Some k'
      -> gamma |- (eRhs (fieldAssign (p, f) (aliasOf p'))) : type s' k' ==> gamma''
  | expr_funcall (gamma gamma' gamma'' : context) (p : path) (args : list (@aliased path)) (s : typeId) (b : baseCapability)
      (mId : methodId) (mArgs : Program.arrayVarMap aliasedType) (returnType : ponyType) (body : expressionSeq)
  : @Program.methodLookup P s mId (Program.mDef b mArgs returnType body)
    -> typing_list gamma (eAPaths args) (Program.argValues mArgs) gamma'
    -> gamma' |- (eAlias (ePath p)) : (type s (base b)) ==> gamma''
    -> gamma |- (eRhs (methodCall (aliasOf p) mId args)) : returnType ==> gamma''
  | expr_becall (gamma gamma' gamma'' : context) (p : path) (args : list (@aliased path)) (s : typeId)
      (bId : behaviourId) (bArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.behaviourLookup P s bId (Program.bDef bArgs body)
    -> typing_list gamma (eAPaths args) (Program.argValues bArgs) gamma'
    -> gamma' |- (eAlias (ePath p)) : (type s (base tag)) ==> gamma''
    -> gamma |- (eRhs (behaviourCall (aliasOf p) bId args)) : (type s (base tag)) ==> gamma''
  | expr_classcon (gamma gamma' : context) (args : list (@aliased path)) (c : classId)
      (kId : constructorId) (cnArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.constructorLookup P (inl c) kId (Program.cnDef cnArgs body)
    -> typing_list gamma (eAPaths args) (Program.argValues cnArgs) gamma'
    -> gamma |- (eRhs (constructorCall (inl c) kId args)) : (type (inl c) (base ref)) ==> gamma'
  | expr_actorcon (gamma gamma' : context) (args : list (@aliased path)) (a : actorId)
      (kId : constructorId) (cnArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.constructorLookup P (inr a) kId (Program.cnDef cnArgs body)
    -> typing_list gamma (eAPaths args) (Program.argValues cnArgs) gamma'
    -> gamma |- (eRhs (constructorCall (inr a) kId args)) : (type (inr a) (base tag)) ==> gamma'
where "G |- x : T ==> G'" := (typing G x T G')
with
typing_list { P : Program.program } : context -> list cw_encoding -> list ponyType -> context -> Prop :=
  | typing_list_nil (gamma : context)
  : typing_list gamma nil nil gamma
  | typing_list_cons (gamma gamma' gamma'' : context) (x : cw_encoding) (t : ponyType) (lx : list cw_encoding) (lt : list ponyType)
  : gamma |- x : t ==> gamma'
    -> typing_list gamma' lx lt gamma''
    -> typing_list gamma (x :: lx) (t :: lt) gamma''.

Lemma typing_paths_func_on_type_and_outcome :
  forall P : Program.program,
  forall gamma gamma' gamma'' : context,
  forall p : path,
  forall T T' : ponyType,
  @typing P gamma (ePath p) T gamma'
  -> @typing P gamma (ePath p) T' gamma''
  -> T = T' /\ gamma' = gamma''.
  intros P gamma gamma' gamma'' p T T' p_type_T_gamma' p_type_T'_gamma''.
  
  destruct p as [ x | x | t ].
  { inversion p_type_T_gamma' as [ _gamma0 _x0 aT p_mapsto_aT | | | | | | | | | | | | ].
    inversion p_type_T'_gamma'' as [ _gamma1 _x1 aT' p_mapsto_aT' | | | | | | | | | | | | ].
    assert (gamma' = gamma'') as ctxts_same by (transitivity gamma; auto).

    split.
    { enough (aT = aT') as aTs_equal.
      rewrite <- aTs_equal. 
      reflexivity.

      apply VarMapsTo_func with (m:=gamma') (var:=x).
      assumption.
      rewrite ctxts_same; assumption.
    }
    { assumption.
    }
  }
  { inversion p_type_T_gamma' as [ | | _gamma0 _x0 aT p_mapsto_aT | | | | | | | | | | ].
    inversion p_type_T'_gamma'' as [ | | _gamma1 _x1 aT' p_mapsto_aT' | | | | | | | | | | ].

    assert (gamma' = gamma'') as ctxts_same by (transitivity (removeVar x gamma); auto).

    split.
    { enough (aT = aT') as aTs_equal.
      rewrite <- aTs_equal.
      reflexivity.

      apply VarMapsTo_func with (m:=gamma) (var:=x); assumption.
    }
    { reflexivity.
    }
  }
  { inversion p_type_T_gamma' as [ | _gamma0 _t0 _T0 t_mapsto_T | | | | | | | | | | | ].
    inversion p_type_T'_gamma'' as [ | _gamma1 _t1 _T'0 t_mapsto_T' | | | | | | | | | | | ].
    
    split.
    { apply TempMapsTo_func with (m:=gamma) (temp:=t); assumption.
    }
    { reflexivity.
    }
  }
  Qed.

Lemma typing_func_on_type_and_outcome :
  forall P : Program.program,
  forall gamma gamma' gamma'' : context,
  forall x : cw_encoding,
  forall T T' : ponyType,
  @typing P gamma x T gamma'
  -> @typing P gamma x T' gamma''
  -> T = T' /\ gamma' = gamma''.
Proof.
  intros P gamma gamma' gamma'' x T T' x_type_T_gamma' x_type_T'_gamma''.
  induction x as [ p | fp | x' IHx' | [] | [] ].
  (* Case for paths is shown as a lemma *)
  { apply typing_paths_func_on_type_and_outcome with (P:=P) (p:=p) (gamma:=gamma); assumption.
  }
  { inversion x_type_T_gamma' as [ | | | _gamma0 _gamma'0 p1 S1 S1' k1 k1' b1 f1 p1_typed_s1_k1 lookup_s1_f1_is_s1'_k1' viewadapt_k1_b1_k1' | | | | | | | | | ].
    inversion x_type_T'_gamma'' as [ | | | _gamma1 _gamma'1 p2 S2 S2' k2 k2' b2 f2 p2_typed_s2_k2 lookup_s2_f2_is_s2'_k2' viewadapt_k2_b2_k2' | | | | | | | | | ].

    assert (p1 = p2 /\ f1 = f2) as [ paths_same fields_same ].
    { assert ((p1, f1) = (p2, f2)) as fps_same by (transitivity fp; auto).
      now inversion fps_same.
    }

    assert (type S1 k1 = type S2 k2 /\ gamma' = gamma'') as [ paths_typed_same ctxts_same ].
    { apply typing_paths_func_on_type_and_outcome with (P:=P) (p:=p1) (gamma:=gamma).
      assumption.
      rewrite paths_same.
      assumption.
    }

    split.
    { assert (S1' = S2' /\ b1 = b2) as [ f_type_ids_same bs_same ].
      { assert (aType S1' b1 = aType S2' b2) as aTypes_same.
        { apply Program.fieldLookup_func with (P:=P) (s:=S1) (f:=f1).
          assumption.
          rewrite fields_same.
          assert (S1 = S2) as type_ids_same by (inversion paths_typed_same; auto).
          rewrite type_ids_same.
          assumption.
        }
        
        now inversion aTypes_same.
      }

      enough (k1' = k2') as vAs_same.
      rewrite f_type_ids_same.
      rewrite vAs_same.
      reflexivity.

      assert (Some k1' = Some k2') as somes_eq.
      { transitivity (viewAdapt k1 b1).
        auto.
        rewrite bs_same.
        assert (k1 = k2) as ks_eq by (inversion paths_typed_same; auto).
        rewrite ks_eq.
        auto.
      }

      inversion somes_eq.
      reflexivity.
    }
    { assumption.
    }
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  { admit. (* TODO *)
  }
  Admitted. (* TODO: prove this helper lemma (v. obvious) *)

End Typing.

Require Import Coq.MSets.MSetInterface.

Module WFExpressions (Map : WSfun) (SetM : WSetsOn).

Module Typing := Typing Map.
Include Typing.

Module TempSet := SetM DecidableTemp.
Definition tempSet := TempSet.t.

Definition consumePath (p : path) : tempSet :=
  match p with
  | useTemp t => TempSet.singleton t
  | _         => TempSet.empty
  end.

Definition consumeRhs (r : rhs) : tempSet :=
  match r with
  | rhsPath p => consumePath p
  | fieldAssign (p, _) (aliasOf p') => TempSet.union (consumePath p) (consumePath p')
  | methodCall (aliasOf rcvr) _ args =>
      fold_left 
        (fun consumed ap =>
          match ap with
          | aliasOf p => TempSet.union consumed (consumePath p)
          end
        )
        args
        (consumePath rcvr)
  | behaviourCall (aliasOf rcvr) _ args =>
      fold_left 
        (fun consumed ap =>
          match ap with
          | aliasOf p => TempSet.union consumed (consumePath p)
          end
        )
        args
        (consumePath rcvr)
  | constructorCall _ _ args =>
      fold_left 
        (fun consumed ap =>
          match ap with
          | aliasOf p => TempSet.union consumed (consumePath p)
          end
        )
        args
        TempSet.empty
  end.


Definition consumeExpr (e : expression) : tempSet :=
  match e with
  | varDecl _ => TempSet.empty
  | assign _ (aliasOf r) => consumeRhs r
  | tempAssign _ (p, _) => consumePath p
  end.

Inductive well_formed_expr { P : Program.program } : context -> expressionSeq -> ponyType -> Prop :=
  | wf_return (gamma gamma' : context) (p : path) (t : ponyType)
  : @typing P gamma (ePath p) t gamma'
    -> well_formed_expr gamma (final p) t
  | wf_vardecl (gamma gamma' : context) (x : var) (E : expressionSeq) (t t' : ponyType)
  : @typing P gamma (eExpr (varDecl x)) t' gamma'
    -> well_formed_expr gamma' E t
    -> well_formed_expr gamma (seq (varDecl x) E) t
  | wf_localassign (gamma gamma' : context) (x : var) (arhs : @aliased rhs) (E : expressionSeq) (t t' : ponyType)
  : @typing P gamma (eExpr (assign x arhs)) t' gamma'
    -> well_formed_expr gamma' E t
    -> well_formed_expr gamma (seq (assign x arhs) E) t
  | wf_tempassign_final (gamma gamma' : context) (t : temp) (pf : fieldOfPath) (p : path) (T T' : ponyType)
  : @typing P gamma (eExpr (tempAssign t pf)) T' gamma'
    -> well_formed_expr gamma' (final p) T
    -> well_formed_expr gamma (seq (tempAssign t pf) (final p)) T
  | wf_tempassign (gamma gamma' : context) (t : temp) (pf : fieldOfPath) (e : expression) (E : expressionSeq) (T T' : ponyType)
  : @typing P gamma (eExpr (tempAssign t pf)) T' gamma'
    -> TempSet.In t (consumeExpr e)
    -> well_formed_expr gamma' (seq e E) T
    -> well_formed_expr gamma (seq (tempAssign t pf) (seq e E)) T.

(* For some method arguments, produce the corresponding typing context *)
Definition argsToContext (args : arrayVarMap aliasedType) : context :=
  ArrayVarMap.fold aliasedType (LocalMap.t aliasedType ponyType)
    (fun key val ctxt => LocalMap.addVar key val ctxt)
    args
    (LocalMap.empty aliasedType ponyType).

Definition well_formed_constructor_def { P : Program.program }
  (thisType : aliasedType) (kD : constructorDef) : Prop
  := forall args body, kD = cnDef args body
        -> exists (t : ponyType),
            @well_formed_expr P
              (LocalMap.addVar this thisType (argsToContext args))
              body
              t.

Definition well_formed_method_def { P : Program.program }
  (thisTypeId : typeId) (mD : methodDef) : Prop
  := forall rcvrCap args returnType body, mD = mDef rcvrCap args returnType body
        -> @well_formed_expr P
            (LocalMap.addVar this (aType thisTypeId rcvrCap) (argsToContext args))
            body
            returnType.

Definition well_formed_behaviour_def { P : Program.program }
  (thisTypeId : actorId) (bD : behaviourDef) : Prop
  := forall args body, bD = bDef args body
        -> exists (t : ponyType),
            @well_formed_expr P
              (LocalMap.addVar this (aType (inr thisTypeId) iso) (argsToContext args))
              body
              t.

Definition well_formed_class { P : Program.program } (c : classId) : Prop :=
  (forall k kD, @constructorLookup P (inl c) k kD -> @well_formed_constructor_def P (aType (inl c) ref) kD)
  /\
  (forall m mD, @methodLookup P (inl c) m mD -> @well_formed_method_def P (inl c) mD).

Definition well_formed_actor { P : Program.program } (a : actorId) : Prop :=
  (forall k kD, @constructorLookup P (inr a) k kD -> @well_formed_constructor_def P (aType (inr a) iso) kD)
  /\
  (forall m mD, @methodLookup P (inr a) m mD -> @well_formed_method_def P (inr a) mD)
  /\
  (forall b bD, @behaviourLookup P (inr a) b bD -> @well_formed_behaviour_def P a bD).

Definition well_formed_program (P : Program.program) : Prop :=
  (forall a : actorId, @well_formed_actor P a)
  /\ (forall c : classId, @well_formed_class P c).

End WFExpressions.
