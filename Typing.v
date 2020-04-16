Add LoadPath "." as Pony.
From Pony Require Import Language.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.

Module Context (Map : WSfun).

Module VarTempMap := Map DecidableVarTemp.
Definition varTempMap := VarTempMap.t.

Include Syntax.

Definition context : Type := (varTempMap aliasedType).

Definition contextKey : Type := VarTempMap.key.

Definition sendableCtxt (gamma : context) : context :=
  VarTempMap.fold
    (fun var varType sendableMap =>
      match varType with
      | aType _ b =>
          if isSendable b
            then VarTempMap.add var varType sendableMap
            else sendableMap
      end)
    (VarTempMap.empty aliasedType)
    gamma.

Definition VarMapsTo (var : var) (aT : aliasedType) (gamma : context) : Prop :=
  VarTempMap.MapsTo (inl var) aT gamma.

Definition TempMapsTo (temp : temp) (aT : aliasedType) (gamma : context) : Prop :=
  VarTempMap.MapsTo (inr temp) aT gamma.

Definition VarIn (var : var) (gamma : context) : Prop :=
  VarTempMap.In (inl var) gamma.

Definition addVar (var : var) (aT : aliasedType) (gamma : context) : context :=
  VarTempMap.add (inl var) aT gamma.

Definition removeVar (var : var) (gamma : context) : context :=
  VarTempMap.remove (inl var) gamma.

Fixpoint removeMany (keys : list contextKey) (gamma : context) :=
  match keys with
  | h :: t => VarTempMap.remove h (removeMany t gamma)
  | nil => gamma
  end.

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
 
Reserved Notation "g |-{ X } x : T ==> g'" (at level 9, x at level 50, T at level 50).

Inductive typing { P : Program.program } : forall ( X : Type), context -> X -> ponyType -> context -> Prop :=
  (* Path rules *)
  | path_var (gamma : context) (x : var) (aT : aliasedType) 
  : VarMapsTo x aT gamma 
      -> gamma |-{ path } (use x) : asPonyType aT ==> gamma
  | path_consume (gamma : context) (x : var) (aT : aliasedType)
  : VarMapsTo x aT gamma
      -> gamma |-{ path } (consume x) : asPonyType aT ==> (removeVar x gamma)
  | path_field (gamma gamma' : context) (p : path) (s s' : typeId) (k k'' : capability) (k' : baseCapability) (f : fieldId)
  : gamma |-{ path } p : (type s k) ==> gamma'
      -> @Program.fieldLookup P s f (aType s' k')
      -> viewAdapt k k' = Some k''
      -> gamma |-{ fieldOfPath } (p, f) : (type s' k'') ==> gamma'
  (* The alias rule *)
  | expr_alias { X : Type } (gamma gamma': context) (x : X) (s : typeId) (k : capability) (b : baseCapability)
  : gamma |-{ X } x : (type s k) ==> gamma'
    -> (alias k <; base b)
    -> gamma |-{ aliased } (aliasOf x) : (type s (base b)) ==> gamma'
  | expr_vardecl (gamma : context) (x : var) (aT : aliasedType)
  : ~ VarIn x gamma
      -> gamma |-{ expression } varDecl x : asPonyType aT ==> (addVar x aT gamma)
  | expr_localassign (gamma gamma' : context) (x : var) (arhs : @aliased rhs) (aT : aliasedType)
  : gamma |-{ @aliased rhs } arhs : asPonyType aT ==> gamma
    -> VarMapsTo x aT gamma'
    -> gamma |-{ expression } assign x arhs : hat aT ==> gamma'
  | expr_fieldassign (gamma gamma' gamma'' : context) (p p' : path) (f : fieldId) (s s' : typeId) (k k' : capability) (b b' : baseCapability)
  : gamma |-{ aliased } (aliasOf p') : (type s' (base b)) ==> gamma'
      -> gamma' |-{ path } p : (type s k) ==> gamma''
      -> @Program.fieldLookup P s f (aType s' b')
      -> safeToWrite k b
      -> (base b) <; (base b')
      -> writeAdapt k b' = Some k'
      -> gamma |-{ rhs } fieldAssign (p, f) (aliasOf p') : type s' k' ==> gamma''
  | expr_funcall (gamma gamma' gamma'' : context) (ap : @aliased path) (args : list (@aliased path)) (s : typeId) (b : baseCapability)
      (mId : methodId) (mArgs : Program.arrayVarMap aliasedType) (returnType : ponyType) (body : expressionSeq)
  : @Program.methodLookup P s mId (Program.mDef b mArgs returnType body)
    -> typing_list (@aliased path) gamma args (Program.argValues mArgs) gamma'
    -> gamma' |-{ @aliased path } ap : (type s (base b)) ==> gamma''
    -> gamma |-{ rhs } methodCall ap mId args : returnType ==> gamma''
  | expr_becall (gamma gamma' gamma'' : context) (ap : @aliased path) (args : list (@aliased path)) (s : typeId)
      (bId : behaviourId) (bArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.behaviourLookup P s bId (Program.bDef bArgs body)
    -> typing_list (@aliased path) gamma args (Program.argValues bArgs) gamma'
    -> gamma' |-{ @aliased path } ap : (type s (base tag)) ==> gamma''
    -> gamma |-{ rhs } behaviourCall ap bId args : (type s (base tag)) ==> gamma''
  | expr_classcon (gamma gamma' : context) (args : list (@aliased path)) (c : classId)
      (kId : constructorId) (cnArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.constructorLookup P (inl c) kId (Program.cnDef cnArgs body)
    -> typing_list (@aliased path) gamma args (Program.argValues cnArgs) gamma'
    -> gamma |-{ rhs } constructorCall (inl c) kId args : (type (inl c) (base ref)) ==> gamma'
  | expr_actorcon (gamma gamma' : context) (args : list (@aliased path)) (a : actorId)
      (kId : constructorId) (cnArgs : Program.arrayVarMap aliasedType) (body : expressionSeq)
  : @Program.constructorLookup P (inr a) kId (Program.cnDef cnArgs body)
    -> typing_list (@aliased path) gamma args (Program.argValues cnArgs) gamma'
    -> gamma |-{ rhs } constructorCall (inr a) kId args : (type (inr a) (base tag)) ==> gamma'
where "G |-{ X } x : T ==> G'" := (typing X G x T G')
with
typing_list { P : Program.program } : forall (X : Type), context -> list X -> list ponyType -> context -> Prop :=
  | typing_list_nil (X : Type) (gamma : context)
  : typing_list X gamma nil nil gamma
  | typing_list_cons (X : Type) (gamma gamma' gamma'' : context) (x : X) (t : ponyType) (lx : list X) (lt : list ponyType)
  : gamma |-{ X } x : t ==> gamma'
    -> typing_list X gamma' lx lt gamma''
    -> typing_list X gamma (x :: lx) (t :: lt) gamma''.

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
  : @typing P path gamma p t gamma'
    -> well_formed_expr gamma (final p) t
  | wf_vardecl (gamma gamma' : context) (x : var) (E : expressionSeq) (t t' : ponyType)
  : @typing P expression gamma (varDecl x) t' gamma'
    -> well_formed_expr gamma' E t
    -> well_formed_expr gamma (seq (varDecl x) E) t
  | wf_localassign (gamma gamma' : context) (x : var) (arhs : @aliased rhs) (E : expressionSeq) (t t' : ponyType)
  : @typing P expression gamma (assign x arhs) t' gamma'
    -> well_formed_expr gamma' E t
    -> well_formed_expr gamma (seq (assign x arhs) E) t
  | wf_tempassign_final (gamma gamma' : context) (t : temp) (pf : fieldOfPath) (p : path) (T T' : ponyType)
  : @typing P expression gamma (tempAssign t pf) T' gamma'
    -> well_formed_expr gamma' (final p) T
    -> well_formed_expr gamma (seq (tempAssign t pf) (final p)) T
  | wf_tempassign (gamma gamma' : context) (t : temp) (pf : fieldOfPath) (e : expression) (E : expressionSeq) (T T' : ponyType)
  : @typing P expression gamma (tempAssign t pf) T' gamma'
    -> TempSet.In t (consumeExpr e)
    -> well_formed_expr gamma' (seq e E) T
    -> well_formed_expr gamma (seq (tempAssign t pf) (seq e E)) T.


End WFExpressions.
