Add LoadPath "." as Pony.
From Pony Require Import Language.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.

Module Context (Map : WSfun).

Module VarTempMap := Map DecidableVarTemp.
Definition varTempMap := VarTempMap.t.

Definition context : Type := (varTempMap Syntax.aliasedType).

Definition sendableCtxt (gamma : context) : context :=
  VarTempMap.fold
    (fun var varType sendableMap =>
      match varType with
      | Syntax.aType _ b =>
          if Syntax.isSendable b
            then VarTempMap.add var varType sendableMap
            else sendableMap
      end)
    (VarTempMap.empty Syntax.aliasedType)
    gamma.

Definition VarMapsTo (var : Syntax.var) (aT : Syntax.aliasedType) (gamma : context) : Prop :=
  VarTempMap.MapsTo (inl var) aT gamma.

Definition TempMapsTo (temp : Syntax.temp) (aT : Syntax.aliasedType) (gamma : context) : Prop :=
  VarTempMap.MapsTo (inr temp) aT gamma.

Definition VarIn (var : Syntax.var) (gamma : context) : Prop :=
  VarTempMap.In (inl var) gamma.

Definition addVar (var : Syntax.var) (aT : Syntax.aliasedType) (gamma : context) : context :=
  VarTempMap.add (inl var) aT gamma.

Definition removeVar (var : Syntax.var) (gamma : context) : context :=
  VarTempMap.remove (inl var) gamma.

End Context.

Module Typing (Map : WSfun).

Module Program := Program Map.
Include Program.
Include Syntax.

Module Context := Context Map.
Include Context.

Definition viewAdapt
  (objCap : { k : Syntax.capability | k <> Syntax.base Syntax.tag })
  (fieldCap : Syntax.baseCapability) 
  : Syntax.capability.
Proof.
  Admitted.

Definition writeAdapt
  (objCap : Syntax.capability)
  (fieldCap : Syntax.baseCapability)
  : Syntax.capability.
Proof.
  Admitted.

Definition safeToWrite
  (objCap : Syntax.capability)
  (valCap : Syntax.baseCapability)
  : Prop.
Proof.
  Admitted.
 
Reserved Notation "g |-{ X } x : T ==> g'" (at level 9, x at level 50, T at level 50).

Inductive typing { P : Program.program } : forall ( X : Type), context -> X -> Syntax.ponyType -> context -> Prop :=
  (* Path rules *)
  | path_var (gamma : context) (x : Syntax.var) (aT : Syntax.aliasedType) 
  : VarMapsTo x aT gamma 
      -> gamma |-{ Syntax.path } (Syntax.use x) : Syntax.asPonyType aT ==> gamma
  | path_consume (gamma : context) (x : Syntax.var) (aT : Syntax.aliasedType)
  : VarMapsTo x aT gamma
      -> gamma |-{ Syntax.path } (Syntax.consume x) : Syntax.asPonyType aT ==> (removeVar x gamma)
  | path_field (gamma gamma' : context) (p : Syntax.path) (s s' : Syntax.typeId) (k : Syntax.capability) (k' : Syntax.baseCapability) (f : Syntax.fieldId) (witness_k_not_tag : k <> Syntax.base Syntax.tag)
  : gamma |-{ Syntax.path } p : (Syntax.type s k) ==> gamma'
      -> @Program.fieldLookup P s f (Syntax.aType s' k')
      -> gamma |-{ Syntax.fieldOfPath } (p, f) : (Syntax.type s' (viewAdapt (exist (fun x => x <> Syntax.base Syntax.tag) k witness_k_not_tag) k')) ==> gamma'
  (* The alias rule *)
  | expr_alias { X : Type } (gamma gamma': context) (x : X) (s : Syntax.typeId) (k : Syntax.capability) (b : Syntax.baseCapability)
  : gamma |-{ X } x : (Syntax.type s k) ==> gamma'
    -> (Syntax.alias k <; Syntax.base b)
    -> gamma |-{ Syntax.aliased } (Syntax.aliasOf x) : (Syntax.type s (Syntax.base b)) ==> gamma'
  | expr_vardecl (gamma : context) (x : Syntax.var) (aT : Syntax.aliasedType)
  : ~ VarIn x gamma
      -> gamma |-{ Syntax.expression } Syntax.varDecl x : Syntax.asPonyType aT ==> (addVar x aT gamma)
  | expr_localassign (gamma gamma' : context) (x : Syntax.var) (arhs : @Syntax.aliased Syntax.rhs) (aT : Syntax.aliasedType)
  : gamma |-{ @Syntax.aliased Syntax.rhs } arhs : Syntax.asPonyType aT ==> gamma
    -> VarMapsTo x aT gamma'
    -> gamma |-{ Syntax.expression } Syntax.assign x arhs : Syntax.hat aT ==> gamma'
  | expr_fieldassign (gamma gamma' gamma'' : context) (p p' : Syntax.path) (f : Syntax.fieldId) (s s' : Syntax.typeId) (k : Syntax.capability) (b b' : Syntax.baseCapability)
  : gamma |-{ Syntax.aliased } (Syntax.aliasOf p') : (Syntax.type s' (Syntax.base b)) ==> gamma'
      -> gamma' |-{ Syntax.path } p : (Syntax.type s k) ==> gamma''
      -> @Program.fieldLookup P s f (Syntax.aType s' b')
      -> safeToWrite k b
      -> (Syntax.base b) <; (Syntax.base b')
      -> gamma |-{ Syntax.rhs } Syntax.fieldAssign (p, f) (Syntax.aliasOf p') : Syntax.type s' (writeAdapt k b') ==> gamma''
where "G |-{ X } x : T ==> G'" := (typing X G x T G')
with
typing_list { P : Program.program } : forall (X : Type), context -> list X -> list Syntax.ponyType -> context -> Prop :=
  | typing_list_nil (X : Type) (gamma : context)
  : typing_list X gamma nil nil gamma
  | typing_list_cons (X : Type) (gamma gamma' gamma'' : context) (x : X) (t : Syntax.ponyType) (lx : list X) (lt : list Syntax.ponyType)
  : gamma |-{ X } x : t ==> gamma'
    -> typing_list X gamma' lx lt gamma''
    -> typing_list X gamma (x :: lx) (t :: lt) gamma''.

End Typing.
