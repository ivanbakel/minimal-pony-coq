Add LoadPath "." as Pony.
From Pony Require Import Language.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.

Module Context (Map : WSfun).

Module VarTempMap := Map DecidableVarTemp.
Definition varTempMap := VarTempMap.t.

Include Syntax.

Definition context : Type := (varTempMap aliasedType).

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

Definition writeAdapt
  (objCap : capability)
  (fieldCap : baseCapability)
  : capability.
Proof.
  Admitted.

Definition safeToWrite
  (objCap : capability)
  (valCap : baseCapability)
  : Prop.
Proof.
  Admitted.
 
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
  | expr_fieldassign (gamma gamma' gamma'' : context) (p p' : path) (f : fieldId) (s s' : typeId) (k : capability) (b b' : baseCapability)
  : gamma |-{ aliased } (aliasOf p') : (type s' (base b)) ==> gamma'
      -> gamma' |-{ path } p : (type s k) ==> gamma''
      -> @Program.fieldLookup P s f (aType s' b')
      -> safeToWrite k b
      -> (base b) <; (base b')
      -> gamma |-{ rhs } fieldAssign (p, f) (aliasOf p') : type s' (writeAdapt k b') ==> gamma''
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
