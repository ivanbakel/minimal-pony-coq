Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Module Syntax.

Inductive baseCapability : Type :=
  | iso
  | trn
  | ref
  | val
  | box
  | tag.

Inductive capability : Type :=
  | base : baseCapability -> capability
  | isohat : capability
  | trnhat : capability. 

Reserved Notation "k <; k'" (at level 80).

Inductive subcapability : capability -> capability -> Prop :=
  | subcap_refl (k : capability) : k <; k
  | subcap_trans (k k' k'' : capability) : k <; k' -> k' <; k'' -> k <; k''
  | subcap_isohat_iso : isohat <; base iso
  | subcap_isohat_trnhat : isohat <; trnhat
  | subcap_trnhat_trn : trnhat <; base trn
  | subcap_trnhat_ref : trnhat <; base ref
  | subcap_trnhat_val : trnhat <; base val
  | subcap_trn_box : base trn <; base box
  | subcap_ref_box : base ref <; base box
  | subcap_val_box : base val <; base box
  | subcap_iso_tag : base iso <; base tag
  | subcap_box_tag : base box <; base tag
where "k <; k'" := (subcapability k k').

Example all_subcap_tag (k : capability) : k <; base tag :=
  match k with
    | isohat => subcap_trans isohat (base iso) (base tag) (subcap_isohat_iso) (subcap_iso_tag)
    | trnhat => subcap_trans trnhat (base trn) (base tag) (subcap_trnhat_trn) (subcap_trans (base trn) (base box) (base tag) (subcap_trn_box) (subcap_box_tag))
    | base iso => subcap_iso_tag
    | base trn => subcap_trans (base trn) (base box) (base tag) (subcap_trn_box) (subcap_box_tag)
    | base ref => subcap_trans (base ref) (base box) (base tag) (subcap_ref_box) (subcap_box_tag)
    | base val => subcap_trans (base val) (base box) (base tag) (subcap_val_box) (subcap_box_tag)
    | base box => subcap_box_tag
    | base tag => subcap_refl (base tag)
  end.

Definition alias (cap : capability) : capability :=
  match cap with
    | isohat => base iso
    | trnhat => base trn
    | base iso => base tag
    | base trn => base box
    | base b => base b
  end.

Inductive sendable : baseCapability -> Prop :=
  | sendable_tag : sendable tag
  | sendable_val : sendable val
  | sendable_iso : sendable iso.

Definition isSendable (cap : baseCapability) : bool :=
  match cap with
    | tag => true
    | val => true
    | iso => true
    | _   => false
  end.

Inductive classId : Type :=
  | cId : string -> classId.

Inductive actorId : Type :=
  | aId : string -> actorId.

Definition typeId : Type := classId + actorId.

Inductive ponyType : Type :=
  | type (s : typeId) (k : capability).

Inductive aliasedType : Type :=
  | aType (s : typeId) (b : baseCapability).

Definition asPonyType (aT : aliasedType) : ponyType :=
  match aT with
    | aType s b => type s (base b)
  end.

Definition hat (aT : aliasedType) : ponyType :=
  match aT with
    | aType s iso => type s isohat
    | aType s trn => type s trnhat
    | aType s b   => type s (base b)
  end.

Inductive var : Type :=
  | variable : string -> var.

Inductive temp : Type :=
  | temporary : string -> temp.

Inductive path : Type :=
  | use (x : var)
  | consume (x : var)
  | useTemp (t : temp).

Inductive fieldId : Type :=
  | fId : string -> fieldId.

Definition fieldOfPath : Type := prod path fieldId.

Inductive methodId : Type :=
  | mId : string -> methodId.

Inductive behaviourId : Type :=
  | bId : string -> behaviourId.

Inductive constructorId : Type :=
  | cnId : string -> constructorId.

Inductive aliased { X : Type } : Type :=
  | aliasOf (x : X).

Inductive rhs : Type :=
  | rhsPath (p : path)
  | fieldAssign (pf : fieldOfPath) (ap : @aliased path)
  | methodCall (rcvr : @aliased path) (m : methodId) (args : list (@aliased path))
  | behaviourCall (rcvr : @aliased path) (b : behaviourId) (args : list (@aliased path))
  | constructorCall (rcvrType : ponyType) (k : constructorId) (args : list (@aliased path)).

Inductive expression : Type :=
  | varDecl (x : var)
  | assign (x : var) (arhs : @aliased rhs)
  | tempAssign (t : temp) (pf : fieldOfPath).

Inductive expressionSeq : Type :=
  | final : path -> expressionSeq
  | seq : expression -> expressionSeq -> expressionSeq.

End Syntax.

Require Import Coq.Structures.Equalities.

Module DecidableVar.
Include (UsualDecidableTypeBoth with Definition t := Syntax.var).
Scheme Equality for Syntax.var.
End DecidableVar.

Module DecidableTemp.
Include (UsualDecidableTypeBoth with Definition t := Syntax.temp).
Scheme Equality for Syntax.temp.
End DecidableTemp.

Module DecidableVarTemp.
Include (UsualDecidableTypeBoth with Definition t := sum Syntax.var Syntax.temp).
End DecidableVarTemp.

Module DecidableField.
Include (UsualDecidableTypeBoth with Definition t := Syntax.fieldId).
Scheme Equality for Syntax.fieldId.
End DecidableField.

Module DecidableConstructor.
Include (UsualDecidableTypeBoth with Definition t := Syntax.constructorId).
Scheme Equality for Syntax.constructorId.
End DecidableConstructor.

Module DecidableMethod.
Include (UsualDecidableTypeBoth with Definition t := Syntax.methodId).
Scheme Equality for Syntax.methodId.
End DecidableMethod.

Module DecidableBehaviour.
Include (UsualDecidableTypeBoth with Definition t := Syntax.behaviourId).
Scheme Equality for Syntax.behaviourId.
End DecidableBehaviour.

Module DecidableClass.
Include (UsualDecidableTypeBoth with Definition t := Syntax.classId).
Scheme Equality for Syntax.classId.
End DecidableClass.

Module DecidableActor.
Include (UsualDecidableTypeBoth with Definition t := Syntax.actorId).
Scheme Equality for Syntax.actorId.
End DecidableActor.

Require Import Coq.FSets.FMapInterface.

Module Program (Map : WSfun).

Module VarMap := Map DecidableVar.
Definition varMap := VarMap.t.

Module FieldMap := Map DecidableField.
Definition fieldMap := FieldMap.t.

Module ConstructorMap := Map DecidableConstructor.
Definition constructorMap := ConstructorMap.t.

Module MethodMap := Map DecidableMethod.
Definition methodMap := MethodMap.t.

Module BehaviourMap := Map DecidableBehaviour.
Definition behaviourMap := BehaviourMap.t.

Module ClassMap := Map DecidableClass.
Definition classMap := ClassMap.t.

Module ActorMap := Map DecidableActor.
Definition actorMap := ActorMap.t.

Inductive constructorDef : Type :=
  | cnDef (args : varMap Syntax.aliasedType) (body : Syntax.expressionSeq).

Inductive methodDef : Type :=
  | mDef
      (receiverCap : Syntax.baseCapability)
      (args : varMap Syntax.aliasedType)
      (returnType : Syntax.ponyType)
      (body : Syntax.expressionSeq).

Inductive behaviourDef : Type :=
  | bDef (args : varMap Syntax.aliasedType) (body : Syntax.expressionSeq).

Record classDef : Type :=
  cDef
  { classFields : fieldMap Syntax.aliasedType
  ; classConstructors : constructorMap constructorDef
  ; classMethods : methodMap methodDef
  }.

Record actorDef : Type :=
  aDef 
  { actorFields : fieldMap Syntax.aliasedType
  ; actorConstructors : constructorMap constructorDef
  ; actorMethods : methodMap methodDef
  ; actorBehaviours : behaviourMap behaviourDef
  }.

Record program : Type :=
  prog
  { classes : classMap classDef
  ; actors : actorMap actorDef
  }.

Definition fieldLookup { p : program } (s : Syntax.typeId) (f : Syntax.fieldId) (t : Syntax.aliasedType) : Prop
  := exists (c : Syntax.classId) (cd : classDef), s = inl c /\ ClassMap.MapsTo c cd (classes p) /\ FieldMap.MapsTo f t (classFields cd)
      \/ exists (a : Syntax.actorId) (ad : actorDef), s = inr a /\ ActorMap.MapsTo a ad (actors p) /\ FieldMap.MapsTo f t (actorFields ad).

End Program.
