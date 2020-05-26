From Pony Require Import Language.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.Equalities.

Module Address.

Definition addr : Type := nat.

Inductive actorAddr : Type := actorAddress : addr -> actorAddr.
Inductive objectAddr : Type := objectAddress : addr -> objectAddr.
Inductive messageAddr : Type := messageAddress : addr -> messageAddr.
Inductive frameAddr : Type := frameAddress : addr -> frameAddr.

Notation "'someAddr'" := ((sum ( sum (sum actorAddr objectAddr) messageAddr) frameAddr)).

End Address.

Module DecidableActorAddr.
Include (UsualDecidableTypeBoth with Definition t := Address.actorAddr).
Scheme Equality for Address.actorAddr.
End DecidableActorAddr.

Module DecidableObjectAddr.
Include (UsualDecidableTypeBoth with Definition t := Address.objectAddr).
Scheme Equality for Address.objectAddr.
End DecidableObjectAddr.

Module DecidableMessageAddr.
Include (UsualDecidableTypeBoth with Definition t := Address.messageAddr).
Scheme Equality for Address.messageAddr.
End DecidableMessageAddr.

Module DecidableFrameAddr.
Include (UsualDecidableTypeBoth with Definition t := Address.frameAddr).
Scheme Equality for Address.frameAddr.
End DecidableFrameAddr.

Module DecidableSomeAddr.
Include Address.
Include (UsualDecidableTypeBoth with Definition t := someAddr).
End DecidableSomeAddr.

Module Heap (Map : WSfun).

Include Address.

Notation "t ?" := (option t) (at level 50).

Module ActorMap := Map DecidableActorAddr.
Definition actorMap := ActorMap.t.

Module ObjectMap := Map DecidableObjectAddr.
Definition objectMap := ObjectMap.t.

Module MessageMap := Map DecidableMessageAddr.
Definition messageMap := MessageMap.t.

Module FrameMap := Map DecidableFrameAddr.
Definition frameMap := FrameMap.t.

Module FieldMap := Map DecidableField.
Definition fieldMap := FieldMap.t.

Module VarMap := Map DecidableVar.
Definition varMap := VarMap.t.

Definition value : Type := someAddr?.

Definition localVars : Type := varMap value.

Record actor : Type :=
  actorAlloc
  { actorId : Syntax.actorId 
  ; actorFields : fieldMap value
  ; messageQueue : messageAddr?
  ; frameStack : frameAddr?
  }.

Instance setActor : Settable _ := settable! actorAlloc <actorId; actorFields; messageQueue; frameStack>.

Definition addActorField (f : Syntax.fieldId) (v : value) (a : actor) : actor :=
  a <|actorFields := (FieldMap.add f v (actorFields a))|>.

Record object : Type :=
  objectAlloc
  { objectId : Syntax.classId
  ; objectFields : fieldMap value
  }.

Instance setObject : Settable _ := settable! objectAlloc <objectId; objectFields>.

Definition addObjectField (f : Syntax.fieldId) (v : value) (o : object) : object :=
  o <|objectFields := (FieldMap.add f v (objectFields o))|>.

Record message : Type :=
  messageAlloc
  { messageId : Syntax.behaviourId
  ; receiverId : Syntax.actorId
  ; messageArgs : list value
  ; nextMessage : messageAddr?
  }.

Record frame : Type :=
  frameAlloc
  { lVars : localVars 
  ; toExecute : Syntax.expressionSeq
  ; returnVar : Syntax.var?
  ; superFrame : frameAddr?
  }.

Record heap : Type :=
  heapAlloc
  { actors : actorMap actor
  ; objects : objectMap object
  ; messages : messageMap message
  ; frames : frameMap frame
  }.

Instance setHeap : Settable _ := settable! heapAlloc <actors; objects; messages; frames>.

Definition addActor (iota : actorAddr) (a : actor) (chi : heap) : heap :=
  chi <|actors := (ActorMap.add iota a (actors chi))|>.

Definition addObject (iota : objectAddr) (o : object) (chi : heap) : heap :=
  chi <|objects := (ObjectMap.add iota o (objects chi))|>.

Definition someActorAddr (iota : actorAddr) : someAddr := (inl (inl (inl iota))).
Definition someObjectAddr (iota : objectAddr) : someAddr := (inl (inl (inr iota))).
Definition someMessageAddr (iota : messageAddr) : someAddr := (inl (inr iota)).
Definition someFrameAddr (iota : frameAddr) : someAddr := (inr iota).

Inductive HeapMapsTo : forall X : Type, someAddr -> X -> heap -> Prop :=
  | ActorMapsTo (iota : actorAddr) (a : actor) (chi : heap)
  : ActorMap.MapsTo iota a (actors chi) 
      -> HeapMapsTo actor (someActorAddr iota) a chi
  | ObjectMapsTo (iota : objectAddr) (a : object) (chi : heap)
  : ObjectMap.MapsTo iota a (objects chi) 
      -> HeapMapsTo object (someObjectAddr iota) a chi
  | MessageMapsTo (iota : messageAddr) (a : message) (chi : heap)
  : MessageMap.MapsTo iota a (messages chi) 
      -> HeapMapsTo message (someMessageAddr iota) a chi
  | FrameMapsTo (iota : frameAddr) (a : frame) (chi : heap)
  : FrameMap.MapsTo iota a (frames chi) 
      -> HeapMapsTo frame (someFrameAddr iota) a chi.

Definition HeapIn (iota : someAddr) (chi : heap) : Prop :=
  exists X : Type, exists x : X, HeapMapsTo X iota x chi.

Definition HeapAddrType (iota : someAddr) (s : Syntax.typeId) (chi : heap) : Prop :=
  exists a F mQ fS, inr a = s /\ HeapMapsTo actor iota (actorAlloc a F mQ fS) chi
  \/
  exists c F, inl c = s /\ HeapMapsTo object iota (objectAlloc c F) chi.

Definition HeapValueType (v : value) (s : Syntax.typeId) (chi : heap) : Prop :=
  forall iota, v = Some iota -> HeapAddrType iota s chi.

Definition HeapFieldLookup (v : value) (f : Syntax.fieldId) (v' : value) (chi : heap) : Prop :=
  ( v = None /\ v' = None )
  \/
  ( exists iota a, v = Some iota /\ HeapMapsTo actor iota a chi /\ FieldMap.MapsTo f v' (actorFields a) )
  \/
  ( exists iota o, v = Some iota /\ HeapMapsTo object iota o chi /\ FieldMap.MapsTo f v' (objectFields o) ).

(* Insert the second value into the field mapping of the first value at the given field id *)
Inductive HeapFieldAdd : value -> Syntax.fieldId -> value -> heap -> heap -> Prop :=
  | HeapFieldAdd_null (f : Syntax.fieldId) (v : value) (chi : heap)
  : HeapFieldAdd None f v chi chi
  | HeapFieldAdd_actor (iota : actorAddr) (a : actor) (f : Syntax.fieldId) (v : value) (chi : heap)
  : HeapMapsTo actor (someActorAddr iota) a chi
    -> HeapFieldAdd (Some (someActorAddr iota)) f v chi (addActor iota a chi)
  | HeapFieldAdd_object (iota : objectAddr) (o : object) (f : Syntax.fieldId) (v : value) (chi : heap)
  : HeapMapsTo object (someObjectAddr iota) o chi
    -> HeapFieldAdd (Some (someObjectAddr iota)) f v chi (addObject iota o chi).

(* Types in the heap *)

(* Module temporarily disabled for type reasons *)

(*Module HeapTyping (Map : WSfun).

Include Heap Map.*)

Inductive heapTyping : value -> Syntax.typeId -> heap -> Prop :=
  | heaptyp_object (iota : someAddr) (obj : object) (C : Syntax.classId) (chi : heap)
  : HeapMapsTo object iota obj chi
    -> objectId obj = C
    -> heapTyping (Some iota) (Syntax.classTypeId C) chi
  | heaptyp_actor (iota : someAddr) (act : actor) (A : Syntax.actorId) (chi : heap)
  : HeapMapsTo actor iota act chi
    -> actorId act = A
    -> heapTyping (Some iota) (Syntax.actorTypeId A) chi
  | heaptyp_null (S : Syntax.typeId) (chi : heap)
  : heapTyping None S chi.

(*End HeapTyping.*)

End Heap.

