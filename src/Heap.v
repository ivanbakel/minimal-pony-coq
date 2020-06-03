From Pony Require Import Language LocalMap.

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

Module ActorInstMap := Map DecidableActorAddr.
Definition actorInstMap := ActorInstMap.t.

Module ObjectMap := Map DecidableObjectAddr.
Definition objectMap := ObjectMap.t.

Module MessageMap := Map DecidableMessageAddr.
Definition messageMap := MessageMap.t.

Module FrameMap := Map DecidableFrameAddr.
Definition frameMap := FrameMap.t.

Module FieldMap := Map DecidableField.
Definition fieldMap := FieldMap.t.

Module LocalMap := LocalMap Map.
Import LocalMap.

Definition value : Type := someAddr?.

Definition localVars : Type := LocalMap.t value value.
Definition emptyLocals : localVars := LocalMap.empty value value.

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
  ; messageArgs : arrayVarMap value
  ; nextMessage : messageAddr?
  }.

Instance setMessage : Settable _ := settable! messageAlloc <messageId; messageArgs; nextMessage>.

Record frame : Type :=
  frameAlloc
  { lVars : localVars 
  ; toExecute : Syntax.expressionSeq
  ; returnVar : Syntax.var?
  ; superFrame : frameAddr?
  }.

Record heap : Type :=
  heapAlloc
  { actors : actorInstMap actor
  ; objects : objectMap object
  ; messages : messageMap message
  ; frames : frameMap frame
  }.

Instance setHeap : Settable _ := settable! heapAlloc <actors; objects; messages; frames>.

Definition addActor (iota : actorAddr) (a : actor) (chi : heap) : heap :=
  chi <|actors := (ActorInstMap.add iota a (actors chi))|>.

Definition addObject (iota : objectAddr) (o : object) (chi : heap) : heap :=
  chi <|objects := (ObjectMap.add iota o (objects chi))|>.

Definition addMessage (iota : messageAddr) (m : message) (chi : heap) : heap :=
  chi <|messages := (MessageMap.add iota m (messages chi))|>.

Definition addFrame (iota : frameAddr) (f : frame) (chi : heap) : heap :=
  chi <|frames := (FrameMap.add iota f (frames chi))|>.

Definition removeMessage (iota : messageAddr) (chi : heap) : heap :=
  chi <| messages := (MessageMap.remove iota (messages chi)) |>.

Definition someActorAddr (iota : actorAddr) : someAddr := (inl (inl (inl iota))).
Definition someObjectAddr (iota : objectAddr) : someAddr := (inl (inl (inr iota))).
Definition someMessageAddr (iota : messageAddr) : someAddr := (inl (inr iota)).
Definition someFrameAddr (iota : frameAddr) : someAddr := (inr iota).

Inductive HeapMapsTo : forall X : Type, someAddr -> X -> heap -> Prop :=
  | ActorInstMapsTo (iota : actorAddr) (a : actor) (chi : heap)
  : ActorInstMap.MapsTo iota a (actors chi) 
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

Definition HeapFresh (iota : someAddr) (chi : heap) := ~ HeapIn iota chi.

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

Inductive HeapMessageAppend : value -> Syntax.behaviourId -> arrayVarMap value -> heap -> heap -> Prop :=
  | HeapMessageAppend_null (b : Syntax.behaviourId) (A : arrayVarMap value) (chi : heap)
  : HeapMessageAppend None b A chi chi
  | HeapMessageAppend_noqueue (iota : actorAddr) (a : actor) (b : Syntax.behaviourId) (A : arrayVarMap value) (chi : heap) (freshAddr : messageAddr)
  : messageQueue a = None
    -> HeapMapsTo actor (someActorAddr iota) a chi
    -> HeapFresh (someMessageAddr freshAddr) chi
    -> HeapMessageAppend (Some (someActorAddr iota)) b A chi (addActor iota (a <| messageQueue := (Some freshAddr) |>) (addMessage freshAddr (messageAlloc b A None) chi))
  | HeapMessageAppend_queue (iota : actorAddr) (iota_m : messageAddr) (a : actor) (b : Syntax.behaviourId) (A : arrayVarMap value) (chi chi' : heap)
  : messageQueue a = Some iota_m 
    -> HeapMapsTo actor (someActorAddr iota) a chi
    -> HeapMessageAppendQueue iota_m b A chi chi'
    -> HeapMessageAppend (Some (someActorAddr iota)) b A chi chi'
with
HeapMessageAppendQueue : messageAddr -> Syntax.behaviourId -> arrayVarMap value -> heap -> heap -> Prop :=
  | HeapMessageAppendQueue_end (iota freshAddr : messageAddr) (m : message) (b : Syntax.behaviourId) (A : arrayVarMap value) (chi : heap)
  : nextMessage m = None
    -> HeapMapsTo message (someMessageAddr iota) m chi
    -> HeapFresh (someMessageAddr freshAddr) chi
    -> HeapMessageAppendQueue iota b A chi (addMessage iota (m <| nextMessage := (Some freshAddr) |>) (addMessage freshAddr (messageAlloc b A None) chi))
  | HeapMessageAppendQueue_cons (iota iota' : messageAddr) (m : message) (b : Syntax.behaviourId) (A : arrayVarMap value) (chi chi' : heap)
  : nextMessage m = Some iota'
    -> HeapMapsTo message (someMessageAddr iota) m chi
    -> HeapMessageAppendQueue iota' b A chi chi'
    -> HeapMessageAppendQueue iota b A chi chi'.
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

