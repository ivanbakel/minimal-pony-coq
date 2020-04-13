Add LoadPath "." as Pony.
From Pony Require Import Language.

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

Definition value : Type := (actorAddr + objectAddr)?.

Record actor : Type :=
  actorAlloc
  { actorId : Syntax.actorId 
  ; actorFields : fieldMap value
  ; messageQueue : messageAddr?
  ; frameStack : frameAddr?
  }.

Record object : Type :=
  objectAlloc
  { objectId : Syntax.classId
  ; objectFields : fieldMap value
  }.

Record message : Type :=
  messageAlloc
  { messageId : Syntax.methodId
  ; receiverId : Syntax.actorId
  ; messageArgs : varMap value
  ; nextMessage : messageAddr?
  }.

Record frame : Type :=
  frameAlloc
  { localVars : varMap value
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

End Heap.
