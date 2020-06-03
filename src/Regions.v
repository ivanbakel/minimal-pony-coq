From Pony Require Import Language Typing Heap.

Require Import Coq.FSets.FMapInterface.
Require Import Coq.MSets.MSetInterface.

Module Regions (Map : WSfun).

Module Heap := Heap Map.
Export Heap.

Module SomeAddrMap := Map DecidableSomeAddr.
Definition someAddrMap := SomeAddrMap.t.

Definition owner : Type := someAddr.

Inductive accessor : Type :=
  | fieldAcc : Syntax.fieldId -> accessor
  | varAcc : Syntax.var -> accessor
  | next : accessor
  | super : accessor.

Inductive region : Type :=
  | isoReg : owner -> accessor -> region
  | trnReg : owner -> accessor -> region
  | valReg : region.

Definition sentinelMap : Type := someAddrMap someAddr.
Definition regionMap : Type := someAddrMap region.

Definition RegionPartition (s : sentinelMap) (r : regionMap) (chi : heap) : Prop :=
  forall (iota : someAddr), HeapIn iota chi -> SomeAddrMap.In iota s
  /\
  forall (iota iota' : someAddr), SomeAddrMap.MapsTo iota iota' s -> SomeAddrMap.MapsTo iota' iota' s
  /\
  forall (iota : someAddr), SomeAddrMap.In iota r <-> exists (iota' : someAddr), SomeAddrMap.MapsTo iota' iota s. 

Definition regPart (chi : heap) : Type := { r : (sentinelMap * regionMap) | RegionPartition (fst r) (snd r) chi }.

Definition SentinelMapsTo { chi : heap } (iota iota' : someAddr) (r : regPart chi) : Prop :=
  SomeAddrMap.MapsTo iota iota' (fst (proj1_sig r)).

Definition RegionMapsTo { chi : heap } (iota : someAddr) (reg : region) (r : regPart chi) : Prop :=
  SomeAddrMap.MapsTo iota reg (snd (proj1_sig r)).

Inductive perspJudgement (chi : heap) (r : regPart chi) : someAddr -> accessor -> someAddr? -> Syntax.baseCapability -> Prop :=
  | persp_iso (iota iota' : someAddr) (a : accessor)
  : SentinelMapsTo iota' iota' r
      -> RegionMapsTo iota' (isoReg iota a) r
      -> perspJudgement chi r iota a (Some iota') Syntax.iso
  | persp_trn (iota iota' : someAddr) (a : accessor)
  : SentinelMapsTo iota' iota' r
      -> RegionMapsTo iota' (trnReg iota a) r
      -> perspJudgement chi r iota a (Some iota') Syntax.trn
  | persp_ref (iota iota' iota'' : someAddr) (a : accessor)
  : SentinelMapsTo iota iota'' r
    -> SentinelMapsTo iota' iota'' r
    -> perspJudgement chi r iota a (Some iota') Syntax.ref
  | persp_val (iota iota' iota'' : someAddr) (a : accessor)
  : SentinelMapsTo iota' iota'' r
      -> RegionMapsTo iota'' valReg r
      -> perspJudgement chi r iota a (Some iota') Syntax.val
  | persp_val_region (iota iota' iota'' iota''' : someAddr) (a : accessor) (b : Syntax.baseCapability)
  : SentinelMapsTo iota iota'' r
      -> RegionMapsTo iota'' valReg r
      -> SentinelMapsTo iota' iota''' r
      -> RegionMapsTo iota''' valReg r
      -> perspJudgement chi r iota a (Some iota') b
  | persp_box (iota iota' iota'' : someAddr) (a : accessor)
  : SentinelMapsTo iota iota'' r
    -> SentinelMapsTo iota' iota'' r
    -> perspJudgement chi r iota a (Some iota') Syntax.box
  | persp_box_trans (iota iota' iota'' : someAddr) (alpha beta gamma : accessor)
  : perspJudgement chi r iota beta (Some iota'') Syntax.box
    -> perspJudgement chi r iota'' gamma (Some iota') Syntax.box
    -> perspJudgement chi r iota alpha (Some iota') Syntax.box
  | persp_tag (iota iota' : someAddr) (a : accessor)
  : perspJudgement chi r iota a (Some iota') Syntax.tag
  | persp_subsume (iota iota' : someAddr) (a : accessor) (b b' : Syntax.baseCapability)
  : Syntax.subcapability (Syntax.base b) (Syntax.base b')
    -> perspJudgement chi r iota a (Some iota') b
    -> perspJudgement chi r iota a (Some iota') b'
  | persp_nul (iota : someAddr) (a : accessor) (b : Syntax.baseCapability)
  : perspJudgement chi r iota a None b.

End Regions.

Module WellFormedHeaps (Map : WSfun) (SetM : WSetsOn).

Module Regions := Regions Map.
Export Regions.

Module WFExpr := WFExpressions Map SetM.
Export WFExpr.

Import Typing.Context.

Definition well_typed_locals (chi : heap) (r : regPart chi) (iota : someAddr) (L : localVars) (gamma : Typing.Context.context) : Prop :=
  ( forall x : Syntax.var, 
    forall S : Syntax.typeId,
    forall b : Syntax.baseCapability,
    forall v : value,
      Typing.Context.LocalMap.VarMapsTo x (Syntax.aType S b) gamma
      -> Heap.LocalMap.VarMapsTo x v L
      -> heapTyping v S chi
          /\ perspJudgement chi r iota (varAcc x) v b)
  /\ 
  ( forall t : Syntax.temp,
    forall S : Syntax.typeId,
    forall k : Syntax.capability,
    forall v : value,
      Typing.Context.LocalMap.TempMapsTo t (Syntax.type S k) gamma
      -> Heap.LocalMap.TempMapsTo t v L
      -> heapTyping v S chi).

Definition argsToLocals (args : arrayVarMap value) : localVars :=
  ArrayVarMap.fold (fun var val localMap => Heap.LocalMap.addVar var val localMap) args emptyLocals.

Definition well_typed_fields { P : program } (chi : heap) (r : regPart chi) (iota : someAddr) (F : Heap.fieldMap value) (S : Syntax.typeId) : Prop :=
  ( forall f : Syntax.fieldId, 
    forall S' : Syntax.typeId,
    forall b : Syntax.baseCapability,
    forall v : value,
      @fieldLookup P S f (Syntax.aType S' b) 
      -> Heap.FieldMap.MapsTo f v F
      -> heapTyping v S' chi
          /\ perspJudgement chi r iota (fieldAcc f) v b).

Inductive well_formed_message { p : program } (chi : heap) (r : regPart chi) : option messageAddr -> Syntax.actorId -> Prop :=
  | wf_message (iota : messageAddr) (rcvrId : Syntax.actorId) (bId : Syntax.behaviourId) (mArgs : arrayVarMap value) (mNext : option messageAddr)
      (bArgs : arrayVarMap Syntax.aliasedType) (bBody : Syntax.expressionSeq)
  : HeapMapsTo message (someMessageAddr iota) (messageAlloc bId mArgs mNext) chi
    -> @behaviourLookup p (inr rcvrId)  bId (bDef bArgs bBody) 
    -> perspJudgement chi r (someMessageAddr iota) next (option_map someMessageAddr mNext) Syntax.iso
    -> well_typed_locals chi r (someMessageAddr iota) (argsToLocals mArgs) (argsToContext bArgs)
    -> well_formed_message chi r mNext rcvrId
    -> well_formed_message chi r (Some iota) rcvrId
  | wf_message_nul (a : Syntax.actorId)
  : well_formed_message chi r None a.

Inductive well_formed_frame (chi : heap) (r : regPart chi) : option frameAddr -> Prop :=
  (* TODO: This is not complete *)
  | wf_frame_top (iota : frameAddr) (gamma : context) (L : localVars) (E : Syntax.expressionSeq) (v_super : frameAddr?)
  : HeapMapsTo frame (someFrameAddr iota) (frameAlloc L E None v_super) chi
    -> False (* TODO: check local variables are well-typed w.r.t. something *)
    -> False (* TODO: check the return type is good for the superframe *)
    -> perspJudgement chi r (someFrameAddr iota) super (option_map someFrameAddr v_super) Syntax.iso
    -> well_formed_frame chi r (Some iota)
  | wf_frame_null
  : well_formed_frame chi r None
with
well_formed_frame_if_returned (chi : heap) (r : regPart chi) : option frameAddr -> Syntax.ponyType -> Prop :=
  | wf_frame_ir (iota : frameAddr) (gamma : context) (L : localVars) (E : Syntax.expressionSeq) (v_super : frameAddr?)
      (t : Syntax.ponyType)
  : HeapMapsTo frame (someFrameAddr iota) (frameAlloc L E None v_super) chi
    -> False (* TODO: check local variables are well-typed w.r.t. something *)
    -> False (* TODO: check the return type is good for the superframe *)
    -> perspJudgement chi r (someFrameAddr iota) super (option_map someFrameAddr v_super) Syntax.iso
    -> well_formed_frame_if_returned chi r (Some iota) t
  | wf_frame_ir_no_return (v : option frameAddr) (t : Syntax.ponyType)
  : well_formed_frame chi r v 
    -> well_formed_frame_if_returned chi r v t.

Definition well_formed_object { P : program } (chi : heap) (r : regPart chi) (iota : objectAddr) : Prop :=
  exists c : Syntax.classId,
  exists F : Heap.fieldMap value,
    HeapMapsTo object (someObjectAddr iota) (objectAlloc c F) chi
    /\ @well_typed_fields P chi r (someObjectAddr iota) F (classTypeId c).

Definition well_formed_actor { P : program } (chi : heap) (r : regPart chi) (iota : actorAddr) : Prop :=
  exists a : Syntax.actorId,
  exists F : Heap.fieldMap value,
  exists v_mes : option messageAddr,
  exists v_frm : option frameAddr,
    HeapMapsTo actor (someActorAddr iota) (actorAlloc a F v_mes v_frm) chi
    /\ perspJudgement chi r (someActorAddr iota) (varAcc Syntax.this) (Some (someActorAddr iota)) Syntax.iso
    /\ @well_typed_fields P chi r (someActorAddr iota) F (actorTypeId a)
    /\ @well_formed_message P chi r v_mes a
    /\ well_formed_frame chi r v_frm. 

Definition well_formed_heap { P : program } (chi : heap) (r : regPart chi) : Prop :=
  ( forall iota_a : actorAddr,
      @well_formed_actor P chi r iota_a )
  /\
  ( forall iota_o : objectAddr,
      @well_formed_object P chi r iota_o ).

End WellFormedHeaps.
