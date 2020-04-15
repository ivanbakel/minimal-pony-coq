Add LoadPath "." as Pony.
From Pony Require Import Language Typing Semantics.

Require Import Coq.FSets.FMapInterface.

Module Regions (Map : WSfun).

Include Heap Map.

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

Module WellFormedHeaps (Map : WSfun).

Include Regions Map.

Module Program := Program Map.

Module Typing := Typing Map.

Inductive values_typed (chi : heap) (r : regPart chi) (iota : someAddr) : list value -> list accessor -> list Syntax.aliasedType -> Prop :=
  | values_typed_nil
  : values_typed chi r iota nil nil nil
  | values_typed_cons (v : value) (lv : list value) (a : accessor) (la : list accessor)
      (s : Syntax.typeId) (b : Syntax.baseCapability) (lt : list Syntax.aliasedType)
  : HeapValueType v s chi
    -> perspJudgement chi r iota a v b
    -> values_typed chi r iota lv la lt 
    -> values_typed chi r iota (v :: lv) (a :: la) ((Syntax.aType s b) :: lt).

Inductive well_formed_message { p : Program.program } (chi : heap) (r : regPart chi) : option messageAddr -> Syntax.actorId -> Prop :=
  | wf_message (iota : messageAddr) (rcvrId : Syntax.actorId) (bId : Syntax.behaviourId) (mArgs : list value) (mNext : option messageAddr)
      (bArgs : Program.arrayVarMap Syntax.aliasedType) (bBody : Syntax.expressionSeq)
  : HeapMapsTo message (someMessageAddr iota) (messageAlloc bId rcvrId mArgs mNext) chi
    -> @Program.behaviourLookup p (inr rcvrId)  bId (Program.bDef bArgs bBody) 
    -> perspJudgement chi r (someMessageAddr iota) next (option_map someMessageAddr mNext) Syntax.iso
    -> values_typed chi r (someMessageAddr iota)
          mArgs
          (map varAcc (map fst (Program.ArrayVarMap.elements bArgs)))
          (map snd (Program.ArrayVarMap.elements bArgs))
    -> well_formed_message chi r mNext rcvrId
    -> well_formed_message chi r (Some iota) rcvrId
  | wf_message_nul (a : Syntax.actorId)
  : well_formed_message chi r None a.


End WellFormedHeaps.
