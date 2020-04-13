Add LoadPath "." as Pony.
From Pony Require Import Language Semantics.

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
