From Pony Require Import Language.

Require Import Coq.FSets.FMapInterface.

Module LocalMap (Map : WSfun).

Module VarTempMap := Map DecidableVarTemp.

Include VarTempMap.

Definition VarMapsTo { E : Type } (var : Syntax.var) (e : E) (m : t E) : Prop :=
  VarTempMap.MapsTo (inl var) e m.

Definition TempMapsTo { E : Type } (temp : Syntax.temp) (e : E) (m : t E) : Prop :=
  VarTempMap.MapsTo (inr temp) e m.

Definition VarIn { E : Type } (var : Syntax.var) (m : t E) : Prop :=
  VarTempMap.In (inl var) m.

Definition addVar { E : Type } (var : Syntax.var) (e : E) (m : t E) : t E :=
  VarTempMap.add (inl var) e m.

Definition removeVar { E : Type } (var : Syntax.var) (m : t E) : t E :=
  VarTempMap.remove (inl var) m.

End LocalMap.
