From Pony Require Import Language.

Require Import Coq.FSets.FMapInterface.

Module LocalMap (Map : WSfun).

Module VarMap := Map DecidableVar.
Module TempMap := Map DecidableTemp.

Definition t (X Y : Type) : Type := ((VarMap.t X) * (TempMap.t Y)).

Definition VarMapsTo { E F : Type } (var : Syntax.var) (e : E) (m : t E F) : Prop :=
  VarMap.MapsTo var e (fst m).

Definition TempMapsTo { E F : Type } (temp : Syntax.temp) (f : F) (m : t E F) : Prop :=
  TempMap.MapsTo temp f (snd m).

Definition VarIn { E F : Type } (var : Syntax.var) (m : t E F) : Prop :=
  VarMap.In var (fst m).

Definition addVar { E F : Type } (var : Syntax.var) (e : E) (m : t E F) : t E F :=
  (VarMap.add var e (fst m), snd m).

Definition addTemp { E F : Type } (temp : Syntax.temp) (f : F) (m : t E F) : t E F :=
  (fst m, TempMap.add temp f (snd m)).

Definition removeVar { E F : Type } (var : Syntax.var) (m : t E F) : t E F :=
  (VarMap.remove var (fst m), snd m).

Definition removeTemp { E F : Type } (temp : Syntax.temp) (m : t E F) : t E F :=
  (fst m, TempMap.remove temp (snd m)).

Definition empty (E F : Type) : t E F := (VarMap.empty E, TempMap.empty F).

Definition fold_var { E F B : Type } (f : Syntax.var -> E -> B -> B) (m : t E F) (init : B) : B
  := VarMap.fold f (fst m) init.

Lemma VarMapsTo_func { E F : Type } :
  forall m : t E F,
  forall var : Syntax.var,
  forall e1 e2 : E,
  VarMapsTo var e1 m
    -> VarMapsTo var e2 m
    -> e1 = e2.
Proof.
  Admitted. (* TODO: Prove this lemma (v. obvious) *)

Lemma TempMapsTo_func { E F : Type } :
  forall m : t E F,
  forall temp : Syntax.temp,
  forall f1 f2 : F,
  TempMapsTo temp f1 m
    -> TempMapsTo temp f2 m
    -> f1 = f2.
Proof.
  Admitted. (* TODO: Prove this lemma (v. obvious) *)

End LocalMap.
