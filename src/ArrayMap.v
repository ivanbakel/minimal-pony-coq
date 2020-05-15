Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.Equalities.

(* Helper module for maps where an indexing on keys is necessary *)
Module ArrayMap (X : DecidableTypeOrig).

Module M := FMapWeakList.Make X.
Include M.

End ArrayMap.

