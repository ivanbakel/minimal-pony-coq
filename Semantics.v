Add LoadPath "." as Pony.
From Pony Require Import Language Heap.

Require Import Coq.FSets.FMapInterface.

Module Semantics (Map : WSfun).

Module Heap := Heap Map.
Include Heap.

End Semantics.
