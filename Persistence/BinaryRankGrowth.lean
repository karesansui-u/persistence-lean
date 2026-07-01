import Persistence.BinarySpanEscapePMF
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Binary Rank Growth (deterministic one-step layer)

This module sits between the one-step finite-uniform PMF bridge and any future
random-prefix process.

`BinarySpanEscapePMF` proves that, for a fixed independent prefix `v`, the
finite-uniform PMF mass of the event

`w ∉ span(v)`

is `1 - 2^k/2^r`.  This file records the deterministic rank-growth meaning of
that event:

> if the prefix is linearly independent and the next column escapes its span,
> then appending that column keeps the extended prefix linearly independent,
> and the span of the extended prefix has rank `k + 1`.

## What this does not prove

No random-prefix process is introduced here.  There is no sampled-column
independence theorem, conditional-probability product, random-matrix rank
probability, or Shannon achievability theorem.  This is only the deterministic
event-to-rank-growth bridge consumed by those later layers.
-/

namespace Persistence.BinaryRankGrowth

open Persistence.BinarySpanEscapePMF

/-- Append one binary column to an existing prefix.  The new column is placed at
the last index, matching the usual sequential rank-growth reading. -/
def appendColumn {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (w : Fin r → ZMod 2) :
    Fin (k + 1) → (Fin r → ZMod 2) :=
  Fin.snoc v w

/-- The span-escape event is exactly the condition needed to preserve linear
independence after appending the next column.  This is a deterministic
transition lemma, not a probability statement. -/
theorem linearIndependent_appendColumn_of_span_escape {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (w : Fin r → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v)
    (hw : w ∉ Submodule.span (ZMod 2) (Set.range v)) :
    LinearIndependent (ZMod 2) (appendColumn v w) := by
  exact linearIndependent_fin_snoc.mpr ⟨hv, hw⟩

/-- Equivalence form of the deterministic rank-growth condition: appending a
column is linearly independent exactly when the previous prefix is linearly
independent and the appended column escapes the previous span. -/
theorem linearIndependent_appendColumn_iff {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (w : Fin r → ZMod 2) :
    LinearIndependent (ZMod 2) (appendColumn v w) ↔
      LinearIndependent (ZMod 2) v ∧
        w ∉ Submodule.span (ZMod 2) (Set.range v) := by
  exact linearIndependent_fin_snoc

/-- If the next column escapes the span of an independent prefix, the span of
the appended prefix has rank `k + 1`.  This is the deterministic rank increment
that the later random-prefix layer will turn into a conditional event. -/
theorem finrank_span_appendColumn_eq_succ_of_span_escape {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (w : Fin r → ZMod 2)
    (hv : LinearIndependent (ZMod 2) v)
    (hw : w ∉ Submodule.span (ZMod 2) (Set.range v)) :
    Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range (appendColumn v w))) = k + 1 := by
  rw [finrank_span_eq_card
    (linearIndependent_appendColumn_of_span_escape v w hv hw), Fintype.card_fin]

end Persistence.BinaryRankGrowth
