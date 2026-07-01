import Persistence.BinaryRankGrowth

/-!
# Binary Prefix State (deterministic prefix layer)

This module repackages the one-step rank-growth bridge in the language used by
sequential random-matrix arguments: a tuple of `k + 1` columns is split into its
first `k` columns and its last column.

`BinaryRankGrowth` proved the local transition

`prefix independent ∧ next ∉ span(prefix) → append(prefix,next) independent`.

Here we connect that local `appendColumn` representation to an actual
`cols : Fin (k + 1) → (Fin r → ZMod 2)` prefix state by using `Fin.init` and
`Fin.last`.

## What this does not prove

No random-prefix process is introduced here.  There is no sampled-column
independence theorem, conditional-probability product, random-matrix rank
probability, or Shannon achievability theorem.  This is only the deterministic
prefix-state bridge consumed by those later layers.
-/

namespace Persistence.BinaryPrefixState

open Persistence.BinaryRankGrowth

/-- The first `k` columns of a `(k + 1)`-column binary prefix. -/
def prefixColumns {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2)) :
    Fin k → (Fin r → ZMod 2) :=
  Fin.init cols

/-- The last column of a `(k + 1)`-column binary prefix. -/
def lastColumn {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2)) :
    Fin r → ZMod 2 :=
  cols (Fin.last k)

/-- Splitting a `(k + 1)`-column prefix into `prefixColumns` and `lastColumn`
and appending them again recovers the original tuple. -/
theorem appendColumn_prefix_last_eq_self {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2)) :
    appendColumn (prefixColumns cols) (lastColumn cols) = cols := by
  unfold appendColumn prefixColumns lastColumn
  exact Fin.snoc_init_self cols

/-- A `(k + 1)`-column prefix is linearly independent exactly when its first
`k` columns are linearly independent and its last column escapes their span. -/
theorem linearIndependent_cols_iff_prefix_escape {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2)) :
    LinearIndependent (ZMod 2) cols ↔
      LinearIndependent (ZMod 2) (prefixColumns cols) ∧
        lastColumn cols ∉
          Submodule.span (ZMod 2) (Set.range (prefixColumns cols)) := by
  constructor
  · intro hcols
    have happ :
        LinearIndependent (ZMod 2)
          (appendColumn (prefixColumns cols) (lastColumn cols)) := by
      simpa [appendColumn_prefix_last_eq_self cols] using hcols
    exact (linearIndependent_appendColumn_iff
      (prefixColumns cols) (lastColumn cols)).mp happ
  · intro h
    have happ :
        LinearIndependent (ZMod 2)
          (appendColumn (prefixColumns cols) (lastColumn cols)) :=
      (linearIndependent_appendColumn_iff
        (prefixColumns cols) (lastColumn cols)).mpr h
    simpa [appendColumn_prefix_last_eq_self cols] using happ

/-- If the first `k` columns are independent and the last column escapes their
span, the whole `(k + 1)`-column prefix is independent. -/
theorem linearIndependent_cols_of_prefix_escape {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2))
    (hv : LinearIndependent (ZMod 2) (prefixColumns cols))
    (hw : lastColumn cols ∉
      Submodule.span (ZMod 2) (Set.range (prefixColumns cols))) :
    LinearIndependent (ZMod 2) cols := by
  exact (linearIndependent_cols_iff_prefix_escape cols).mpr ⟨hv, hw⟩

/-- In prefix-state form: if the first `k` columns are independent and the last
column escapes their span, then the span of the whole `(k + 1)`-column prefix
has rank `k + 1`. -/
theorem finrank_span_cols_eq_succ_of_prefix_escape {r k : ℕ}
    (cols : Fin (k + 1) → (Fin r → ZMod 2))
    (hv : LinearIndependent (ZMod 2) (prefixColumns cols))
    (hw : lastColumn cols ∉
      Submodule.span (ZMod 2) (Set.range (prefixColumns cols))) :
    Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range cols)) = k + 1 := by
  rw [← appendColumn_prefix_last_eq_self cols]
  exact finrank_span_appendColumn_eq_succ_of_span_escape
    (prefixColumns cols) (lastColumn cols) hv hw

end Persistence.BinaryPrefixState
