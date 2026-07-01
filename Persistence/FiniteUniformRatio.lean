import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

/-!
# Finite Uniform Ratios

This module is the small combinatorial layer between cardinality ratios and a
future PMF-based probability layer.

For a finite ambient type `α` and a finite event subtype `{x // p x}`, it names
the uniform finite ratio

`# {x // p x} / # α`.

## What this proves

The ratio is nonnegative, bounded above by one, and positive when both the
ambient space and event subtype are nonempty.

## What this does not prove

No PMF, measure, random variable, independence theorem, random-matrix
rank-probability theorem, or Shannon achievability theorem is introduced here.
This is only the finite cardinality-ratio layer that such later probability
statements can consume.
-/

namespace Persistence.FiniteUniformRatio

noncomputable section

/-- Cardinality of an event subtype inside a finite ambient type. -/
def eventCount (α : Type*) [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] : ℕ :=
  Fintype.card {x // p x}

/-- Cardinality of the finite ambient type. -/
def totalCount (α : Type*) [Fintype α] : ℕ :=
  Fintype.card α

/-- The finite-uniform event ratio `#event / #space`.

This is a cardinality ratio, not a `PMF` or measure-theoretic probability. -/
def finiteUniformRatio (α : Type*) [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] : ℝ :=
  (eventCount α p : ℝ) / (totalCount α : ℝ)

/-- An event subtype cannot have more elements than its finite ambient type. -/
theorem eventCount_le_totalCount (α : Type*) [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] :
    eventCount α p ≤ totalCount α := by
  unfold eventCount totalCount
  exact Fintype.card_subtype_le p

/-- Finite-uniform ratios are nonnegative. -/
theorem finiteUniformRatio_nonneg (α : Type*) [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] :
    0 ≤ finiteUniformRatio α p := by
  unfold finiteUniformRatio
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Finite-uniform ratios are bounded above by one. -/
theorem finiteUniformRatio_le_one (α : Type*) [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] :
    finiteUniformRatio α p ≤ 1 := by
  unfold finiteUniformRatio
  have hnum_nat : eventCount α p ≤ totalCount α :=
    eventCount_le_totalCount α p
  have hnum : (eventCount α p : ℝ) ≤ (totalCount α : ℝ) := by
    exact_mod_cast hnum_nat
  have hden_nonneg : 0 ≤ (totalCount α : ℝ) := by
    exact Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hnum hden_nonneg
  by_cases hden : (totalCount α : ℝ) = 0
  · simp [hden]
  · simpa [div_self hden] using hdiv

/-- If both the ambient finite type and event subtype are nonempty, the
finite-uniform ratio is positive. -/
theorem finiteUniformRatio_pos (α : Type*) [Fintype α] [Nonempty α]
    (p : α → Prop) [Fintype {x // p x}] [Nonempty {x // p x}] :
    0 < finiteUniformRatio α p := by
  unfold finiteUniformRatio
  exact div_pos
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card {x // p x}))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α))

end

end Persistence.FiniteUniformRatio
