import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Persistence.TelescopingExp

/-!
# Admissible-Map Invariant and Covariant Readouts

This module provides the light Lean wrapper requested by the admissible-map
supplement.  It does **not** formalize the full category of structural
maintenance problems.  Instead, it isolates the finite positive-mass readout
level on which the supplement's first two layers are mathematically immediate:

* mass-readout isomorphism preserves cumulative log-ratio loss;
* positive gauge readout makes cumulative log-ratio loss covariant by the gauge
  factor;
* positive gauges preserve ordering and regime sign.

This is intentionally thin.  Coarse-graining defect identities and proxy
validation belong to later wrappers.
-/

open scoped BigOperators
open Finset

namespace Persistence.AdmissibleMapInvariants

open Persistence.TelescopingExp

noncomputable section

/-- Cumulative log-ratio loss for a finite mass readout. -/
def cumulativeStageLoss (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stageLoss m t

/-- Two finite mass readouts are isomorphic up to horizon `n` when they agree
on all masses used by the horizon. -/
def MassReadoutIso (m m' : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ t, t ≤ n → m' t = m t

/-- A positive-gauge readout relation at the stage-loss level.  This avoids
claiming that `m(A)^α` is itself a measure; only the ratio readout is required
to scale by `α`. -/
def PositiveGaugeReadout (m m' : ℕ → ℝ) (α : ℝ) (n : ℕ) : Prop :=
  ∀ t, t ∈ Finset.range n → stageLoss m' t = α * stageLoss m t

/-- Isomorphic finite mass readouts preserve cumulative log-ratio loss. -/
theorem iso_invariance (m m' : ℕ → ℝ) (n : ℕ)
    (hiso : MassReadoutIso m m' n) :
    cumulativeStageLoss m' n = cumulativeStageLoss m n := by
  unfold cumulativeStageLoss
  refine Finset.sum_congr rfl ?_
  intro t ht
  unfold stageLoss
  have ht_le : t ≤ n := Nat.le_of_lt (Finset.mem_range.mp ht)
  have hsucc_le : t + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
  rw [hiso t ht_le, hiso (t + 1) hsucc_le]

/-- Positive-gauge readouts make cumulative log-ratio loss covariant by the
same gauge factor. -/
theorem positive_gauge_covariance (m m' : ℕ → ℝ) (α : ℝ) (n : ℕ)
    (hgauge : PositiveGaugeReadout m m' α n) :
    cumulativeStageLoss m' n = α * cumulativeStageLoss m n := by
  unfold cumulativeStageLoss
  calc
    (∑ t ∈ Finset.range n, stageLoss m' t)
        = ∑ t ∈ Finset.range n, α * stageLoss m t := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            exact hgauge t ht
    _ = α * ∑ t ∈ Finset.range n, stageLoss m t := by
            exact (Finset.mul_sum (Finset.range n) (fun t => stageLoss m t) α).symm

/-- Positive gauges preserve order comparisons between cumulative readouts. -/
theorem positive_gauge_preserves_order {α x y : ℝ}
    (hα : 0 < α) :
    α * x ≤ α * y ↔ x ≤ y := by
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hα
  · intro h
    exact mul_le_mul_of_nonneg_left h hα.le

/-- Positive gauges preserve the nonnegative regime. -/
theorem positive_gauge_preserves_nonnegative {α x : ℝ}
    (hα : 0 < α) :
    0 ≤ α * x ↔ 0 ≤ x := by
  simpa using
    (positive_gauge_preserves_order (α := α) (x := 0) (y := x) hα)

end

end Persistence.AdmissibleMapInvariants
