import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Foster-Lyapunov Sign Bridge

This module is a small sign-convention guardrail for the Foster--Lyapunov /
queueing bridge.

It does not prove positive recurrence, geometric ergodicity, or a full
Foster--Lyapunov theorem.  It only fixes the direction of the correspondence:

* a badness/load potential `φ` increases when the structural net change is
  positive;
* `b(x,y) = φ(y) - φ(x)`;
* if `φ = -log m`, then this is the Core log-ratio
  `-log (m(y) / m(x))`;
* a Foster-style stabilizing drift is a negative expected net change outside a
  safe set;
* stationarity of the marginal makes the marginal mean potential increment
  vanish.

The purpose is to prevent the common sign error: positive `b_t` is the
destabilizing / load-increasing direction, not the stabilizing one.
-/

open scoped BigOperators

namespace Persistence.FosterLyapunovSignBridge

noncomputable section

variable {α : Type*}

/-- A load/badness potential induced by a positive mass readout. -/
def structuralPotential (m : α → ℝ) (x : α) : ℝ :=
  -Real.log (m x)

/-- One-step potential increment, read as Core-style net structural change. -/
def potentialIncrement (φ : α → ℝ) (x y : α) : ℝ :=
  φ y - φ x

/-- Core log-ratio net change induced by a mass readout. -/
def coreNetChangeFromMass (m : α → ℝ) (x y : α) : ℝ :=
  -Real.log (m y / m x)

/-- The `φ = -log m` convention recovers the Core net log-ratio exactly. -/
theorem potentialIncrement_structuralPotential_eq_coreNetChangeFromMass
    (m : α → ℝ) (x y : α)
    (hmx : 0 < m x) (hmy : 0 < m y) :
    potentialIncrement (structuralPotential m) x y =
      coreNetChangeFromMass m x y := by
  unfold potentialIncrement structuralPotential coreNetChangeFromMass
  rw [Real.log_div (ne_of_gt hmy) (ne_of_gt hmx)]
  ring

/-- Negative net change means the load/badness potential decreases. -/
theorem negative_netChange_decreases_potential
    (φ : α → ℝ) (x y : α)
    (h : potentialIncrement φ x y < 0) :
    φ y < φ x := by
  unfold potentialIncrement at h
  linarith

/-- Positive net change means the load/badness potential increases. -/
theorem positive_netChange_increases_potential
    (φ : α → ℝ) (x y : α)
    (h : 0 < potentialIncrement φ x y) :
    φ x < φ y := by
  unfold potentialIncrement at h
  linarith

/-- Potential decrease is equivalent to negative net change. -/
theorem potential_decreases_iff_negative_netChange
    (φ : α → ℝ) (x y : α) :
    φ y < φ x ↔ potentialIncrement φ x y < 0 := by
  unfold potentialIncrement
  constructor <;> intro h <;> linarith

/-- Potential increase is equivalent to positive net change. -/
theorem potential_increases_iff_positive_netChange
    (φ : α → ℝ) (x y : α) :
    φ x < φ y ↔ 0 < potentialIncrement φ x y := by
  unfold potentialIncrement
  constructor <;> intro h <;> linarith

variable [Fintype α]

/-- Finite-state conditional expected net change from state `x`. -/
def expectedNetChange
    (K : α → PMF α) (φ : α → ℝ) (x : α) : ℝ :=
  ∑ y, (K x y).toReal * potentialIncrement φ x y

/-- Foster-style negative drift outside a safe set.

This is only a sign convention / expectation-level guardrail.  It does not
assert recurrence. -/
def OutsideSafeNegativeDrift
    (K : α → PMF α) (φ : α → ℝ) (safe : α → Prop) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ x, ¬ safe x → expectedNetChange K φ x ≤ -ε

/-- Positive drift in every state, read as the destabilizing direction. -/
def EverywherePositiveDrift
    (K : α → PMF α) (φ : α → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ x, ε ≤ expectedNetChange K φ x

/-- The reader-facing name for the Foster-style condition is exactly the
negative expected net-change condition. -/
theorem foster_negative_drift_matches_expectedNetChange
    (K : α → PMF α) (φ : α → ℝ) (safe : α → Prop) (ε : ℝ) :
    OutsideSafeNegativeDrift K φ safe ε ↔
      0 < ε ∧ ∀ x, ¬ safe x → expectedNetChange K φ x ≤ -ε := by
  rfl

/-- Outside the safe set, Foster-style negative drift is nonpositive
Core-style expected net change. -/
theorem outsideSafeNegativeDrift_expectedNetChange_nonpos
    {K : α → PMF α} {φ : α → ℝ} {safe : α → Prop} {ε : ℝ}
    (h : OutsideSafeNegativeDrift K φ safe ε)
    {x : α} (hx : ¬ safe x) :
    expectedNetChange K φ x ≤ 0 := by
  have hle : expectedNetChange K φ x ≤ -ε := h.2 x hx
  have hε : 0 < ε := h.1
  linarith

/-- With a positive margin, the outside-safe drift is strictly negative. -/
theorem outsideSafeNegativeDrift_expectedNetChange_neg
    {K : α → PMF α} {φ : α → ℝ} {safe : α → Prop} {ε : ℝ}
    (h : OutsideSafeNegativeDrift K φ safe ε)
    {x : α} (hx : ¬ safe x) :
    expectedNetChange K φ x < 0 := by
  have hle : expectedNetChange K φ x ≤ -ε := h.2 x hx
  have hε : 0 < ε := h.1
  linarith

/-- Positive expected net change is the destabilizing/load-increasing
direction. -/
theorem positive_drift_is_destabilizing_direction
    {K : α → PMF α} {φ : α → ℝ} {ε : ℝ}
    (h : EverywherePositiveDrift K φ ε) (x : α) :
    0 < expectedNetChange K φ x := by
  have hle : ε ≤ expectedNetChange K φ x := h.2 x
  have hε : 0 < ε := h.1
  linarith

/-- Finite-state average of a potential under a PMF. -/
def stateAverage (π : PMF α) (φ : α → ℝ) : ℝ :=
  ∑ x, (π x).toReal * φ x

/-- Marginal mean potential increment under one transition step. -/
def marginalMeanIncrement
    (π : PMF α) (K : α → PMF α) (φ : α → ℝ) : ℝ :=
  stateAverage (π.bind K) φ - stateAverage π φ

/-- A stationary marginal has zero marginal mean potential increment.

This is not a recurrence theorem.  It is the finite-state mean-level identity
that prevents reading a stationary regime as having positive Core net change. -/
theorem stationary_mean_increment_eq_zero
    (π : PMF α) (K : α → PMF α) (φ : α → ℝ)
    (hstationary : π.bind K = π) :
    marginalMeanIncrement π K φ = 0 := by
  unfold marginalMeanIncrement
  rw [hstationary]
  ring

end

end Persistence.FosterLyapunovSignBridge
