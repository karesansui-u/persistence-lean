import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Linarith
import Persistence.AdmissibleMapInvariants

/-!
# Saturation-Defect Readout Spec

This module is the narrow Lean-facing specification for the saturation-defect
identity in the admissible-map supplement.

It deliberately stays at the finite readout level.  It does **not** formalize a
full measurable coarse-graining map, push-forward measure, or unconditional DPI.
Instead, it records the exact algebra that any later set-level coarse-graining
interface must instantiate:

* if the coarse one-step log-ratio loss differs from the micro one by the
  defect difference `e t - e (t+1)`, then
* cumulative coarse loss equals cumulative micro loss plus initial defect minus
  terminal defect.

Consequently, coarse loss is below micro loss only under the additional defect
condition `e 0 ≤ e n`.
-/

open scoped BigOperators
open Finset

namespace Persistence.SaturationDefect

open Persistence.AdmissibleMapInvariants
open Persistence.TelescopingExp

noncomputable section

/-- Readout-level saturation-defect relation up to horizon `n`.

This is the intentionally narrow spec:

`coarse stage loss = micro stage loss + initial-stage defect - next-stage defect`.

The set-level definition
`eπ(A) = log (m (π⁻¹(π(A))) / m(A))` should instantiate this relation only
after positive finite mass and coarse-graining compatibility assumptions have
been supplied. -/
def SaturationDefectReadout (m mcoarse e : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ t, t ∈ Finset.range n →
    stageLoss mcoarse t = stageLoss m t + e t - e (t + 1)

/-- Saturation defect between a micro mass readout and a saturated/coarse mass
readout.

At the set level this will be instantiated as
`log (mass (π ⁻¹' (π '' A)) / mass A)`. -/
def saturationDefect (m msat : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (msat t / m t)

/-- Stage-level form of the saturation-defect readout. -/
theorem coarse_stageLoss_eq_micro_add_defect_diff
    {m mcoarse e : ℕ → ℝ} {n t : ℕ}
    (hdef : SaturationDefectReadout m mcoarse e n)
    (ht : t ∈ Finset.range n) :
    stageLoss mcoarse t = stageLoss m t + e t - e (t + 1) :=
  hdef t ht

/-- Positive saturated mass readouts instantiate the readout-level
saturation-defect relation.  This is the algebraic bridge from the set-level
formula `eπ(A)` to the telescoping readout spec. -/
theorem saturationDefectReadout_of_positive
    (m msat : ℕ → ℝ) (n : ℕ)
    (hm : ∀ t, t ≤ n → 0 < m t)
    (hsat : ∀ t, t ≤ n → 0 < msat t) :
    SaturationDefectReadout m msat (saturationDefect m msat) n := by
  intro t ht
  have ht_lt : t < n := Finset.mem_range.mp ht
  have ht_le : t ≤ n := Nat.le_of_lt ht_lt
  have hsucc_le : t + 1 ≤ n := Nat.succ_le_of_lt ht_lt
  have hmt : m t ≠ 0 := ne_of_gt (hm t ht_le)
  have hmn : m (t + 1) ≠ 0 := ne_of_gt (hm (t + 1) hsucc_le)
  have hst : msat t ≠ 0 := ne_of_gt (hsat t ht_le)
  have hsn : msat (t + 1) ≠ 0 := ne_of_gt (hsat (t + 1) hsucc_le)
  unfold stageLoss saturationDefect
  rw [Real.log_div hsn hst]
  rw [Real.log_div hmn hmt]
  rw [Real.log_div hst hmt]
  rw [Real.log_div hsn hmn]
  ring

/-- Saturation of a micro set by a coarse map: push forward, then pull back. -/
def saturationBy (π : X → Y) (A : Set X) : Set X :=
  π ⁻¹' (π '' A)

/-- Every set is contained in its saturation. -/
theorem subset_saturationBy (π : X → Y) (A : Set X) :
    A ⊆ saturationBy π A := by
  intro x hx
  exact ⟨x, hx, rfl⟩

/-- Micro mass readout along a finite set trajectory. -/
def setMassReadout (mass : Set X → ℝ) (V : ℕ → Set X) : ℕ → ℝ :=
  fun t => mass (V t)

/-- Saturated/coarse mass readout along a finite set trajectory. -/
def saturatedSetMassReadout
    (mass : Set X → ℝ) (sat : Set X → Set X) (V : ℕ → Set X) : ℕ → ℝ :=
  fun t => mass (sat (V t))

/-- Set-level saturation defect for an abstract saturation operator. -/
def saturationDefectOfSets
    (mass : Set X → ℝ) (sat : Set X → Set X) (V : ℕ → Set X) (t : ℕ) : ℝ :=
  Real.log (mass (sat (V t)) / mass (V t))

/-- Set-level saturation defect induced by an actual coarse map. -/
def saturationDefectOfCoarseMap
    (mass : Set X → ℝ) (π : X → Y) (V : ℕ → Set X) (t : ℕ) : ℝ :=
  saturationDefectOfSets mass (saturationBy π) V t

/-- Positive finite set-mass readouts instantiate the saturation-defect spec.

This is still intentionally narrow: it does not assert that a given coarse map
is admissible, nor does it prove an unconditional DPI.  It only connects the
set-level formula for `eπ(A)` to the readout-level theorem above. -/
theorem saturationDefectReadout_of_positive_setMass
    (mass : Set X → ℝ) (sat : Set X → Set X) (V : ℕ → Set X) (n : ℕ)
    (hm : ∀ t, t ≤ n → 0 < mass (V t))
    (hsat : ∀ t, t ≤ n → 0 < mass (sat (V t))) :
    SaturationDefectReadout
      (setMassReadout mass V)
      (saturatedSetMassReadout mass sat V)
      (saturationDefectOfSets mass sat V) n := by
  simpa [setMassReadout, saturatedSetMassReadout, saturationDefectOfSets,
    saturationDefect] using
    (saturationDefectReadout_of_positive
      (m := setMassReadout mass V)
      (msat := saturatedSetMassReadout mass sat V)
      (n := n) hm hsat)

/-- An actual coarse map `π : X → Y` gives the canonical saturation operator
`A ↦ π ⁻¹' (π '' A)`, and therefore instantiates the same readout spec under
positive mass assumptions. -/
theorem coarseMap_saturationDefectReadout_of_positive_setMass
    (mass : Set X → ℝ) (π : X → Y) (V : ℕ → Set X) (n : ℕ)
    (hm : ∀ t, t ≤ n → 0 < mass (V t))
    (hsat : ∀ t, t ≤ n → 0 < mass (saturationBy π (V t))) :
    SaturationDefectReadout
      (setMassReadout mass V)
      (saturatedSetMassReadout mass (saturationBy π) V)
      (saturationDefectOfCoarseMap mass π V) n := by
  simpa [saturationDefectOfCoarseMap] using
    (saturationDefectReadout_of_positive_setMass
      (mass := mass) (sat := saturationBy π) (V := V) (n := n) hm hsat)

/-- If stage losses differ by a telescoping defect difference, then cumulative
coarse loss equals cumulative micro loss plus initial defect minus terminal
defect. -/
theorem coarse_cumulativeStageLoss_eq_micro_add_initial_defect_sub_terminal
    (m mcoarse e : ℕ → ℝ) (n : ℕ)
    (hdef : SaturationDefectReadout m mcoarse e n) :
    cumulativeStageLoss mcoarse n =
      cumulativeStageLoss m n + e 0 - e n := by
  induction n with
  | zero =>
      simp [cumulativeStageLoss]
  | succ n ih =>
      have hprefix : SaturationDefectReadout m mcoarse e n := by
        intro t ht
        exact hdef t
          (Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self n)))
      have ih' := ih hprefix
      unfold cumulativeStageLoss at ih' ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [hdef n (by simp)]
      rw [ih']
      ring

/-- Conditional coarse-graining monotonicity: the coarse cumulative loss is
bounded above by the micro cumulative loss when terminal saturation defect is at
least the initial defect.

This is the Lean guardrail against an unconditional coarse-graining DPI claim. -/
theorem coarse_cumulativeStageLoss_le_micro_of_terminal_defect_ge_initial
    (m mcoarse e : ℕ → ℝ) (n : ℕ)
    (hdef : SaturationDefectReadout m mcoarse e n)
    (hmono : e 0 ≤ e n) :
    cumulativeStageLoss mcoarse n ≤ cumulativeStageLoss m n := by
  rw [coarse_cumulativeStageLoss_eq_micro_add_initial_defect_sub_terminal
    m mcoarse e n hdef]
  linarith

/-- If the terminal defect is no larger than the initial defect, the inequality
can reverse.  This theorem is not a claim that reversal always happens; it is a
reader-facing reminder that the sign is controlled by the defect comparison. -/
theorem micro_cumulativeStageLoss_le_coarse_of_terminal_defect_le_initial
    (m mcoarse e : ℕ → ℝ) (n : ℕ)
    (hdef : SaturationDefectReadout m mcoarse e n)
    (hmono : e n ≤ e 0) :
    cumulativeStageLoss m n ≤ cumulativeStageLoss mcoarse n := by
  rw [coarse_cumulativeStageLoss_eq_micro_add_initial_defect_sub_terminal
    m mcoarse e n hdef]
  linarith

end

end Persistence.SaturationDefect
