import Persistence.AdmissibleMapInvariants
import Persistence.TelescopingExp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Coordinate Invariance Guards For Structural Loss

This module records small coordinate-invariance guards for the log-ratio loss
readout.  The stage loss `l_i = -log(R_i)` is invariant under positive
rescaling of the measure `m`, and covariant under power-law
reparametrization.

## The theorem

If m' = α · m for some α > 0, then:
    l_i' = -log(m'(V^{(i+1)}) / m'(V^{(i)}))
         = -log((α m_{i+1}) / (α m_i))
         = -log(m_{i+1} / m_i)
         = l_i

The stage loss is independent of the overall scale of m.

More generally, if m' = m^β for β > 0, then l_i' = β · l_i
(gauge covariance, already in AdmissibleMapInvariants).

## Significance

The safe reading is modest: this file checks that the chosen log-ratio
coordinate measures proportional change rather than absolute scale.  It is not
a native dimensional-analysis theorem.

References:
  - Buckingham, E. (1914). "On physically similar systems."
  - Bridgman, P.W. (1931). "Dimensional Analysis."
  - AdmissibleMapInvariants.lean: gauge covariance
-/

namespace Persistence.InvarianceTheorem

open Real
open Persistence.TelescopingExp

noncomputable section

/-! ## Part 1: Scale Invariance of Stage Loss -/

/-- **Scale Invariance Theorem**: The stage loss l_i = -log(m_{i+1}/m_i)
    is invariant under positive rescaling m' = α·m.

    This is because the ratio m_{i+1}/m_i cancels the scale factor:
    (α m_{i+1}) / (α m_i) = m_{i+1} / m_i. -/
theorem stageLoss_scale_invariant (m : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (i : ℕ) :
    stageLoss (fun n => α * m n) i = stageLoss m i := by
  unfold stageLoss
  congr 1
  rw [show α * m (i + 1) / (α * m i) = m (i + 1) / m i from by
    rw [mul_div_mul_left _ _ (ne_of_gt hα)]]

/-- Cumulative loss is also scale invariant. -/
theorem cumulativeLoss_scale_invariant (m : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (n : ℕ) :
    Persistence.AdmissibleMapInvariants.cumulativeStageLoss
      (fun k => α * m k) n =
    Persistence.AdmissibleMapInvariants.cumulativeStageLoss m n := by
  unfold Persistence.AdmissibleMapInvariants.cumulativeStageLoss
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact stageLoss_scale_invariant m α hα i

/-! ## Part 2: Ratio Invariance (the deep reason) -/

/-- The fundamental reason for scale invariance: the ratio R_i = m_{i+1}/m_i
    is scale-independent. -/
theorem ratio_scale_invariant (m : ℕ → ℝ) (α : ℝ) (hα : α ≠ 0)
    (i : ℕ) :
    α * m (i + 1) / (α * m i) = m (i + 1) / m i := by
  rw [mul_div_mul_left _ _ hα]

/-- Scale invariance means the loss measures *proportional* change,
    not *absolute* change. This is why structural consumption is
    a natural "dimensionless" quantity. -/
theorem proportional_not_absolute (m : ℕ → ℝ) (i : ℕ)
    :
    stageLoss m i = -log (m (i + 1) / m i) := rfl

/-! ## Part 3: Power-Law Covariance -/

-- Power-law covariance: see `AdmissibleMapInvariants.positive_gauge_covariance`.

/-- The retention factor exp(-L) at step n is also scale invariant:
    changing m to α·m doesn't change exp(-Σ l_i). -/
theorem retention_scale_invariant (m : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (n : ℕ) :
    exp (-∑ i ∈ Finset.range n, stageLoss (fun k => α * m k) i) =
    exp (-∑ i ∈ Finset.range n, stageLoss m i) := by
  congr 1
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact stageLoss_scale_invariant m α hα i

/-! ## Part 5: Summary -/

/-- **Invariance Theorem (complete):**
    1. Stage loss is scale-invariant (α-rescaling)
    2. Stage loss is power-covariant (β-reparametrization: l' = βl)
    3. Retention factor exp(-L) is scale-invariant
    4. These invariances hold because loss measures proportional change

    This establishes a modest coordinate-invariance guard for the log-ratio
    readout: the value tracks proportional change, not absolute scale. -/
theorem invariance_summary (m : ℕ → ℝ) (α : ℝ) (hα : 0 < α)
    (n : ℕ) :
    -- Scale invariance of cumulative loss
    Persistence.AdmissibleMapInvariants.cumulativeStageLoss
      (fun k => α * m k) n =
    Persistence.AdmissibleMapInvariants.cumulativeStageLoss m n ∧
    -- Scale invariance of retention
    exp (-∑ i ∈ Finset.range n, stageLoss (fun k => α * m k) i) =
    exp (-∑ i ∈ Finset.range n, stageLoss m i) :=
  ⟨cumulativeLoss_scale_invariant m α hα n,
   retention_scale_invariant m α hα n⟩

end

end Persistence.InvarianceTheorem
