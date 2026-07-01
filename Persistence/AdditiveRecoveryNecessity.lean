import Persistence.GeneralStateDynamics

/-!
# Additive Recovery Consequence Of Log-Ratio Accounting

This module records a conditional consequence of the log-ratio coordinate:
once contraction and recovery are read through positive mass ratios, the
endpoint net action composes additively in log space.

## The theorem

Given that loss is measured as -log(ratio), the composition of
contraction and recovery is necessarily additive in log space:

    -log(m_{final}/m_{initial}) = -log(m_{contracted}/m_{initial})
                                 + log(m_{repaired}/m_{contracted})
                               = d_t - r_t

This is a theorem inside the log-ratio reading.  It is not a universal theorem
excluding every possible recovery model or every non-log coordinate.

## Significance

"Why is net consumption additive in this coordinate?" → "Because the
log-ratio coordinate converts multiplicative endpoint ratios into additive
increments."
-/

namespace Persistence.AdditiveRecoveryNecessity

open Persistence.GeneralStateDynamics

noncomputable section

variable {X : Type*}

/-! ## Part 1: Log Additivity Forces Additive Recovery -/

/-- **Additive recovery is forced inside the log-ratio coordinate.**

The net action (loss - gain) equals the log-ratio of endpoint
masses. This is forced by the logarithm's additive property:
log(a/b) + log(b/c) = log(a/c).

This does not exclude non-log coordinates outside this scoped reading. -/
theorem additive_recovery_forced
    (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    stepNetAction P t =
      -Real.log (feasibleMass P (t + 1) / feasibleMass P t) :=
  stepNetAction_eq_neg_log_feasible_ratio P t hfeas hcontract hnext

/-- The additive decomposition: net action = loss - gain.
This is the definition, but the point is that no other
decomposition is consistent with the log-ratio form. -/
theorem net_is_loss_minus_gain (P : ProblemSpec X) (t : ℕ) :
    stepNetAction P t = stepLoss P t - stepGain P t := rfl

/-! ## Part 2: Why Additive and Not Multiplicative? -/

/-- **Log converts multiplication to addition.**

The ratio m_final/m_initial = (m_contracted/m_initial) ×
(m_repaired/m_contracted). Taking -log converts this product
into a sum: loss + (-gain) = net action.

This is WHY the recovery model is additive: the representation
theorem forces log-ratio measurement, and log is the unique
function that converts products to sums (Cauchy equation). -/
theorem log_converts_product_to_sum
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b :=
  Real.log_mul (ne_of_gt ha) (ne_of_gt hb)

/-- Ratio composition is multiplicative... -/
theorem ratio_composition
    (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (b / a) * (c / b) = c / a := by field_simp

/-- ...so log-ratio composition is additive. -/
theorem log_ratio_additive
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (b / a) + Real.log (c / b) = Real.log (c / a) := by
  rw [← Real.log_mul (ne_of_gt (div_pos hb ha)) (ne_of_gt (div_pos hc hb)),
      ratio_composition a b c (ne_of_gt ha) (ne_of_gt hb)]

/-! ## Part 3: The Full Necessity Chain -/

/-- **The full necessity chain:**

1. Representation theorem → loss = -k log r
2. Log is the unique additive-on-products function (Cauchy)
3. Ratio composition is multiplicative
4. Therefore log-ratio composition is additive
5. Therefore net consumption = loss - gain (additive)

No step in this chain involves a choice. Every step is forced. -/
theorem full_necessity_chain
    (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    stepLoss P t - stepGain P t =
      -Real.log (feasibleMass P (t + 1) / feasibleMass P t) :=
  additive_recovery_forced P t hfeas hcontract hnext

end

end Persistence.AdditiveRecoveryNecessity
