import Persistence.GeneralStateDynamics

/-!
Repair Budget / Resource Constraint for the Set-Valued Dynamical Representation of Structural Persistence
構造持続の集合値力学的表現に対する repair budget / resource constraint

This module adds a conservative resource-accounting interface on top of
`Persistence.GeneralStateDynamics`.

The core modeling assumption is pointwise:

  stepGain ≤ stepCost

That is, repair / learning / rollback is not free: every gain must be paid for
by at least as much external or internal resource cost.
-/

open scoped BigOperators
open Finset

namespace Persistence.ResourceBudget

open Persistence.GeneralStateDynamics

noncomputable section

variable {X : Type*}

/-- A repair budget assigns a nonnegative resource cost to each step and
bounds the repair gain from above. -/
structure RepairBudget (P : ProblemSpec X) where
  stepCost : ℕ → ℝ
  cost_nonneg : ∀ t, 0 ≤ stepCost t
  gain_le_cost : ∀ t, stepGain P t ≤ stepCost t

/-- Cumulative resource cost up to time `n`. -/
def cumulativeCost {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, B.stepCost t

theorem cumulativeCost_nonneg {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) :
    0 ≤ cumulativeCost B n := by
  unfold cumulativeCost
  refine Finset.sum_nonneg ?_
  intro t ht
  exact B.cost_nonneg t

theorem cumulativeGain_le_cumulativeCost {P : ProblemSpec X}
    (B : RepairBudget P) (n : ℕ) :
    cumulativeGain P n ≤ cumulativeCost B n := by
  unfold cumulativeGain cumulativeCost
  refine Finset.sum_le_sum ?_
  intro t ht
  exact B.gain_le_cost t

end

end Persistence.ResourceBudget
