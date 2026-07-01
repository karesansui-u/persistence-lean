import Mathlib.Tactic.Linarith
import Persistence.ResourceBudget

/-!
Total Production for the Set-Valued Dynamical Representation of Structural Persistence
構造持続の集合値力学的表現に対する total production の定義層

This module formalizes the conservative definition

  Σ = A + C

where `A` is the signed net action and `C` is a resource cost supplied by a
`RepairBudget`.

The main algebraic fact is that total production splits as

  Σ = L^- + slack

where `slack = C - G`. Under the repair-budget hypothesis `G ≤ C`, this slack is
nonnegative, so total production dominates cumulative contraction loss.

This is a definition layer: it does not yet prove monotonicity or a full
second-law analogue.
-/

open scoped BigOperators
open Finset Real

namespace Persistence.TotalProduction

open Persistence.GeneralStateDynamics
open Persistence.ResourceBudget

noncomputable section

variable {X : Type*}

/-- Stepwise repair slack: resource cost minus realized repair gain. -/
def stepRepairSlack {P : ProblemSpec X} (B : RepairBudget P) (t : ℕ) : ℝ :=
  B.stepCost t - stepGain P t

/-- Cumulative repair slack up to time `n`. -/
def cumulativeRepairSlack {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stepRepairSlack B t

/-- Stepwise total production `Σ_t = A_t + C_t`. -/
def stepTotalProduction {P : ProblemSpec X} (B : RepairBudget P) (t : ℕ) : ℝ :=
  stepNetAction P t + B.stepCost t

/-- Cumulative total production `Σ_n = B_n + C_n`. -/
def cumulativeTotalProduction {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) : ℝ :=
  cumulativeNetAction P n + cumulativeCost B n

theorem stepRepairSlack_nonneg {P : ProblemSpec X}
    (B : RepairBudget P) (t : ℕ) :
    0 ≤ stepRepairSlack B t := by
  unfold stepRepairSlack
  linarith [B.gain_le_cost t]

theorem cumulativeRepairSlack_nonneg {P : ProblemSpec X}
    (B : RepairBudget P) (n : ℕ) :
    0 ≤ cumulativeRepairSlack B n := by
  unfold cumulativeRepairSlack
  refine Finset.sum_nonneg ?_
  intro t ht
  exact stepRepairSlack_nonneg B t

/-- Pointwise total production splits as contraction loss plus repair slack. -/
theorem stepTotalProduction_eq_stepLoss_add_stepRepairSlack {P : ProblemSpec X}
    (B : RepairBudget P) (t : ℕ) :
    stepTotalProduction B t = stepLoss P t + stepRepairSlack B t := by
  unfold stepTotalProduction stepRepairSlack stepNetAction
  ring

/-- The cumulative total production decomposes as
`Σ = cumulativeLoss + cumulativeRepairSlack`. -/
theorem cumulativeTotalProduction_eq_cumulativeLoss_add_cumulativeRepairSlack
    {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) :
    cumulativeTotalProduction B n =
      cumulativeLoss P n + cumulativeRepairSlack B n := by
  unfold cumulativeTotalProduction cumulativeNetAction cumulativeCost
    cumulativeLoss cumulativeRepairSlack
  calc
    (∑ t ∈ Finset.range n, stepNetAction P t) + ∑ t ∈ Finset.range n, B.stepCost t
        = ∑ t ∈ Finset.range n, (stepNetAction P t + B.stepCost t) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ t ∈ Finset.range n, (stepLoss P t + stepRepairSlack B t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          unfold stepRepairSlack stepNetAction
          ring
    _ = (∑ t ∈ Finset.range n, stepLoss P t) + ∑ t ∈ Finset.range n, stepRepairSlack B t := by
          rw [Finset.sum_add_distrib]

/-- Total production dominates cumulative contraction loss whenever repair
must be paid for by resource cost. -/
theorem cumulativeLoss_le_cumulativeTotalProduction {P : ProblemSpec X}
    (B : RepairBudget P) (n : ℕ) :
    cumulativeLoss P n ≤ cumulativeTotalProduction B n := by
  rw [cumulativeTotalProduction_eq_cumulativeLoss_add_cumulativeRepairSlack]
  have hslack : 0 ≤ cumulativeRepairSlack B n := cumulativeRepairSlack_nonneg B n
  linarith

/-- Under exact payment, total production collapses to cumulative loss. -/
theorem cumulativeTotalProduction_eq_cumulativeLoss_of_exact_payment
    {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ)
    (hexact : ∀ t, B.stepCost t = stepGain P t) :
    cumulativeTotalProduction B n = cumulativeLoss P n := by
  rw [cumulativeTotalProduction_eq_cumulativeLoss_add_cumulativeRepairSlack]
  unfold cumulativeRepairSlack
  have hzero :
      ∑ t ∈ Finset.range n, stepRepairSlack B t = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    unfold stepRepairSlack
    rw [hexact t]
    ring
  rw [hzero]
  ring

end

end Persistence.TotalProduction
