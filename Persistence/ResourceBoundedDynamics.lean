import Mathlib.Tactic.Linarith
import Persistence.CoarseTotalProduction
import Persistence.TypicalNondecrease

/-!
Resource-Bounded Dynamics
resource-bounded dynamics の仮定層

This module connects three previously separated layers:

* `RepairBudget`: repair / learning is never free
* `TotalProduction`: `Σ = A + C`
* `TypicalNondecrease`: nonnegative drift implies monotone expectation

The deterministic core proved here is:

1. contraction loss is nonnegative
2. repair slack is nonnegative under a repair budget
3. therefore one-step total production is nonnegative
4. cumulative total production is monotone

This gives the simplest resource-bounded version of a "law of tendency",
before introducing genuine randomness.
-/

open scoped BigOperators
open Finset Real

namespace Persistence.ResourceBoundedDynamics

open Persistence.GeneralStateDynamics
open Persistence.ResourceBudget
open Persistence.TotalProduction
open Persistence.CoarseGraining
open Persistence.CoarseTotalProduction
open Persistence.TypicalNondecrease

noncomputable section

variable {X Y : Type*}

/-- A resource-bounded dynamics consists of a repair budget together with
global positivity of feasible and contracted masses, so that all log-ratio
quantities are well-defined at every step. -/
structure BoundedTrajectory (P : ProblemSpec X) (B : RepairBudget P) : Prop where
  feasible_pos : ∀ t, 0 < feasibleMass P t
  contracted_pos : ∀ t, 0 < contractedMass P t

/-- A resource-bounded dynamics yields a positive trajectory on every finite horizon. -/
def toPositiveTrajectory
    {P : ProblemSpec X} {B : RepairBudget P}
    (R : BoundedTrajectory P B) (n : ℕ) :
    PositiveTrajectory P n where
  feasible_pos := fun t _ => R.feasible_pos t
  contracted_pos := fun t _ => R.contracted_pos t

/-- Contraction loss is nonnegative because contraction never enlarges the feasible mass. -/
theorem stepLoss_nonneg
    (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t) :
    0 ≤ stepLoss P t := by
  have hratio_nonneg : 0 ≤ contractedMass P t / feasibleMass P t := by
    positivity
  have hratio_le_one : contractedMass P t / feasibleMass P t ≤ 1 := by
    have hle : contractedMass P t ≤ feasibleMass P t := contractedMass_le_feasibleMass P t
    exact (div_le_iff₀ hfeas).2 (by simpa using hle)
  have hlog_nonpos :
      Real.log (contractedMass P t / feasibleMass P t) ≤ 0 :=
    Real.log_nonpos hratio_nonneg hratio_le_one
  unfold stepLoss
  linarith

/-- Under a repair budget, one-step total production is nonnegative. -/
theorem stepTotalProduction_nonneg
    {P : ProblemSpec X} (B : RepairBudget P) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t) :
    0 ≤ stepTotalProduction B t := by
  rw [stepTotalProduction_eq_stepLoss_add_stepRepairSlack]
  have hloss : 0 ≤ stepLoss P t := stepLoss_nonneg P t hfeas hcontract
  have hslack : 0 ≤ stepRepairSlack B t := stepRepairSlack_nonneg B t
  linarith

/-- Cumulative total production satisfies a one-step recursion. -/
theorem cumulativeTotalProduction_succ
    {P : ProblemSpec X} (B : RepairBudget P) (n : ℕ) :
    cumulativeTotalProduction B (n + 1) =
      cumulativeTotalProduction B n + stepTotalProduction B n := by
  unfold cumulativeTotalProduction cumulativeNetAction cumulativeCost stepTotalProduction
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring

/-- As a consequence, cumulative total production is monotone one step at a time. -/
theorem cumulativeTotalProduction_le_succ
    {P : ProblemSpec X} {B : RepairBudget P}
    (R : BoundedTrajectory P B) (t : ℕ) :
    cumulativeTotalProduction B t ≤ cumulativeTotalProduction B (t + 1) := by
  rw [cumulativeTotalProduction_succ]
  have hstep : 0 ≤ stepTotalProduction B t :=
    stepTotalProduction_nonneg B t (R.feasible_pos t) (R.contracted_pos t)
  linarith

/-- Deterministic total production viewed as an expected process. -/
def deterministicExpectedTotalProduction
    {P : ProblemSpec X} (B : RepairBudget P) : ExpectedTotalProduction where
  expectedCumulative := cumulativeTotalProduction B
  expectedIncrement := stepTotalProduction B
  expected_succ := cumulativeTotalProduction_succ B

/-- Resource-bounded dynamics induce nonnegative drift in the deterministic
expected-total-production process. -/
theorem deterministicExpectedTotalProduction_has_nonnegative_drift
    {P : ProblemSpec X} {B : RepairBudget P}
    (R : BoundedTrajectory P B) :
    ExpectedNonnegativeDrift (deterministicExpectedTotalProduction B) := by
  intro t
  exact stepTotalProduction_nonneg B t (R.feasible_pos t) (R.contracted_pos t)

/-- Hence cumulative total production is monotone under resource-bounded dynamics. -/
theorem cumulativeTotalProduction_monotone
    {P : ProblemSpec X} {B : RepairBudget P}
    (R : BoundedTrajectory P B) :
    Monotone (cumulativeTotalProduction B) := by
  simpa [deterministicExpectedTotalProduction] using
    expectedCumulative_monotone
      (deterministicExpectedTotalProduction B)
      (deterministicExpectedTotalProduction_has_nonnegative_drift R)

/-- Coarse cumulative total production is monotone whenever it is linked to a
resource-bounded micro dynamics by admissible coarse-graining, uniform mass
scaling, and cost-invariant budgeting. -/
theorem coarse_cumulativeTotalProduction_monotone
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (R : BoundedTrajectory P Bmicro) :
    Monotone (cumulativeTotalProduction Bcoarse) := by
  have hmono_micro : Monotone (cumulativeTotalProduction Bmicro) :=
    cumulativeTotalProduction_monotone R
  intro m n hmn
  have hm :
      cumulativeTotalProduction Bcoarse m = cumulativeTotalProduction Bmicro m :=
    cumulativeTotalProduction_preserved cg hs hB m (toPositiveTrajectory R m)
  have hn :
      cumulativeTotalProduction Bcoarse n = cumulativeTotalProduction Bmicro n :=
    cumulativeTotalProduction_preserved cg hs hB n (toPositiveTrajectory R n)
  rw [hm, hn]
  exact hmono_micro hmn

end

end Persistence.ResourceBoundedDynamics
