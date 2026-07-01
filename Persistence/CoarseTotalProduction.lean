import Persistence.CoarseGraining
import Persistence.TotalProduction

/-!
Coarse-Grained Total Production
coarse-grained total production の定義層

This module lifts total production to the coarse-grained setting.

The conservative interface is:

* an admissible coarse-graining between `P` and `Q`
* uniform mass scaling, so the signed net action is preserved
* a cost-invariant budget, so the same resource accounting is used before and
  after coarse-graining

Under these assumptions, cumulative cost, repair slack, and total production
are preserved exactly.
-/

open scoped BigOperators
open Finset

namespace Persistence.CoarseTotalProduction

open Persistence.GeneralStateDynamics
open Persistence.CoarseGraining
open Persistence.ResourceBudget
open Persistence.TotalProduction

noncomputable section

variable {X Y : Type*}

/-- Budget compatibility across coarse-graining: the stepwise resource cost is
preserved under the passage from the micro problem `P` to the coarse problem `Q`. -/
structure CostInvariantBudget
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (Bmicro : RepairBudget P) (Bcoarse : RepairBudget Q) : Prop where
  stepCost_eq : ∀ t, Bcoarse.stepCost t = Bmicro.stepCost t

theorem cumulativeCost_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse) (n : ℕ) :
    cumulativeCost Bcoarse n = cumulativeCost Bmicro n := by
  unfold cumulativeCost
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact hB.stepCost_eq t

theorem stepRepairSlack_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (t : ℕ)
    (hcontract : 0 < contractedMass P t) :
    stepRepairSlack Bcoarse t = stepRepairSlack Bmicro t := by
  unfold stepRepairSlack
  rw [hB.stepCost_eq, stepGain_preserved cg hs t hcontract]

theorem cumulativeRepairSlack_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (n : ℕ)
    (hpos : PositiveTrajectory P n) :
    cumulativeRepairSlack Bcoarse n = cumulativeRepairSlack Bmicro n := by
  unfold cumulativeRepairSlack
  refine Finset.sum_congr rfl ?_
  intro t ht
  have ht_lt : t < n := Finset.mem_range.mp ht
  exact stepRepairSlack_preserved cg hs hB t (hpos.contracted_pos t ht_lt)

theorem stepTotalProduction_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    stepTotalProduction Bcoarse t = stepTotalProduction Bmicro t := by
  unfold stepTotalProduction
  rw [hB.stepCost_eq, stepNetAction_preserved cg hs t hfeas hcontract hnext]

theorem cumulativeTotalProduction_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (n : ℕ)
    (hpos : PositiveTrajectory P n) :
    cumulativeTotalProduction Bcoarse n = cumulativeTotalProduction Bmicro n := by
  unfold cumulativeTotalProduction
  rw [cumulativeNetAction_preserved cg hs n hpos, cumulativeCost_preserved hB n]

theorem cumulativeTotalProduction_eq_cumulativeLoss_add_cumulativeRepairSlack_coarse
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    {Bmicro : RepairBudget P} {Bcoarse : RepairBudget Q}
    (hB : CostInvariantBudget Bmicro Bcoarse)
    (n : ℕ)
    (hpos : PositiveTrajectory P n) :
    cumulativeTotalProduction Bcoarse n =
      cumulativeLoss P n + cumulativeRepairSlack Bmicro n := by
  rw [cumulativeTotalProduction_preserved cg hs hB n hpos]
  exact cumulativeTotalProduction_eq_cumulativeLoss_add_cumulativeRepairSlack Bmicro n

end

end Persistence.CoarseTotalProduction
