import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Persistence.TelescopingExp

/-!
General state dynamics and signed exponential kernel

This module formalizes the mathematically proved core of the supplement
"General state dynamics and the signed exponential kernel".

What is formalized here:

* General state dynamics given by contraction `K_t` followed by repair `R_t`
* Ratio-defined loss, gain, and net action
* Proposition 1: net action is a start/end log-ratio
* Proposition 2: local net-consumption identity
* Theorem 3: signed exponential kernel via telescoping
* Corollary 4: pure contraction recovers the original shrinkage mode

What is intentionally *not* formalized here:

* representation covariance
* weak-dependence bounds for signed action
* naturality of the mass model
* resource-theoretic extensions with explicit `M`
-/

open scoped BigOperators
open Finset Real

namespace Persistence.GeneralStateDynamics

noncomputable section

variable {X : Type*}

/-- A general state dynamics updates a feasible region by first contracting it
and then applying a repair/expansion map. -/
structure Dynamics (X : Type*) where
  contract : ℕ → Set X → Set X
  repair : ℕ → Set X → Set X
  contract_sub : ∀ t A, contract t A ⊆ A
  repair_sup : ∀ t A, A ⊆ repair t A

/-- Abstract mass model used to compare feasible regions. -/
structure MassModel (X : Type*) where
  mass : Set X → ℝ
  mono : ∀ {A B : Set X}, A ⊆ B → mass A ≤ mass B

/-- Minimal mathematical specification for the proved kernel. -/
structure ProblemSpec (X : Type*) where
  V0 : Set X
  M : MassModel X
  D : Dynamics X

/-- One update step: contract, then repair. -/
def step (P : ProblemSpec X) (t : ℕ) (A : Set X) : Set X :=
  P.D.repair t (P.D.contract t A)

/-- Reachable / feasible region under the dynamics. -/
def feasible (P : ProblemSpec X) : ℕ → Set X
  | 0 => P.V0
  | t + 1 => step P t (feasible P t)

/-- Region immediately after contraction and before repair. -/
def contracted (P : ProblemSpec X) (t : ℕ) : Set X :=
  P.D.contract t (feasible P t)

/-- Region after repair. This is definitionally the next feasible region. -/
def repaired (P : ProblemSpec X) (t : ℕ) : Set X :=
  P.D.repair t (contracted P t)

@[simp] theorem feasible_succ (P : ProblemSpec X) (t : ℕ) :
    feasible P (t + 1) = repaired P t := rfl

/-- Mass of the feasible region at time `t`. -/
def feasibleMass (P : ProblemSpec X) (t : ℕ) : ℝ :=
  P.M.mass (feasible P t)

/-- Mass right after contraction. -/
def contractedMass (P : ProblemSpec X) (t : ℕ) : ℝ :=
  P.M.mass (contracted P t)

/-- Mass right after repair. -/
def repairedMass (P : ProblemSpec X) (t : ℕ) : ℝ :=
  P.M.mass (repaired P t)

@[simp] theorem repairedMass_eq_feasibleMass_succ (P : ProblemSpec X) (t : ℕ) :
    repairedMass P t = feasibleMass P (t + 1) := rfl

theorem contracted_subset_feasible (P : ProblemSpec X) (t : ℕ) :
    contracted P t ⊆ feasible P t :=
  P.D.contract_sub t (feasible P t)

theorem contracted_subset_repaired (P : ProblemSpec X) (t : ℕ) :
    contracted P t ⊆ repaired P t :=
  P.D.repair_sup t (contracted P t)

theorem contractedMass_le_feasibleMass (P : ProblemSpec X) (t : ℕ) :
    contractedMass P t ≤ feasibleMass P t :=
  P.M.mono (contracted_subset_feasible P t)

theorem contractedMass_le_repairedMass (P : ProblemSpec X) (t : ℕ) :
    contractedMass P t ≤ repairedMass P t :=
  P.M.mono (contracted_subset_repaired P t)

/-- Stage loss induced by contraction. -/
def stepLoss (P : ProblemSpec X) (t : ℕ) : ℝ :=
  -Real.log (contractedMass P t / feasibleMass P t)

/-- Stage gain induced by repair. -/
def stepGain (P : ProblemSpec X) (t : ℕ) : ℝ :=
  Real.log (repairedMass P t / contractedMass P t)

/-- Signed net action = loss minus gain. -/
def stepNetAction (P : ProblemSpec X) (t : ℕ) : ℝ :=
  stepLoss P t - stepGain P t

/-- Cumulative contraction loss. -/
def cumulativeLoss (P : ProblemSpec X) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stepLoss P t

/-- Cumulative repair gain. -/
def cumulativeGain (P : ProblemSpec X) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stepGain P t

/-- Cumulative signed net action. -/
def cumulativeNetAction (P : ProblemSpec X) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, stepNetAction P t

/-- Positivity assumptions needed to take logarithms up to horizon `n`. -/
structure PositiveTrajectory (P : ProblemSpec X) (n : ℕ) : Prop where
  feasible_pos : ∀ t ≤ n, 0 < feasibleMass P t
  contracted_pos : ∀ t < n, 0 < contractedMass P t

/-- Proposition 1: the signed net action is the log-ratio from the current feasible mass
to the next feasible mass. -/
theorem stepNetAction_eq_neg_log_feasible_ratio (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    stepNetAction P t = -Real.log (feasibleMass P (t + 1) / feasibleMass P t) := by
  have hlog :
      Real.log (contractedMass P t / feasibleMass P t) +
        Real.log (feasibleMass P (t + 1) / contractedMass P t) =
      Real.log ((contractedMass P t / feasibleMass P t) *
        (feasibleMass P (t + 1) / contractedMass P t)) := by
    symm
    exact Real.log_mul (by positivity) (by positivity)
  have hratio :
      (contractedMass P t / feasibleMass P t) *
        (feasibleMass P (t + 1) / contractedMass P t) =
      feasibleMass P (t + 1) / feasibleMass P t := by
    field_simp [ne_of_gt hfeas, ne_of_gt hcontract]
  calc
    stepNetAction P t
        = -Real.log (contractedMass P t / feasibleMass P t) -
            Real.log (feasibleMass P (t + 1) / contractedMass P t) := by
          simp [stepNetAction, stepLoss, stepGain]
    _ = -(Real.log (contractedMass P t / feasibleMass P t) +
            Real.log (feasibleMass P (t + 1) / contractedMass P t)) := by
          ring
    _ = -Real.log ((contractedMass P t / feasibleMass P t) *
            (feasibleMass P (t + 1) / contractedMass P t)) := by
          rw [hlog]
    _ = -Real.log (feasibleMass P (t + 1) / feasibleMass P t) := by
          rw [hratio]

/-- Compatibility with the A1–A2 telescoping core: a signed step is still a log-ratio step. -/
theorem stepNetAction_eq_stageLoss (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    stepNetAction P t = Persistence.TelescopingExp.stageLoss (feasibleMass P) t := by
  simpa [Persistence.TelescopingExp.stageLoss] using
    stepNetAction_eq_neg_log_feasible_ratio P t hfeas hcontract hnext

/-- Proposition 2: local net-consumption identity. -/
theorem feasibleMass_succ_eq_mass_mul_exp_neg_stepNetAction
    (P : ProblemSpec X) (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (hnext : 0 < feasibleMass P (t + 1)) :
    feasibleMass P (t + 1) =
      feasibleMass P t * Real.exp (-stepNetAction P t) := by
  have hratio :
      feasibleMass P t * (feasibleMass P (t + 1) / feasibleMass P t) =
        feasibleMass P (t + 1) := by
    field_simp [ne_of_gt hfeas]
  have hexp :
      Real.exp (-stepNetAction P t) = feasibleMass P (t + 1) / feasibleMass P t := by
    rw [stepNetAction_eq_neg_log_feasible_ratio P t hfeas hcontract hnext]
    rw [neg_neg, Real.exp_log (div_pos hnext hfeas)]
  calc
    feasibleMass P (t + 1)
        = feasibleMass P t * (feasibleMass P (t + 1) / feasibleMass P t) := by
          simpa using hratio.symm
    _ = feasibleMass P t * Real.exp (-stepNetAction P t) := by
          rw [hexp]

/-- The cumulative signed action is the sum of log-ratio stage losses
for the feasible-mass sequence. -/
theorem cumulativeNetAction_eq_sum_stageLoss (P : ProblemSpec X) (n : ℕ)
    (hpos : PositiveTrajectory P n) :
    cumulativeNetAction P n =
      ∑ t ∈ Finset.range n, Persistence.TelescopingExp.stageLoss (feasibleMass P) t := by
  refine Finset.sum_congr rfl ?_
  intro t ht
  have ht_lt : t < n := Finset.mem_range.mp ht
  have hfeas : 0 < feasibleMass P t := hpos.feasible_pos t (Nat.le_of_lt ht_lt)
  have hcontract : 0 < contractedMass P t := hpos.contracted_pos t ht_lt
  have hnext : 0 < feasibleMass P (t + 1) := hpos.feasible_pos (t + 1) (Nat.succ_le_of_lt ht_lt)
  exact stepNetAction_eq_stageLoss P t hfeas hcontract hnext

/-- Theorem 3: signed exponential kernel. -/
theorem feasibleMass_eq_initial_mul_exp_neg_cumulativeNetAction
    (P : ProblemSpec X) (n : ℕ) (hpos : PositiveTrajectory P n) :
    feasibleMass P n =
      feasibleMass P 0 * Real.exp (-cumulativeNetAction P n) := by
  have htele :
      feasibleMass P n =
        feasibleMass P 0 *
          Real.exp
            (-∑ t ∈ Finset.range n,
              Persistence.TelescopingExp.stageLoss (feasibleMass P) t) := by
    simpa using
      Persistence.TelescopingExp.measure_eq_initial_mul_exp_neg_cumulative_loss
        (m := feasibleMass P) n hpos.feasible_pos
  calc
    feasibleMass P n =
        feasibleMass P 0 *
          Real.exp
            (-∑ t ∈ Finset.range n,
              Persistence.TelescopingExp.stageLoss (feasibleMass P) t) := htele
    _ = feasibleMass P 0 * Real.exp (-cumulativeNetAction P n) := by
          rw [← cumulativeNetAction_eq_sum_stageLoss P n hpos]

/-- Pure contraction means repair does nothing. -/
def PureContraction (D : Dynamics X) : Prop :=
  ∀ t A, D.repair t A = A

/-- In pure contraction mode the stage gain vanishes. -/
theorem stepGain_eq_zero_of_pureContraction
    (P : ProblemSpec X) (t : ℕ)
    (hpure : PureContraction P.D)
    (hcontract : 0 < contractedMass P t) :
    stepGain P t = 0 := by
  have hcontract_ne : contractedMass P t ≠ 0 := ne_of_gt hcontract
  unfold stepGain repairedMass repaired
  rw [hpure t (contracted P t)]
  simp [contractedMass]

/-- In pure contraction mode the cumulative gain vanishes. -/
theorem cumulativeGain_eq_zero_of_pureContraction
    (P : ProblemSpec X) (n : ℕ)
    (hpure : PureContraction P.D)
    (hpos : PositiveTrajectory P n) :
    cumulativeGain P n = 0 := by
  refine Finset.sum_eq_zero ?_
  intro t ht
  exact stepGain_eq_zero_of_pureContraction P t hpure
    (hpos.contracted_pos t (Finset.mem_range.mp ht))

/-- Corollary 4: pure contraction recovers the original shrinkage-mode action. -/
theorem cumulativeNetAction_eq_cumulativeLoss_of_pureContraction
    (P : ProblemSpec X) (n : ℕ)
    (hpure : PureContraction P.D)
    (hpos : PositiveTrajectory P n) :
    cumulativeNetAction P n = cumulativeLoss P n := by
  unfold cumulativeNetAction cumulativeLoss
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [stepNetAction, stepGain_eq_zero_of_pureContraction P t hpure
    (hpos.contracted_pos t (Finset.mem_range.mp ht))]
  ring

/-- Under pure contraction, the signed kernel reduces to the original shrinkage kernel. -/
theorem feasibleMass_eq_initial_mul_exp_neg_cumulativeLoss_of_pureContraction
    (P : ProblemSpec X) (n : ℕ)
    (hpure : PureContraction P.D)
    (hpos : PositiveTrajectory P n) :
    feasibleMass P n = feasibleMass P 0 * Real.exp (-cumulativeLoss P n) := by
  rw [← cumulativeNetAction_eq_cumulativeLoss_of_pureContraction P n hpure hpos]
  exact feasibleMass_eq_initial_mul_exp_neg_cumulativeNetAction P n hpos

end

end Persistence.GeneralStateDynamics
