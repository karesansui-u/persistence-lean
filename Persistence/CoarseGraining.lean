import Mathlib.Data.Set.Image
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Persistence.GeneralStateDynamics

/-!
Coarse Graining for the Set-Valued Dynamical Representation of Structural Persistence
構造持続の集合値力学的表現に対する coarse-graining の定義層

This module adds a conservative formal interface for admissible coarse-graining.

What is formalized here:

* a coarse map `π : X → Y` and its action on feasible sets
* admissibility as commutation with initial region, contraction, and repair
* feasibility commutes with admissible coarse-graining
* a uniform mass-scaling condition under which the signed kernel is preserved exactly

This is intentionally a definition layer, not yet a full universality theorem.
-/

open scoped BigOperators
open Finset

namespace Persistence.CoarseGraining

open Persistence.GeneralStateDynamics

noncomputable section

variable {X Y : Type*}

/-- A coarse-graining map from microstates `X` to macrostates `Y`. -/
structure CoarseMap (X Y : Type*) where
  proj : X → Y

/-- Push a set of microstates forward along the coarse-graining map. -/
def CoarseMap.pushSet (cg : CoarseMap X Y) (A : Set X) : Set Y :=
  cg.proj '' A

theorem CoarseMap.pushSet_mono (cg : CoarseMap X Y) {A B : Set X}
    (hAB : A ⊆ B) :
    cg.pushSet A ⊆ cg.pushSet B := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  exact ⟨x, hAB hxA, rfl⟩

/-- A coarse-graining is admissible when it commutes with the initial region,
contraction, and repair. -/
structure AdmissibleCoarseGraining
    (P : ProblemSpec X) (Q : ProblemSpec Y) where
  map : CoarseMap X Y
  initial_commutes : map.pushSet P.V0 = Q.V0
  contract_commutes :
    ∀ t A, map.pushSet (P.D.contract t A) = Q.D.contract t (map.pushSet A)
  repair_commutes :
    ∀ t A, map.pushSet (P.D.repair t A) = Q.D.repair t (map.pushSet A)

/-- Under an admissible coarse-graining, the reachable / feasible region commutes
with the projection at every time. -/
theorem feasible_commutes
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q) :
    ∀ n, cg.map.pushSet (feasible P n) = feasible Q n
  | 0 => cg.initial_commutes
  | n + 1 => by
      rw [feasible_succ, feasible_succ, repaired, repaired]
      rw [cg.repair_commutes]
      congr 1
      rw [contracted, cg.contract_commutes]
      congr 1
      exact feasible_commutes cg n

theorem contracted_commutes'
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q) (t : ℕ) :
    cg.map.pushSet (contracted P t) = contracted Q t := by
  rw [contracted, cg.contract_commutes]
  congr 1
  exact feasible_commutes cg t

theorem repaired_commutes
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q) (t : ℕ) :
    cg.map.pushSet (repaired P t) = repaired Q t := by
  rw [repaired, cg.repair_commutes]
  congr 1
  exact contracted_commutes' cg t

/-- Uniform mass scaling across feasible and contracted regions.
This is the exact-symmetry case in which the signed kernel is preserved. -/
structure UniformMassScaling
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q) where
  c : ℝ
  c_pos : 0 < c
  feasible_scale : ∀ n, feasibleMass Q n = c * feasibleMass P n
  contracted_scale : ∀ t, contractedMass Q t = c * contractedMass P t

theorem stepLoss_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    (t : ℕ)
    (hfeas : 0 < feasibleMass P t) :
    stepLoss Q t = stepLoss P t := by
  have hc : hs.c ≠ 0 := ne_of_gt hs.c_pos
  rw [stepLoss, stepLoss, hs.contracted_scale, hs.feasible_scale]
  have hratio :
      (hs.c * contractedMass P t) / (hs.c * feasibleMass P t) =
        contractedMass P t / feasibleMass P t := by
    field_simp [hc, ne_of_gt hfeas]
  rw [hratio]

theorem stepGain_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    (t : ℕ)
    (hcontract : 0 < contractedMass P t) :
    stepGain Q t = stepGain P t := by
  have hc : hs.c ≠ 0 := ne_of_gt hs.c_pos
  rw [stepGain, stepGain, repairedMass_eq_feasibleMass_succ, repairedMass_eq_feasibleMass_succ,
    hs.feasible_scale, hs.contracted_scale]
  have hratio :
      (hs.c * feasibleMass P (t + 1)) / (hs.c * contractedMass P t) =
        feasibleMass P (t + 1) / contractedMass P t := by
    field_simp [hc, ne_of_gt hcontract]
  rw [hratio]

theorem stepNetAction_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    (t : ℕ)
    (hfeas : 0 < feasibleMass P t)
    (hcontract : 0 < contractedMass P t)
    (_hnext : 0 < feasibleMass P (t + 1)) :
    stepNetAction Q t = stepNetAction P t := by
  rw [stepNetAction, stepNetAction,
    stepLoss_preserved cg hs t hfeas,
    stepGain_preserved cg hs t hcontract]

theorem cumulativeNetAction_preserved
    {P : ProblemSpec X} {Q : ProblemSpec Y}
    (cg : AdmissibleCoarseGraining P Q)
    (hs : UniformMassScaling cg)
    (n : ℕ)
    (hpos : PositiveTrajectory P n) :
    cumulativeNetAction Q n = cumulativeNetAction P n := by
  unfold cumulativeNetAction
  refine Finset.sum_congr rfl ?_
  intro t ht
  have ht_lt : t < n := Finset.mem_range.mp ht
  have hfeas : 0 < feasibleMass P t := hpos.feasible_pos t (Nat.le_of_lt ht_lt)
  have hcontract : 0 < contractedMass P t := hpos.contracted_pos t ht_lt
  have hnext : 0 < feasibleMass P (t + 1) := hpos.feasible_pos (t + 1) (Nat.succ_le_of_lt ht_lt)
  exact stepNetAction_preserved cg hs t hfeas hcontract hnext

end

end Persistence.CoarseGraining
