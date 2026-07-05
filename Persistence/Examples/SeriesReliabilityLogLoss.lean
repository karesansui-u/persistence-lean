import Persistence.LogUniqueness
import Persistence.FosterLyapunovSignBridge

/-!
# Finite Series Reliability Log-Loss Example

This file is a small theorem-bearing adapter connecting the elementary
series-composition law of reliability engineering to the Core log-ratio
coordinate.  The series-composition law is supplied as the input:

```text
system survival = product of component survivals
```

Design choice: the burden coordinate is not freshly defined here.  It is
`Persistence.FosterLyapunovSignBridge.structuralPotential id`, the same
potential used by the finite queue drift-sign example.  The two examples share
one coordinate by definition, not by analogy.

What is proved:

* series systems with component survivals in `(0, 1]` also live in `(0, 1]`;
* series composition is additive in the burden coordinate `-log r`;
* by `log_ratio_uniqueness`, every admissible scalar loss in the Core class
  (continuous, nonnegative, log-additive) reads series burden as a nonnegative
  rescaling of the same sum;
* a survival threshold in ratio space is exactly a burden budget in log space;
* within series (AND) composition, a single component whose burden exceeds the
  budget forces non-viability of the series system.

Scope limitations:

* the series law `R = ∏ r_i` is a domain-side input; in reliability practice it
  usually encodes independence assumptions that are not derived here;
* this is static composition only: no repair, no time dynamics, no recurrence;
* series (AND) systems only: parallel or redundant composition is outside this
  file's scope;
* vector-valued risk profiles, discontinuous diagnostics, and non-additive
  readouts are not excluded by the uniqueness theorem.
-/

open Finset

namespace Persistence.Examples.SeriesReliabilityLogLoss

noncomputable section

/--
The burden coordinate: the same `structuralPotential id` used by the queue
drift-sign example, i.e. `-log r` in structural nats.
-/
def burden : ℝ -> ℝ :=
  Persistence.FosterLyapunovSignBridge.structuralPotential (id : ℝ -> ℝ)

theorem burden_def (x : ℝ) : burden x = -Real.log x := rfl

variable {ι : Type*} (s : Finset ι) (r : ι -> ℝ)

/--
Series-composition survival.  This is the reliability-engineering composition
input, not a theorem derived from independence assumptions in this file.
-/
def seriesSurvival : ℝ := ∏ i ∈ s, r i

variable (hr0 : ∀ i ∈ s, 0 < r i) (hr1 : ∀ i ∈ s, r i <= 1)

include hr0 hr1 in
/--
Domain soundness: a series system of component survivals in `(0, 1]` also has
survival in `(0, 1]`, so it lies in the Core ratio domain.
-/
theorem seriesSurvival_mem_Ioc :
    seriesSurvival s r ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_pos hr0
  · exact Finset.prod_le_one (fun i hi => le_of_lt (hr0 i hi)) hr1

include hr0 in
/--
Burden additivity: in the shared coordinate, the burden of a series system is
the sum of component burdens.
-/
theorem burden_seriesSurvival_eq_sum :
    burden (seriesSurvival s r) = ∑ i ∈ s, burden (r i) := by
  unfold seriesSurvival
  rw [burden_def, Real.log_prod (fun i hi => ne_of_gt (hr0 i hi))]
  rw [← Finset.sum_neg_distrib]
  simp [burden_def]

include hr0 hr1 in
/--
No rival admissible scalar log-additive coordinate: any loss function satisfying
the Core assumptions (nonnegativity on `(0,1]`, normalization, log-additivity,
and continuity) reads the series system as a nonnegative rescaling of the same
burden sum, by `log_ratio_uniqueness`.

This excludes only rivals inside that admissible scalar class.  It does not
exclude vector-valued, discontinuous, or non-additive readouts.
-/
theorem admissible_loss_reads_series_as_burden_sum
    (f : ℝ -> ℝ)
    (hf_nonneg : ∀ x, 0 < x -> x <= 1 -> 0 <= f x)
    (hf_one : f 1 = 0)
    (hf_add : Persistence.IsLogAdditive f)
    (hf_cont : Continuous f) :
    ∃ k : ℝ, 0 <= k ∧
      f (seriesSurvival s r) = k * ∑ i ∈ s, burden (r i) := by
  obtain ⟨k, hk0, hk⟩ :=
    Persistence.log_ratio_uniqueness f hf_nonneg hf_one hf_add hf_cont
  have hmem := seriesSurvival_mem_Ioc s r hr0 hr1
  refine ⟨k, hk0, ?_⟩
  rw [hk _ hmem.1 hmem.2]
  have hsum := burden_seriesSurvival_eq_sum s r hr0
  rw [burden_def] at hsum
  rw [show -k * Real.log (seriesSurvival s r) =
        k * -Real.log (seriesSurvival s r) from by ring, hsum]

include hr0 hr1 in
/--
Boundary readout as burden budget: for a survival threshold `theta`, the series
system meets the threshold iff total burden stays within the budget
`burden theta`.
-/
theorem seriesSurvival_ge_iff_burden_le_budget
    (theta : ℝ) (htheta : 0 < theta) :
    theta <= seriesSurvival s r ↔
      ∑ i ∈ s, burden (r i) <= burden theta := by
  have hpos : 0 < seriesSurvival s r :=
    (seriesSurvival_mem_Ioc s r hr0 hr1).1
  rw [← burden_seriesSurvival_eq_sum s r hr0, burden_def, burden_def]
  constructor
  · intro h
    have := Real.log_le_log htheta h
    linarith
  · intro h
    have hlog : Real.log theta <= Real.log (seriesSurvival s r) := by
      linarith
    calc theta = Real.exp (Real.log theta) := (Real.exp_log htheta).symm
      _ <= Real.exp (Real.log (seriesSurvival s r)) :=
        Real.exp_le_exp.mpr hlog
      _ = seriesSurvival s r := Real.exp_log hpos

include hr0 hr1 in
/--
Red test for series composition: if even one component's burden exceeds the
budget, the series system is non-viable, no matter how good every other
component is.

This is a series (AND) statement.  Parallel redundancy or repair would change
the composition law and is outside this file's scope.
-/
theorem single_burden_overshoot_forces_nonviable
    (theta : ℝ) (htheta : 0 < theta)
    {j : ι} (hj : j ∈ s)
    (hover : burden theta < burden (r j)) :
    seriesSurvival s r < theta := by
  classical
  have hrj0 : 0 < r j := hr0 j hj
  have hrjtheta : r j < theta := by
    rw [burden_def, burden_def] at hover
    have hlog : Real.log (r j) < Real.log theta := by
      linarith
    calc r j = Real.exp (Real.log (r j)) := (Real.exp_log hrj0).symm
      _ < Real.exp (Real.log theta) := Real.exp_lt_exp.mpr hlog
      _ = theta := Real.exp_log htheta
  have hrest : ∏ i ∈ s.erase j, r i <= 1 :=
    Finset.prod_le_one
      (fun i hi => le_of_lt (hr0 i (Finset.mem_of_mem_erase hi)))
      (fun i hi => hr1 i (Finset.mem_of_mem_erase hi))
  calc seriesSurvival s r = r j * ∏ i ∈ s.erase j, r i :=
        (Finset.mul_prod_erase s r hj).symm
    _ <= r j * 1 := by
        exact mul_le_mul_of_nonneg_left hrest (le_of_lt hrj0)
    _ = r j := mul_one _
    _ < theta := hrjtheta

end

end Persistence.Examples.SeriesReliabilityLogLoss
