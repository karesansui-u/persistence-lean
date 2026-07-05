import Persistence.FosterLyapunovSignBridge

/-!
# Finite Geo/Geo/1 Buffer Drift-Sign Example

This file is a small theorem-bearing adapter for the drift-sign interface in
`Persistence.FosterLyapunovSignBridge`.

It models a discrete-time one-server queue with a one-slot finite buffer:

* states are queue lengths `0`, `1`, and `2`;
* Bernoulli arrivals have probability `p`;
* Bernoulli service completions have probability `q`;
* arrivals are blocked when the buffer is full.

Scope limitations:

* this is a finite-buffer drift-sign example, not a recurrence theorem;
* the chain is finite, so this does not prove infinite-buffer queue stability;
* the readout is relative to the declared safe set.

The useful check is that the interface-level expected net change at the
interior state computes to `p - q`.  Thus, after the safe set `{0}` is fixed,
the negative-drift boundary agrees with the utilization comparison `p < q`.
The file also proves a contrast theorem: widening the safe set changes the
readout obligation, demonstrating that the choice of viable/safe region is
load-bearing rather than automatic.
-/

open Persistence.FosterLyapunovSignBridge

namespace Persistence.Examples.QueueGeoGeo1Drift

noncomputable section

/-- Queue-length potential on the three-state buffer: 0, 1, or 2 jobs. -/
def queuePotential : Fin 3 -> ℝ := fun i => (i : ℝ)

variable (p q : ℝ)

/--
Transition masses for the finite-buffer Geo/Geo/1 queue.

From state `0`, an arrival moves the queue to `1`.  From state `1`, arrival
without service moves to `2`, service without arrival moves to `0`, and the
other cases stay at `1`.  From state `2`, arrivals are blocked and service
completion moves the queue to `1`.
-/
def mass : Fin 3 -> Fin 3 -> ℝ
  | 0, 0 => 1 - p
  | 0, 1 => p
  | 0, 2 => 0
  | 1, 0 => q * (1 - p)
  | 1, 1 => 1 - p * (1 - q) - q * (1 - p)
  | 1, 2 => p * (1 - q)
  | 2, 0 => 0
  | 2, 1 => q
  | 2, 2 => 1 - q

variable (hp0 : 0 <= p) (hp1 : p <= 1) (hq0 : 0 <= q) (hq1 : q <= 1)

include hp0 hp1 hq0 hq1 in
theorem mass_nonneg (x y : Fin 3) : 0 <= mass p q x y := by
  have hpq : 0 <= p * q := mul_nonneg hp0 hq0
  have hpq' : 0 <= (1 - p) * (1 - q) := by nlinarith
  fin_cases x <;> fin_cases y <;> simp [mass] <;> nlinarith

theorem mass_sum_one (x : Fin 3) : (∑ y, mass p q x y) = 1 := by
  fin_cases x <;> (simp [Fin.sum_univ_three, mass]; try ring)

/-- Probability kernel in the shape expected by the drift-sign bridge. -/
def kernel : Fin 3 -> PMF (Fin 3) := fun x =>
  PMF.ofFintype (fun y => ENNReal.ofReal (mass p q x y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun y _ => mass_nonneg p q hp0 hp1 hq0 hq1 x y)]
    rw [mass_sum_one p q x]
    exact ENNReal.ofReal_one)

theorem kernel_apply (x y : Fin 3) :
    ((kernel p q hp0 hp1 hq0 hq1 x) y).toReal = mass p q x y := by
  simp [kernel, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (mass_nonneg p q hp0 hp1 hq0 hq1 x y)]

/-- Safe set containing only the empty queue. -/
def emptySafe (x : Fin 3) : Prop := x = 0

/-- Wider safe set that treats the non-full states as safe. -/
def notFullSafe (x : Fin 3) : Prop := x = 0 ∨ x = 1

/-- At the empty state, the expected queue-length change is `p`. -/
theorem expectedNetChange_empty :
    expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 0 = p := by
  unfold expectedNetChange
  rw [Fin.sum_univ_three]
  rw [kernel_apply, kernel_apply, kernel_apply]
  unfold potentialIncrement queuePotential mass
  norm_num

/--
At the interior state, the interface-level expected net change is exactly
`p - q`.
-/
theorem expectedNetChange_interior :
    expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 1 =
      p - q := by
  unfold expectedNetChange
  rw [Fin.sum_univ_three]
  rw [kernel_apply, kernel_apply, kernel_apply]
  unfold potentialIncrement queuePotential mass
  norm_num
  ring

/-- At the full state, arrivals are blocked and service drains at rate `q`. -/
theorem expectedNetChange_full :
    expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 2 =
      -q := by
  unfold expectedNetChange
  rw [Fin.sum_univ_three]
  rw [kernel_apply, kernel_apply, kernel_apply]
  unfold potentialIncrement queuePotential mass
  norm_num

/--
Interior drift is negative exactly when the arrival probability is smaller
than the service-completion probability.
-/
theorem interior_drift_neg_iff_utilization_lt :
    expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 1 < 0 ↔
      p < q := by
  rw [expectedNetChange_interior]
  constructor <;> intro h <;> linarith

/-- Ratio form of the same interior drift readout, for positive service rate. -/
theorem interior_drift_neg_iff_utilization_ratio_lt_one (hq : 0 < q) :
    expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 1 < 0 ↔
      p / q < 1 := by
  rw [interior_drift_neg_iff_utilization_lt, div_lt_one hq]

/--
With `emptySafe`, the outside-safe drift condition holds when `p < q`, with
margin `q - p`.
-/
theorem underloaded_emptySafe_negativeDrift (hlt : p < q) :
    OutsideSafeNegativeDrift (kernel p q hp0 hp1 hq0 hq1) queuePotential
      (emptySafe) (q - p) := by
  refine ⟨by linarith, ?_⟩
  intro x hx
  fin_cases x
  · exact False.elim (hx rfl)
  · change
      expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 1 <=
        -(q - p)
    rw [expectedNetChange_interior]
    linarith
  · change
      expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 2 <=
        -(q - p)
    rw [expectedNetChange_full]
    linarith

/--
With `emptySafe`, if `q <= p`, no margin can make the outside-safe negative
drift condition hold.  The interior state blocks it.
-/
theorem overloaded_emptySafe_noNegativeDrift (hge : q <= p) (eps : ℝ) :
    ¬ OutsideSafeNegativeDrift (kernel p q hp0 hp1 hq0 hq1) queuePotential
      (emptySafe) eps := by
  rintro ⟨heps, hdrift⟩
  have h1 := hdrift 1 (by simp [emptySafe])
  rw [expectedNetChange_interior] at h1
  linarith

/--
With `notFullSafe`, only the full state is outside the safe set.  The readout
obligation therefore changes: positive service rate alone gives negative
drift outside this wider safe set.
-/
theorem notFullSafe_negativeDrift (hq : 0 < q) :
    OutsideSafeNegativeDrift (kernel p q hp0 hp1 hq0 hq1) queuePotential
      (notFullSafe) q := by
  refine ⟨hq, ?_⟩
  intro x hx
  fin_cases x
  · exact False.elim (hx (Or.inl rfl))
  · exact False.elim (hx (Or.inr rfl))
  · change
      expectedNetChange (kernel p q hp0 hp1 hq0 hq1) queuePotential 2 <=
        -q
    rw [expectedNetChange_full]

/--
Safe-set contrast: when `q <= p`, the `emptySafe` readout fails for every
margin, while the wider `notFullSafe` readout still holds if `0 < q`.

This is intentional.  It demonstrates that the viable/safe region is part of
the claim interface and can change the boundary obligation.
-/
theorem overloaded_safeSet_contrast (hq : 0 < q) (hge : q <= p) (eps : ℝ) :
    (¬ OutsideSafeNegativeDrift
        (kernel p q hp0 hp1 hq0 hq1) queuePotential (emptySafe) eps) ∧
      OutsideSafeNegativeDrift
        (kernel p q hp0 hp1 hq0 hq1) queuePotential (notFullSafe) q := by
  exact
    ⟨overloaded_emptySafe_noNegativeDrift p q hp0 hp1 hq0 hq1 hge eps,
      notFullSafe_negativeDrift p q hp0 hp1 hq0 hq1 hq⟩

end

end Persistence.Examples.QueueGeoGeo1Drift
