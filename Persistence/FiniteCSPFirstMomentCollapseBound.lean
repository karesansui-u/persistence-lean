import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith

/-!
# Finite CSP First-Moment Collapse Bound

This module is a small theorem-side anchor for the specification-fixed layer.
It does not prove a sharp threshold and it does not model solver dynamics.

It proves the finite first-moment step used in the prose supplement:

* a nonempty feasible set means the feasible-count random variable `Z` is at
  least `1`;
* therefore the finite probability of nonemptiness is bounded by `E[Z]`;
* if the exposure model gives `E[Z] <= A * exp (-L)`, then the same expression
  bounds the nonemptiness probability;
* if additionally `L >= log A + lambda`, the nonemptiness probability is at
  most `exp (-lambda)`.

Thus the loss coordinate is not used as a post-hoc realized count ratio here:
the theorem assumes a pre-fixed first-moment loss from the exposure model and
connects it to the independently defined endpoint `Z > 0`.
-/

open scoped BigOperators

namespace Persistence.FiniteCSPFirstMomentCollapseBound

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- Finite PMF probability of an event, written as a real-valued finite sum. -/
def eventProb (P : PMF Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  ∑ ω, (P ω).toReal * if E ω then (1 : ℝ) else 0

/-- Finite PMF expectation of a natural-valued feasible-count random variable. -/
def countExpectation (P : PMF Ω) (Z : Ω → ℕ) : ℝ :=
  ∑ ω, (P ω).toReal * (Z ω : ℝ)

/-- The operational endpoint: at least one feasible candidate remains. -/
def nonemptyEvent (Z : Ω → ℕ) (ω : Ω) : Prop :=
  0 < Z ω

instance instDecidablePredNonemptyEvent (Z : Ω → ℕ) :
    DecidablePred (nonemptyEvent Z) := by
  intro ω
  unfold nonemptyEvent
  infer_instance

/-- Markov/first-moment core: the probability that a natural-valued count is
positive is bounded by its expectation. -/
theorem eventProb_nonempty_le_countExpectation
    (P : PMF Ω) (Z : Ω → ℕ) :
    eventProb P (nonemptyEvent Z) ≤ countExpectation P Z := by
  classical
  unfold eventProb countExpectation nonemptyEvent
  refine Finset.sum_le_sum ?_
  intro ω _
  by_cases h : 0 < Z ω
  · have hz : (1 : ℝ) ≤ (Z ω : ℝ) := by
      exact_mod_cast h
    simpa [h] using mul_le_mul_of_nonneg_left hz (ENNReal.toReal_nonneg)
  · have hzero : Z ω = 0 := Nat.eq_zero_of_not_pos h
    simp [hzero]

/-- If the exposure model gives a pre-fixed first-moment bound
`E[Z] <= A * exp (-L)`, then nonemptiness has the same one-sided bound. -/
theorem nonemptyProbability_le_firstMomentBound
    (P : PMF Ω) (Z : Ω → ℕ) {A L : ℝ}
    (hFM : countExpectation P Z ≤ A * Real.exp (-L)) :
    eventProb P (nonemptyEvent Z) ≤ A * Real.exp (-L) :=
  le_trans (eventProb_nonempty_le_countExpectation P Z) hFM

/-- Log-margin algebra: if `L >= log A + lambda`, then
`A * exp (-L) <= exp (-lambda)`. -/
theorem prefactor_exp_loss_le_exp_neg_margin
    {A L lambda : ℝ}
    (hA : 0 < A) (hmargin : Real.log A + lambda ≤ L) :
    A * Real.exp (-L) ≤ Real.exp (-lambda) := by
  calc
    A * Real.exp (-L)
        = Real.exp (Real.log A) * Real.exp (-L) := by
            rw [Real.exp_log hA]
    _ = Real.exp (Real.log A + (-L)) := by
            rw [← Real.exp_add]
    _ ≤ Real.exp (-lambda) := by
            exact Real.exp_le_exp.mpr (by linarith)

/-- First-moment collapse bound with an explicit logarithmic margin. -/
theorem nonemptyProbability_le_exp_neg_margin
    (P : PMF Ω) (Z : Ω → ℕ) {A L lambda : ℝ}
    (hA : 0 < A)
    (hFM : countExpectation P Z ≤ A * Real.exp (-L))
    (hmargin : Real.log A + lambda ≤ L) :
    eventProb P (nonemptyEvent Z) ≤ Real.exp (-lambda) :=
  le_trans (nonemptyProbability_le_firstMomentBound P Z hFM)
    (prefactor_exp_loss_le_exp_neg_margin hA hmargin)

end

end Persistence.FiniteCSPFirstMomentCollapseBound
