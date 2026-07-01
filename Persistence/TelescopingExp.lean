import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Telescoping exponential identity for Paper 2 §3

This module formalizes the A1–A2-only algebraic core used in Paper 2:
for a positive sequence `m₀, m₁, ..., mₙ`, if the stage losses are

  lᵢ = -log (m_{i+1} / m_i),

then the cumulative loss telescopes to

  mₙ = m₀ * exp ( - Σᵢ lᵢ ).

Unlike `AxiomsToExp.lean`, this file does not assume probabilistic
independence or a product model over constraints. It is a purely
algebraic consequence of ratio-defined stage loss.
-/

open scoped BigOperators
open Finset Real

namespace Persistence.TelescopingExp

noncomputable section

/-- Stage loss from step `i` to `i+1`. -/
def stageLoss (m : ℕ → ℝ) (i : ℕ) : ℝ :=
  -Real.log (m (i + 1) / m i)

/-- Finite products of successive ratios telescope. -/
theorem prod_ratios_telescope (m : ℕ → ℝ) (n : ℕ)
    (hm : ∀ i ≤ n, m i ≠ 0) :
    (∏ i ∈ Finset.range n, m (i + 1) / m i) = m n / m 0 := by
  induction n with
  | zero =>
      simp [hm 0 (Nat.le_refl 0)]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      rw [ih (fun i hi => hm i (Nat.le_trans hi (Nat.le_succ n)))]
      have h0 : m 0 ≠ 0 := hm 0 (Nat.zero_le n.succ)
      have hn : m n ≠ 0 := hm n (Nat.le_succ n)
      field_simp [h0, hn]

/-- The exponential of the cumulative negative stage loss equals the end/start ratio. -/
theorem exp_neg_sum_stageLoss_eq_ratio (m : ℕ → ℝ) (n : ℕ)
    (hm : ∀ i ≤ n, 0 < m i) :
    Real.exp (-∑ i ∈ Finset.range n, stageLoss m i) = m n / m 0 := by
  unfold stageLoss
  have hsum :
      -(∑ i ∈ Finset.range n, -Real.log (m (i + 1) / m i)) =
        ∑ i ∈ Finset.range n, Real.log (m (i + 1) / m i) := by
    simp
  rw [hsum, Real.exp_sum]
  have hprod :
      (∏ x ∈ Finset.range n, Real.exp (Real.log (m (x + 1) / m x))) =
        (∏ x ∈ Finset.range n, m (x + 1) / m x) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Real.exp_log]
    exact div_pos
      (hm (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
      (hm i (Nat.le_of_lt (Finset.mem_range.mp hi)))
  rw [hprod, prod_ratios_telescope m n (fun i hi => ne_of_gt (hm i hi))]

/-- Paper 2 §3: the A1–A2-only telescoping exponential identity. -/
theorem measure_eq_initial_mul_exp_neg_cumulative_loss (m : ℕ → ℝ) (n : ℕ)
    (hm : ∀ i ≤ n, 0 < m i) :
    m n = m 0 * Real.exp (-∑ i ∈ Finset.range n, stageLoss m i) := by
  have h0 : m 0 ≠ 0 := ne_of_gt (hm 0 (Nat.zero_le n))
  calc
    m n = m 0 * (m n / m 0) := by
      field_simp [h0]
    _ = m 0 * Real.exp (-∑ i ∈ Finset.range n, stageLoss m i) := by
      rw [exp_neg_sum_stageLoss_eq_ratio m n hm]

end

end Persistence.TelescopingExp
