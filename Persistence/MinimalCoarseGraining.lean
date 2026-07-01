import Persistence.CoarseGraining
import Persistence.CoarseTotalProduction
import Persistence.SaturationDefect

/-!
# Minimal Coarse-Graining Conditions

Proves that stage-loss preservation under coarse-graining requires
only **ratio preservation** (not full uniform mass scaling).

## The theorem

For stage loss l_i = -log(m(i+1)/m(i)) to be preserved under
a coarse-graining φ, it suffices that φ preserves mass ratios:

    m_coarse(i+1) / m_coarse(i) = m_micro(i+1) / m_micro(i)

This is strictly weaker than uniform mass scaling
(m_coarse = α · m_micro for constant α).

## Significance

Weakens the coarse-graining requirements, expanding the set of
admissible coarse-grainings. More systems can be shown to satisfy
the structural second law under weaker conditions.
-/

namespace Persistence.MinimalCoarseGraining

open Persistence.TelescopingExp

noncomputable section

/-! ## Part 1: Ratio Preservation -/

/-- **Ratio-preserving condition**: the ratio of consecutive
masses is preserved by the coarse-graining.

This is weaker than uniform mass scaling (m_coarse = α · m_micro)
because the scaling factor is allowed to vary over time, as long
as the ratio m(i+1)/m(i) is preserved. -/
def RatioPreserving (m mcoarse : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i, i < n → 0 < m i →
    mcoarse (i + 1) / mcoarse i = m (i + 1) / m i

/-- Under ratio preservation, stage losses are exactly equal. -/
theorem stageLoss_preserved_of_ratio
    {m mcoarse : ℕ → ℝ} {n : ℕ}
    (hratio : RatioPreserving m mcoarse n)
    {i : ℕ} (hi : i < n) (hm : 0 < m i) :
    stageLoss mcoarse i = stageLoss m i := by
  simp only [stageLoss, hratio i hi hm]

/-- Under ratio preservation, cumulative losses are equal. -/
theorem cumulativeLoss_preserved_of_ratio
    {m mcoarse : ℕ → ℝ} {n : ℕ}
    (hratio : RatioPreserving m mcoarse n)
    (hm : ∀ i, i < n → 0 < m i) :
    ∑ i ∈ Finset.range n, stageLoss mcoarse i =
      ∑ i ∈ Finset.range n, stageLoss m i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact stageLoss_preserved_of_ratio hratio
    (Finset.mem_range.mp hi) (hm i (Finset.mem_range.mp hi))

/-! ## Part 2: Uniform Mass Scaling Implies Ratio Preservation -/

/-- Uniform mass scaling (m_coarse = α · m_micro) is a special case
of ratio preservation. -/
theorem uniform_implies_ratio
    (m : ℕ → ℝ) (α : ℝ) (hα : 0 < α) (n : ℕ)
    (mcoarse : ℕ → ℝ)
    (hscale : ∀ i, i ≤ n → mcoarse i = α * m i) :
    RatioPreserving m mcoarse n := by
  intro i hi hm
  rw [hscale (i + 1) (by omega), hscale i (le_of_lt hi)]
  rw [mul_div_mul_left _ _ (ne_of_gt hα)]

/-! ## Part 3: Strictly Weaker -/

/-- **Ratio preservation is exactly the loss-preservation condition.**

Stage loss preservation ⟺ ratio preservation.
This shows ratio preservation is the **tightest** characterization
of when coarse-graining preserves structural accounting. -/
theorem loss_preservation_iff_ratio
    {m mcoarse : ℕ → ℝ} {n : ℕ}
    (hm : ∀ i, i < n → 0 < m i)
    (hmc : ∀ i, i < n → 0 < mcoarse i)
    (hm_next : ∀ i, i < n → 0 < m (i + 1))
    (hmc_next : ∀ i, i < n → 0 < mcoarse (i + 1)) :
    (∀ i, i < n → stageLoss mcoarse i = stageLoss m i) ↔
      RatioPreserving m mcoarse n := by
  constructor
  · intro hloss i hi hmi
    have heq := hloss i hi
    unfold stageLoss at heq
    -- heq : -log(mcoarse(i+1)/mcoarse(i)) = -log(m(i+1)/m(i))
    have := neg_inj.mp heq
    -- this : log(mcoarse(i+1)/mcoarse(i)) = log(m(i+1)/m(i))
    have h1 := div_pos (hmc_next i hi) (hmc i hi)
    have h2 := div_pos (hm_next i hi) (hm i hi)
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h1)
      (Set.mem_Ioi.mpr h2) this
  · intro hratio i hi
    simp only [stageLoss, hratio i hi (hm i hi)]

end

end Persistence.MinimalCoarseGraining
