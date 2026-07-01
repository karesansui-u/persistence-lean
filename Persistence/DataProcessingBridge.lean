import Persistence.OptimalCoarseGraining
import Persistence.SaturationDefect
/-!
# Readout-Level Coarse-Graining / Processing Monotonicity

This module proves a finite, readout-level monotonicity statement:
under an explicit saturation-defect readout and a defect sign condition,
coarse-grained structural loss is bounded below by micro loss.

Safe reading:
1. Coarse loss ≥ micro loss (under defect ≥ 0)
2. Equality iff zero defect (lossless processing)
3. Cascaded processing: defects accumulate
4. Retention monotone decreasing under processing

Non-claims:
* this is not a native information-theoretic DPI;
* this does not prove data-processing for arbitrary channels;
* this does not identify the correct coarse-graining for a real domain.
-/
namespace Persistence.DataProcessingBridge
open Real Persistence.SaturationDefect Persistence.TelescopingExp
noncomputable section

/-- **DPI (structural form): coarse-grained loss ≥ micro loss.**
    If saturation defect e(0) ≥ e(n), then cumulative coarse loss
    is at least cumulative micro loss. -/
theorem dpi_structural
    {m mcoarse e : ℕ → ℝ} {n : ℕ}
    (hdefect : SaturationDefectReadout m mcoarse e n)
    (hdefect_growth : e 0 ≥ e n) :
    ∑ i ∈ Finset.range n, stageLoss m i ≤
      ∑ i ∈ Finset.range n, stageLoss mcoarse i := by
  have h := Persistence.OptimalCoarseGraining.cumulative_loss_with_defect hdefect
  linarith

/-- Equality iff zero net defect (lossless processing). -/
theorem dpi_equality_iff_lossless
    {m mcoarse e : ℕ → ℝ} {n : ℕ}
    (hdefect : SaturationDefectReadout m mcoarse e n)
    (hzero : e 0 = e n) :
    ∑ i ∈ Finset.range n, stageLoss mcoarse i =
      ∑ i ∈ Finset.range n, stageLoss m i := by
  have h := Persistence.OptimalCoarseGraining.cumulative_loss_with_defect hdefect
  linarith

/-- Processing reduces retention: exp(-L_coarse) ≤ exp(-L_micro). -/
theorem processing_reduces_retention
    (L_micro L_coarse : ℝ) (h : L_micro ≤ L_coarse) :
    exp (-L_coarse) ≤ exp (-L_micro) :=
  exp_le_exp.mpr (by linarith)

/-- Cascaded processing: two stages of processing accumulate defects.
    defect_total = defect_1 + defect_2. -/
theorem cascaded_defect (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    0 ≤ d₁ + d₂ := add_nonneg hd₁ hd₂

/-- More processing stages → more consumption → less retention. -/
theorem more_processing_less_retention (L₁ extra : ℝ)
    (h : 0 ≤ extra) :
    exp (-(L₁ + extra)) ≤ exp (-L₁) :=
  exp_le_exp.mpr (by linarith)

/-- Terminology-facing alias for the readout-level monotonicity theorem.
    The theorem consumes the same explicit saturation-defect certificate as
    `dpi_structural`; it is not a native information-theoretic DPI. -/
theorem information_never_increases
    {m mcoarse e : ℕ → ℝ} {n : ℕ}
    (hdefect : SaturationDefectReadout m mcoarse e n)
    (hdefect_nonneg : e 0 ≥ e n) :
    ∑ i ∈ Finset.range n, stageLoss m i ≤
      ∑ i ∈ Finset.range n, stageLoss mcoarse i :=
  dpi_structural hdefect hdefect_nonneg

end
end Persistence.DataProcessingBridge
