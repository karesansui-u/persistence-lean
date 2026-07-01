import Mathlib.Tactic
import Persistence.ConcentrationInterface
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Bernoulli CSP Template

This module factors out the Bernoulli algebra behind the non-flat SAT
clause-exposure chain.

The SAT specialization has bad-event probability `p = 1 / 8`; a `k`-SAT or
other one-sided CSP exposure model can reuse the same template with a different
`p`.  The file deliberately stays at the algebra / failure-profile level:
domain-specific path measures and MGF-product witnesses can instantiate it
after they prove their own prefix-product law.
-/

namespace Persistence.BernoulliCSPTemplate

open Persistence.ConcentrationInterface
open InformationTheory

noncomputable section

/-- Bernoulli relative entropy `D(q || p)` in closed form. -/
def bernoulliRelativeEntropy (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

/-- Moment-generating function of a Bernoulli bad-event indicator with
probability `p`. -/
def bernoulliBadMGF (p t : ℝ) : ℝ :=
  (1 - p) + p * Real.exp t

/-- Standard Bernoulli lower-tail exponential tilt. -/
def bernoulliLowerTailTilt (q p : ℝ) : ℝ :=
  Real.log ((q * (1 - p)) / (p * (1 - q)))

/-- A clipped lower-tail tilt, kept admissible for `t ≤ 0`. -/
def clippedLowerTailTilt (q p : ℝ) : ℝ :=
  min 0 (bernoulliLowerTailTilt q p)

theorem clippedLowerTailTilt_nonpos (q p : ℝ) :
    clippedLowerTailTilt q p ≤ 0 :=
  min_le_left 0 (bernoulliLowerTailTilt q p)

theorem clippedLowerTailTilt_eq_of_nonpos
    {q p : ℝ} (h : bernoulliLowerTailTilt q p ≤ 0) :
    clippedLowerTailTilt q p = bernoulliLowerTailTilt q p :=
  min_eq_right h

/-- At the lower-tail optimizer, the Bernoulli MGF has a closed form. -/
theorem bernoulliBadMGF_lowerTailTilt
    {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliBadMGF p (bernoulliLowerTailTilt q p) =
      (1 - p) / (1 - q) := by
  unfold bernoulliBadMGF bernoulliLowerTailTilt
  have hden_pos : 0 < p * (1 - q) :=
    mul_pos hp0 (sub_pos.mpr hq1)
  have harg_pos : 0 < (q * (1 - p)) / (p * (1 - q)) :=
    div_pos (mul_pos hq0 (sub_pos.mpr hp1)) hden_pos
  have hqsub : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  rw [Real.exp_log harg_pos]
  field_simp [hqsub]
  ring

/-- The optimized Bernoulli exponent is exactly the negative KL rate. -/
theorem bernoulliLowerTailTilt_log_mgf_identity
    {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    -q * bernoulliLowerTailTilt q p +
        Real.log (bernoulliBadMGF p (bernoulliLowerTailTilt q p)) =
      -bernoulliRelativeEntropy q p := by
  rw [bernoulliBadMGF_lowerTailTilt hq0 hq1 hp0 hp1]
  unfold bernoulliLowerTailTilt bernoulliRelativeEntropy
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hqsub_ne : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hpsub_ne : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  rw [Real.log_div (mul_ne_zero hq_ne hpsub_ne)
    (mul_ne_zero hp_ne hqsub_ne)]
  rw [Real.log_mul hq_ne hpsub_ne]
  rw [Real.log_mul hp_ne hqsub_ne]
  rw [Real.log_div hpsub_ne hqsub_ne]
  rw [Real.log_div hq_ne hp_ne]
  rw [Real.log_div hqsub_ne hpsub_ne]
  ring

/-- Bernoulli KL is nonnegative in the probability interior. -/
theorem bernoulliRelativeEntropy_nonneg
    {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ bernoulliRelativeEntropy q p := by
  unfold bernoulliRelativeEntropy
  have hx1 : 0 < q / p := div_pos hq0 hp0
  have hx2 : 0 < (1 - q) / (1 - p) :=
    div_pos (sub_pos.mpr hq1) (sub_pos.mpr hp1)
  have hlog1 := Real.one_sub_inv_le_log_of_pos hx1
  have hlog2 := Real.one_sub_inv_le_log_of_pos hx2
  have hmul1 : q * (1 - (q / p)⁻¹) ≤ q * Real.log (q / p) :=
    mul_le_mul_of_nonneg_left hlog1 hq0.le
  have hmul2 :
      (1 - q) * (1 - ((1 - q) / (1 - p))⁻¹) ≤
        (1 - q) * Real.log ((1 - q) / (1 - p)) :=
    mul_le_mul_of_nonneg_left hlog2 (sub_nonneg_of_le hq1.le)
  have hterm1 : q * (1 - (q / p)⁻¹) = q - p := by
    field_simp [hq0.ne', hp0.ne']
  have hterm2 :
      (1 - q) * (1 - ((1 - q) / (1 - p))⁻¹) = p - q := by
    have hq : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    have hp : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
    field_simp [hq, hp]
    ring_nf
  have hsum := add_le_add hmul1 hmul2
  linarith

/-- Bernoulli relative entropy as a weighted sum of `klFun` terms. -/
theorem bernoulliRelativeEntropy_eq_weighted_klFun
    {q p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliRelativeEntropy q p =
      p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p)) := by
  unfold bernoulliRelativeEntropy klFun
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have h1mp_ne : 1 - p ≠ 0 := by linarith [hp1.ne]
  field_simp [hp_ne, h1mp_ne]
  ring

/-- Bernoulli relative entropy is strictly positive away from equality in the
interior, in the `q < p` direction. -/
theorem bernoulliRelativeEntropy_pos_of_lt
    {q p : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hqp : q < p) :
    0 < bernoulliRelativeEntropy q p := by
  rw [bernoulliRelativeEntropy_eq_weighted_klFun hp0 hp1]
  have hq_div_nonneg : 0 ≤ q / p := div_nonneg hq0.le hp0.le
  have h1q_div_nonneg : 0 ≤ (1 - q) / (1 - p) := by
    exact div_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hp1.le)
  have hkl₁_nonneg : 0 ≤ klFun (q / p) := klFun_nonneg hq_div_nonneg
  have hratio₂_ne_one : ((1 - q) / (1 - p)) ≠ 1 := by
    intro h
    have h1mp_ne : 1 - p ≠ 0 := by linarith [hp1.ne]
    have hEq : 1 - q = 1 - p := (div_eq_one_iff_eq h1mp_ne).1 h
    linarith
  have hkl₂_pos : 0 < klFun ((1 - q) / (1 - p)) := by
    have hkl₂_nonneg : 0 ≤ klFun ((1 - q) / (1 - p)) := klFun_nonneg h1q_div_nonneg
    have hkl₂_ne_zero : klFun ((1 - q) / (1 - p)) ≠ 0 := by
      intro hzero
      have hEq := (klFun_eq_zero_iff h1q_div_nonneg).1 hzero
      exact hratio₂_ne_one hEq
    exact lt_of_le_of_ne hkl₂_nonneg (Ne.symm hkl₂_ne_zero)
  have hterm₁_nonneg : 0 ≤ p * klFun (q / p) := mul_nonneg hp0.le hkl₁_nonneg
  have hterm₂_pos : 0 < (1 - p) * klFun ((1 - q) / (1 - p)) :=
    mul_pos (sub_pos.mpr hp1) hkl₂_pos
  linarith

/-- Gap-form corollary used in threshold-gap pipelines:
`q ≤ p - η` with `η > 0` implies strict positivity of Bernoulli KL. -/
theorem bernoulliRelativeEntropy_pos_of_le_sub
    {q p η : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hη : 0 < η)
    (hgap : q ≤ p - η) :
    0 < bernoulliRelativeEntropy q p := by
  have hqp : q < p := by linarith
  exact bernoulliRelativeEntropy_pos_of_lt hq0 hq1 hp0 hp1 hqp

/-- Bernoulli relative entropy is strictly positive in the `q > p` direction
inside `(0,1)`. -/
theorem bernoulliRelativeEntropy_pos_of_gt
    {q p : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hpq : p < q) :
    0 < bernoulliRelativeEntropy q p := by
  rw [bernoulliRelativeEntropy_eq_weighted_klFun hp0 hp1]
  have hq_div_nonneg : 0 ≤ q / p := div_nonneg hq0.le hp0.le
  have h1q_div_nonneg : 0 ≤ (1 - q) / (1 - p) := by
    exact div_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hp1.le)
  have hratio₁_ne_one : (q / p) ≠ 1 := by
    intro h
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    have hEq : q = p := (div_eq_one_iff_eq hp_ne).1 h
    linarith
  have hkl₁_pos : 0 < klFun (q / p) := by
    have hkl₁_nonneg : 0 ≤ klFun (q / p) := klFun_nonneg hq_div_nonneg
    have hkl₁_ne_zero : klFun (q / p) ≠ 0 := by
      intro hzero
      have hEq := (klFun_eq_zero_iff hq_div_nonneg).1 hzero
      exact hratio₁_ne_one hEq
    exact lt_of_le_of_ne hkl₁_nonneg (Ne.symm hkl₁_ne_zero)
  have hkl₂_nonneg : 0 ≤ klFun ((1 - q) / (1 - p)) := klFun_nonneg h1q_div_nonneg
  have hterm₁_pos : 0 < p * klFun (q / p) := mul_pos hp0 hkl₁_pos
  have hterm₂_nonneg : 0 ≤ (1 - p) * klFun ((1 - q) / (1 - p)) :=
    mul_nonneg (sub_nonneg.mpr hp1.le) hkl₂_nonneg
  linarith

/-- Monotone-on-right helper for uniform KL lower bounds:
if `q ↦ D(q || p)` is monotone on `[p,1]`, then any `q ≥ p + γ` is bounded
below by the reference value at `p + γ`. -/
theorem bernoulliRelativeEntropy_lower_bound_of_ge_add_and_monotoneOn_right
    {q p γ : ℝ}
    (hγ : 0 < γ)
    (hpg1 : p + γ ≤ 1)
    (hq_ge : p + γ ≤ q) (hq1 : q ≤ 1)
    (hmono_right :
      MonotoneOn (fun x => bernoulliRelativeEntropy x p) (Set.Icc p 1)) :
    bernoulliRelativeEntropy (p + γ) p ≤ bernoulliRelativeEntropy q p := by
  have hleft_mem : p + γ ∈ Set.Icc p 1 := by constructor <;> linarith
  have hright_mem : q ∈ Set.Icc p 1 := by constructor <;> linarith
  exact hmono_right hleft_mem hright_mem hq_ge

/-- Readable specialization of right-side monotonicity on `[p,1]`. -/
theorem bernoulliRelativeEntropy_le_of_le_right_of_p_le
    {q₁ q₂ p : ℝ}
    (hpq₁ : p ≤ q₁) (hq₁q₂ : q₁ ≤ q₂) (hq₂ : q₂ ≤ 1)
    (hmono_right :
      MonotoneOn (fun x => bernoulliRelativeEntropy x p) (Set.Icc p 1)) :
    bernoulliRelativeEntropy q₁ p ≤ bernoulliRelativeEntropy q₂ p := by
  have hq₁_mem : q₁ ∈ Set.Icc p 1 := by constructor <;> linarith
  have hq₂_mem : q₂ ∈ Set.Icc p 1 := by constructor <;> linarith
  exact hmono_right hq₁_mem hq₂_mem hq₁q₂

/-- Derivative of `q ↦ D(q || p)` in the Bernoulli interior. -/
theorem hasDerivAt_bernoulliRelativeEntropy
    {q p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt
      (fun x => bernoulliRelativeEntropy x p)
      (Real.log (q / p) - Real.log ((1 - q) / (1 - p)))
      q := by
  have hfun :
      (fun x : ℝ => bernoulliRelativeEntropy x p) =
        (fun x : ℝ => p * klFun (x / p) + (1 - p) * klFun ((1 - x) / (1 - p))) := by
    funext x
    simpa using (bernoulliRelativeEntropy_eq_weighted_klFun (q := x) hp0 hp1)
  rw [hfun]
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have h1mp_ne : 1 - p ≠ 0 := by linarith [hp1.ne]
  have hq_div_ne_zero : q / p ≠ 0 := by
    exact div_ne_zero (ne_of_gt hq0) hp_ne
  have h1q_div_ne_zero : (1 - q) / (1 - p) ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hq1.ne') h1mp_ne
  have hdiv₁ : HasDerivAt (fun x : ℝ => x / p) (1 / p) q := by
    simpa [one_div] using (hasDerivAt_id q).div_const p
  have hdiv₂ : HasDerivAt (fun x : ℝ => (1 - x) / (1 - p)) (-(1 - p)⁻¹) q := by
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
      simpa using (hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)
    have hdiv₂_raw :
        HasDerivAt (fun x : ℝ => (1 - x) / (1 - p)) ((-1) / (1 - p)) q := by
      simpa using hsub.div_const (1 - p)
    simpa [div_eq_mul_inv] using hdiv₂_raw
  have hterm₁ :
      HasDerivAt
        (fun x : ℝ => p * klFun (x / p))
        (p * (Real.log (q / p) * (1 / p)))
        q := by
    exact ((hasDerivAt_klFun hq_div_ne_zero).comp q hdiv₁).const_mul p
  have hterm₂ :
      HasDerivAt
        (fun x : ℝ => (1 - p) * klFun ((1 - x) / (1 - p)))
        ((1 - p) * (Real.log ((1 - q) / (1 - p)) * (-(1 - p)⁻¹)))
        q := by
    exact
      ((hasDerivAt_klFun h1q_div_ne_zero).comp q hdiv₂).const_mul (1 - p)
  have hterm₁_simp :
      p * (Real.log (q / p) * (1 / p)) = Real.log (q / p) := by
    field_simp [hp_ne]
  have hterm₂_simp :
      (1 - p) * (Real.log ((1 - q) / (1 - p)) * (-(1 - p)⁻¹)) =
        -Real.log ((1 - q) / (1 - p)) := by
    field_simp [h1mp_ne]
  have hsum :
      HasDerivAt
        (fun x : ℝ => p * klFun (x / p) + (1 - p) * klFun ((1 - x) / (1 - p)))
        (p * (Real.log (q / p) * (1 / p)) +
          (1 - p) * (Real.log ((1 - q) / (1 - p)) * (-(1 - p)⁻¹)))
        q := hterm₁.add hterm₂
  have hderiv_simp :
      p * (Real.log (q / p) * (1 / p)) +
        (1 - p) * (Real.log ((1 - q) / (1 - p)) * (-(1 - p)⁻¹)) =
      Real.log (q / p) - Real.log ((1 - q) / (1 - p)) := by
    rw [hterm₁_simp, hterm₂_simp]
    ring
  exact hderiv_simp ▸ hsum

/-- Native right-side monotonicity of Bernoulli relative entropy:
for fixed `p ∈ (0,1)`, `q ↦ D(q || p)` is monotone on `[p,1]`. -/
theorem bernoulliRelativeEntropy_monotoneOn_right
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    MonotoneOn (fun q => bernoulliRelativeEntropy q p) (Set.Icc p 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc p 1)
  · have hEq :
        (fun q : ℝ => bernoulliRelativeEntropy q p) =
          fun q =>
            p * klFun (q / p) + (1 - p) * klFun ((1 - q) / (1 - p)) := by
        funext q
        simpa using (bernoulliRelativeEntropy_eq_weighted_klFun (q := q) hp0 hp1)
    rw [hEq]
    refine (continuous_const.mul (continuous_klFun.comp (continuous_id.div_const p))).add ?_ |>.continuousOn
    refine continuous_const.mul ?_
    refine continuous_klFun.comp ?_
    exact (continuous_const.sub continuous_id).div_const (1 - p)
  · intro q hq
    have hq' : q ∈ Set.Ioo p 1 := by simpa [interior_Icc] using hq
    have hq0 : 0 < q := lt_trans hp0 hq'.1
    have hq1 : q < 1 := hq'.2
    exact (hasDerivAt_bernoulliRelativeEntropy hp0 hp1 hq0 hq1).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo p 1 := by simpa [interior_Icc] using hq
    have hq0 : 0 < q := lt_trans hp0 hq'.1
    have hq1 : q < 1 := hq'.2
    have hderiv :
        deriv (fun x => bernoulliRelativeEntropy x p) q =
          Real.log (q / p) - Real.log ((1 - q) / (1 - p)) := by
      simpa using (hasDerivAt_bernoulliRelativeEntropy hp0 hp1 hq0 hq1).deriv
    rw [hderiv]
    have hratio1_ge_one : 1 ≤ q / p := by
      have hmul :
          p * p⁻¹ ≤ q * p⁻¹ :=
        mul_le_mul_of_nonneg_right hq'.1.le (inv_nonneg.mpr hp0.le)
      simpa [div_eq_mul_inv, hp0.ne'] using hmul
    have hlog1_nonneg : 0 ≤ Real.log (q / p) := by
      exact Real.log_nonneg hratio1_ge_one
    have hratio2_nonneg : 0 ≤ (1 - q) / (1 - p) := by
      exact div_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hp1.le)
    have hratio2_le_one : (1 - q) / (1 - p) ≤ 1 := by
      have h1mp_ne : 1 - p ≠ 0 := by linarith [hp1.ne]
      have hmul :
          (1 - q) * (1 - p)⁻¹ ≤ (1 - p) * (1 - p)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (sub_le_sub_left hq'.1.le 1)
          (inv_nonneg.mpr (sub_nonneg.mpr hp1.le))
      have hright : (1 - p) * (1 - p)⁻¹ = (1 : ℝ) := by
        field_simp [h1mp_ne]
      calc
        (1 - q) / (1 - p) = (1 - q) * (1 - p)⁻¹ := by simp [div_eq_mul_inv]
        _ ≤ (1 - p) * (1 - p)⁻¹ := hmul
        _ = 1 := hright
    have hlog2_nonpos : Real.log ((1 - q) / (1 - p)) ≤ 0 := by
      exact Real.log_nonpos hratio2_nonneg hratio2_le_one
    linarith

/-- Witness-free right-gap lower bound:
`q ≥ p + γ` implies `D(p + γ || p) ≤ D(q || p)` for `p ∈ (0,1)`. -/
theorem bernoulliRelativeEntropy_lower_bound_of_ge_add
    {q p γ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hγ : 0 < γ)
    (hpg1 : p + γ ≤ 1)
    (hq_ge : p + γ ≤ q) (hq1 : q ≤ 1) :
    bernoulliRelativeEntropy (p + γ) p ≤ bernoulliRelativeEntropy q p := by
  exact
    bernoulliRelativeEntropy_lower_bound_of_ge_add_and_monotoneOn_right
      hγ hpg1 hq_ge hq1 (bernoulliRelativeEntropy_monotoneOn_right hp0 hp1)

/-- Complement symmetry of Bernoulli KL:
`D(q || p) = D(1 - q || 1 - p)`. -/
theorem bernoulliRelativeEntropy_complement
    (q p : ℝ) :
    bernoulliRelativeEntropy q p =
      bernoulliRelativeEntropy (1 - q) (1 - p) := by
  unfold bernoulliRelativeEntropy
  ring_nf

/-- Native left-side antitonicity of Bernoulli KL:
for fixed `p ∈ (0,1)`, `q ↦ D(q || p)` is antitone on `[0,p]`. -/
theorem bernoulliRelativeEntropy_antitoneOn_left
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    AntitoneOn (fun q => bernoulliRelativeEntropy q p) (Set.Icc 0 p) := by
  intro q₁ hq₁ q₂ hq₂ hq₁₂
  have hp0' : 0 < 1 - p := by linarith
  have hp1' : 1 - p < 1 := by linarith
  have hmono_right :
      MonotoneOn (fun x => bernoulliRelativeEntropy x (1 - p)) (Set.Icc (1 - p) 1) :=
    bernoulliRelativeEntropy_monotoneOn_right hp0' hp1'
  have hq₂c_mem : (1 - q₂) ∈ Set.Icc (1 - p) 1 := by
    constructor
    · linarith [hq₂.2]
    · linarith [hq₂.1]
  have hq₁c_mem : (1 - q₁) ∈ Set.Icc (1 - p) 1 := by
    constructor
    · linarith [hq₁.2]
    · linarith [hq₁.1]
  have hcomp_le : (1 - q₂) ≤ (1 - q₁) := by linarith
  have hmono :=
    hmono_right hq₂c_mem hq₁c_mem hcomp_le
  calc
    bernoulliRelativeEntropy q₂ p =
        bernoulliRelativeEntropy (1 - q₂) (1 - p) :=
          bernoulliRelativeEntropy_complement q₂ p
    _ ≤ bernoulliRelativeEntropy (1 - q₁) (1 - p) := hmono
    _ = bernoulliRelativeEntropy q₁ p :=
          (bernoulliRelativeEntropy_complement q₁ p).symm

/-- The lower-tail optimizer is admissible whenever the target proportion is at
or below the Bernoulli mean. -/
theorem bernoulliLowerTailTilt_nonpos_of_le
    {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hqp : q ≤ p) :
    bernoulliLowerTailTilt q p ≤ 0 := by
  unfold bernoulliLowerTailTilt
  apply Real.log_nonpos
  · exact
      div_nonneg
        (mul_nonneg hq0.le (sub_nonneg_of_le hp1.le))
        (mul_nonneg hp0.le (sub_nonneg_of_le hq1.le))
  · have hden_pos : 0 < p * (1 - q) :=
      mul_pos hp0 (sub_pos.mpr hq1)
    rw [div_le_iff₀ hden_pos]
    nlinarith

/-- The closed optimized MGF expression equals the exponential KL profile. -/
theorem optimizedClosedMGFReal_eq_exp_neg_bernoulliRelativeEntropy
    (n : ℕ) {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    Real.exp (-bernoulliLowerTailTilt q p * ((n : ℝ) * q)) *
        bernoulliBadMGF p (bernoulliLowerTailTilt q p) ^ n =
      Real.exp (-((n : ℝ) * bernoulliRelativeEntropy q p)) := by
  let M := bernoulliBadMGF p (bernoulliLowerTailTilt q p)
  have hM_eq : M = (1 - p) / (1 - q) :=
    bernoulliBadMGF_lowerTailTilt hq0 hq1 hp0 hp1
  have hM_pos : 0 < M := by
    rw [hM_eq]
    exact div_pos (sub_pos.mpr hp1) (sub_pos.mpr hq1)
  have hid :=
    bernoulliLowerTailTilt_log_mgf_identity hq0 hq1 hp0 hp1
  calc
    Real.exp (-bernoulliLowerTailTilt q p * ((n : ℝ) * q)) *
        bernoulliBadMGF p (bernoulliLowerTailTilt q p) ^ n
        = Real.exp (-bernoulliLowerTailTilt q p * ((n : ℝ) * q)) *
            M ^ n := by rfl
    _ = Real.exp (-bernoulliLowerTailTilt q p * ((n : ℝ) * q)) *
          Real.exp ((n : ℝ) * Real.log M) := by
          rw [← Real.exp_log (pow_pos hM_pos n), Real.log_pow]
    _ = Real.exp
          (-bernoulliLowerTailTilt q p * ((n : ℝ) * q) +
            (n : ℝ) * Real.log M) := by
          rw [← Real.exp_add]
    _ = Real.exp
          ((n : ℝ) *
            (-q * bernoulliLowerTailTilt q p + Real.log M)) := by
          congr 1
          ring
    _ = Real.exp ((n : ℝ) * (-bernoulliRelativeEntropy q p)) := by
          rw [hid]
    _ = Real.exp (-((n : ℝ) * bernoulliRelativeEntropy q p)) := by
          congr 1
          ring

/-- Parameters for a one-sided Bernoulli CSP exposure model.  The bad event
probability is the only probabilistic parameter at this algebraic layer. -/
structure Parameters where
  badProb : ℝ
  badProb_pos : 0 < badProb
  badProb_lt_one : badProb < 1

namespace Parameters

/-- Mean information-production drift for one Bernoulli CSP exposure. -/
def drift (P : Parameters) : ℝ :=
  Real.log (1 / (1 - P.badProb))

theorem drift_pos (P : Parameters) :
    0 < P.drift := by
  unfold drift
  have hden_pos : 0 < 1 - P.badProb := sub_pos.mpr P.badProb_lt_one
  have hgt : 1 < 1 / (1 - P.badProb) := by
    rw [lt_div_iff₀ hden_pos]
    linarith [P.badProb_pos]
  exact Real.log_pos hgt

theorem drift_nonneg (P : Parameters) :
    0 ≤ P.drift :=
  (P.drift_pos).le

/-- One-sided bad-event emission scale chosen so that the mean increment is
exactly `drift`. -/
def badEmissionScale (P : Parameters) : ℝ :=
  P.drift / P.badProb

theorem badEmissionScale_pos (P : Parameters) :
    0 < P.badEmissionScale := by
  exact div_pos P.drift_pos P.badProb_pos

theorem expectedBadEmission_eq_drift (P : Parameters) :
    P.badProb * P.badEmissionScale = P.drift := by
  unfold badEmissionScale
  field_simp [P.badProb_pos.ne']

/-- Count threshold induced by a lower-deviation budget `r`. -/
def countThreshold (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  ((n : ℝ) * P.drift - r) / P.badEmissionScale

/-- Normalized count threshold ratio. -/
def thresholdRatio (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  if n = 0 then 0 else P.countThreshold n r / (n : ℝ)

theorem countThreshold_eq_nat_mul_thresholdRatio_of_ne_zero
    (P : Parameters) (n : ℕ) (r : ℝ) (hn : n ≠ 0) :
    P.countThreshold n r = (n : ℝ) * P.thresholdRatio n r := by
  rw [thresholdRatio, if_neg hn]
  have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnpos]

theorem thresholdRatio_pos_of_nonneg_of_lt_activeDrift
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    0 < P.thresholdRatio n r := by
  by_cases hn : n = 0
  · subst n
    simp at hlt
    linarith
  · have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    have hnum : 0 < (n : ℝ) * P.drift - r := by
      linarith
    rw [thresholdRatio, if_neg hn]
    unfold countThreshold
    exact div_pos (div_pos hnum P.badEmissionScale_pos) hnpos

theorem thresholdRatio_le_badProb_of_nonneg
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) :
    P.thresholdRatio n r ≤ P.badProb := by
  by_cases hn : n = 0
  · subst n
    simp [thresholdRatio, P.badProb_pos.le]
  · have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos_nat
    rw [thresholdRatio, if_neg hn]
    rw [div_le_iff₀ hnpos]
    unfold countThreshold
    rw [div_le_iff₀ P.badEmissionScale_pos]
    calc
      (n : ℝ) * P.drift - r ≤ (n : ℝ) * P.drift := by linarith
      _ = (n : ℝ) * (P.badProb * P.badEmissionScale) := by
            rw [P.expectedBadEmission_eq_drift]
      _ = (n : ℝ) * P.badProb * P.badEmissionScale := by ring
      _ = P.badProb * (n : ℝ) * P.badEmissionScale := by ring

theorem thresholdRatio_lt_one_of_nonneg
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) :
    P.thresholdRatio n r < 1 := by
  exact lt_of_le_of_lt
    (P.thresholdRatio_le_badProb_of_nonneg hr)
    P.badProb_lt_one

/-- In the active lower-tail interior, the clipped tilt is the usual Bernoulli
tilt. -/
theorem clippedTilt_eq_lowerTailTilt_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    clippedLowerTailTilt (P.thresholdRatio n r) P.badProb =
      bernoulliLowerTailTilt (P.thresholdRatio n r) P.badProb := by
  have hq0 := P.thresholdRatio_pos_of_nonneg_of_lt_activeDrift hr hlt
  have hq1 := P.thresholdRatio_lt_one_of_nonneg (n := n) (r := r) hr
  have hqp := P.thresholdRatio_le_badProb_of_nonneg (n := n) (r := r) hr
  exact clippedLowerTailTilt_eq_of_nonpos
    (bernoulliLowerTailTilt_nonpos_of_le
      hq0 hq1 P.badProb_pos P.badProb_lt_one hqp)

/-- Count-threshold-dependent optimized lower-tail tilt. -/
def optimizingTilt (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  clippedLowerTailTilt (P.thresholdRatio n r) P.badProb

theorem optimizingTilt_nonpos (P : Parameters) (n : ℕ) (r : ℝ) :
    P.optimizingTilt n r ≤ 0 :=
  clippedLowerTailTilt_nonpos (P.thresholdRatio n r) P.badProb

theorem optimizingTilt_eq_lowerTailTilt_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    P.optimizingTilt n r =
      bernoulliLowerTailTilt (P.thresholdRatio n r) P.badProb :=
  P.clippedTilt_eq_lowerTailTilt_of_interior hr hlt

/-- Closed MGF profile after substituting the threshold-dependent optimized
tilt. -/
def optimizedClosedMGFReal (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  Real.exp (-(P.optimizingTilt n r) * P.countThreshold n r) *
    bernoulliBadMGF P.badProb (P.optimizingTilt n r) ^ n

/-- Chernoff / KL count rate for a Bernoulli CSP prefix. -/
def chernoffRate (P : Parameters) (n : ℕ) (r : ℝ) : ℝ :=
  max 0 <|
    if n = 0 then
      0
    else
      (n : ℝ) *
        bernoulliRelativeEntropy (P.thresholdRatio n r) P.badProb

/-- Exponential Chernoff / KL failure profile. -/
def chernoffFailureBound (P : Parameters) (n : ℕ) (r : ℝ) : ENNReal :=
  largeDeviationFailureBound P.chernoffRate n r

theorem chernoffRate_eq_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    P.chernoffRate n r =
      (n : ℝ) *
        bernoulliRelativeEntropy (P.thresholdRatio n r) P.badProb := by
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    simp at hlt
    linarith
  have hq0 := P.thresholdRatio_pos_of_nonneg_of_lt_activeDrift hr hlt
  have hq1 := P.thresholdRatio_lt_one_of_nonneg (n := n) (r := r) hr
  have hD : 0 ≤ bernoulliRelativeEntropy (P.thresholdRatio n r) P.badProb :=
    bernoulliRelativeEntropy_nonneg hq0 hq1 P.badProb_pos P.badProb_lt_one
  unfold chernoffRate
  rw [if_neg hn]
  exact max_eq_right (mul_nonneg (Nat.cast_nonneg n) hD)

/-- On the genuine lower-tail interior, the optimized closed-MGF expression is
exactly the exponential KL profile. -/
theorem optimizedClosedMGFReal_eq_exp_neg_chernoffRate_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    P.optimizedClosedMGFReal n r =
      Real.exp (-(P.chernoffRate n r)) := by
  have hn : n ≠ 0 := by
    intro hn0
    subst n
    simp at hlt
    linarith
  let q := P.thresholdRatio n r
  have hq0 : 0 < q :=
    P.thresholdRatio_pos_of_nonneg_of_lt_activeDrift hr hlt
  have hq1 : q < 1 :=
    P.thresholdRatio_lt_one_of_nonneg hr
  have ht : P.optimizingTilt n r = bernoulliLowerTailTilt q P.badProb := by
    exact P.optimizingTilt_eq_lowerTailTilt_of_interior hr hlt
  have hthreshold : P.countThreshold n r = (n : ℝ) * q := by
    unfold q
    exact P.countThreshold_eq_nat_mul_thresholdRatio_of_ne_zero n r hn
  have hrate :
      P.chernoffRate n r =
        (n : ℝ) * bernoulliRelativeEntropy q P.badProb := by
    unfold q
    exact P.chernoffRate_eq_of_interior hr hlt
  unfold optimizedClosedMGFReal
  rw [ht, hthreshold, hrate]
  exact
    optimizedClosedMGFReal_eq_exp_neg_bernoulliRelativeEntropy
      n hq0 hq1 P.badProb_pos P.badProb_lt_one

/-- ENNReal form of the interior optimized-MGF / KL identity. -/
theorem optimizedClosedMGFReal_failure_eq_chernoffFailureBound_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    ENNReal.ofReal (P.optimizedClosedMGFReal n r) =
      P.chernoffFailureBound n r := by
  unfold chernoffFailureBound largeDeviationFailureBound
  rw [P.optimizedClosedMGFReal_eq_exp_neg_chernoffRate_of_interior hr hlt]

end Parameters

/-- The Bernoulli parameter corresponding to random 3-SAT clause exposure. -/
def random3SATParameters : Parameters where
  badProb := (1 / 8 : ℝ)
  badProb_pos := by norm_num
  badProb_lt_one := by norm_num

theorem random3SATParameters_drift_eq_log :
    random3SATParameters.drift = Real.log (8 / 7 : ℝ) := by
  unfold random3SATParameters Parameters.drift
  norm_num

theorem random3SATParameters_badEmissionScale_eq :
    random3SATParameters.badEmissionScale =
      8 * Real.log (8 / 7 : ℝ) := by
  unfold random3SATParameters Parameters.badEmissionScale
    Parameters.drift
  norm_num
  ring

end

end Persistence.BernoulliCSPTemplate
