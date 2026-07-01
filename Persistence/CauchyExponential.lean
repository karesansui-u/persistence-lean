/-
Persistence Model - Cauchy Functional Equation Characterization
Cauchy関数方程式の特性定理

Theorem: If f : ℝ → ℝ satisfies
  (1) f(x + y) = f(x) · f(y)     [multiplicativity]
  (2) f(0) = 1                    [normalization]
  (3) f is continuous             [regularity]
  (4) f is strictly decreasing    [survival interpretation]
then ∃ c > 0, ∀ x, f(x) = exp(-c · x).

This characterizes the exponential decay form e^{-cδ} used in the survival equation,
and the sensitivity exponent c from Paper 2.

Paper 2 results:
  CDCL:    c ≈ 0.24 (structure-sensitive)
  WalkSAT: c ≈ 0.21 (structure-blind)
  Random:  c = 1.0  (mathematical identity, theoretical upper bound)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Rat

namespace Persistence

/-! ## Forward Direction: exp(-cx) satisfies all four properties -/

/-- exp(-cx) satisfies the multiplicative property over addition -/
theorem exp_neg_mul_add (c x y : ℝ) :
    Real.exp (-c * (x + y)) = Real.exp (-c * x) * Real.exp (-c * y) := by
  have : -c * (x + y) = -c * x + -c * y := by ring
  rw [this, Real.exp_add]

/-- exp(-c · 0) = 1 -/
theorem exp_neg_mul_zero (c : ℝ) : Real.exp (-c * 0) = 1 := by
  simp

/-- exp(-cx) is strictly anti-monotone when c > 0 -/
theorem exp_neg_mul_strictAnti (c : ℝ) (hc : 0 < c) :
    StrictAnti (fun x => Real.exp (-c * x)) := by
  intro x y hxy
  exact Real.exp_strictMono (by nlinarith)

/-- exp(-cx) is continuous -/
theorem exp_neg_mul_continuous (c : ℝ) :
    Continuous (fun x => Real.exp (-c * x)) := by
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id')

/-! ## Backward Direction: Uniqueness of exponential form -/

/-- A multiplicative function is nonnegative: f(x) = f(x/2)² ≥ 0 -/
lemma cauchy_mul_nonneg (f : ℝ → ℝ) (hf_mul : ∀ x y, f (x + y) = f x * f y) :
    ∀ x, 0 ≤ f x := by
  intro x
  have h : f x = f (x / 2) * f (x / 2) := by
    have := hf_mul (x / 2) (x / 2)
    rw [add_halves] at this
    exact this
  rw [h]
  exact mul_self_nonneg _

/-- A multiplicative function with f(0) = 1 is strictly positive -/
lemma cauchy_mul_pos (f : ℝ → ℝ) (hf_mul : ∀ x y, f (x + y) = f x * f y)
    (hf_zero : f 0 = 1) : ∀ x, 0 < f x := by
  intro x
  have hnn := cauchy_mul_nonneg f hf_mul
  by_contra h
  push_neg at h
  have hfx : f x = 0 := le_antisymm h (hnn x)
  have key : f 0 = f x * f (-x) := by
    have := hf_mul x (-x)
    rw [add_neg_cancel] at this
    exact this
  rw [hf_zero, hfx, zero_mul] at key
  exact one_ne_zero key

/-- log of a positive multiplicative function is additive -/
lemma cauchy_log_additive (f : ℝ → ℝ) (hf_mul : ∀ x y, f (x + y) = f x * f y)
    (hf_zero : f 0 = 1) :
    ∀ x y, Real.log (f (x + y)) = Real.log (f x) + Real.log (f y) := by
  intro x y
  rw [hf_mul]
  exact Real.log_mul (ne_of_gt (cauchy_mul_pos f hf_mul hf_zero x))
                      (ne_of_gt (cauchy_mul_pos f hf_mul hf_zero y))

/-- log(f(0)) = 0 -/
lemma cauchy_log_zero (f : ℝ → ℝ) (hf_zero : f 0 = 1) :
    Real.log (f 0) = 0 := by
  rw [hf_zero, Real.log_one]

/-- Additive function maps 0 to 0 -/
lemma additive_zero (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    g 0 = 0 := by
  have h := hg 0 0
  simp only [add_zero] at h
  linarith

/-- Additive function satisfies g(-x) = -g(x) -/
lemma additive_neg (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    ∀ x, g (-x) = -g x := by
  intro x
  have h0 := additive_zero g hg
  have := hg x (-x)
  rw [add_neg_cancel] at this
  linarith

/-- Additive function on ℕ: g(↑n) = ↑n * g(1) -/
lemma additive_natCast (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    ∀ n : ℕ, g (↑n) = ↑n * g 1 := by
  intro n
  induction n with
  | zero => simp [additive_zero g hg]
  | succ k ih =>
    have : (↑(k + 1) : ℝ) = ↑k + 1 := by push_cast; ring
    rw [this, hg, ih]
    ring

/-- Additive function on ℤ: g(↑n) = ↑n * g(1) -/
lemma additive_intCast (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    ∀ n : ℤ, g (↑n) = ↑n * g 1 := by
  intro n
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact additive_natCast g hg k
  | negSucc k =>
    have : (↑(Int.negSucc k) : ℝ) = -(↑(k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, additive_neg g hg, additive_natCast g hg]
    push_cast; ring

/-- Additive function satisfies g(n * x) = n * g(x) for ℕ -/
lemma additive_natMul (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    ∀ (n : ℕ) (x : ℝ), g (↑n * x) = ↑n * g x := by
  intro n
  induction n with
  | zero => intro x; simp [additive_zero g hg]
  | succ k ih =>
    intro x
    have : (↑(k + 1) : ℝ) * x = ↑k * x + x := by push_cast; ring
    rw [this, hg, ih]
    push_cast; ring

/-- Additive function on ℚ: g(↑q) = ↑q * g(1) -/
lemma additive_ratCast (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y) :
    ∀ q : ℚ, g (↑q) = ↑q * g 1 := by
  intro q
  have hden_pos : (0 : ℝ) < ↑q.den := Nat.cast_pos.mpr q.pos
  have hden_ne : (q.den : ℝ) ≠ 0 := ne_of_gt hden_pos
  have h1 : g (↑q.den * ↑q) = ↑q.den * g (↑q) :=
    additive_natMul g hg q.den (↑q)
  have hq_def : (↑q : ℝ) = ↑q.num / ↑q.den := Rat.cast_def q
  have h2 : (↑q.den : ℝ) * ↑q = ↑q.num := by
    rw [hq_def]; field_simp
  rw [h2] at h1
  rw [additive_intCast g hg] at h1
  -- Now h1 : ↑q.num * g 1 = ↑q.den * g ↑q
  have : g (↑q) = (↑q.num / ↑q.den) * g 1 := by
    field_simp at h1 ⊢; linarith
  rw [this, hq_def]

/-- A continuous additive function ℝ → ℝ is linear: g(x) = g(1) · x.
    This is the core of the Cauchy functional equation characterization.
    Proof: g agrees with the linear function on ℚ (dense in ℝ),
    and two continuous functions agreeing on a dense set are equal. -/
theorem continuous_additive_is_linear (g : ℝ → ℝ) (hg : ∀ x y, g (x + y) = g x + g y)
    (hg_cont : Continuous g) :
    ∀ x, g x = g 1 * x := by
  -- Define the linear function h(x) = g(1) * x
  set h : ℝ → ℝ := fun x => g 1 * x with hh_def
  -- h is continuous
  have hh_cont : Continuous h := continuous_const.mul continuous_id'
  -- g and h agree on ℚ (dense in ℝ)
  have hS : Dense (Set.range (Rat.cast : ℚ → ℝ)) :=
    Rat.isDenseEmbedding_coe_real.dense
  -- g = h on the dense set
  have heq : Set.EqOn g h (Set.range (Rat.cast : ℚ → ℝ)) := by
    rintro _ ⟨q, rfl⟩
    simp only [hh_def]
    rw [additive_ratCast g hg q, mul_comm]
  -- By continuity + density, g = h everywhere
  have hext := Continuous.ext_on hS hg_cont hh_cont heq
  exact fun x => congr_fun hext x

/-! ## Main Characterization Theorem -/

/-- **Cauchy Exponential Characterization Theorem**

If f : ℝ → ℝ satisfies:
  (1) f(x + y) = f(x) · f(y)     — multiplicative over addition
  (2) f(0) = 1                    — normalization
  (3) f is continuous             — regularity
  (4) f is strictly decreasing    — physical/survival interpretation

then there exists a unique c > 0 such that f(x) = exp(-c · x) for all x.

This theorem justifies the exponential form e^{-cδ} in the survival equation
S = N_eff · e^{-δ} · f(μ/μ_c), showing it is the ONLY continuous function
compatible with independent multiplicative accumulation of constraints. -/
theorem cauchy_exponential_characterization (f : ℝ → ℝ)
    (hf_mul : ∀ x y, f (x + y) = f x * f y)
    (hf_zero : f 0 = 1)
    (hf_cont : Continuous f)
    (hf_anti : StrictAnti f) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, f x = Real.exp (-c * x) := by
  -- Step 1: f is positive everywhere
  have hf_pos := cauchy_mul_pos f hf_mul hf_zero
  -- Step 2: Define g = log ∘ f. Then g is additive.
  set g : ℝ → ℝ := fun x => Real.log (f x) with hg_def
  have hg_add : ∀ x y, g (x + y) = g x + g y :=
    cauchy_log_additive f hf_mul hf_zero
  -- Step 3: g is continuous (log is continuous on positive reals, f is continuous and positive)
  have hg_cont : Continuous g := by
    exact Real.continuous_log.comp (hf_cont.codRestrict fun x => ne_of_gt (hf_pos x))
  -- Step 4: By the Cauchy additive theorem, g(x) = g(1) * x for all x
  have hg_linear := continuous_additive_is_linear g hg_add hg_cont
  -- Step 5: f(x) = exp(g(x)) = exp(g(1) * x)
  have hf_exp : ∀ x, f x = Real.exp (g 1 * x) := by
    intro x
    rw [← Real.exp_log (hf_pos x)]
    congr 1
    exact hg_linear x
  -- Step 6: f is strictly decreasing, so g(1) < 0
  have hg1_neg : g 1 < 0 := by
    by_contra h
    push_neg at h
    -- If g(1) ≥ 0, then exp(g(1) * x) is non-decreasing
    -- contradicting strict anti-monotonicity of f
    have h01 : (0 : ℝ) < 1 := zero_lt_one
    have hf01 := hf_anti h01
    rw [hf_exp 0, hf_exp 1] at hf01
    simp only [mul_zero, mul_one] at hf01
    have : g 1 < 0 := by
      have hlt : Real.exp (g 1) < Real.exp 0 := by simpa using hf01
      exact Real.exp_lt_exp.mp hlt
    linarith
  -- Step 7: Define c = -g(1) > 0
  refine ⟨-g 1, by linarith, fun x => ?_⟩
  rw [hf_exp x]
  ring_nf

/-- Uniqueness: the exponent c is determined by f(1) -/
theorem cauchy_exponent_unique (f : ℝ → ℝ)
    (c₁ c₂ : ℝ) (h₁ : ∀ x, f x = Real.exp (-c₁ * x))
    (h₂ : ∀ x, f x = Real.exp (-c₂ * x)) : c₁ = c₂ := by
  have h : Real.exp (-c₁ * 1) = Real.exp (-c₂ * 1) := by
    rw [← h₁ 1, ← h₂ 1]
  simp only [mul_one] at h
  have := Real.exp_injective h
  linarith

/-- c = 1 is the theoretical upper bound for the survival equation.
    Random search pays the full cost of δ (mathematical identity). -/
theorem c_one_is_identity (x : ℝ) :
    Real.exp (-(1 : ℝ) * x) = Real.exp (-x) := by
  ring_nf

/-! ## Corollaries for the Persistence Equation -/

/-- Multiplicative accumulation: two independent constraints combine multiplicatively -/
theorem constraint_multiplicativity (c δ₁ δ₂ : ℝ) :
    Real.exp (-c * (δ₁ + δ₂)) = Real.exp (-c * δ₁) * Real.exp (-c * δ₂) := by
  have : -c * (δ₁ + δ₂) = -c * δ₁ + -c * δ₂ := by ring
  rw [this, Real.exp_add]

/-- Log-additivity: survival budget in nats is additive -/
theorem log_survival_additive (c δ₁ δ₂ : ℝ) :
    Real.log (Real.exp (-c * (δ₁ + δ₂))) =
    Real.log (Real.exp (-c * δ₁)) + Real.log (Real.exp (-c * δ₂)) := by
  rw [constraint_multiplicativity]
  exact Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _))

/-- Parameter-free ratio prediction: δ_c cancels in the ratio α₁/α₂ = I₂/I₁ -/
theorem ratio_prediction (I₁ I₂ δ_c : ℝ) (hI₁ : 0 < I₁) (hI₂ : 0 < I₂) (hδ : 0 < δ_c) :
    (δ_c / I₁) / (δ_c / I₂) = I₂ / I₁ := by
  field_simp

end Persistence
