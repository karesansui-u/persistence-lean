/-
Persistence Model — Log-Ratio Uniqueness (Paper 1 §3)
対数比損失の一意性定理

Theorem: If f : ℝ → ℝ satisfies, on the ratio space (0, 1]:
  (B1)       f is a function on (0, 1]       — representation (implicit)
  (B2)       f(1) = 0                          — normalization
  (B3)       ∀ r₁, r₂ ∈ (0, 1], f(r₁ · r₂) = f(r₁) + f(r₂)   — additivity
  (B4)       f is continuous                   — regularity
  (codomain) ∀ r ∈ (0, 1], 0 ≤ f(r)            — corresponds to the paper's
                                                 codomain restriction
                                                 f : (0, 1] → [0, ∞)
then there exists a unique k ≥ 0 such that for all r ∈ (0, 1],
  f(r) = -k · Real.log r.

Naming note: In the paper (Paper 1 §3.1), axiom B5 is *monotonicity*
(f non-increasing on (0, 1]), and non-negativity is built into the codomain
of B1. In Lean we work with f : ℝ → ℝ, so the codomain restriction becomes
an explicit hypothesis here. The paper's B5 (monotonicity) is not assumed
separately: it follows as a consequence of the theorem, since k ≥ 0 forces
r ↦ -k · log r to be non-increasing on (0, 1].

This is the Shannon/Hartley-type axiomatic characterization that elevates
the log-ratio form of loss (A2 in Paper 2) from a definition to a theorem.

References:
  - Hartley, R. V. L. (1928). "Transmission of Information."
  - Shannon, C. E. (1948). "A Mathematical Theory of Communication."

Proof strategy:
  Define g(t) := f(exp(-t)) for t ≥ 0 and g(t) := -f(exp(t)) for t < 0.
  This maps B3 (multiplicativity of ratios) to additivity of g on ℝ, and
  reduces log-ratio uniqueness to the existing Cauchy functional equation
  characterization (CauchyExponential.continuous_additive_is_linear).
  Independent of A3 (probabilistic independence), so this module stands
  alongside AxiomsToExp.lean rather than depending on it.
-/

import Persistence.CauchyExponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Persistence

open Real

/-! ## Substitution g(t) = f(exp(-t)) with odd extension -/

/-- Substitution used to reduce log-ratio uniqueness to a Cauchy additive
    equation on ℝ. For t ≥ 0 it reads f at exp(-t) ∈ (0, 1]; for t < 0 it is
    the odd extension, which evaluates -f at exp(t) ∈ (0, 1). Both branches
    stay inside f's axiomatized domain (0, 1]. -/
noncomputable def logSubstitute (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then f (Real.exp (-t)) else -f (Real.exp t)

lemma logSubstitute_of_nonneg (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    logSubstitute f t = f (Real.exp (-t)) := by
  unfold logSubstitute; rw [if_pos ht]

lemma logSubstitute_of_neg (f : ℝ → ℝ) {t : ℝ} (ht : t < 0) :
    logSubstitute f t = -f (Real.exp t) := by
  unfold logSubstitute; rw [if_neg (not_le.mpr ht)]

lemma logSubstitute_zero (f : ℝ → ℝ) (hf_one : f 1 = 0) :
    logSubstitute f 0 = 0 := by
  rw [logSubstitute_of_nonneg f le_rfl]; simp [hf_one]

/-! ## Domain facts: exp sends [0,∞) and (-∞,0) into (0, 1] -/

lemma exp_neg_mem_Ioc {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_le_exp.mpr (by linarith)

lemma exp_mem_Ioc {t : ℝ} (ht : t < 0) : Real.exp t ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
  exact Real.exp_le_exp.mpr (le_of_lt ht)

/-! ## Additivity of logSubstitute on ℝ -/

/-- Abbreviation for the additivity hypothesis B3 on (0, 1]. -/
def IsLogAdditive (f : ℝ → ℝ) : Prop :=
  ∀ r₁ r₂, 0 < r₁ → r₁ ≤ 1 → 0 < r₂ → r₂ ≤ 1 → f (r₁ * r₂) = f r₁ + f r₂

/-- B3 on the image exp(-·) of [0, ∞). -/
lemma f_exp_add_nonneg (f : ℝ → ℝ) (hf_add : IsLogAdditive f)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    f (Real.exp (-(s + t))) = f (Real.exp (-s)) + f (Real.exp (-t)) := by
  have key : Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t) := by
    rw [show -(s + t) = -s + -t from by ring, Real.exp_add]
  rw [key]
  have hs1 := exp_neg_mem_Ioc hs
  have ht1 := exp_neg_mem_Ioc ht
  exact hf_add _ _ hs1.1 hs1.2 ht1.1 ht1.2

/-- B3 applied to the split exp(-s) = exp(-(s+t)) · exp(t) when s + t ≥ 0. -/
lemma f_exp_split_pos (f : ℝ → ℝ) (hf_add : IsLogAdditive f)
    {s t : ℝ} (_hs : 0 ≤ s) (ht : t < 0) (hst : 0 ≤ s + t) :
    f (Real.exp (-s)) = f (Real.exp (-(s + t))) + f (Real.exp t) := by
  have key : Real.exp (-s) = Real.exp (-(s + t)) * Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [key]
  have h1 := exp_neg_mem_Ioc hst
  have h2 := exp_mem_Ioc ht
  exact hf_add _ _ h1.1 h1.2 h2.1 h2.2

/-- B3 applied to the split exp(t) = exp(-s) · exp(s+t) when s + t < 0. -/
lemma f_exp_split_neg (f : ℝ → ℝ) (hf_add : IsLogAdditive f)
    {s t : ℝ} (hs : 0 ≤ s) (_ht : t < 0) (hst : s + t < 0) :
    f (Real.exp t) = f (Real.exp (-s)) + f (Real.exp (s + t)) := by
  have key : Real.exp t = Real.exp (-s) * Real.exp (s + t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [key]
  have h1 := exp_neg_mem_Ioc hs
  have h2 := exp_mem_Ioc hst
  exact hf_add _ _ h1.1 h1.2 h2.1 h2.2

/-- B3 on the image exp(·) of (-∞, 0). -/
lemma f_exp_add_neg (f : ℝ → ℝ) (hf_add : IsLogAdditive f)
    {s t : ℝ} (hs : s < 0) (ht : t < 0) :
    f (Real.exp (s + t)) = f (Real.exp s) + f (Real.exp t) := by
  rw [Real.exp_add]
  have h1 := exp_mem_Ioc hs
  have h2 := exp_mem_Ioc ht
  exact hf_add _ _ h1.1 h1.2 h2.1 h2.2

/-- The substitution g is additive on ℝ: g(s + t) = g(s) + g(t).
    Proof by case analysis on the signs of s, t, and s + t. -/
theorem logSubstitute_add (f : ℝ → ℝ) (hf_add : IsLogAdditive f) (s t : ℝ) :
    logSubstitute f (s + t) = logSubstitute f s + logSubstitute f t := by
  rcases le_or_gt 0 s with hs | hs
  · rcases le_or_gt 0 t with ht | ht
    · -- s ≥ 0, t ≥ 0
      rw [logSubstitute_of_nonneg f (add_nonneg hs ht),
          logSubstitute_of_nonneg f hs, logSubstitute_of_nonneg f ht]
      exact f_exp_add_nonneg f hf_add hs ht
    · -- s ≥ 0, t < 0
      rcases le_or_gt 0 (s + t) with hst | hst
      · rw [logSubstitute_of_nonneg f hst,
            logSubstitute_of_nonneg f hs, logSubstitute_of_neg f ht]
        have h := f_exp_split_pos f hf_add hs ht hst
        linarith
      · rw [logSubstitute_of_neg f hst,
            logSubstitute_of_nonneg f hs, logSubstitute_of_neg f ht]
        have h := f_exp_split_neg f hf_add hs ht hst
        linarith
  · rcases le_or_gt 0 t with ht | ht
    · -- s < 0, t ≥ 0 (mirror of previous case via add_comm)
      rcases le_or_gt 0 (s + t) with hst | hst
      · rw [logSubstitute_of_nonneg f hst,
            logSubstitute_of_neg f hs, logSubstitute_of_nonneg f ht]
        have hst' : 0 ≤ t + s := by linarith
        have h := f_exp_split_pos f hf_add ht hs hst'
        rw [show t + s = s + t from by ring] at h
        linarith
      · rw [logSubstitute_of_neg f hst,
            logSubstitute_of_neg f hs, logSubstitute_of_nonneg f ht]
        have hst' : t + s < 0 := by linarith
        have h := f_exp_split_neg f hf_add ht hs hst'
        rw [show t + s = s + t from by ring] at h
        linarith
    · -- s < 0, t < 0
      rw [logSubstitute_of_neg f (by linarith),
          logSubstitute_of_neg f hs, logSubstitute_of_neg f ht]
      have h := f_exp_add_neg f hf_add hs ht
      linarith

/-! ## Continuity of logSubstitute -/

/-- The substitution g is continuous on ℝ, provided f is continuous and
    f(1) = 0 (so the two branches meet at t = 0). Uses `Continuous.if_le`
    applied with the boundary predicate `0 ≤ t`. -/
theorem logSubstitute_continuous {f : ℝ → ℝ} (hf_cont : Continuous f)
    (hf_one : f 1 = 0) : Continuous (logSubstitute f) := by
  -- logSubstitute f t = if 0 ≤ t then f(exp(-t)) else -f(exp t)
  -- Rewrite as `if (fun _ => 0) x ≤ id x` form for `Continuous.if_le`.
  have h_eq : logSubstitute f =
      fun t => if (fun _ : ℝ => (0 : ℝ)) t ≤ id t then f (Real.exp (-t))
               else -f (Real.exp t) := by
    funext t
    by_cases ht : (0 : ℝ) ≤ t
    · rw [logSubstitute_of_nonneg f ht]
      simp [ht]
    · push_neg at ht
      rw [logSubstitute_of_neg f ht]
      simp [not_le.mpr ht]
  rw [h_eq]
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · -- f ∘ (exp ∘ neg) continuous
    exact hf_cont.comp (Real.continuous_exp.comp continuous_neg)
  · -- -(f ∘ exp) continuous
    exact (hf_cont.comp Real.continuous_exp).neg
  · -- at the boundary x = 0, both branches agree to 0
    intro x hx
    -- hx : (fun _ => 0) x = id x, i.e., 0 = x (after β/id reduction)
    have hx0 : (0 : ℝ) = x := hx
    subst hx0
    simp [hf_one]

/-! ## Main theorem: log-ratio uniqueness -/

/-- **Log-Ratio Uniqueness Theorem** (Paper 1 §3).

If f : ℝ → ℝ satisfies, on the ratio space (0, 1]:
  (B2)       f(1) = 0
  (B3)       f(r₁ · r₂) = f(r₁) + f(r₂)  for all r₁, r₂ ∈ (0, 1]
  (B4)       f is continuous
  (codomain) f(r) ≥ 0 for r ∈ (0, 1]   — the paper's codomain [0, ∞)
then there exists k ≥ 0 such that
  ∀ r ∈ (0, 1], f(r) = -k · Real.log r.

This elevates A2 (log-ratio loss) of Paper 2 from a definition to a theorem,
and provides the axiomatic justification sought in Paper 1 §3. The derivation
is independent of A3 (probabilistic independence of stage losses).

Naming note: The paper's axiom B5 is monotonicity, which is *not* assumed
here and instead follows as a consequence of k ≥ 0. The non-negativity
hypothesis `hf_nonneg` corresponds to the paper's codomain restriction on B1,
not to B5. -/
theorem log_ratio_uniqueness (f : ℝ → ℝ)
    (hf_nonneg : ∀ r, 0 < r → r ≤ 1 → 0 ≤ f r)
    (hf_one : f 1 = 0)
    (hf_add : IsLogAdditive f)
    (hf_cont : Continuous f) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ r, 0 < r → r ≤ 1 → f r = -k * Real.log r := by
  -- Step 1: Define g = logSubstitute f. Then g is additive on ℝ, continuous,
  -- and g(0) = 0.
  set g : ℝ → ℝ := logSubstitute f with hg_def
  have hg_add : ∀ s t, g (s + t) = g s + g t := fun s t =>
    logSubstitute_add f hf_add s t
  have hg_cont : Continuous g := logSubstitute_continuous hf_cont hf_one
  -- Step 2: By the Cauchy additive theorem, g(t) = g(1) · t for all t.
  have hg_linear := continuous_additive_is_linear g hg_add hg_cont
  -- Step 3: Set k := g(1) = f(exp(-1)). Then k ≥ 0 by B5 since exp(-1) ∈ (0, 1].
  set k : ℝ := g 1 with hk_def
  have hk_eq : k = f (Real.exp (-1)) := by
    rw [hk_def, hg_def, logSubstitute_of_nonneg f (by norm_num : (0 : ℝ) ≤ 1)]
  have hexp_neg1 : Real.exp (-1) ∈ Set.Ioc (0 : ℝ) 1 :=
    exp_neg_mem_Ioc (by norm_num : (0 : ℝ) ≤ 1)
  have hk_nn : 0 ≤ k := by
    rw [hk_eq]
    exact hf_nonneg _ hexp_neg1.1 hexp_neg1.2
  -- Step 4: For r ∈ (0, 1], set t := -log r ≥ 0. Then exp(-t) = r, so
  -- f(r) = g(t) = k · t = -k · log r.
  refine ⟨k, hk_nn, fun r hr_pos hr_le => ?_⟩
  have ht_nn : 0 ≤ -Real.log r := by
    have : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr_pos) hr_le
    linarith
  have hr_exp : Real.exp (-(-Real.log r)) = r := by
    rw [neg_neg, Real.exp_log hr_pos]
  -- Compute f(r) via g:
  have h1 : g (-Real.log r) = f r := by
    rw [hg_def, logSubstitute_of_nonneg f ht_nn, hr_exp]
  -- Apply linearity:
  have h2 : g (-Real.log r) = k * (-Real.log r) := hg_linear (-Real.log r)
  linarith

/-! ## Corollary: uniqueness of k given f -/

/-- The coefficient k in the log-ratio characterization is unique: it is
    determined by f(exp(-1)). Two representations of the same f must share k. -/
theorem log_ratio_coefficient_unique (f : ℝ → ℝ)
    (k₁ k₂ : ℝ)
    (h₁ : ∀ r, 0 < r → r ≤ 1 → f r = -k₁ * Real.log r)
    (h₂ : ∀ r, 0 < r → r ≤ 1 → f r = -k₂ * Real.log r) :
    k₁ = k₂ := by
  have hexp_neg1 : Real.exp (-1) ∈ Set.Ioc (0 : ℝ) 1 :=
    exp_neg_mem_Ioc (by norm_num : (0 : ℝ) ≤ 1)
  have hlog : Real.log (Real.exp (-1)) = -1 := Real.log_exp _
  have e1 := h₁ _ hexp_neg1.1 hexp_neg1.2
  have e2 := h₂ _ hexp_neg1.1 hexp_neg1.2
  rw [hlog] at e1 e2
  linarith

/-! ## Corollary: the unit convention k = 1 gives f(r) = -log r -/

/-- Under the unit convention k = 1 (structural nat), the loss function is
    f(r) = -log r for r ∈ (0, 1]. Any non-trivial log-ratio loss is a positive
    rescaling of this, by `log_ratio_uniqueness`. -/
theorem log_ratio_structural_nat (r : ℝ) :
    (fun s => -Real.log s) r = -Real.log r := rfl

end Persistence
