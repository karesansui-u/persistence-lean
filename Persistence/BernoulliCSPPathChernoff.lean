import Persistence.BernoulliCSPPathMeasure

/-!
# Bernoulli CSP Path Chernoff Bound

This module connects the reusable Bernoulli-CSP path measure to the reusable
Bernoulli-CSP MGF/KL algebra.

The previous path-space layer proves the exact MGF product for the active-prefix
bad-count process.  Here we apply the standard Chernoff step to the actual path
measure and then substitute the optimized lower-tail tilt from
`BernoulliCSPTemplate`.

The main output is:

* an unconditional MGF Chernoff upper bound for the actual finite path PMF;
* an optimized closed-MGF upper bound;
* an interior KL/Chernoff upper bound using the template failure profile.
-/

namespace Persistence.BernoulliCSPPathChernoff

open MeasureTheory
open ProbabilityTheory
open Persistence.BernoulliCSPTemplate
open Persistence.BernoulliCSPPathMeasure

noncomputable section

/-- A closed-form upper-bound candidate for a count lower-tail failure profile. -/
abbrev CountFailureProfile := ℕ → ℝ → ENNReal

/-- Canonical bad-count lower-tail event induced by the Bernoulli-CSP
deviation budget `r`. -/
def countBelowThresholdEvent
    (P : Parameters) (N n : ℕ) (r : ℝ) : Set (Trajectory N) :=
  {τ | (badCountPrefix τ n : ℝ) < P.countThreshold n r}

/-- Exact active-prefix bad-count lower-tail failure profile. -/
def exactCountFailureBound
    (P : Parameters) (N n : ℕ) (r : ℝ) : ENNReal :=
  pathMeasure P N (countBelowThresholdEvent P N n r)

/-- Count-tail upper-bound predicate for the actual Bernoulli-CSP path PMF. -/
def HasCountFailureUpperBound
    (P : Parameters) (N : ℕ) (B : CountFailureProfile) : Prop :=
  ∀ ⦃n : ℕ⦄, n ≤ N + 1 → ∀ r,
    exactCountFailureBound P N n r ≤ B n r

theorem badCountPrefix_le {N : ℕ} (τ : Trajectory N) :
    ∀ n, badCountPrefix τ n ≤ n
  | 0 => by
      simp [badCountPrefix]
  | n + 1 => by
      have hrec := badCountPrefix_le τ n
      by_cases hbad : outcomeAt τ n = Outcome.bad
      · simp [badCountPrefix, hbad]
        omega
      · simp [badCountPrefix, hbad]
        omega

theorem badCountRV_mem_Icc
    (P : Parameters) (N n : ℕ) :
    ∀ᵐ τ ∂pathMeasure P N, badCountRV P N n τ ∈ Set.Icc 0 (n : ℝ) := by
  refine Filter.Eventually.of_forall ?_
  intro τ
  constructor
  · dsimp [badCountRV]
    positivity
  · dsimp [badCountRV]
    exact_mod_cast badCountPrefix_le τ n

/-- The exponential moment of the active-prefix bad count is finite. -/
theorem integrable_exp_mul_badCountRV
    (P : Parameters) (N n : ℕ) (t : ℝ) :
    Integrable
      (fun τ : Trajectory N => Real.exp (t * badCountRV P N n τ))
      (pathMeasure P N) := by
  exact
    ProbabilityTheory.integrable_exp_mul_of_mem_Icc
      (a := 0)
      (b := (n : ℝ))
      (t := t)
      ((measurable_from_top : Measurable (badCountRV P N n)).aemeasurable)
      (badCountRV_mem_Icc P N n)

theorem countBelowThresholdEvent_subset_badCountRV_le
    (P : Parameters) (N n : ℕ) (r : ℝ) :
    countBelowThresholdEvent P N n r ⊆
      {τ : Trajectory N | badCountRV P N n τ ≤ P.countThreshold n r} := by
  intro τ hτ
  change (badCountPrefix τ n : ℝ) < P.countThreshold n r at hτ
  change (badCountPrefix τ n : ℝ) ≤ P.countThreshold n r
  exact le_of_lt hτ

/-- Generic Chernoff/MGF upper bound for the active-prefix bad-count lower
tail. -/
theorem exactCountFailureBound_le_mgfChernoff
    (P : Parameters) (N : ℕ) {n : ℕ} (_hn : n ≤ N + 1) (r : ℝ)
    {t : ℝ} (ht : t ≤ 0) :
    exactCountFailureBound P N n r ≤
      ENNReal.ofReal
        (Real.exp (-t * P.countThreshold n r) *
          mgf (badCountRV P N n) (pathMeasure P N) t) := by
  let s : Set (Trajectory N) :=
    {τ | badCountRV P N n τ ≤ P.countThreshold n r}
  have hsub : countBelowThresholdEvent P N n r ⊆ s :=
    countBelowThresholdEvent_subset_badCountRV_le P N n r
  have hmono :
      pathMeasure P N (countBelowThresholdEvent P N n r) ≤ pathMeasure P N s :=
    measure_mono hsub
  have hmonoReal :
      Measure.real (pathMeasure P N) (countBelowThresholdEvent P N n r) ≤
        Measure.real (pathMeasure P N) s := by
    exact
      (ENNReal.toReal_le_toReal
        (measure_ne_top (pathMeasure P N) _)
        (measure_ne_top (pathMeasure P N) _)).2 hmono
  have hchernoff :
      Measure.real (pathMeasure P N) s ≤
        Real.exp (-t * P.countThreshold n r) *
          mgf (badCountRV P N n) (pathMeasure P N) t := by
    simpa [s] using
      ProbabilityTheory.measure_le_le_exp_mul_mgf
        (μ := pathMeasure P N)
        (X := badCountRV P N n)
        (ε := P.countThreshold n r)
        (t := t)
        ht
        (integrable_exp_mul_badCountRV P N n t)
  have hreal :
      Measure.real (pathMeasure P N) (countBelowThresholdEvent P N n r) ≤
        Real.exp (-t * P.countThreshold n r) *
          mgf (badCountRV P N n) (pathMeasure P N) t :=
    hmonoReal.trans hchernoff
  unfold exactCountFailureBound
  rw [← ENNReal.ofReal_toReal (measure_ne_top (pathMeasure P N) _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Closed Bernoulli-sum MGF profile for the active-prefix count tail. -/
def countClosedMGFChernoffFailureBound
    (P : Parameters) (t : ℝ) : CountFailureProfile :=
  fun n r =>
    ENNReal.ofReal
      (Real.exp (-t * P.countThreshold n r) *
        bernoulliBadMGF P.badProb t ^ n)

/-- The closed MGF Chernoff profile is an actual count-tail upper bound for the
generic Bernoulli-CSP path PMF. -/
theorem hasCountFailureUpperBound_closedMGF_pathPMF
    (P : Parameters) (N : ℕ) {t : ℝ} (ht : t ≤ 0) :
    HasCountFailureUpperBound P N (countClosedMGFChernoffFailureBound P t) := by
  intro n hn r
  calc
    exactCountFailureBound P N n r
        ≤ ENNReal.ofReal
            (Real.exp (-t * P.countThreshold n r) *
              mgf (badCountRV P N n) (pathMeasure P N) t) := by
          exact exactCountFailureBound_le_mgfChernoff P N hn r ht
    _ = countClosedMGFChernoffFailureBound P t n r := by
          rw [mgf_badCountRV_eq_bernoulliBadMGF_pow P N t hn]
          rfl

/-- Optimized closed-MGF Chernoff profile obtained by substituting the
threshold-dependent lower-tail tilt. -/
def countOptimizedClosedMGFChernoffFailureBound
    (P : Parameters) : CountFailureProfile :=
  fun n r => countClosedMGFChernoffFailureBound P (P.optimizingTilt n r) n r

/-- The optimized closed-MGF profile is an actual count-tail upper bound for the
generic Bernoulli-CSP path PMF. -/
theorem hasCountFailureUpperBound_optimizedClosedMGF_pathPMF
    (P : Parameters) (N : ℕ) :
    HasCountFailureUpperBound P N
      (countOptimizedClosedMGFChernoffFailureBound P) := by
  intro n hn r
  exact
    hasCountFailureUpperBound_closedMGF_pathPMF
      P N (P.optimizingTilt_nonpos n r) hn r

/-- Direct exact count-tail bound by the optimized closed-MGF profile. -/
theorem exactCountFailureBound_le_optimizedClosedMGF_pathPMF
    (P : Parameters) (N : ℕ) {n : ℕ} (hn : n ≤ N + 1) (r : ℝ) :
    exactCountFailureBound P N n r ≤
      countOptimizedClosedMGFChernoffFailureBound P n r :=
  hasCountFailureUpperBound_optimizedClosedMGF_pathPMF P N hn r

/-- On the lower-tail interior, the optimized path-space bound is exactly the
KL/Chernoff failure profile from `BernoulliCSPTemplate`. -/
theorem countOptimizedClosedMGF_eq_chernoffFailureBound_of_interior
    (P : Parameters) {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    countOptimizedClosedMGFChernoffFailureBound P n r =
      P.chernoffFailureBound n r := by
  unfold countOptimizedClosedMGFChernoffFailureBound
    countClosedMGFChernoffFailureBound
  simpa [Parameters.optimizedClosedMGFReal] using
    P.optimizedClosedMGFReal_failure_eq_chernoffFailureBound_of_interior
      hr hlt

/-- Interior KL/Chernoff count-tail bound for the actual Bernoulli-CSP path
PMF. -/
theorem exactCountFailureBound_le_chernoffFailureBound_of_interior
    (P : Parameters) (N : ℕ) {n : ℕ} (hn : n ≤ N + 1) {r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    exactCountFailureBound P N n r ≤ P.chernoffFailureBound n r := by
  calc
    exactCountFailureBound P N n r
        ≤ countOptimizedClosedMGFChernoffFailureBound P n r := by
          exact exactCountFailureBound_le_optimizedClosedMGF_pathPMF P N hn r
    _ = P.chernoffFailureBound n r := by
          exact countOptimizedClosedMGF_eq_chernoffFailureBound_of_interior P hr hlt

/-- One-sided cumulative production for the generic Bernoulli-CSP path: bad
outcomes carry `badEmissionScale`, good outcomes carry zero. -/
def cumulativeProduction
    (P : Parameters) (s₀ : ℝ) {N : ℕ} (τ : Trajectory N) (n : ℕ) : ℝ :=
  s₀ + (badCountPrefix τ n : ℝ) * P.badEmissionScale

/-- Exact linear center induced by the mean drift. -/
def linearCenter (P : Parameters) (s₀ : ℝ) (n : ℕ) : ℝ :=
  s₀ + (n : ℝ) * P.drift

/-- Lower-tail failure event for the generic cumulative production observable.
-/
def cumulativeLowerTailEvent
    (P : Parameters) (s₀ : ℝ) (N n : ℕ) (r : ℝ) : Set (Trajectory N) :=
  {τ | cumulativeProduction P s₀ τ n < linearCenter P s₀ n - r}

theorem cumulativeLowerTailEvent_eq_countBelowThresholdEvent
    (P : Parameters) (s₀ : ℝ) (N n : ℕ) (r : ℝ) :
    cumulativeLowerTailEvent P s₀ N n r =
      countBelowThresholdEvent P N n r := by
  ext τ
  constructor <;> intro hτ
  · unfold cumulativeLowerTailEvent cumulativeProduction linearCenter at hτ
    change
      s₀ + (badCountPrefix τ n : ℝ) * P.badEmissionScale <
        s₀ + (n : ℝ) * P.drift - r at hτ
    unfold countBelowThresholdEvent Parameters.countThreshold
    have hmul :
        (badCountPrefix τ n : ℝ) * P.badEmissionScale <
          (n : ℝ) * P.drift - r := by
      linarith
    exact (lt_div_iff₀ P.badEmissionScale_pos).2 hmul
  · unfold cumulativeLowerTailEvent cumulativeProduction linearCenter
    unfold countBelowThresholdEvent Parameters.countThreshold at hτ
    have hmul :
        (badCountPrefix τ n : ℝ) * P.badEmissionScale <
          (n : ℝ) * P.drift - r := by
      exact (lt_div_iff₀ P.badEmissionScale_pos).1 hτ
    change
      s₀ + (badCountPrefix τ n : ℝ) * P.badEmissionScale <
        s₀ + (n : ℝ) * P.drift - r
    linarith

/-- Interior KL/Chernoff lower-tail bound for the generic cumulative production
observable. -/
theorem cumulativeLowerTailMeasure_le_chernoffFailureBound_of_interior
    (P : Parameters) (N : ℕ) {n : ℕ} (hn : n ≤ N + 1) {s₀ r : ℝ}
    (hr : 0 ≤ r)
    (hlt : r < (n : ℝ) * P.drift) :
    pathMeasure P N (cumulativeLowerTailEvent P s₀ N n r) ≤
      P.chernoffFailureBound n r := by
  rw [cumulativeLowerTailEvent_eq_countBelowThresholdEvent]
  exact exactCountFailureBound_le_chernoffFailureBound_of_interior P N hn hr hlt

end

end Persistence.BernoulliCSPPathChernoff
