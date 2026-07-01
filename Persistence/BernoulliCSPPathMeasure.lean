import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Persistence.BernoulliCSPTemplate

/-!
# Bernoulli CSP Path Measure

This module provides the reusable finite path-space layer for one-sided
Bernoulli CSP exposure models.

`BernoulliCSPTemplate` contains the algebraic MGF/KL profile for an abstract
bad-event probability `p`.  Here we instantiate the actual finite-horizon law:
an i.i.d. path of `good` / `bad` outcomes with bad-event probability `p`, and we
prove that the active-prefix bad-count MGF factors as

`mgf(count_n)(t) = ((1 - p) + p * exp t)^n`.

The SAT-specific clause-exposure chain is the `p = 1 / 8` specialization of this
generic path layer.
-/

open scoped ProbabilityTheory

namespace Persistence.BernoulliCSPPathMeasure

open MeasureTheory
open ProbabilityTheory
open Persistence.BernoulliCSPTemplate

noncomputable section

/-- Binary outcome for a one-sided Bernoulli CSP exposure. -/
inductive Outcome where
  | good
  | bad
  deriving DecidableEq, Fintype, Repr

instance instMeasurableSpaceOutcome : MeasurableSpace Outcome := ⊤

instance instMeasurableSingletonClassOutcome :
    MeasurableSingletonClass Outcome where
  measurableSet_singleton _ := by
    trivial

/-- Finite trajectories of Bernoulli CSP outcomes. -/
abbrev Trajectory (N : ℕ) := Fin (N + 1) → Outcome

instance instMeasurableSpaceTrajectory (N : ℕ) : MeasurableSpace (Trajectory N) := ⊤

instance instMeasurableSingletonClassTrajectory (N : ℕ) :
    MeasurableSingletonClass (Trajectory N) where
  measurableSet_singleton _ := by
    trivial

/-- The bad-event probability as an `NNReal`, for use with `PMF.bernoulli`. -/
def badProbNNReal (P : Parameters) : NNReal :=
  ⟨P.badProb, P.badProb_pos.le⟩

theorem badProbNNReal_coe (P : Parameters) :
    (badProbNNReal P : ℝ) = P.badProb := rfl

theorem badProbNNReal_le_one (P : Parameters) :
    badProbNNReal P ≤ 1 := by
  change P.badProb ≤ (1 : ℝ)
  exact P.badProb_lt_one.le

/-- One-step Bernoulli CSP outcome law. -/
def oneStepPMF (P : Parameters) : PMF Outcome :=
  (PMF.bernoulli (badProbNNReal P) (badProbNNReal_le_one P)).map
    (fun b => if b then Outcome.bad else Outcome.good)

/-- Length-1 trajectory from a single outcome. -/
def singletonTraj (s : Outcome) : Trajectory 0 := fun _ => s

/-- Extend a trajectory by one final outcome. -/
def snoc {N : ℕ} (τ : Trajectory N) (s : Outcome) : Trajectory (N + 1)
  | ⟨i, _⟩ =>
      if h : i < N + 1 then
        τ ⟨i, h⟩
      else
        s

/-- Finite-horizon i.i.d. Bernoulli CSP path PMF. -/
def pathPMF (P : Parameters) : ∀ N : ℕ, PMF (Trajectory N)
  | 0 => (oneStepPMF P).map singletonTraj
  | N + 1 =>
      (pathPMF P N).bind fun τ =>
        (oneStepPMF P).map (snoc τ)

/-- The corresponding finite-horizon probability measure. -/
def pathMeasure (P : Parameters) (N : ℕ) : Measure (Trajectory N) :=
  (pathPMF P N).toMeasure

instance instIsProbabilityMeasurePathMeasure (P : Parameters) (N : ℕ) :
    IsProbabilityMeasure (pathMeasure P N) := by
  dsimp [pathMeasure]
  infer_instance

/-- Outside the active finite horizon, use the benign default `good`. -/
def outcomeAt {N : ℕ} (τ : Trajectory N) (t : ℕ) : Outcome :=
  if ht : t ≤ N then
    τ ⟨t, Nat.lt_succ_of_le ht⟩
  else
    .good

/-- Recursive count of bad outcomes on the first `n` exposures. -/
def badCountPrefix {N : ℕ} (τ : Trajectory N) : ℕ → ℕ
  | 0 => 0
  | n + 1 => badCountPrefix τ n + if outcomeAt τ n = Outcome.bad then 1 else 0

/-- Real-valued active-prefix bad count. -/
def badCountRV (_P : Parameters) (N n : ℕ) : Trajectory N → ℝ :=
  fun τ => (badCountPrefix τ n : ℝ)

/-- Real-valued indicator of a bad one-step outcome. -/
def badIndicator (s : Outcome) : ℝ :=
  if s = Outcome.bad then 1 else 0

theorem finset_univ_outcome :
    (Finset.univ : Finset Outcome) = {Outcome.good, Outcome.bad} := by
  ext x
  cases x <;> simp

@[simp] theorem oneStepPMF_apply_bad (P : Parameters) :
    oneStepPMF P Outcome.bad = (badProbNNReal P : ENNReal) := by
  rw [oneStepPMF, PMF.map_apply]
  simp [PMF.bernoulli_apply]

@[simp] theorem oneStepPMF_apply_good (P : Parameters) :
    oneStepPMF P Outcome.good = 1 - (badProbNNReal P : ENNReal) := by
  rw [oneStepPMF, PMF.map_apply]
  simp [PMF.bernoulli_apply]

@[simp] theorem oneStepPMF_apply_bad_toReal (P : Parameters) :
    (oneStepPMF P Outcome.bad).toReal = P.badProb := by
  rw [oneStepPMF_apply_bad]
  simp [badProbNNReal]

@[simp] theorem oneStepPMF_apply_good_toReal (P : Parameters) :
    (oneStepPMF P Outcome.good).toReal = 1 - P.badProb := by
  rw [oneStepPMF_apply_good]
  rw [ENNReal.toReal_sub_of_le]
  · simp [badProbNNReal]
  · exact_mod_cast badProbNNReal_le_one P
  · exact ENNReal.one_ne_top

/-- The one-step MGF of the bad indicator is `(1 - p) + p * exp t`. -/
theorem oneStepBadIndicatorMGF_eq_bernoulliBadMGF
    (P : Parameters) (t : ℝ) :
    ∫ s, Real.exp (t * badIndicator s) ∂(oneStepPMF P).toMeasure =
      bernoulliBadMGF P.badProb t := by
  rw [PMF.integral_eq_sum]
  rw [finset_univ_outcome]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
    not_false_eq_true, oneStepPMF_apply_good_toReal,
    oneStepPMF_apply_bad_toReal, badIndicator, reduceCtorEq, ite_false,
    ite_true, mul_zero, Real.exp_zero, mul_one, smul_eq_mul, bernoulliBadMGF]

theorem outcomeAt_snoc_of_le {N : ℕ} (τ : Trajectory N) (s : Outcome) {t : ℕ}
    (ht : t ≤ N) :
    outcomeAt (snoc τ s) t = outcomeAt τ t := by
  have hts : t < N + 1 := Nat.lt_succ_of_le ht
  have hnot : ¬ N + 1 < t := not_lt.mpr (Nat.le_trans ht (Nat.le_succ N))
  simp [outcomeAt, snoc, ht, hts, hnot]

theorem outcomeAt_snoc_last {N : ℕ} (τ : Trajectory N) (s : Outcome) :
    outcomeAt (snoc τ s) (N + 1) = s := by
  simp [outcomeAt, snoc]

/-- Extending a path by a final outcome does not affect old prefix counts. -/
theorem badCountPrefix_snoc_of_le {N : ℕ} (τ : Trajectory N) (s : Outcome) :
    ∀ ⦃n : ℕ⦄, n ≤ N + 1 →
      badCountPrefix (snoc τ s) n = badCountPrefix τ n
  | 0, _ => by
      simp [badCountPrefix]
  | n + 1, hn => by
      have hprefix : n ≤ N + 1 := Nat.le_trans (Nat.le_succ n) hn
      have hstep : n ≤ N := Nat.le_of_succ_le_succ hn
      simp [badCountPrefix, badCountPrefix_snoc_of_le τ s hprefix,
        outcomeAt_snoc_of_le τ s hstep]

/-- The terminal prefix count after `snoc` is the old full count plus the new
bad indicator. -/
theorem badCountPrefix_snoc_last {N : ℕ} (τ : Trajectory N) (s : Outcome) :
    badCountPrefix (snoc τ s) (N + 2) =
      badCountPrefix τ (N + 1) + if s = Outcome.bad then 1 else 0 := by
  change
    badCountPrefix (snoc τ s) ((N + 1) + 1) =
      badCountPrefix τ (N + 1) + if s = Outcome.bad then 1 else 0
  rw [badCountPrefix]
  rw [badCountPrefix_snoc_of_le τ s (Nat.le_refl (N + 1))]
  rw [outcomeAt_snoc_last]

/-- A finite-type bind integral rule for PMFs. -/
theorem integral_bind_eq_sum
    {α β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    ∫ b, f b ∂(p.bind q).toMeasure =
      ∑ a, (p a).toReal * ∫ b, f b ∂(q a).toMeasure := by
  classical
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.integral_eq_sum]
  simp_rw [PMF.bind_apply]
  have htsum :
      ∀ b : β,
        (∑' a : α, p a * q a b).toReal =
          ∑ a : α, (p a).toReal * (q a b).toReal := by
    intro b
    calc
      (∑' a : α, p a * q a b).toReal
          = (∑ a : α, p a * q a b).toReal := by
              rw [tsum_eq_sum (s := Finset.univ)]
              intro a ha
              simp at ha
      _ = ∑ a : α, (p a * q a b).toReal := by
              rw [ENNReal.toReal_sum]
              intro a _ha
              exact ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
      _ = ∑ a : α, (p a).toReal * (q a b).toReal := by
              simp [ENNReal.toReal_mul]
  simp_rw [htsum]
  calc
    ∑ b : β, (∑ a : α, (p a).toReal * (q a b).toReal) • f b
        = ∑ b : β, (∑ a : α, (p a).toReal * (q a b).toReal) * f b := by
            simp [smul_eq_mul]
    _ = ∑ b : β, ∑ a : α, ((p a).toReal * (q a b).toReal) * f b := by
            simp [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ((p a).toReal * (q a b).toReal) * f b := by
            exact Finset.sum_comm
    _ = ∑ a : α, (p a).toReal * ∑ b : β, (q a b).toReal * f b := by
            refine Finset.sum_congr rfl ?_
            intro a _ha
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _hb
            ring

theorem mgf_badCountRV_succ_of_le
    (P : Parameters) {N n : ℕ} (hn : n ≤ N + 1) (t : ℝ) :
    mgf (badCountRV P (N + 1) n) (pathMeasure P (N + 1)) t =
      mgf (badCountRV P N n) (pathMeasure P N) t := by
  change
    ∫ τ', Real.exp (t * ((badCountPrefix τ' n : ℕ) : ℝ))
      ∂(pathPMF P (N + 1)).toMeasure =
    ∫ τ, Real.exp (t * ((badCountPrefix τ n : ℕ) : ℝ))
      ∂(pathPMF P N).toMeasure
  rw [pathPMF]
  rw [integral_bind_eq_sum]
  have hinner :
      ∀ τ : Trajectory N,
        ∫ τ', Real.exp (t * ((badCountPrefix τ' n : ℕ) : ℝ))
            ∂((oneStepPMF P).map (snoc τ)).toMeasure =
          Real.exp (t * ((badCountPrefix τ n : ℕ) : ℝ)) := by
    intro τ
    rw [← PMF.toMeasure_map
      (p := oneStepPMF P)
      (f := snoc τ)
      (hf := (measurable_from_top : Measurable (snoc τ)))]
    calc
      ∫ τ', Real.exp (t * ((badCountPrefix τ' n : ℕ) : ℝ))
          ∂Measure.map (snoc τ) (oneStepPMF P).toMeasure
          = ∫ s, Real.exp (t * ((badCountPrefix (snoc τ s) n : ℕ) : ℝ))
              ∂(oneStepPMF P).toMeasure := by
              exact
                MeasureTheory.integral_map
                  (μ := (oneStepPMF P).toMeasure)
                  (φ := snoc τ)
                  (measurable_from_top : Measurable (snoc τ)).aemeasurable
                  ((measurable_from_top :
                    Measurable
                      (fun τ' : Trajectory (N + 1) =>
                        Real.exp (t * ((badCountPrefix τ' n : ℕ) : ℝ)))).aestronglyMeasurable)
      _ = ∫ s, Real.exp (t * ((badCountPrefix τ n : ℕ) : ℝ))
              ∂(oneStepPMF P).toMeasure := by
              congr with s
              rw [badCountPrefix_snoc_of_le τ s hn]
      _ = Real.exp (t * ((badCountPrefix τ n : ℕ) : ℝ)) := by
              simp
  simp_rw [hinner]
  rw [PMF.integral_eq_sum]
  simp [smul_eq_mul]

theorem innerTerminalMGF_eq
    (P : Parameters) {N : ℕ} (τ : Trajectory N) (t : ℝ) :
    ∫ τ', Real.exp (t * ((badCountPrefix τ' (N + 2) : ℕ) : ℝ))
        ∂((oneStepPMF P).map (snoc τ)).toMeasure =
      Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
        bernoulliBadMGF P.badProb t := by
  rw [← PMF.toMeasure_map
    (p := oneStepPMF P)
    (f := snoc τ)
    (hf := (measurable_from_top : Measurable (snoc τ)))]
  calc
    ∫ τ', Real.exp (t * ((badCountPrefix τ' (N + 2) : ℕ) : ℝ))
        ∂Measure.map (snoc τ) (oneStepPMF P).toMeasure
        = ∫ s, Real.exp (t * ((badCountPrefix (snoc τ s) (N + 2) : ℕ) : ℝ))
            ∂(oneStepPMF P).toMeasure := by
            exact
              MeasureTheory.integral_map
                (μ := (oneStepPMF P).toMeasure)
                (φ := snoc τ)
                (measurable_from_top : Measurable (snoc τ)).aemeasurable
                ((measurable_from_top :
                  Measurable
                    (fun τ' : Trajectory (N + 1) =>
                      Real.exp (t * ((badCountPrefix τ' (N + 2) : ℕ) : ℝ)))).aestronglyMeasurable)
    _ = ∫ s,
          Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
            Real.exp (t * badIndicator s) ∂(oneStepPMF P).toMeasure := by
            congr with s
            rw [badCountPrefix_snoc_last τ s]
            cases s <;>
              simp [badIndicator, Nat.cast_add, Real.exp_add, mul_add,
                add_comm, mul_comm]
    _ = Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
          bernoulliBadMGF P.badProb t := by
            rw [integral_const_mul]
            rw [oneStepBadIndicatorMGF_eq_bernoulliBadMGF]

/-- Terminal-step MGF recursion for the generic Bernoulli CSP path PMF. -/
theorem mgf_badCountRV_succ_last
    (P : Parameters) (N : ℕ) (t : ℝ) :
    mgf (badCountRV P (N + 1) (N + 2)) (pathMeasure P (N + 1)) t =
      mgf (badCountRV P N (N + 1)) (pathMeasure P N) t *
        bernoulliBadMGF P.badProb t := by
  change
    ∫ τ', Real.exp (t * ((badCountPrefix τ' (N + 2) : ℕ) : ℝ))
      ∂(pathPMF P (N + 1)).toMeasure =
      mgf (badCountRV P N (N + 1)) (pathMeasure P N) t *
        bernoulliBadMGF P.badProb t
  rw [pathPMF]
  rw [integral_bind_eq_sum]
  simp_rw [innerTerminalMGF_eq]
  change
    ∑ τ : Trajectory N,
        (pathPMF P N τ).toReal *
          (Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
            bernoulliBadMGF P.badProb t) =
      (∫ τ, Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ))
        ∂(pathPMF P N).toMeasure) *
        bernoulliBadMGF P.badProb t
  rw [PMF.integral_eq_sum]
  change
    ∑ τ : Trajectory N,
        (pathPMF P N τ).toReal *
          (Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
            bernoulliBadMGF P.badProb t) =
      (∑ τ : Trajectory N,
        (pathPMF P N τ).toReal •
          Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ))) *
        bernoulliBadMGF P.badProb t
  have hleft :
      ∑ τ : Trajectory N,
          (pathPMF P N τ).toReal *
            (Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ)) *
              bernoulliBadMGF P.badProb t)
        =
      (∑ τ : Trajectory N,
          (pathPMF P N τ).toReal *
            Real.exp (t * ((badCountPrefix τ (N + 1) : ℕ) : ℝ))) *
        bernoulliBadMGF P.badProb t := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro τ _hτ
    ring
  rw [hleft]
  simp [smul_eq_mul]

/-- Exact Bernoulli-product MGF for the active-prefix bad count. -/
theorem mgf_badCountRV_eq_bernoulliBadMGF_pow
    (P : Parameters) (N : ℕ) (t : ℝ) :
    ∀ ⦃n : ℕ⦄, n ≤ N + 1 →
      mgf (badCountRV P N n) (pathMeasure P N) t =
        bernoulliBadMGF P.badProb t ^ n := by
  induction N with
  | zero =>
      intro n hn
      interval_cases n
      · rw [pow_zero]
        rw [ProbabilityTheory.mgf]
        simp [badCountRV, badCountPrefix]
      · change
          ∫ τ, Real.exp (t * ((badCountPrefix τ 1 : ℕ) : ℝ))
            ∂(pathPMF P 0).toMeasure =
            bernoulliBadMGF P.badProb t ^ 1
        rw [pow_one]
        change
          ∫ τ, Real.exp (t * ((badCountPrefix τ 1 : ℕ) : ℝ))
            ∂((oneStepPMF P).map singletonTraj).toMeasure =
            bernoulliBadMGF P.badProb t
        rw [← PMF.toMeasure_map
          (p := oneStepPMF P)
          (f := singletonTraj)
          (hf := (measurable_from_top : Measurable singletonTraj))]
        calc
          ∫ τ, Real.exp (t * ((badCountPrefix τ 1 : ℕ) : ℝ))
              ∂Measure.map singletonTraj (oneStepPMF P).toMeasure
              =
            ∫ s, Real.exp (t * ((badCountPrefix (singletonTraj s) 1 : ℕ) : ℝ))
              ∂(oneStepPMF P).toMeasure := by
              exact
                MeasureTheory.integral_map
                  (μ := (oneStepPMF P).toMeasure)
                  (φ := singletonTraj)
                  (measurable_from_top : Measurable singletonTraj).aemeasurable
                  ((measurable_from_top :
                    Measurable
                      (fun τ : Trajectory 0 =>
                        Real.exp (t * ((badCountPrefix τ 1 : ℕ) : ℝ)))).aestronglyMeasurable)
          _ = ∫ s, Real.exp (t * badIndicator s) ∂(oneStepPMF P).toMeasure := by
              congr with s
              cases s <;> simp [badIndicator, singletonTraj, badCountPrefix, outcomeAt]
          _ = bernoulliBadMGF P.badProb t := oneStepBadIndicatorMGF_eq_bernoulliBadMGF P t
  | succ N ih =>
      intro n hn
      by_cases hprefix : n ≤ N + 1
      · rw [mgf_badCountRV_succ_of_le P hprefix t]
        exact ih hprefix
      · have hnlast : n = N + 2 := by
          exact Nat.le_antisymm hn (Nat.succ_le_of_lt (lt_of_not_ge hprefix))
        subst hnlast
        rw [mgf_badCountRV_succ_last P N t]
        rw [ih (Nat.le_refl (N + 1))]
        simpa using (pow_succ (bernoulliBadMGF P.badProb t) (N + 1)).symm

/-- Closed Bernoulli MGF witness generated directly by the generic path PMF. -/
theorem hasBernoulliMGFUpperBound_pathPMF
    (P : Parameters) (N : ℕ) (t : ℝ) :
    ∀ ⦃n : ℕ⦄, n ≤ N + 1 →
      mgf (badCountRV P N n) (pathMeasure P N) t ≤
        bernoulliBadMGF P.badProb t ^ n := by
  intro n hn
  rw [mgf_badCountRV_eq_bernoulliBadMGF_pow P N t hn]

end

end Persistence.BernoulliCSPPathMeasure
