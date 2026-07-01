import Persistence.HighProbabilityCollapse
import Persistence.MartingaleDrift

/-!
Concentration Inequality Interface
concentration inequality の抽象 interface

This module adds a conservative abstraction layer for concentration
inequalities.

The interface is event-based rather than inequality-specific:

* a deterministic center trajectory `center n`
* a family of good events indexed by time `n` and deviation budget `r`
* on each good event, the cumulative process stays above `center n - r`
* the complement of the good event has an explicit failure bound

From this alone, one can derive high-probability threshold crossing and hence
high-probability collapse bounds.

An additional large-deviation wrapper records the common case where the failure
bound has exponential form.
-/

namespace Persistence.ConcentrationInterface

open Persistence.ProbabilityConnection
open Persistence.HighProbabilityCollapse
open Persistence.MartingaleDrift

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Generic exponential / large-deviation failure profile. -/
def largeDeviationFailureBound
    (rate : ℕ → ℝ → ℝ) (n : ℕ) (r : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-rate n r))

/-- Abstract lower-tail concentration around a deterministic center trajectory. -/
structure LowerDeviationConcentration
    (S : StochasticExpectedProcess (μ := μ)) where
  center : ℕ → ℝ
  goodEvent : ℕ → ℝ → Set Ω
  measurable_goodEvent : ∀ n r, MeasurableSet (goodEvent n r)
  lower_bound_on_good :
    ∀ n r ω, ω ∈ goodEvent n r → center n - r ≤ S.cumulativeRV n ω
  failureBound : ℕ → ℝ → ENNReal
  failure_bound : ∀ n r, μ ((goodEvent n r)ᶜ) ≤ failureBound n r

/-- Specialization where the deterministic center trajectory is the expectation
of the cumulative process. -/
structure ExpectationLowerConcentration
    (S : StochasticExpectedProcess (μ := μ))
    extends LowerDeviationConcentration (μ := μ) S where
  center_eq_expected : center = S.toExpectedProcess.expectedCumulative

/-- Large-deviation specialization: the failure profile has exponential form. -/
structure LargeDeviationLowerConcentration
    (S : StochasticExpectedProcess (μ := μ))
    extends LowerDeviationConcentration (μ := μ) S where
  rateFn : ℕ → ℝ → ℝ
  failure_eq : ∀ n r, failureBound n r = largeDeviationFailureBound rateFn n r

theorem thresholdCrossingWithFailureBound_of_center_margin
    {S : StochasticExpectedProcess (μ := μ)}
    (C : LowerDeviationConcentration (μ := μ) S)
    {n : ℕ} {θ r : ℝ}
    (hmargin : -Real.log θ ≤ C.center n - r) :
    ThresholdCrossingWithFailureBound (μ := μ) S n θ (C.failureBound n r) := by
  refine ⟨C.goodEvent n r, ?_, ?_⟩
  · exact ⟨C.measurable_goodEvent n r, C.failure_bound n r⟩
  · intro ω hω
    have hgood := C.lower_bound_on_good n r ω hω
    linarith

theorem collapseWithFailureBound_of_center_margin
    {S : StochasticExpectedProcess (μ := μ)}
    (C : LowerDeviationConcentration (μ := μ) S)
    {n : ℕ} {θ r : ℝ} (hθ : 0 < θ)
    (hmargin : -Real.log θ ≤ C.center n - r) :
    CollapseWithFailureBound (μ := μ) S n θ (C.failureBound n r) := by
  exact collapseWithFailureBound_of_thresholdCrossingWithFailureBound S n hθ
    (thresholdCrossingWithFailureBound_of_center_margin C hmargin)

theorem thresholdCrossingWithFailureBound_of_expected_center
    {S : StochasticExpectedProcess (μ := μ)}
    (C : ExpectationLowerConcentration (μ := μ) S)
    {n : ℕ} {θ r : ℝ}
    (hmargin : -Real.log θ ≤ S.toExpectedProcess.expectedCumulative n - r) :
    ThresholdCrossingWithFailureBound (μ := μ) S n θ (C.failureBound n r) := by
  have hmargin' : -Real.log θ ≤ C.center n - r := by
    simpa [C.center_eq_expected] using hmargin
  exact thresholdCrossingWithFailureBound_of_center_margin C.toLowerDeviationConcentration hmargin'

theorem collapseWithFailureBound_of_expected_center
    {S : StochasticExpectedProcess (μ := μ)}
    (C : ExpectationLowerConcentration (μ := μ) S)
    {n : ℕ} {θ r : ℝ} (hθ : 0 < θ)
    (hmargin : -Real.log θ ≤ S.toExpectedProcess.expectedCumulative n - r) :
    CollapseWithFailureBound (μ := μ) S n θ (C.failureBound n r) := by
  exact collapseWithFailureBound_of_thresholdCrossingWithFailureBound S n hθ
    (thresholdCrossingWithFailureBound_of_expected_center C hmargin)

theorem collapseWithLargeDeviationBound_of_center_margin
    {S : StochasticExpectedProcess (μ := μ)}
    (C : LargeDeviationLowerConcentration (μ := μ) S)
    {n : ℕ} {θ r : ℝ} (hθ : 0 < θ)
    (hmargin : -Real.log θ ≤ C.center n - r) :
    CollapseWithFailureBound (μ := μ) S n θ
      (largeDeviationFailureBound C.rateFn n r) := by
  rcases collapseWithFailureBound_of_center_margin C.toLowerDeviationConcentration hθ hmargin with
    ⟨E, hE, hcollapse⟩
  refine ⟨E, ?_, hcollapse⟩
  rcases hE with ⟨hmeas, hfail⟩
  refine ⟨hmeas, ?_⟩
  simpa [C.failure_eq n r] using hfail

theorem collapseWithLargeDeviationBound_of_expected_center
    {S : StochasticExpectedProcess (μ := μ)}
    (C : ExpectationLowerConcentration (μ := μ) S)
    (L : LargeDeviationLowerConcentration (μ := μ) S)
    (hcenter :
      C.toLowerDeviationConcentration.center =
        L.toLowerDeviationConcentration.center)
    {n : ℕ} {θ r : ℝ} (hθ : 0 < θ)
    (hmargin : -Real.log θ ≤ S.toExpectedProcess.expectedCumulative n - r) :
    CollapseWithFailureBound (μ := μ) S n θ
      (largeDeviationFailureBound L.rateFn n r) := by
  have hmargin' : -Real.log θ ≤ L.center n - r := by
    simpa [← C.center_eq_expected, hcenter]
      using hmargin
  exact collapseWithLargeDeviationBound_of_center_margin L hθ hmargin'

end

end Persistence.ConcentrationInterface
