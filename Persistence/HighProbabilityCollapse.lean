import Persistence.StochasticCollapseTimeBound

/-!
High-Probability Collapse
collapse の高確率版 / large-deviation 版

This module packages the stochastic collapse criterion into an explicit
high-probability / large-deviation interface.

The key idea is conservative:

* do not try to prove measurability of the threshold event from the process;
* instead, let the user provide a measurable event `E`;
* if threshold crossing holds on `E`, then collapse holds on `E`;
* therefore any failure bound attached to `E` transfers unchanged to the
  collapse statement.
-/

open MeasureTheory

namespace Persistence.HighProbabilityCollapse

open Persistence.ProbabilityConnection
open Persistence.StochasticCollapseTimeBound

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- A measurable event whose failure probability is bounded by `ε`. -/
def EventWithFailureBound (E : Set Ω) (ε : ENNReal) : Prop :=
  MeasurableSet E ∧ μ (Eᶜ) ≤ ε

/-- Threshold crossing on a given event. -/
def ThresholdCrossingOnEvent
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ : ℝ) (E : Set Ω) : Prop :=
  ∀ ω ∈ E, -Real.log θ ≤ S.cumulativeRV n ω

/-- Collapse on a given event. -/
def CollapseOnEvent
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ : ℝ) (E : Set Ω) : Prop :=
  ∀ ω ∈ E, survivalRatioRV S n ω ≤ θ

/-- Threshold crossing with failure bound `ε`. -/
def ThresholdCrossingWithFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ : ℝ) (ε : ENNReal) : Prop :=
  ∃ E : Set Ω,
    EventWithFailureBound (μ := μ) E ε ∧
      ThresholdCrossingOnEvent (μ := μ) S n θ E

/-- Collapse with failure bound `ε`. -/
def CollapseWithFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ : ℝ) (ε : ENNReal) : Prop :=
  ∃ E : Set Ω,
    EventWithFailureBound (μ := μ) E ε ∧
      CollapseOnEvent (μ := μ) S n θ E

/-- Pointwise threshold crossing on an event implies pointwise collapse on the
same event. -/
theorem collapseOnEvent_of_thresholdCrossingOnEvent
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ)
    {E : Set Ω}
    (hE : ThresholdCrossingOnEvent (μ := μ) S n θ E) :
    CollapseOnEvent (μ := μ) S n θ E := by
  intro ω hω
  dsimp [ThresholdCrossingOnEvent, CollapseOnEvent, survivalRatioRV]
  have hth : -Real.log θ ≤ S.cumulativeRV n ω := hE ω hω
  have hexp : Real.exp (-S.cumulativeRV n ω) ≤ Real.exp (Real.log θ) := by
    exact (Real.exp_le_exp).2 (by linarith)
  simpa [Real.exp_log hθ] using hexp

/-- Failure-bound transfer: any event-level threshold crossing bound gives the
same event-level collapse bound. -/
theorem collapseWithFailureBound_of_thresholdCrossingWithFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ)
    {ε : ENNReal}
    (hth : ThresholdCrossingWithFailureBound (μ := μ) S n θ ε) :
    CollapseWithFailureBound (μ := μ) S n θ ε := by
  rcases hth with ⟨E, hE, hcross⟩
  refine ⟨E, hE, collapseOnEvent_of_thresholdCrossingOnEvent S n hθ hcross⟩

/-- Exponential failure profile `exp(-c n)`, packaged as an `ENNReal` bound. -/
def exponentialFailureBound (c : ℝ) (n : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-c * (n : ℝ)))

/-- Threshold crossing with exponential / large-deviation style failure bound. -/
def ThresholdCrossingWithExponentialFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ c : ℝ) : Prop :=
  ThresholdCrossingWithFailureBound (μ := μ) S n θ (exponentialFailureBound c n)

/-- Collapse with exponential / large-deviation style failure bound. -/
def CollapseWithExponentialFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ) (θ c : ℝ) : Prop :=
  CollapseWithFailureBound (μ := μ) S n θ (exponentialFailureBound c n)

/-- Large-deviation transfer: exponential threshold-crossing bounds imply
exponential collapse bounds with the same rate function. -/
theorem collapseWithExponentialFailureBound_of_thresholdCrossingWithExponentialFailureBound
    (S : StochasticExpectedProcess (μ := μ)) (n : ℕ)
    {θ c : ℝ} (hθ : 0 < θ)
    (hth : ThresholdCrossingWithExponentialFailureBound (μ := μ) S n θ c) :
    CollapseWithExponentialFailureBound (μ := μ) S n θ c :=
  collapseWithFailureBound_of_thresholdCrossingWithFailureBound S n hθ hth

end

end Persistence.HighProbabilityCollapse
