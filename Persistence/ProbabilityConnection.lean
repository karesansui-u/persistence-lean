import Mathlib.Probability.Independence.Integration
import Persistence.ResourceBoundedDynamics

/-!
Probability Connection — From Actual Probability Spaces to Expected Processes
actual probability space への接続

This module connects the abstract expectation interface from
`Persistence.TypicalNondecrease` to an actual probability space.

The idea is minimal:

* start with a probability space `(Ω, μ)`
* model a cumulative real-valued stochastic process `Xₙ`
* model one-step increments `Δₙ`
* assume the recursion `Xₙ₊₁ = Xₙ + Δₙ` almost everywhere

Then the sequence of expectations forms an `ExpectedProcess`, and if the
increments are almost surely nonnegative, the expected cumulative quantity is
monotone.

This is the first actual-probability instantiation of the previously abstract
`ExpectedProcess` layer.
-/

open MeasureTheory

namespace Persistence.ProbabilityConnection

open Persistence.TypicalNondecrease

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- A real-valued cumulative stochastic process together with its one-step
increment process on a probability space. -/
structure StochasticExpectedProcess where
  cumulativeRV : ℕ → Ω → ℝ
  incrementRV : ℕ → Ω → ℝ
  integrable_cumulative : ∀ n, Integrable (cumulativeRV n) μ
  integrable_increment : ∀ n, Integrable (incrementRV n) μ
  cumulative_succ_ae :
    ∀ t, cumulativeRV (t + 1) =ᵐ[μ] fun ω => cumulativeRV t ω + incrementRV t ω

/-- Convert an actual stochastic process on `(Ω, μ)` into the abstract
expectation-level process used by `TypicalNondecrease`. -/
def StochasticExpectedProcess.toExpectedProcess
    (S : StochasticExpectedProcess (μ := μ)) : ExpectedProcess where
  expectedCumulative n := ∫ ω, S.cumulativeRV n ω ∂μ
  expectedIncrement t := ∫ ω, S.incrementRV t ω ∂μ
  expected_succ t := by
    calc
      ∫ ω, S.cumulativeRV (t + 1) ω ∂μ
          = ∫ ω, (S.cumulativeRV t ω + S.incrementRV t ω) ∂μ := by
              exact integral_congr_ae (S.cumulative_succ_ae t)
      _ = (∫ ω, S.cumulativeRV t ω ∂μ) + ∫ ω, S.incrementRV t ω ∂μ := by
            exact integral_add (S.integrable_cumulative t) (S.integrable_increment t)

/-- Almost sure nonnegativity of the one-step increment process. -/
def AENonnegativeIncrement
    (S : StochasticExpectedProcess (μ := μ)) : Prop :=
  ∀ t, 0 ≤ᵐ[μ] S.incrementRV t

/-- Almost sure nonnegative increments imply nonnegative expected drift. -/
theorem toExpectedProcess_has_nonnegative_drift
    (S : StochasticExpectedProcess (μ := μ))
    (hinc : AENonnegativeIncrement (μ := μ) S) :
    ExpectedNonnegativeDrift S.toExpectedProcess := by
  intro t
  change 0 ≤ ∫ ω, S.incrementRV t ω ∂μ
  exact integral_nonneg_of_ae (hinc t)

/-- Therefore the expected cumulative quantity is monotone. -/
theorem expectedCumulative_monotone_of_ae_nonnegative_increment
    (S : StochasticExpectedProcess (μ := μ))
    (hinc : AENonnegativeIncrement (μ := μ) S) :
    Monotone S.toExpectedProcess.expectedCumulative := by
  exact expectedCumulative_monotone _ (toExpectedProcess_has_nonnegative_drift S hinc)

/-- Specialization of the previous interface to total production:
this is the actual-probability version of expected total production. -/
abbrev StochasticTotalProductionProcess := StochasticExpectedProcess (μ := μ)

theorem expectedTotalProduction_monotone_of_ae_nonnegative_increment
    (S : StochasticTotalProductionProcess (μ := μ))
    (hinc : AENonnegativeIncrement (μ := μ) S) :
    Monotone S.toExpectedProcess.expectedCumulative :=
  expectedCumulative_monotone_of_ae_nonnegative_increment S hinc

section ProbabilitySpace

variable [IsProbabilityMeasure μ]

/-- On an actual probability space, the expectation of a constant is that constant. -/
theorem expected_constant_eq (c : ℝ) :
    ∫ _ : Ω, c ∂μ = c := by
  simp [MeasureTheory.integral_const]

end ProbabilitySpace

end

end Persistence.ProbabilityConnection
