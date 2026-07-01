import Persistence.ProbabilityConnection

/-!
Martingale / Supermartingale Drift Interface
martingale / supermartingale 型の drift 条件

This module adds a conservative drift-language on top of
`ProbabilityConnection`.

It does **not** formalize full conditional-expectation martingales. Instead, it
captures the expectation-level drift conditions that are most useful for the
survival program:

* lower drift bounds
* upper drift bounds
* submartingale-like expected nonnegative drift
* supermartingale-like expected nonpositive drift
* martingale-like zero expected drift

These conditions are enough to prove monotonicity, antitonicity, and explicit
finite-time expectation bounds for cumulative quantities.
-/

namespace Persistence.MartingaleDrift

open Persistence.ProbabilityConnection

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Lower bound on the expected one-step drift. -/
def ExpectedDriftLowerBound
    (S : StochasticExpectedProcess (μ := μ)) (d : ℕ → ℝ) : Prop :=
  ∀ t, d t ≤ S.toExpectedProcess.expectedIncrement t

/-- Upper bound on the expected one-step drift. -/
def ExpectedDriftUpperBound
    (S : StochasticExpectedProcess (μ := μ)) (u : ℕ → ℝ) : Prop :=
  ∀ t, S.toExpectedProcess.expectedIncrement t ≤ u t

/-- Submartingale-like drift condition at the expectation level:
each expected increment is nonnegative. -/
def SubmartingaleLike
    (S : StochasticExpectedProcess (μ := μ)) : Prop :=
  ExpectedDriftLowerBound (μ := μ) S (fun _ => 0)

/-- Supermartingale-like drift condition at the expectation level:
each expected increment is nonpositive. -/
def SupermartingaleLike
    (S : StochasticExpectedProcess (μ := μ)) : Prop :=
  ExpectedDriftUpperBound (μ := μ) S (fun _ => 0)

/-- Martingale-like drift condition at the expectation level:
each expected increment vanishes. -/
def MartingaleLike
    (S : StochasticExpectedProcess (μ := μ)) : Prop :=
  ∀ t, S.toExpectedProcess.expectedIncrement t = 0

theorem expectedNonnegativeDrift_of_submartingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hsub : SubmartingaleLike (μ := μ) S) :
    Persistence.TypicalNondecrease.ExpectedNonnegativeDrift S.toExpectedProcess := by
  intro t
  exact hsub t

theorem expectedCumulative_monotone_of_submartingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hsub : SubmartingaleLike (μ := μ) S) :
    Monotone S.toExpectedProcess.expectedCumulative := by
  exact Persistence.TypicalNondecrease.expectedCumulative_monotone
    _ (expectedNonnegativeDrift_of_submartingaleLike S hsub)

theorem expectedCumulative_succ_le_of_supermartingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hsuper : SupermartingaleLike (μ := μ) S) (t : ℕ) :
    S.toExpectedProcess.expectedCumulative (t + 1) ≤
      S.toExpectedProcess.expectedCumulative t := by
  rw [S.toExpectedProcess.expected_succ t]
  have hinc : S.toExpectedProcess.expectedIncrement t ≤ 0 := hsuper t
  linarith

theorem expectedCumulative_antitone_of_supermartingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hsuper : SupermartingaleLike (μ := μ) S) :
    Antitone S.toExpectedProcess.expectedCumulative := by
  intro m n hmn
  induction hmn with
  | refl =>
      rfl
  | @step n hle ih =>
      exact le_trans (expectedCumulative_succ_le_of_supermartingaleLike S hsuper n) ih

theorem submartingaleLike_of_martingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hmg : MartingaleLike (μ := μ) S) :
    SubmartingaleLike (μ := μ) S := by
  intro t
  rw [hmg t]

theorem supermartingaleLike_of_martingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hmg : MartingaleLike (μ := μ) S) :
    SupermartingaleLike (μ := μ) S := by
  intro t
  rw [hmg t]

theorem expectedCumulative_eq_initial_of_martingaleLike
    (S : StochasticExpectedProcess (μ := μ))
    (hmg : MartingaleLike (μ := μ) S) :
    ∀ n,
      S.toExpectedProcess.expectedCumulative n =
        S.toExpectedProcess.expectedCumulative 0
  | 0 => rfl
  | n + 1 => by
      rw [S.toExpectedProcess.expected_succ n]
      rw [expectedCumulative_eq_initial_of_martingaleLike S hmg n, hmg n]
      ring

theorem expectedCumulative_lower_bound_of_expectedDriftLowerBound
    (S : StochasticExpectedProcess (μ := μ)) {d : ℕ → ℝ}
    (hdrift : ExpectedDriftLowerBound (μ := μ) S d) :
    ∀ n,
      S.toExpectedProcess.expectedCumulative 0 + Finset.sum (Finset.range n) d ≤
        S.toExpectedProcess.expectedCumulative n
  | 0 => by
      simp
  | n + 1 => by
      rw [Finset.sum_range_succ, S.toExpectedProcess.expected_succ n]
      have ih := expectedCumulative_lower_bound_of_expectedDriftLowerBound S hdrift n
      have hstep := hdrift n
      linarith

theorem expectedCumulative_upper_bound_of_expectedDriftUpperBound
    (S : StochasticExpectedProcess (μ := μ)) {u : ℕ → ℝ}
    (hdrift : ExpectedDriftUpperBound (μ := μ) S u) :
    ∀ n,
      S.toExpectedProcess.expectedCumulative n ≤
        S.toExpectedProcess.expectedCumulative 0 + Finset.sum (Finset.range n) u
  | 0 => by
      simp
  | n + 1 => by
      rw [Finset.sum_range_succ, S.toExpectedProcess.expected_succ n]
      have ih := expectedCumulative_upper_bound_of_expectedDriftUpperBound S hdrift n
      have hstep := hdrift n
      linarith

end

end Persistence.MartingaleDrift
