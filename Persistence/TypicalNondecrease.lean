import Persistence.CoarseTotalProduction

/-!
Typical Nondecrease — Probabilistic / Expectation Interface
典型的非減少のための probabilistic / expectation interface

This module does **not** yet build a full probability space. Instead, it
formalizes the minimal expectation-level interface needed for a
"typical nondecrease" theorem.

The interface is submartingale-like:

* `expectedCumulative n` is the expected cumulative quantity at time `n`
* `expectedIncrement t` is the expected one-step drift at time `t`
* `expected_succ` states the discrete evolution law

If every expected increment is nonnegative, then the expected cumulative
quantity is monotone.

This is the conservative expectation layer that can later be instantiated by
actual stochastic dynamics, random initial data, or randomized constraints.
-/

namespace Persistence.TypicalNondecrease

noncomputable section

/-- Minimal expectation interface for a cumulative process.
It is intentionally agnostic about the underlying probability space. -/
structure ExpectedProcess where
  expectedCumulative : ℕ → ℝ
  expectedIncrement : ℕ → ℝ
  expected_succ :
    ∀ t, expectedCumulative (t + 1) =
      expectedCumulative t + expectedIncrement t

/-- Expected nonnegative drift: the expectation of each one-step increment is
nonnegative. -/
def ExpectedNonnegativeDrift (E : ExpectedProcess) : Prop :=
  ∀ t, 0 ≤ E.expectedIncrement t

theorem expectedCumulative_le_succ
    (E : ExpectedProcess) (hdrift : ExpectedNonnegativeDrift E) (t : ℕ) :
    E.expectedCumulative t ≤ E.expectedCumulative (t + 1) := by
  rw [E.expected_succ t]
  have hinc : 0 ≤ E.expectedIncrement t := hdrift t
  linarith

/-- Nonnegative expected drift implies monotonicity of the expected cumulative process. -/
theorem expectedCumulative_monotone
    (E : ExpectedProcess) (hdrift : ExpectedNonnegativeDrift E) :
    Monotone E.expectedCumulative := by
  intro m n hmn
  induction hmn with
  | refl =>
      rfl
  | @step n hle ih =>
      exact le_trans ih (expectedCumulative_le_succ E hdrift n)

/-- A lightweight interface specialized to total production:
the quantity under expectation is intended to be cumulative total production `Σ_n`. -/
abbrev ExpectedTotalProduction := ExpectedProcess

/-- Under pointwise equality of expected cumulative trajectories, monotonicity
transfers from one process to another. This is the expectation-level bridge
used after coarse-graining invariance has been established. -/
theorem expectedCumulative_monotone_of_pointwise_eq
    (E₁ E₂ : ExpectedProcess)
    (heq : ∀ n, E₂.expectedCumulative n = E₁.expectedCumulative n)
    (hmono : Monotone E₁.expectedCumulative) :
    Monotone E₂.expectedCumulative := by
  intro m n hmn
  rw [heq m, heq n]
  exact hmono hmn

/-- Coarse expected total production is monotone whenever it coincides pointwise
with a monotone micro expected total production process. -/
theorem coarse_expectedTotalProduction_monotone_of_pointwise_eq
    (Emicro Ecoarse : ExpectedTotalProduction)
    (heq : ∀ n, Ecoarse.expectedCumulative n = Emicro.expectedCumulative n)
    (hdrift : ExpectedNonnegativeDrift Emicro) :
    Monotone Ecoarse.expectedCumulative := by
  apply expectedCumulative_monotone_of_pointwise_eq Emicro Ecoarse heq
  exact expectedCumulative_monotone Emicro hdrift

end

end Persistence.TypicalNondecrease
