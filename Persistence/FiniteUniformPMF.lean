import Persistence.FiniteUniformRatio
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite Uniform PMF Bridge

This module is the first small PMF layer above `FiniteUniformRatio`.

For a finite nonempty type `α`, Mathlib's `PMF.uniformOfFintype α` assigns the
uniform PMF.  This file proves that the PMF mass of an event, converted to a
real number, equals the finite cardinality ratio `#event / #space` named by
`FiniteUniformRatio`.

## What this proves

`uniformOfFintype` realizes `finiteUniformRatio` as a genuine PMF event mass.

## What this does not prove

No random matrix is introduced here.  There is no independence theorem,
rank-failure probability theorem, finite-block coding theorem, or Shannon
achievability theorem.  This is only the generic finite-uniform PMF bridge.
-/

namespace Persistence.FiniteUniformPMF

open Persistence.FiniteUniformRatio

noncomputable section

/-- Mathlib's uniform PMF on a finite nonempty type, named locally for the SPT
finite-ratio bridge. -/
def uniformPMF (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  PMF.uniformOfFintype α

/-- The uniform PMF event mass is the corresponding finite cardinality ratio,
as an `ENNReal` identity. -/
theorem uniformPMF_event_toOuterMeasure_eq
    (α : Type*) [Fintype α] [Nonempty α] (p : α → Prop)
    [Fintype {x // p x}] :
    (uniformPMF α).toOuterMeasure {x : α | p x} =
      (eventCount α p : ENNReal) / (totalCount α : ENNReal) := by
  letI : Fintype ({x : α | p x} : Set α) :=
    inferInstanceAs (Fintype {x // p x})
  unfold uniformPMF eventCount totalCount
  simpa using
    (PMF.toOuterMeasure_uniformOfFintype_apply
      (α := α) (s := {x : α | p x}))

/-- Real-valued form: the uniform PMF event mass realizes
`finiteUniformRatio`. -/
theorem uniformPMF_event_toReal_eq_finiteUniformRatio
    (α : Type*) [Fintype α] [Nonempty α] (p : α → Prop)
    [Fintype {x // p x}] :
    ((uniformPMF α).toOuterMeasure {x : α | p x}).toReal =
      finiteUniformRatio α p := by
  rw [uniformPMF_event_toOuterMeasure_eq α p]
  unfold finiteUniformRatio eventCount totalCount
  simp [ENNReal.toReal_div, ENNReal.toReal_natCast]

end

end Persistence.FiniteUniformPMF
