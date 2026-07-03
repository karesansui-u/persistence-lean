import Persistence.StructuralPersistenceG1CurrentViewExtensionalScopeWitness

/-!
# Small Nonvacuity Witness

This file strengthens the existing `VisibleScopeWitness`: that witness already
shows a nonconstant current-view scope, but its `maintains` predicate is exactly
the viable boundary readout.  Here the maintained target is separated from the
boundary readout:

```text
viable = {ready}  ⊊  maintains = {ready, degraded}  ⊊  all states.
```

This is a kernel-level integration test for the semantic interface, not a
domain validation theorem.
-/

namespace Persistence.StructuralPersistence
namespace Examples.SmallWitness

open VisibleScopeWitness

/--
Separated target-realization predicate for the visible three-state machine.

`ready` and `degraded` still realize the service target; `failed` does not.
This deliberately does not define realization by calling the boundary readout.
-/
def maintains : VisibleState -> VisibleTarget -> Prop
  | .failed, _ => False
  | _, _ => True

/--
Semantic calculation whose realization predicate is strictly wider than the
viable boundary region and strictly smaller than all states.
-/
def separatedCalculation :
    AlternativePersistenceCalculation VisibleState VisibleTarget where
  maintainedTarget := VisibleTarget.service
  maintains := maintains
  boundaryReadout := process.readout
  viable_implies_maintained := by
    intro state h
    cases state <;> simp [process, readout, maintains] at h ⊢

/-- The separated calculation has a viable state. -/
theorem separatedCalculation_nontrivial :
    separatedCalculation.NontrivialReadout where
  viable_state := ⟨VisibleState.ready, rfl⟩

/--
Strict lower witness: `degraded` still realizes the maintained target but is
not viable.  Thus the viable region is strictly contained in realization.
-/
theorem maintains_nonviable_state :
    ∃ s,
      separatedCalculation.maintains s
          separatedCalculation.maintainedTarget ∧
        separatedCalculation.boundaryReadout s ≠ BoundaryStatus.viable := by
  exact ⟨VisibleState.degraded, by simp [separatedCalculation, maintains, process, readout]⟩

/--
Strict upper witness: `failed` does not realize the maintained target.  Thus
realization is strictly smaller than the whole state space.
-/
theorem not_maintains_state :
    ∃ s,
      ¬ separatedCalculation.maintains s
          separatedCalculation.maintainedTarget := by
  exact ⟨VisibleState.failed, by simp [separatedCalculation, maintains]⟩

/--
The raw viable region is nonempty, using the same visible state as the original
scope witness.
-/
theorem stateViableRegion_nonempty :
    separatedCalculation.stateViableRegion.Nonempty :=
  AlternativePersistenceCalculation.nontrivial_stateViableRegion_nonempty
    separatedCalculation separatedCalculation_nontrivial

/--
The concrete visible process satisfies one-step current-view extensionality.

This theorem is stated here so the witness exposes the Prop-side scope used by
the G1 finite-prefix pipeline, rather than merely constructing the process.
-/
theorem currentViewOneStepExtensional :
    CurrentViewOneStepExtensional process :=
  VisibleScopeWitness.currentViewOneStepExtensional

/--
The concrete witness enters the trace-log extensionality pipeline through the
one-step route.

This deliberately applies `currentViewTraceLogExtensional_of_oneStepExtensional`
instead of using the existing injectivity-derived trace-log theorem.
-/
theorem currentViewTraceLogExtensional_via_oneStep :
    CurrentViewTraceLogExtensional process :=
  currentViewTraceLogExtensional_of_oneStepExtensional
    process currentViewOneStepExtensional

/--
Combined nonvacuity summary: the witness has a viable state, a nonviable state
that still realizes the target, a state that does not realize the target, and
it enters the trace-log extensionality pipeline via one-step extensionality.
-/
theorem separated_witness_summary :
    separatedCalculation.stateViableRegion.Nonempty ∧
      (∃ s,
        separatedCalculation.maintains s
            separatedCalculation.maintainedTarget ∧
          separatedCalculation.boundaryReadout s ≠ BoundaryStatus.viable) ∧
      (∃ s,
        ¬ separatedCalculation.maintains s
            separatedCalculation.maintainedTarget) ∧
      CurrentViewOneStepExtensional process ∧
      CurrentViewTraceLogExtensional process := by
  exact
    ⟨stateViableRegion_nonempty,
      maintains_nonviable_state,
      not_maintains_state,
      currentViewOneStepExtensional,
      currentViewTraceLogExtensional_via_oneStep⟩

end Examples.SmallWitness
end Persistence.StructuralPersistence
