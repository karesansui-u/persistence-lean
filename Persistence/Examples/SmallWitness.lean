import Persistence.StructuralPersistenceG1CurrentViewExtensionalScopeWitness

/-!
# Small Nonvacuity Witness

This file strengthens the existing `VisibleScopeWitness`: that witness already
shows a nonconstant current-view scope, but its `maintains` predicate is exactly
the viable boundary readout.  The first witness below separates the maintained
target from the viable boundary region:

```text
viable = {ready}  ⊊  maintains = {ready, degraded}  ⊊  all states.
```

The second witness adds hidden semantic states with the same current
view/readout but different maintained-target realization, while keeping the
one-step response state-dependent.

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

/-!
Four-state hidden semantic witness.

The `hiddenMaintained` and `hiddenLost` states have the same current
view/readout, but only `hiddenMaintained` realizes the maintained target.  This
shows that maintained-target realization can carry semantic information not
recoverable from the current boundary readout alone.
-/
namespace HiddenSemanticWitness

inductive HiddenState where
  | ready
  | hiddenMaintained
  | hiddenLost
  | failed
  deriving DecidableEq, Repr

inductive HiddenAction where
  | repair
  | stress
  deriving DecidableEq, Repr

inductive HiddenObservation where
  | readyView
  | hiddenView
  | failedView
  deriving DecidableEq, Repr

inductive HiddenTarget where
  | service
  deriving DecidableEq, Repr

/-- Observable view forgets the semantic difference between the hidden states. -/
def observe : HiddenState -> HiddenObservation
  | .ready => .readyView
  | .hiddenMaintained => .hiddenView
  | .hiddenLost => .hiddenView
  | .failed => .failedView

/-- Boundary readout also forgets the semantic difference between hidden states. -/
def readout : HiddenState -> BoundaryStatus
  | .ready => .viable
  | .hiddenMaintained => .stopped
  | .hiddenLost => .stopped
  | .failed => .collapsed

/--
State-dependent action dynamics: collapse is absorbing under repair, so the
one-step response is not a constant function of the action.  The two hidden
same-current-view states still have equal one-step responses, which is the
exact content of the one-step extensionality scope.
-/
def step : HiddenState -> HiddenAction -> HiddenState
  | .failed, .repair => .failed
  | _, .repair => .ready
  | _, .stress => .failed

/-- Observational process for the hidden semantic witness. -/
def process :
    ObservationalPersistenceProcess
      HiddenState HiddenAction HiddenObservation where
  observe := observe
  step := step
  readout := readout

/--
Maintained-target realization is semantic, not defined by boundary/readout.

`ready` and `hiddenMaintained` realize the service target; `hiddenLost` and
`failed` do not.
-/
def maintains : HiddenState -> HiddenTarget -> Prop
  | .ready, _ => True
  | .hiddenMaintained, _ => True
  | .hiddenLost, _ => False
  | .failed, _ => False

/--
Semantic calculation for the hidden witness.

The viable boundary region is still contained in maintained-target
realization, but realization is neither the viable readout nor a function of
the full current readout.
-/
def calculation :
    AlternativePersistenceCalculation HiddenState HiddenTarget where
  maintainedTarget := HiddenTarget.service
  maintains := maintains
  boundaryReadout := process.readout
  viable_implies_maintained := by
    intro state h
    cases state <;> simp [process, readout, maintains] at h ⊢

/-- The hidden calculation has a viable state. -/
theorem calculation_nontrivial :
    calculation.NontrivialReadout where
  viable_state := ⟨HiddenState.ready, rfl⟩

/--
Strict lower witness: `hiddenMaintained` realizes the target but is not viable.
-/
theorem maintains_nonviable_state :
    ∃ s,
      calculation.maintains s calculation.maintainedTarget ∧
        calculation.boundaryReadout s ≠ BoundaryStatus.viable := by
  exact
    ⟨HiddenState.hiddenMaintained,
      by simp [calculation, maintains, process, readout]⟩

/-- Strict upper witness: `hiddenLost` does not realize the target. -/
theorem not_maintains_state :
    ∃ s,
      ¬ calculation.maintains s calculation.maintainedTarget := by
  exact ⟨HiddenState.hiddenLost, by simp [calculation, maintains]⟩

/-- The raw viable region is nonempty. -/
theorem stateViableRegion_nonempty :
    calculation.stateViableRegion.Nonempty :=
  AlternativePersistenceCalculation.nontrivial_stateViableRegion_nonempty
    calculation calculation_nontrivial

/--
Same boundary readout, different maintained-target realization.

This is the additional semantic separation absent from the three-state visible
witness.
-/
theorem same_readout_different_maintains :
    ∃ left right : HiddenState,
      left ≠ right ∧
        calculation.boundaryReadout left = calculation.boundaryReadout right ∧
        calculation.maintains left calculation.maintainedTarget ∧
        ¬ calculation.maintains right calculation.maintainedTarget := by
  exact
    ⟨HiddenState.hiddenMaintained, HiddenState.hiddenLost,
      by decide,
      by simp [calculation, process, readout],
      by simp [calculation, maintains],
      by simp [calculation, maintains]⟩

/--
Same full current view, different maintained-target realization.

The two hidden states agree on both observation and boundary readout.
-/
theorem same_currentView_different_maintains :
    ∃ left right : HiddenState,
      left ≠ right ∧
        process.currentView left = process.currentView right ∧
        calculation.maintains left calculation.maintainedTarget ∧
        ¬ calculation.maintains right calculation.maintainedTarget := by
  exact
    ⟨HiddenState.hiddenMaintained, HiddenState.hiddenLost,
      by decide,
      by simp [process, observe, readout,
        ObservationalPersistenceProcess.currentView],
      by simp [calculation, maintains],
      by simp [calculation, maintains]⟩

/-- The hidden witness has non-injective current views. -/
theorem currentView_not_injective :
    ¬ Function.Injective process.currentView := by
  intro hinjective
  have hview :
      process.currentView HiddenState.hiddenMaintained =
        process.currentView HiddenState.hiddenLost := by
    simp [process, observe, readout,
      ObservationalPersistenceProcess.currentView]
  have hstate := hinjective hview
  cases hstate

/--
The one-step response is state-dependent: states with different current views
can respond differently to the same action.

This pins down, at kernel level, that the one-step extensionality below is not
the degenerate consequence of a state-constant response function.
-/
theorem response_state_dependent :
    process.response HiddenState.ready HiddenAction.repair ≠
      process.response HiddenState.failed HiddenAction.repair := by
  decide

/--
The hidden process satisfies one-step extensionality without current-view
injectivity.
-/
theorem currentViewOneStepExtensional :
    CurrentViewOneStepExtensional process := by
  intro sourceState targetState hview action
  cases sourceState <;> cases targetState <;> cases action <;>
    simp [process, observe, readout, step,
      ObservationalPersistenceProcess.currentView,
      ObservationalPersistenceProcess.response] at hview ⊢

/--
The hidden witness enters trace-log extensionality through the one-step route.
-/
theorem currentViewTraceLogExtensional_via_oneStep :
    CurrentViewTraceLogExtensional process :=
  currentViewTraceLogExtensional_of_oneStepExtensional
    process currentViewOneStepExtensional

/--
Combined hidden-witness summary: viable-region nonemptiness, two strict
maintained-target separation witnesses, same-readout and same-current-view
semantic separation, non-injective current views, a state-dependent one-step
response, and the one-step route into trace-log extensionality.
-/
theorem hidden_semantic_witness_summary :
    calculation.stateViableRegion.Nonempty ∧
      (∃ s,
        calculation.maintains s calculation.maintainedTarget ∧
          calculation.boundaryReadout s ≠ BoundaryStatus.viable) ∧
      (∃ s,
        ¬ calculation.maintains s calculation.maintainedTarget) ∧
      (∃ left right : HiddenState,
        left ≠ right ∧
          calculation.boundaryReadout left =
            calculation.boundaryReadout right ∧
          calculation.maintains left calculation.maintainedTarget ∧
          ¬ calculation.maintains right calculation.maintainedTarget) ∧
      (∃ left right : HiddenState,
        left ≠ right ∧
          process.currentView left = process.currentView right ∧
          calculation.maintains left calculation.maintainedTarget ∧
          ¬ calculation.maintains right calculation.maintainedTarget) ∧
      ¬ Function.Injective process.currentView ∧
      (∃ left right : HiddenState,
        ∃ action : HiddenAction,
          process.response left action ≠ process.response right action) ∧
      CurrentViewOneStepExtensional process ∧
      CurrentViewTraceLogExtensional process := by
  exact
    ⟨stateViableRegion_nonempty,
      maintains_nonviable_state,
      not_maintains_state,
      same_readout_different_maintains,
      same_currentView_different_maintains,
      currentView_not_injective,
      ⟨HiddenState.ready, HiddenState.failed, HiddenAction.repair,
        response_state_dependent⟩,
      currentViewOneStepExtensional,
      currentViewTraceLogExtensional_via_oneStep⟩

end HiddenSemanticWitness

end Examples.SmallWitness
end Persistence.StructuralPersistence
