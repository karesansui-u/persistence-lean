import Persistence.StructuralPersistenceG1CurrentViewResponseCompleteness
import Persistence.StructuralPersistenceG1ScopedMLSeparation

/-!
# G1 Scoped Extensional M/L-Separation Entrance

This module folds the current-view response completeness bottleneck into the
scoped additive M/L-separation surface.

The scope is explicit: global current-view response-image inclusion becomes
usable for the scoped M/L entrance only when the target process is
current-view response-image extensional.  This records the current
`current-view-extensional` process class rather than claiming arbitrary
alternative discovery or full semantic G1c.
-/

namespace Persistence.StructuralPersistence

universe u v w x y

namespace ScopedMLSeparation

open AdditiveScalarCompositionObservedTrace

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}

/--
Global current-view response-image inclusion, scoped by target-side
current-view response-image extensionality, enters the target-side scoped
additive M/L-separation surface.

This is not a new transport bridge.  It folds the previously isolated
completeness bottleneck into the existing scoped M/L entrance: the global
image condition finds a matching target state for a response, and
extensionality makes that response available at the selected target state.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalResponseImageIncluded
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (included : CurrentViewGlobalResponseImageIncluded P alternative)
    (targetExtensional : CurrentViewResponseImageExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
    source
    (currentViewResponseImageComplete_of_globalResponseImageIncluded
      included targetExtensional)
    hview

/--
Bidirectional global current-view response-image equivalence, scoped by
current-view response-image extensionality on both processes, enters the same
target-side scoped additive M/L-separation surface.

Only the forward completeness direction is needed for the target-side entrance;
the bidirectional hypothesis records the stronger observable equivalence class
that also gives `CurrentViewResponseImageEquivalent`.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalResponseImageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalResponseImageEquivalent P alternative)
    (sourceExtensional : CurrentViewResponseImageExtensional P)
    (targetExtensional : CurrentViewResponseImageExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageEquivalent
    source
    (currentViewResponseImageEquivalent_of_globalResponseImageEquivalent
      equivalent sourceExtensional targetExtensional)
    hview

/--
Global current-view trace-log language inclusion, scoped by target-side
trace-log extensionality, enters the target-side scoped additive
M/L-separation surface.

This is the trace-language analogue of the response-image fold above.  The
global language hypothesis may find some target state with the right current
view; target-side trace-log extensionality moves the log language to the
selected target initial state.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageIncluded
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (included : CurrentViewGlobalTraceLogLanguageIncluded P alternative)
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageIncluded
    source
    (currentViewTraceLogLanguageIncluded_of_globalTraceLogLanguageIncluded
      included targetExtensional)
    hview

/--
Bidirectional global current-view trace-log language equivalence, scoped by
trace-log extensionality on both processes, enters the same target-side
scoped additive M/L-separation surface.

Only the forward local inclusion is needed for this entrance, but the
bidirectional theorem records the observable equivalence class that also
produces `CurrentViewTraceLogLanguageEquivalent`.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalTraceLogLanguageEquivalent P alternative)
    (sourceExtensional : CurrentViewTraceLogExtensional P)
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageEquivalent
    source
    (currentViewTraceLogLanguageEquivalent_of_globalTraceLogLanguageEquivalent
      equivalent sourceExtensional targetExtensional)
    hview

/--
Bidirectional global response-image equivalence enters the scoped M/L surface
under the visible-state sufficient condition.

Current-view injectivity is only a scope condition that supplies the required
response-image extensionality.  It is not a derivation of arbitrary
alternative adapters.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalResponseEquivInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalResponseImageEquivalent P alternative)
    (sourceInjective : Function.Injective P.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalResponseImageEquivalent
    source
    equivalent
    (currentViewResponseImageExtensional_of_injective_currentView
      P sourceInjective)
    (currentViewResponseImageExtensional_of_injective_currentView
      alternative targetInjective)
    hview

/--
Bidirectional global trace-log language equivalence enters the scoped M/L
surface under the visible-state sufficient condition.

Current-view injectivity supplies trace-log extensionality, but the observable
equivalence itself remains an explicit input.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalTraceEquivInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalTraceLogLanguageEquivalent P alternative)
    (sourceInjective : Function.Injective P.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageEquivalent
    source
    equivalent
    (currentViewTraceLogExtensional_of_currentView_injective
      P sourceInjective)
    (currentViewTraceLogExtensional_of_currentView_injective
      alternative targetInjective)
    hview

/--
Bidirectional global response-image equivalence enters the scoped M/L surface
when both processes are locally one-step extensional by current view.

This weakens the visible-state route: current views need not determine states,
but same-current-view hidden states must have the same observable one-step
responses.  The global equivalence itself is still supplied.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalResponseEquivOneStep
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalResponseImageEquivalent P alternative)
    (sourceOneStep : CurrentViewOneStepExtensional P)
    (targetOneStep : CurrentViewOneStepExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageEquivalent
    source
    (currentViewResponseImageEquivalent_of_globalResponseImageEquivalent_of_oneStep
      equivalent sourceOneStep targetOneStep)
    hview

/--
Bidirectional global trace-log language equivalence enters the scoped M/L
surface when both processes are locally one-step extensional by current view.

The one-step condition supplies finite trace-log extensionality by induction;
it does not discover the global language equivalence or an arbitrary adapter.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_globalTraceEquivOneStep
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalTraceLogLanguageEquivalent P alternative)
    (sourceOneStep : CurrentViewOneStepExtensional P)
    (targetOneStep : CurrentViewOneStepExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageEquivalent
    source
    (currentViewTraceLogLanguageEquivalent_of_globalTraceLogLanguageEquivalent_of_oneStep
      equivalent sourceOneStep targetOneStep)
    hview

/--
A source-covered response-image simulation enters the same scoped M/L surface
through the global response-image lane.

The simulation relation and its source coverage are still explicit inputs.
Target-side current-view response-image extensionality is what moves the
globally realized response image to the selected target initial state.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_sourceCoveredResponseImageSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (simulation : ObservationalResponseImageSimulation P alternative)
    (sourceCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          simulation.related sourceState targetState)
    {targetInitialState : AlternativeState}
    (targetExtensional : CurrentViewResponseImageExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalResponseImageIncluded
    source
    (currentViewGlobalResponseImageIncluded_of_responseImageSimulation_sourceCovered
      simulation sourceCovered)
    targetExtensional
    hview

/--
A source-covered trace simulation enters the same scoped M/L surface through
the global trace-log language lane.

This is stronger than a one-step response-image route but still not arbitrary
adapter discovery: the relation, action translator, and source coverage are
supplied by the simulation.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_sourceCoveredTraceSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (simulation : ObservationalTraceSimulation P alternative)
    (sourceCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          simulation.related sourceState targetState)
    {targetInitialState : AlternativeState}
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageIncluded
    source
    (currentViewGlobalTraceLogLanguageIncluded_of_traceSimulation_sourceCovered
      simulation sourceCovered)
    targetExtensional
    hview

/--
A transition-preserving map enters the global trace-language M/L route when
the selected target process is trace-log extensional by current view.

The step-commuting map is still supplied; this theorem only exposes its
global trace-language consequence before applying the scoped entrance.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_transitionMapGlobalTraceLogLanguage
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (phi : ObservationalTransitionMap P alternative)
    {targetInitialState : AlternativeState}
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageIncluded
    source
    (currentViewGlobalTraceLogLanguageIncluded_of_transitionMap phi)
    targetExtensional
    hview

/--
Bidirectional source-covered response-image simulations enter the scoped M/L
surface through global response-image equivalence.

Both simulation directions and their source-coverage witnesses remain explicit
inputs; extensionality on both processes is still required before the global
equivalence becomes the local current-view response-image equivalence consumed
by the entrance.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirResponseImageSimulations
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalResponseImageSimulation P alternative)
    (reverse : ObservationalResponseImageSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceExtensional : CurrentViewResponseImageExtensional P)
    (targetExtensional : CurrentViewResponseImageExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalResponseImageEquivalent
    source
    (currentViewGlobalResponseImageEquivalent_of_responseImageSimulations_sourceCovered
      forward reverse forwardCovered reverseCovered)
    sourceExtensional
    targetExtensional
    hview

/--
Bidirectional source-covered trace simulations enter the scoped M/L surface
through global trace-log language equivalence.

This route keeps both action translators and coverage witnesses visible.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTraceSimulations
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTraceSimulation P alternative)
    (reverse : ObservationalTraceSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceExtensional : CurrentViewTraceLogExtensional P)
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageEquivalent
    source
    (currentViewGlobalTraceLogLanguageEquivalent_of_traceSimulations_sourceCovered
      forward reverse forwardCovered reverseCovered)
    sourceExtensional
    targetExtensional
    hview

/--
Transition-preserving maps in both directions enter the scoped M/L surface
through global trace-log language equivalence.

The transition maps are still supplied and are not recovered from arbitrary
alternatives.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsTraceLanguage
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTransitionMap P alternative)
    (reverse : ObservationalTransitionMap alternative P)
    {targetInitialState : AlternativeState}
    (sourceExtensional : CurrentViewTraceLogExtensional P)
    (targetExtensional : CurrentViewTraceLogExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageEquivalent
    source
    (currentViewGlobalTraceLogLanguageEquivalent_of_transitionMaps
      forward reverse)
    sourceExtensional
    targetExtensional
    hview

/--
Bidirectional response-image simulations enter the scoped M/L surface in a
visible-state scope.

The simulations and coverage witnesses remain supplied; current-view
injectivity only discharges the extensionality hypotheses.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirResponseSimulationsInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalResponseImageSimulation P alternative)
    (reverse : ObservationalResponseImageSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceInjective : Function.Injective P.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_bidirResponseImageSimulations
    source
    forward
    reverse
    forwardCovered
    reverseCovered
    (currentViewResponseImageExtensional_of_injective_currentView
      P sourceInjective)
    (currentViewResponseImageExtensional_of_injective_currentView
      alternative targetInjective)
    hview

/--
Bidirectional trace simulations enter the scoped M/L surface in a visible-state
scope.

The fixed action translators and coverage witnesses are still inputs; the
injective current views only supply trace-log extensionality.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTraceSimulationsInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTraceSimulation P alternative)
    (reverse : ObservationalTraceSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceInjective : Function.Injective P.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_bidirTraceSimulations
    source
    forward
    reverse
    forwardCovered
    reverseCovered
    (currentViewTraceLogExtensional_of_currentView_injective
      P sourceInjective)
    (currentViewTraceLogExtensional_of_currentView_injective
      alternative targetInjective)
    hview

/--
Bidirectional transition maps enter the scoped M/L surface in a visible-state
scope.

The step-commuting maps remain supplied; current-view injectivity only supplies
the extensionality needed to localize their global trace-language equivalence.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTransitionMap P alternative)
    (reverse : ObservationalTransitionMap alternative P)
    {targetInitialState : AlternativeState}
    (sourceInjective : Function.Injective P.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsTraceLanguage
    source
    forward
    reverse
    (currentViewTraceLogExtensional_of_currentView_injective
      P sourceInjective)
    (currentViewTraceLogExtensional_of_currentView_injective
      alternative targetInjective)
    hview

/--
Bidirectional response-image simulations enter the scoped M/L surface under
local current-view one-step extensionality.

The simulations and coverage witnesses remain supplied; the one-step condition
only replaces the stronger response-image extensionality hypotheses.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirResponseSimulationsOneStep
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalResponseImageSimulation P alternative)
    (reverse : ObservationalResponseImageSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceOneStep : CurrentViewOneStepExtensional P)
    (targetOneStep : CurrentViewOneStepExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalResponseEquivOneStep
    source
    (currentViewGlobalResponseImageEquivalent_of_responseImageSimulations_sourceCovered
      forward reverse forwardCovered reverseCovered)
    sourceOneStep
    targetOneStep
    hview

/--
Bidirectional trace simulations enter the scoped M/L surface under local
current-view one-step extensionality.

The supplied trace simulations give the global language equivalence; one-step
extensionality only localizes it at the selected current view.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTraceSimulationsOneStep
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTraceSimulation P alternative)
    (reverse : ObservationalTraceSimulation alternative P)
    (forwardCovered :
      forall sourceState : State,
        ∃ targetState : AlternativeState,
          forward.related sourceState targetState)
    (reverseCovered :
      forall targetState : AlternativeState,
        ∃ sourceState : State,
          reverse.related targetState sourceState)
    {targetInitialState : AlternativeState}
    (sourceOneStep : CurrentViewOneStepExtensional P)
    (targetOneStep : CurrentViewOneStepExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceEquivOneStep
    source
    (currentViewGlobalTraceLogLanguageEquivalent_of_traceSimulations_sourceCovered
      forward reverse forwardCovered reverseCovered)
    sourceOneStep
    targetOneStep
    hview

/--
Bidirectional transition maps enter the scoped M/L surface under local
current-view one-step extensionality.

The step-commuting maps remain supplied.  The one-step condition only replaces
the broader current-view trace-log extensionality hypotheses.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsOneStep
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (forward : ObservationalTransitionMap P alternative)
    (reverse : ObservationalTransitionMap alternative P)
    {targetInitialState : AlternativeState}
    (sourceOneStep : CurrentViewOneStepExtensional P)
    (targetOneStep : CurrentViewOneStepExtensional alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_globalTraceEquivOneStep
    source
    (currentViewGlobalTraceLogLanguageEquivalent_of_transitionMaps
      forward reverse)
    sourceOneStep
    targetOneStep
    hview

end ScopedMLSeparation

end Persistence.StructuralPersistence
