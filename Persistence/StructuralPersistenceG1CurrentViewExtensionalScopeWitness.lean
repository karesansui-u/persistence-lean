import Persistence.StructuralPersistenceG1ScopedExtensionalMLSeparation

/-!
# G1 Current-View Extensional Scope Witness

This module records that the current-view-extensional scope used by the
semantic G1 entrance is inhabited.

The core result is deliberately modest:

* `currentViewResponseImageExtensional_of_currentView_injective` is the primary
  scope theorem.
* `VisibleScopeWitness.currentViewResponseImageExtensional` is the nonconstant
  finite inhabitant.

The later declarations route that same visible witness through existing
entrance surfaces.  They are application wrappers for nonvacuity checks, not
additional semantic necessity theorem bodies.  In particular, this module does
not claim arbitrary alternatives are extensional.
-/

namespace Persistence.StructuralPersistence

universe u v w x y

variable {State : Type u} {Action : Type v} {Observation : Type w}

/--
If the current observable view determines the state, then one-step response
images are current-view extensional.

This is the visible-state route: no hidden state remains behind the current
view, so moving a response from one same-view state to another is just
transport along equality of states.
-/
theorem currentViewResponseImageExtensional_of_currentView_injective
    (P : ObservationalPersistenceProcess State Action Observation)
    (hinjective : Function.Injective P.currentView) :
    CurrentViewResponseImageExtensional P := by
  intro sourceState targetState hview response hsource
  have hstate : sourceState = targetState := hinjective hview.symm
  subst sourceState
  exact hsource

/--
Bidirectional global response-image equivalence becomes local same-current-view
response-image equivalence when both current views determine their states.

This is the visible-state structural route into the scoped entrance: no hidden
same-view state can carry a different one-step response image on either side.
-/
theorem currentViewResponseImageEquivalent_of_globalResponseImageEquivalent_of_currentView_injective
    {StateA : Type u} {ActionA : Type v} {StateB : Type x}
    {ActionB : Type y} {Observation : Type w}
    {A : ObservationalPersistenceProcess StateA ActionA Observation}
    {B : ObservationalPersistenceProcess StateB ActionB Observation}
    (equivalent : CurrentViewGlobalResponseImageEquivalent A B)
    (sourceInjective : Function.Injective A.currentView)
    (targetInjective : Function.Injective B.currentView) :
    CurrentViewResponseImageEquivalent A B :=
  currentViewResponseImageEquivalent_of_globalResponseImageEquivalent
    equivalent
    (currentViewResponseImageExtensional_of_currentView_injective
      A sourceInjective)
    (currentViewResponseImageExtensional_of_currentView_injective
      B targetInjective)

/-!
## A small nonconstant visible-state witness

The process below has three visible states and two actions.  Its current view
is injective, and its one-step response image is stable across states: repair
always returns to ready and stress always reaches failed.  Thus the process is
nonconstant while still satisfying the current-view-extensional scope.
-/

namespace VisibleScopeWitness

inductive VisibleState where
  | ready
  | degraded
  | failed
  deriving DecidableEq, Repr

inductive VisibleAction where
  | repair
  | stress
  deriving DecidableEq, Repr

inductive VisibleObservation where
  | readyView
  | degradedView
  | failedView
  deriving DecidableEq, Repr

inductive VisibleTarget where
  | service
  deriving DecidableEq, Repr

def observe : VisibleState -> VisibleObservation
  | .ready => .readyView
  | .degraded => .degradedView
  | .failed => .failedView

def readout : VisibleState -> BoundaryStatus
  | .ready => .viable
  | .degraded => .stopped
  | .failed => .collapsed

def step : VisibleState -> VisibleAction -> VisibleState
  | _, .repair => .ready
  | _, .stress => .failed

def process :
    ObservationalPersistenceProcess
      VisibleState VisibleAction VisibleObservation where
  observe := observe
  step := step
  readout := readout

def maintains (state : VisibleState) (_target : VisibleTarget) : Prop :=
  process.readout state = BoundaryStatus.viable

/--
The visible-state witness also has a minimal semantic calculation.

The maintained target is intentionally small: it only records that viable
states realize the visible service target.  This feeds the existing G1a/G1b
semantic scaffold without claiming full role recovery.
-/
def semanticCalculation :
    AlternativePersistenceCalculation VisibleState VisibleTarget where
  maintainedTarget := VisibleTarget.service
  maintains := maintains
  boundaryReadout := process.readout
  viable_implies_maintained := by
    intro state h
    exact h

/-- The visible witness has a nontrivial viable readout. -/
theorem semanticCalculation_nontrivial :
    semanticCalculation.NontrivialReadout where
  viable_state := ⟨VisibleState.ready, rfl⟩

/--
Identity is an explicit same-calculation map for the visible semantic
calculation.
-/
def semanticIdentityMap :
    SameCalculationMap semanticCalculation semanticCalculation where
  toFun := id
  target_eq := rfl
  preserves_boundary := by
    intro state
    rfl
  preserves_maintained_target := by
    intro state h
    exact h

def stateRealizationViabilityRecovery :
    StateRealizationViabilityRecovery
      semanticCalculation semanticCalculation semanticIdentityMap :=
  recoverStateRealizationAndViability
    semanticIdentityMap semanticCalculation_nontrivial

/-- The visible semantic scaffold recovers a nonempty viable region. -/
theorem stateRealizationViabilityRecovery_viableRegion_nonempty :
    stateRealizationViabilityRecovery.viableRegion.Nonempty :=
  stateRealizationViabilityRecovery.viableRegion_nonempty

/--
Viable-region membership in the visible semantic scaffold realizes the
maintained target.
-/
theorem stateRealizationViabilityRecovery_viable_implies_maintained
    (k : stateRealizationViabilityRecovery.K)
    (hk : k ∈ stateRealizationViabilityRecovery.viableRegion) :
    semanticCalculation.maintains
      (stateRealizationViabilityRecovery.carrier k)
      semanticCalculation.maintainedTarget :=
  stateRealizationViabilityRecovery.viable_implies_carrier_realizes k hk

/-- The current visible view separates the three states. -/
theorem currentView_injective :
    Function.Injective process.currentView := by
  intro sourceState targetState hview
  cases sourceState <;> cases targetState
  · rfl
  · cases hview
  · cases hview
  · cases hview
  · rfl
  · cases hview
  · cases hview
  · cases hview
  · rfl

/-- The witness process inhabits the current-view-extensional scope. -/
theorem currentViewResponseImageExtensional :
    CurrentViewResponseImageExtensional process :=
  currentViewResponseImageExtensional_of_currentView_injective
    process currentView_injective

/-- The witness process also inhabits the current-view trace-log scope. -/
theorem currentViewTraceLogExtensional :
    CurrentViewTraceLogExtensional process :=
  currentViewTraceLogExtensional_of_currentView_injective
    process currentView_injective

/--
The witness process is locally one-step extensional by current view.

This is a weaker route than full visible-state injectivity in general; for the
concrete witness it follows from injectivity because there are no hidden
same-view states.
-/
theorem currentViewOneStepExtensional :
    CurrentViewOneStepExtensional process := by
  intro sourceState targetState hview action
  have hstate : sourceState = targetState :=
    currentView_injective hview
  subst sourceState
  rfl

/-- The scope witness is not a one-view process. -/
theorem currentView_ready_ne_degraded :
    process.currentView VisibleState.ready ≠
      process.currentView VisibleState.degraded := by
  decide

/-- The process has genuinely different one-step responses. -/
theorem response_repair_ne_stress_at_ready :
    process.response VisibleState.ready VisibleAction.repair ≠
      process.response VisibleState.ready VisibleAction.stress := by
  decide

/--
The current-view-extensional process class is nonempty in a nonconstant
finite sense: this witness has at least two current views and at least two
different one-step responses.
-/
theorem exists_nonconstant_currentViewResponseImageExtensional_process :
    ∃ (State : Type) (Action : Type) (Observation : Type),
      ∃ P : ObservationalPersistenceProcess State Action Observation,
        CurrentViewResponseImageExtensional P ∧
          (∃ sourceState targetState : State,
            P.currentView sourceState ≠ P.currentView targetState) ∧
          (∃ state : State,
            ∃ left right : Action,
              P.response state left ≠ P.response state right) :=
  ⟨VisibleState, VisibleAction, VisibleObservation, process,
    currentViewResponseImageExtensional,
    ⟨VisibleState.ready, VisibleState.degraded,
      currentView_ready_ne_degraded⟩,
    ⟨VisibleState.ready, VisibleAction.repair, VisibleAction.stress,
      response_repair_ne_stress_at_ready⟩⟩

/--
Self global response-image equivalence is available for the witness, and with
current-view extensionality it yields the local bidirectional response-image
condition used by the scoped entrance.
-/
theorem currentViewResponseImageEquivalent_self :
    CurrentViewResponseImageEquivalent process process :=
  currentViewResponseImageEquivalent_of_globalResponseImageEquivalent
    ⟨fun _ _ h => h, fun _ _ h => h⟩
    currentViewResponseImageExtensional
    currentViewResponseImageExtensional

/-!
## Application wrappers for the same visible witness

The declarations below route the single visible-state inhabitant through
existing scoped entrance surfaces.  They keep the surfaces nonvacuous, but they
do not add new no-alternative proof load and should not be counted as separate
semantic G1 closure results.
-/

/--
The witness process has self global response-image inclusion by current view.

This is the smallest inhabitant of the global-image side of the scoped
extensional entrance: no adapter is discovered, because source and target are
the same visible process.
-/
theorem currentViewGlobalResponseImageIncluded_self :
    CurrentViewGlobalResponseImageIncluded process process := by
  intro view response hsource
  exact hsource

/-- The witness process has self global response-image equivalence. -/
theorem currentViewGlobalResponseImageEquivalent_self :
    CurrentViewGlobalResponseImageEquivalent process process :=
  ⟨currentViewGlobalResponseImageIncluded_self,
    currentViewGlobalResponseImageIncluded_self⟩

/--
The witness process has self global trace-log language inclusion by current
view.
-/
theorem currentViewGlobalTraceLogLanguageIncluded_self :
    CurrentViewGlobalTraceLogLanguageIncluded process process := by
  intro view log hsource
  exact hsource

/-- The witness process has self global trace-log language equivalence. -/
theorem currentViewGlobalTraceLogLanguageEquivalent_self :
    CurrentViewGlobalTraceLogLanguageEquivalent process process :=
  ⟨currentViewGlobalTraceLogLanguageIncluded_self,
    currentViewGlobalTraceLogLanguageIncluded_self⟩

/--
The visible process has an identity transition-preserving observational map.

This exposes the step-commuting map input used by the scoped extensional
entrance in its least surprising inhabited case.  It is still a supplied
self-map, not an adapter recovered from an arbitrary alternative.
-/
def identityTransitionMap :
    ObservationalTransitionMap process process where
  toState := id
  toAction := id
  preserves_observation := by
    intro state
    rfl
  preserves_readout := by
    intro state
    rfl
  step_commutes := by
    intro state action
    rfl

/--
The visible-state witness also carries a concrete response-separated
composition source.

This keeps the "scope is inhabited" claim tied to the active M/L entrance
rather than merely to extensionality: the same nonconstant finite process has
two visible actions with distinct one-step responses and positive composition
units.
-/
def responseSeparatedCompositionSource :
    AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
      process where
  initialState := VisibleState.ready
  burdenAction := VisibleAction.stress
  supportAction := VisibleAction.repair
  burdenUnit := 1
  supportUnit := 1
  burdenUnit_pos := by
    decide
  supportUnit_pos := by
    decide
  response_ne := by
    decide

/--
The visible-state witness reaches the current scoped additive M/L-separation
entrance.

This is still the scoped entrance theorem only: fixed-unit additive scalar
non-decodability plus a positive two-component readout for the concrete
response-separated source.  It does not recover full native `L/B` and
qualified support `M`.
-/
theorem scopedAdditiveMLSeparation :
    ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
      responseSeparatedCompositionSource :=
  ScopedMLSeparation.responseSeparated_forces_scopedAdditiveMLSeparation
    responseSeparatedCompositionSource

/--
The visible witness enters the scoped extensional M/L surface through the
global response-image lane.

This exercises the current-view-extensional entrance on a concrete inhabitant.
It is a self-route witness, not arbitrary adapter discovery.
-/
theorem scopedAdditiveMLSeparation_via_globalResponseImageIncluded :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_globalResponseImageIncluded
    responseSeparatedCompositionSource
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentViewGlobalResponseImageIncluded_self
    currentViewResponseImageExtensional
    rfl

/--
The visible witness also enters the scoped extensional M/L surface through the
bidirectional global response-image lane.
-/
theorem scopedAdditiveMLSeparation_via_globalResponseImageEquivalent :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_globalResponseImageEquivalent
    responseSeparatedCompositionSource
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentViewGlobalResponseImageEquivalent_self
    currentViewResponseImageExtensional
    currentViewResponseImageExtensional
    rfl

/--
The visible witness enters the scoped extensional M/L surface through the
global trace-log language lane.
-/
theorem scopedAdditiveMLSeparation_via_globalTraceLogLanguageIncluded :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageIncluded
    responseSeparatedCompositionSource
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentViewGlobalTraceLogLanguageIncluded_self
    currentViewTraceLogExtensional
    rfl

/--
The visible witness also enters the scoped extensional M/L surface through the
bidirectional global trace-log language lane.
-/
theorem scopedAdditiveMLSeparation_via_globalTraceLogLanguageEquivalent :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_globalTraceLogLanguageEquivalent
    responseSeparatedCompositionSource
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentViewGlobalTraceLogLanguageEquivalent_self
    currentViewTraceLogExtensional
    currentViewTraceLogExtensional
    rfl

/--
The visible witness enters the scoped extensional M/L surface through the
bidirectional transition-map lane in the visible-state scope.

This exercises the `fc56de91` visible-equivalence route on a concrete
self-transition map.  The map is still visible input; this is not arbitrary
adapter discovery.
-/
theorem scopedAdditiveMLSeparation_via_bidirTransitionMapsInjective :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsInjective
    responseSeparatedCompositionSource
    identityTransitionMap
    identityTransitionMap
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentView_injective
    currentView_injective
    rfl

/--
The visible witness also enters the scoped extensional M/L surface through the
bidirectional transition-map lane using only local one-step extensionality.

This exercises the weaker one-step scope on a concrete self-transition map.
The map is still visible input; this is not arbitrary adapter discovery.
-/
theorem scopedAdditiveMLSeparation_via_bidirTransitionMapsOneStep :
    ∃ targetSource :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
        targetSource :=
  ScopedMLSeparation.exists_target_scopedAdditiveMLSeparation_of_bidirTransitionMapsOneStep
    responseSeparatedCompositionSource
    identityTransitionMap
    identityTransitionMap
    (targetInitialState := responseSeparatedCompositionSource.initialState)
    currentViewOneStepExtensional
    currentViewOneStepExtensional
    rfl

/--
The weaker local one-step current-view scope is also nonempty in the same
nonconstant finite sense.

This packages the current visible witness in the exact scope used by the
one-step entrance route: the process is locally one-step extensional by current
view, has nontrivial current views and one-step responses, and reaches the
scoped additive M/L-separation entrance.  It is still a self-route witness, not
arbitrary alternative recovery.
-/
theorem exists_nonconstant_currentViewOneStep_scopedAdditiveMLSeparation_process :
    ∃ (State : Type) (Action : Type) (Observation : Type),
      ∃ P : ObservationalPersistenceProcess State Action Observation,
        CurrentViewOneStepExtensional P ∧
          (∃ source :
            AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
              P,
              ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
                source) ∧
          (∃ sourceState targetState : State,
            P.currentView sourceState ≠ P.currentView targetState) ∧
          (∃ state : State,
            ∃ left right : Action,
              P.response state left ≠ P.response state right) :=
  ⟨VisibleState, VisibleAction, VisibleObservation, process,
    currentViewOneStepExtensional,
    scopedAdditiveMLSeparation_via_bidirTransitionMapsOneStep,
    ⟨VisibleState.ready, VisibleState.degraded,
      currentView_ready_ne_degraded⟩,
    ⟨VisibleState.ready, VisibleAction.repair, VisibleAction.stress,
      response_repair_ne_stress_at_ready⟩⟩

/--
The current-view-extensional scope is nonempty in a way that already triggers
the scoped additive M/L-separation entrance.
-/
theorem exists_nonconstant_currentViewExtensional_scopedAdditiveMLSeparation_process :
    ∃ (State : Type) (Action : Type) (Observation : Type),
      ∃ P : ObservationalPersistenceProcess State Action Observation,
        CurrentViewTraceLogExtensional P ∧
          CurrentViewResponseImageExtensional P ∧
          (∃ source :
            AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
              P,
              ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
                source) ∧
          (∃ sourceState targetState : State,
            P.currentView sourceState ≠ P.currentView targetState) ∧
          (∃ state : State,
            ∃ left right : Action,
              P.response state left ≠ P.response state right) :=
  ⟨VisibleState, VisibleAction, VisibleObservation, process,
    currentViewTraceLogExtensional,
    currentViewResponseImageExtensional,
    ⟨responseSeparatedCompositionSource, scopedAdditiveMLSeparation⟩,
    ⟨VisibleState.ready, VisibleState.degraded,
      currentView_ready_ne_degraded⟩,
    ⟨VisibleState.ready, VisibleAction.repair, VisibleAction.stress,
      response_repair_ne_stress_at_ready⟩⟩

/--
The same nonconstant visible-state process inhabits the extensional scope,
triggers the scoped additive M/L entrance, and enters the semantic F/K/V_K
recovery scaffold with a nonempty viable region.
-/
theorem exists_nonconstant_visible_scope_entrance_and_semanticRecovery_process :
    ∃ (State : Type) (Action : Type) (Observation : Type) (Target : Type),
      ∃ (P : ObservationalPersistenceProcess State Action Observation)
        (A : AlternativePersistenceCalculation State Target),
        CurrentViewTraceLogExtensional P ∧
          CurrentViewResponseImageExtensional P ∧
          A.NontrivialReadout ∧
          (∃ source :
            AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
              P,
              ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion
                source) ∧
          (∃ phi : SameCalculationMap A A,
            ∃ recovery : StateRealizationViabilityRecovery A A phi,
              recovery.viableRegion.Nonempty) ∧
          (∃ sourceState targetState : State,
            P.currentView sourceState ≠ P.currentView targetState) ∧
          (∃ state : State,
            ∃ left right : Action,
              P.response state left ≠ P.response state right) :=
  ⟨VisibleState, VisibleAction, VisibleObservation, VisibleTarget,
    process, semanticCalculation,
    currentViewTraceLogExtensional,
    currentViewResponseImageExtensional,
    semanticCalculation_nontrivial,
    ⟨responseSeparatedCompositionSource, scopedAdditiveMLSeparation⟩,
    ⟨semanticIdentityMap, stateRealizationViabilityRecovery,
      stateRealizationViabilityRecovery_viableRegion_nonempty⟩,
    ⟨VisibleState.ready, VisibleState.degraded,
      currentView_ready_ne_degraded⟩,
    ⟨VisibleState.ready, VisibleAction.repair, VisibleAction.stress,
      response_repair_ne_stress_at_ready⟩⟩

end VisibleScopeWitness

end Persistence.StructuralPersistence
