import Persistence.StructuralPersistenceG1CompositeScoreForcingCore

set_option linter.unusedSectionVars false

/-!
# G1 Scoped M/L Separation Boundary

This file packages the currently closed observation-derived forcing lane into
one deliberately scoped surface.

It does **not** prove the full `L/B` and qualified-support `M` recovery
theorem.  Its claim is narrower:

* a response-separated two-channel observational source induces an observed
  two-count composition language;
* every fixed-unit additive one-scalar readout collides on that language; and
* the two-component coordinate preserves the same observed composition logs.

This is the safe "M/L separation entrance" theorem: it records that, under the
explicit response-separation and positive-unit hypotheses, the burden/support
candidate split cannot be erased by fixed-unit additive scalar accounting.
-/

namespace Persistence.StructuralPersistence

universe u v w x y

namespace ScopedMLSeparation

open AdditiveScalarCompositionObservedTrace

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}

/--
The scoped M/L-separation conclusion for one response-separated source.

It is intentionally limited to fixed-unit additive scalar accounting versus a
two-component burden/support-candidate coordinate over the generated
composition logs.
-/
def ScopedAdditiveMLSeparationConclusion
    (source : ResponseSeparatedCompositionSource P) : Prop :=
  (¬ Exists
    (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
      forall burdenCount supportCount,
        traceLogOfScalar
            ((source.toObservedAdditiveCompositionSource).scalarOfCounts
              burdenCount supportCount) =
          (source.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount)) ∧
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount

/--
The currently closed scoped M/L-separation boundary.

The structure intentionally stores the original response-separated
observational source.  The proof-carrying fields expose exactly the two
consequences that are closed in the current semantic G1 lane: fixed-unit
additive scalar non-decodability and two-component decodability.
-/
structure ScopedAdditiveMLSeparationBoundary
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  source : ResponseSeparatedCompositionSource P
  conclusion : ScopedAdditiveMLSeparationConclusion source

namespace ScopedAdditiveMLSeparationBoundary

variable (boundary : ScopedAdditiveMLSeparationBoundary P)

/--
The scalar no-go part of the scoped boundary.
-/
theorem projects_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((boundary.source.toObservedAdditiveCompositionSource).scalarOfCounts
                burdenCount supportCount) =
            (boundary.source.toObservedAdditiveCompositionSource).traceLogOfCounts
              burdenCount supportCount) :=
  boundary.conclusion.1

/--
The positive two-component readout part of the scoped boundary.
-/
theorem projects_exists_componentCoordinate_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (boundary.source.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount :=
  boundary.conclusion.2

end ScopedAdditiveMLSeparationBoundary

/--
Construct the scoped M/L-separation boundary from a response-separated
two-channel observational source.

This is the main theorem of this file.  It consumes only the already explicit
response-separated source; it does not claim to derive native `L/B`, qualified
support `M`, log accounting, or arbitrary-alternative uniqueness.
-/
def scopedAdditiveMLSeparationBoundaryOfResponseSeparation
    (source : ResponseSeparatedCompositionSource P) :
    ScopedAdditiveMLSeparationBoundary P where
  source := source
  conclusion :=
    ⟨source.no_additiveScalar_traceLog_decoder,
      source.exists_componentCoordinate_traceLog_readout⟩

/--
Response separation forces the scoped additive M/L-separation conclusion.

This is the theorem-body entry for the file.  It is not a full M/L recovery
claim; it is a fixed-unit additive-scalar anti-collapse theorem with a
positive two-component readout in the same scope.
-/
theorem responseSeparated_forces_scopedAdditiveMLSeparation
    (source : ResponseSeparatedCompositionSource P) :
    ScopedAdditiveMLSeparationConclusion source :=
  (scopedAdditiveMLSeparationBoundaryOfResponseSeparation
    source).conclusion

/--
A same-context `TwoChannelTraceLaw` is enough to enter the scoped M/L
separation boundary, once positive burden/support composition units are
chosen.
-/
def scopedAdditiveMLSeparationBoundaryOfTwoChannelTraceLaw
    (law : TwoChannelTraceLaw P)
    (sameContext : law.adverseContext = law.restorativeContext)
    (burdenUnit supportUnit : Nat)
    (hburden : 0 < burdenUnit) (hsupport : 0 < supportUnit) :
    ScopedAdditiveMLSeparationBoundary P :=
  scopedAdditiveMLSeparationBoundaryOfResponseSeparation
    (ResponseSeparatedCompositionSource.ofTwoChannelTraceLawSameContext
      law sameContext burdenUnit supportUnit hburden hsupport)

/--
The target-side response-separated source carried by a generated-prefix-state
transport boundary.

This keeps the scope visible: the target initial state, target generated
actions, and generated-prefix observable-view preservation are still supplied
by the transport boundary.  Nothing here discovers arbitrary adapters or
recovers native `L/B` and qualified-support `M`.
-/
def targetResponseSeparatedSourceOfGeneratedPrefixMappedSource
    {AlternativeState : Type x} {AlternativeAction : Type y}
    (source :
      CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
        P AlternativeState AlternativeAction) :
    ResponseSeparatedCompositionSource source.alternative :=
  source.toPrefixTreeMappedResponseSeparatedCompositionSource
    |>.toTargetResponseSeparatedCompositionSource

/--
A generated-prefix-state transport boundary enters the same scoped M/L
separation surface on the target side.

This is still a scoped entrance theorem only: it packages the fixed-unit
additive scalar no-go and the two-component positive readout after the
generated-prefix-state hypotheses have produced the target response-separated
source.
-/
def scopedAdditiveMLSeparationBoundaryOfGeneratedPrefixMappedSource
    {AlternativeState : Type x} {AlternativeAction : Type y}
    (source :
      CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
        P AlternativeState AlternativeAction) :
    ScopedAdditiveMLSeparationBoundary source.alternative :=
  scopedAdditiveMLSeparationBoundaryOfResponseSeparation
    (targetResponseSeparatedSourceOfGeneratedPrefixMappedSource source)

/--
Generated-prefix-state transport forces the target-side scoped additive M/L
separation conclusion.

The theorem does not quantify over arbitrary alternatives and does not close
full semantic G1c; it records that the latest generated-prefix-state lane feeds
the already closed scoped additive scalar anti-collapse surface.
-/
theorem generatedPrefixMapped_forces_target_scopedAdditiveMLSeparation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    (source :
      CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
        P AlternativeState AlternativeAction) :
    ScopedAdditiveMLSeparationConclusion
      (targetResponseSeparatedSourceOfGeneratedPrefixMappedSource source) :=
  (scopedAdditiveMLSeparationBoundaryOfGeneratedPrefixMappedSource
    source).conclusion

/--
Canonical trace behavior with a fixed translator enters the generated-prefix
scoped additive M/L-separation lane.

This is stronger than the current-view response-image/language entrances: the
fixed translator plus trace-behavior relation supplies generated-prefix
preservation for the translated burden/support actions.  It still does not
derive the translator or trace-behavior relation from arbitrary admissibility.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_traceBehaviorRelated
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (toAction : Action -> AlternativeAction)
    (hbehavior :
      traceBehaviorRelated P alternative toAction
        source.initialState targetInitialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource := by
  let mapped :=
    source.toGeneratedPrefixMappedResponseSeparatedCompositionSource_of_traceBehaviorRelated
      toAction hbehavior
  exact
    ⟨targetResponseSeparatedSourceOfGeneratedPrefixMappedSource mapped,
      generatedPrefixMapped_forces_target_scopedAdditiveMLSeparation mapped⟩

/--
A role-free trace simulation enters the fixed trace-behavior route.

This removes the all-prefix trace-behavior relation as a separate input when
local simulation laws are supplied: `TraceBehaviorRelated.ofTraceSimulation`
derives the fixed behavior relation by induction over finite traces.  The
simulation relation and action translator are still supplied, so this is not
arbitrary adapter discovery or full semantic G1c closure.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_traceSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (simulation : ObservationalTraceSimulation P alternative)
    {targetInitialState : AlternativeState}
    (hrelated :
      simulation.related source.initialState targetInitialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_traceBehaviorRelated
    source simulation.toAction
    (TraceBehaviorRelated.ofTraceSimulation simulation hrelated)

/--
A transition-preserving observational map enters the fixed trace-behavior
route at the image of the source initial state.

This is a stricter supplied-map lane than arbitrary alternatives: observation
preservation, readout preservation, and one-step commutation are the inputs.
From them the existing transition-map theorem derives the canonical
trace-behavior relation, which then feeds the generated-prefix scoped surface.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_transitionMap
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (phi : ObservationalTransitionMap P alternative) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_traceBehaviorRelated
    source phi.toAction
    (TraceBehaviorRelated.ofTransitionMap phi source.initialState)

/--
A response-preserving observational map enters the fixed trace-behavior route
when the selected source initial state's full finite prefix logs are explicitly
preserved by the mapped target traces.

This is weaker than the transition-map lane: no step commutation is assumed.
The all-prefix trace-log equality is still a visible input, exactly because a
plain `ObservationalResponseMap` only preserves singleton prefix logs.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_responseMapTraceLog
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (phi : ObservationalResponseMap P alternative)
    (htrace :
      forall actions : List Action,
        P.traceLog source.initialState actions =
          alternative.traceLog
            (phi.toState source.initialState)
            (actions.map phi.toAction)) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_traceBehaviorRelated
    source phi.toAction
    (phi.traceBehaviorRelated_of_preserves_traceLog
      source.initialState htrace)

/--
A response-preserving observational map also enters the fixed trace-behavior
route when the target process is current-view trace-log extensional.

The scope remains explicit: a response map alone preserves singleton logs, not
all finite prefix logs.  The target-side trace-log extensionality condition is
the visible hypothesis that removes hidden same-current-view continuations.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_responseMapTargetTraceLogExtensional
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (phi : ObservationalResponseMap P alternative)
    (targetExtensional : CurrentViewTraceLogExtensional alternative) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_responseMapTraceLog
    source phi
    (phi.preserves_traceLog_of_target_currentViewTraceLogExtensional
      targetExtensional source.initialState)

/--
A response-preserving observational map enters the same fixed trace-behavior
route when the target process is visible-state: its current view determines
the target state.

This is a sufficient scoped route, not arbitrary adapter discovery.  The
injective current-view hypothesis supplies the target trace-log extensionality
used by the response-map route.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_responseMapTargetCurrentViewInjective
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (phi : ObservationalResponseMap P alternative)
    (targetInjective : Function.Injective alternative.currentView) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_responseMapTargetTraceLogExtensional
    source phi
    (currentViewTraceLogExtensional_of_currentView_injective
      alternative targetInjective)

/--
A role-free response-image simulation gives the weaker target-side scoped
additive M/L-separation entrance.

Unlike the trace-simulation and transition-map routes, this does not choose a
fixed action translator or preserve generated prefixes.  It only uses the
simulation's existential one-step response image at the related initial states
to construct the two target burden/support witnesses needed by the local
response-separated entrance.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_responseImageSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (simulation : ObservationalResponseImageSimulation P alternative)
    {targetInitialState : AlternativeState}
    (hrelated :
      simulation.related source.initialState targetInitialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource := by
  rcases
    source.exists_targetResponseSeparatedCompositionSource_of_responseImageSimulation
      simulation hrelated with
    ⟨targetSource, _⟩
  exact
    ⟨targetSource,
      responseSeparated_forces_scopedAdditiveMLSeparation targetSource⟩

/--
A canonical trace-language image simulation gives the same weaker target-side
scoped additive M/L-separation entrance.

The relatedness condition is now the canonical trace-language image relation:
same current observable view plus target realizability of all finite source
prefix logs.  This still does not choose a fixed action translator or prove
generated-prefix preservation for the discovered target actions.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_traceLanguageImageSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    (simulation : TraceLanguageImageSimulation P alternative)
    {targetInitialState : AlternativeState}
    (hrelated :
      traceLanguageImageRelated P alternative
        source.initialState targetInitialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_responseImageSimulation
    source
    (TraceLanguageImageSimulation.toResponseImageSimulation simulation)
    hrelated

/--
Current-view trace-image completeness enters the scoped surface through the
canonical trace-language image simulation.

This names the image-completeness route directly: every source prefix log is
realizable at any target state with the same current observable view.  It is
still an observational image condition, not arbitrary-adapter discovery.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewTraceImageComplete
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (complete : CurrentViewTraceImageComplete P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_traceLanguageImageSimulation
    source
    (CurrentViewTraceImageComplete.toTraceLanguageImageSimulation complete)
    ⟨hview, complete hview⟩

/--
Local current-view step-image completeness also enters the same scoped
surface.

This is the one-step observable successor-image route.  It iterates to
current-view trace-image completeness before feeding the target-side scoped
M/L entrance, so it remains role-free and does not choose a fixed global
action translator.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewStepImageComplete
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (complete : CurrentViewStepImageComplete P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewTraceImageComplete
    source
    (CurrentViewStepImageComplete.toCurrentViewTraceImageComplete complete)
    hview

/--
Current-view response-image completeness is enough to produce a target-side
scoped additive M/L-separation entrance, existentially.

This is weaker than the generated-prefix-state transport boundary: it discovers
two target actions for the initial burden/support responses and applies the
response-separated entrance theorem on the target side.  It does not provide
generated-prefix preservation for those actions or transport the source
composition logs through fixed target actions.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (complete : CurrentViewResponseImageComplete P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource := by
  rcases
    source.exists_targetResponseSeparatedCompositionSource_of_currentViewResponseImageComplete
      complete hview with
    ⟨targetSource, _⟩
  exact
    ⟨targetSource,
      responseSeparated_forces_scopedAdditiveMLSeparation targetSource⟩

/--
Current-view trace-log language inclusion is another observational entrance to
the same target-side scoped additive M/L-separation surface.

It descends through the response-image bottleneck to discover two target
initial response witnesses.  It still does not prove generated-prefix
preservation for those witnesses or close full semantic G1c.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageIncluded
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (included : CurrentViewTraceLogLanguageIncluded P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource := by
  exact
    exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
      source
      (CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
        included)
      hview

/--
Current-view trace-log language equivalence gives the same target-side scoped
additive M/L-separation entrance by forgetting to forward language inclusion.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewTraceLogLanguageEquivalent P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewTraceLogLanguageIncluded
    source
    (CurrentViewTraceLogLanguageEquivalent.toIncluded equivalent)
    hview

/--
Bidirectional current-view response-image equivalence gives the same
target-side scoped additive M/L-separation entrance.

This is only a reformulation of the observational completeness bottleneck: the
forward response-image side is enough for the target-side entrance, while the
reverse side records that the hypothesis is a bidirectional observable
equivalence rather than a one-way transport claim.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewResponseImageEquivalent P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
    source
    (CurrentViewResponseImageEquivalent.toCurrentViewResponseImageComplete
      equivalent)
    hview

/--
Current-view finite action-response search is a choice-bounded route into the
same target-side scoped additive M/L-separation entrance.

The finite candidate lists remain supplied per same-current-view state pair.
This theorem only records that, once those lists are supplied, the entrance
uses their response-image consequence rather than the general non-finite
translator-choice route.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_currentViewFiniteActionResponseSearch
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (finiteSearch : CurrentViewFiniteActionResponseSearch P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
    source
    (CurrentViewFiniteActionResponseSearch.toCurrentViewResponseImageComplete
      finiteSearch)
    hview

/--
Bidirectional current-view finite action-response search gives the same
target-side scoped additive M/L-separation entrance.

Only the forward finite-search side is needed for this target-side entrance.
The reverse side records bidirectional observable reachability, but this
theorem still does not derive generated-prefix preservation, full `L/B` and
qualified support `M`, or semantic G1c closure.
-/
theorem exists_target_scopedAdditiveMLSeparation_of_bidirectionalFiniteSearch
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (source : ResponseSeparatedCompositionSource P)
    {targetInitialState : AlternativeState}
    (bidirectional :
      CurrentViewBidirectionalFiniteActionResponseSearch P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource :=
  exists_target_scopedAdditiveMLSeparation_of_currentViewFiniteActionResponseSearch
    source bidirectional.forward hview

end ScopedMLSeparation

end Persistence.StructuralPersistence
