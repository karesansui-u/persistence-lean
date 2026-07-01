import Persistence.StructuralPersistenceG1SemanticCore
import Persistence.StructuralPersistenceG1ObservationalCore
import Persistence.StructuralPersistenceG1CompositeScoreForcingCore
import Persistence.StructuralPersistenceG1ScopedMLSeparation
import Persistence.StructuralPersistenceG1CurrentViewResponseCompleteness
import Persistence.StructuralPersistenceG1ScopedExtensionalMLSeparation
import Persistence.StructuralPersistenceG1CurrentViewExtensionalScopeWitness
import Persistence.StructuralPersistenceG1RigorousToScopedMLSeparation
import Persistence.StructuralPersistenceG1CurrentInevitabilitySkeletonInterface
import Persistence.StructuralPersistenceG1FixedTranslatorWall

/-!
# G1 Semantic Spine

This module is a narrow import spine for the semantic G1 proof-substance work.
It deliberately does not add a new theorem, status label, wrapper, or capstone.

Use it as the Lean entry point for the load-bearing semantic track:

* `StructuralPersistenceG1SemanticCore`:
  the minimal `F/K/V_K` semantic scaffold and same-calculation maps.
* `StructuralPersistenceG1ObservationalCore`:
  role-free observational processes, response/trace preservation, prefix-log
  anti-collapse, candidate role bridges, and certificate-relative
  factorization/log-accounting boundaries.
* `StructuralPersistenceG1CompositeScoreForcingCore`:
  two-channel composition traces and fixed-unit additive one-scalar no-go
  material.
* `StructuralPersistenceG1ScopedMLSeparation`:
  the scoped additive M/L-separation entrance theorem.
* `StructuralPersistenceG1CurrentViewResponseCompleteness`:
  current-view global-to-local completeness, gap/counterexample boundaries,
  and one-step localization folds.
* `StructuralPersistenceG1ScopedExtensionalMLSeparation`:
  extensional and one-step scoped routes into the M/L entrance.
* `StructuralPersistenceG1CurrentViewExtensionalScopeWitness`:
  a nonconstant finite witness showing the extensional/one-step scopes are
  nonempty and reach the scoped entrance.
* `StructuralPersistenceG1ObservationalRigorousCalc` and
  `StructuralPersistenceG1RigorousToScopedMLSeparation` and
  `StructuralPersistenceG1CurrentInevitabilitySkeletonInterface`:
  the observation-only strong-G1 skeleton: a state-carrier `F/K/V_K` scaffold,
  induced viable boundary predicate, non-collapse, scoped M/L entrance, and an
  output-only skeleton interface from an observation-only response-separation
  predicate.
* `StructuralPersistenceG1FixedTranslatorWall`:
  a red-test process showing that current-view response-image completeness can
  hold while no fixed action translator preserves all finite prefix logs.

Safe reading:

```text
role-free observation and prefix logs
-> response/trace anti-collapse
-> fixed-unit additive one-scalar no-go
-> scoped additive M/L-separation entrance
-> current-view extensional / one-step scoped entrance routes
-> nonempty finite witness for the scope
```

The canonical public spine theorem below is the visible-state route:

```text
current-view injective source/target
+ global current-view response-image equivalence
-> current-view response-image extensionality
-> current-view response-image completeness/equivalence
-> target-side scoped additive M/L-separation entrance
```

This is not the old G1 status/readout capstone and not a full semantic
no-alternative theorem.  In particular it does not prove arbitrary adapter
discovery, full native `L/B` and qualified-support `M` recovery,
certificate-free log accounting, or universal factorization for all
alternative representations.
-/

namespace Persistence.StructuralPersistence
namespace G1SemanticSpine

open AdditiveScalarCompositionObservedTrace
open ScopedMLSeparation

universe u v w x y z

/--
Canonical visible-state route into the current semantic G1 spine.

This theorem is the narrow public reading of the current load-bearing semantic
track.  It does not discover an arbitrary adapter: the global current-view
response-image equivalence, visible-state injectivity on both sides, and the
selected same-current-view target state remain explicit hypotheses.  Under
those scoped observational hypotheses, injectivity supplies extensionality,
global equivalence folds to local current-view response-image equivalence, and
the existing scoped additive M/L-separation entrance is reached on the target
side.
-/
theorem currentViewInjective_globalResponseEquiv_forces_scopedAdditiveMLSeparation
    {State : Type u} {Action : Type v} {Observation : Type w}
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {P : ObservationalPersistenceProcess State Action Observation}
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
      ScopedAdditiveMLSeparationConclusion targetSource := by
  have sourceExtensional : CurrentViewResponseImageExtensional P :=
    currentViewResponseImageExtensional_of_injective_currentView
      P sourceInjective
  have targetExtensional : CurrentViewResponseImageExtensional alternative :=
    currentViewResponseImageExtensional_of_injective_currentView
      alternative targetInjective
  have localEquivalent : CurrentViewResponseImageEquivalent P alternative :=
    currentViewResponseImageEquivalent_of_globalResponseImageEquivalent
      equivalent sourceExtensional targetExtensional
  exact
    exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageEquivalent
      source localEquivalent hview

/--
Canonical observation-only skeleton route for the strong G1 inevitability
target.

This theorem exposes the current non-ledger core in one place: from an
observation-only response separation, the state-carrier `F/K/V_K` scaffold
induces the same viable predicate as the observed readout, constant-response
collapse is blocked, and the calculation reaches the scoped additive
M/L-separation entrance.

It is not the full no-alternative theorem.  It does not yet quantify over a
competing representation and does not recover full native `L/B` or qualified
support `M`.
-/
theorem observationOnly_responseSeparated_forces_currentInevitabilitySkeleton
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (h : A.ResponseSeparated) :
    (forall s,
      s ∈ A.coreInterface.inducedViableState ↔
        A.process.readout s = BoundaryStatus.viable) ∧
    A.NonCollapse ∧
    ∃ source : ResponseSeparatedCompositionSource A.process,
      ScopedAdditiveMLSeparationConclusion source :=
  A.responseSeparated_forces_current_inevitability_skeleton h

/--
Observation-only response separation produces the current output-only G1
inevitability skeleton interface.

This is the package form of
`observationOnly_responseSeparated_forces_currentInevitabilitySkeleton`: the
core `F/K/V_K`, induced boundary agreement, non-collapse proof, and scoped
M/L-separation entrance are returned in the conclusion.  The theorem is still a
skeleton, not full semantic no-alternative closure.
-/
theorem observationOnly_responseSeparated_forces_currentSkeletonInterface
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (h : A.ResponseSeparated) :
    Nonempty (CurrentInevitabilitySkeletonInterface A) :=
  A.nonempty_currentInevitabilitySkeletonInterface h

/--
Observation-only source separation transports to a scoped target-side M/L
entrance under the current visible-state equivalence route.

Unlike `currentViewInjective_globalResponseEquiv_forces_scopedAdditiveMLSeparation`,
this theorem does not take a supplied response-separated composition source as
an input.  The source is constructed from the observation-only response
difference at `sourceState`.  This is still a scoped entrance theorem, not the
full no-alternative factorization theorem.
-/
theorem observationOnly_globalResponseEquiv_forces_targetScopedAdditiveMLSeparation
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalResponseImageEquivalent A.process alternative)
    (sourceInjective : Function.Injective A.process.currentView)
    (targetInjective : Function.Injective alternative.currentView)
    (hview :
      alternative.currentView targetInitialState =
        A.process.currentView sourceState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      ScopedAdditiveMLSeparationConclusion targetSource := by
  let source : ResponseSeparatedCompositionSource A.process :=
    { initialState := sourceState
      burdenAction := adverseAction
      supportAction := recoveryAction
      burdenUnit := 1
      supportUnit := 1
      burdenUnit_pos := by decide
      supportUnit_pos := by decide
      response_ne := response_ne }
  exact
    currentViewInjective_globalResponseEquiv_forces_scopedAdditiveMLSeparation
      source equivalent sourceInjective targetInjective hview

/--
Observation-only source separation forces a target-side current skeleton
interface under the current visible-state equivalence route.

Compared with
`observationOnly_globalResponseEquiv_forces_targetScopedAdditiveMLSeparation`,
the target side is also required to be an observation-only rigorous calculation
for the same target type.  No target `K/V_K/L-B/M` fields are supplied: once the
target response-separated source is obtained by the visible-state route, the
target skeleton interface is constructed by
`nonempty_currentInevitabilitySkeletonInterface`.

Target identity is still explicit: the theorem requires and returns equality of
the maintained targets.  It does not derive that equality from response-image
equivalence.

This is still not the full no-alternative theorem: it shows that the target
also enters the current skeleton, not yet that two skeletons are uniquely the
same interface up to equivalence.
-/
theorem observationOnly_globalResponseEquiv_forces_targetSkeletonInterface
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewGlobalResponseImageEquivalent A.process B.process)
    (target_eq : B.maintainedTarget = A.maintainedTarget)
    (sourceInjective : Function.Injective A.process.currentView)
    (targetInjective : Function.Injective B.process.currentView)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState) :
    B.maintainedTarget = A.maintainedTarget ∧
      Nonempty (CurrentInevitabilitySkeletonInterface B) := by
  rcases
    observationOnly_globalResponseEquiv_forces_targetScopedAdditiveMLSeparation
      A sourceState adverseAction recoveryAction response_ne
      equivalent sourceInjective targetInjective hview with
    ⟨targetSource, _targetConclusion⟩
  exact
    ⟨target_eq,
      B.nonempty_currentInevitabilitySkeletonInterface
        ⟨targetSource.initialState,
          targetSource.burdenAction,
          targetSource.supportAction,
          targetSource.response_ne⟩⟩

/--
Current-view response-image completeness gives source and target current
skeleton interfaces without a fixed action translator.

This is the translator-free Gate-5 boundary.  It removes the supplied
`toAction` / `traceBehaviorRelated` hypotheses by using only role-free
current-view response-image completeness, but the conclusion is deliberately
weaker than `TraceAligned`: the target skeleton exists and factors through the
current surface, yet the source-generated burden/support composition traces
are not identified with the target-generated traces.  That trace alignment is
the remaining fixed-translator / generated-prefix wall.
-/
theorem observationOnly_responseImageComplete_forces_unalignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (complete : CurrentViewResponseImageComplete A.process B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        B.maintainedTarget = A.maintainedTarget := by
  let source : ResponseSeparatedCompositionSource A.process :=
    { initialState := sourceState
      burdenAction := adverseAction
      supportAction := recoveryAction
      burdenUnit := 1
      supportUnit := 1
      burdenUnit_pos := by decide
      supportUnit_pos := by decide
      response_ne := response_ne }
  rcases
    exists_target_scopedAdditiveMLSeparation_of_currentViewResponseImageComplete
      source complete hview with
    ⟨targetSource, targetSeparation⟩
  let I : CurrentInevitabilitySkeletonInterface A :=
    { core := A.coreInterface
      viable_agrees := fun s => A.core_inducedViableState_iff s
      nonCollapse := A.nonCollapse_of_responseSeparated
        ⟨sourceState, adverseAction, recoveryAction, response_ne⟩
      mlSource := source
      mlSeparation :=
        responseSeparated_forces_scopedAdditiveMLSeparation source }
  let J : CurrentInevitabilitySkeletonInterface B :=
    { core := B.coreInterface
      viable_agrees := fun s => B.core_inducedViableState_iff s
      nonCollapse := B.nonCollapse_of_responseSeparated
        ⟨targetSource.initialState,
          targetSource.burdenAction,
          targetSource.supportAction,
          targetSource.response_ne⟩
      mlSource := targetSource
      mlSeparation := targetSeparation }
  exact
    ⟨I, J, I.factorsThroughCurrentSkeleton,
      J.factorsThroughCurrentSkeleton, target_eq⟩

/--
Global response-image inclusion plus target-side extensionality gives the same
translator-free source/target skeleton pair.

Target-side current-view response-image extensionality supplies the wall needed
to turn global image inclusion into local response-image completeness.  As
above, the result intentionally stops before `TraceAligned`: no fixed
translator or generated-prefix behavior is produced here.
-/
theorem observationOnly_globalResponseIncluded_forces_unalignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (included : CurrentViewGlobalResponseImageIncluded A.process B.process)
    (targetExtensional : CurrentViewResponseImageExtensional B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        B.maintainedTarget = A.maintainedTarget := by
  have localComplete :
      CurrentViewResponseImageComplete A.process B.process :=
    currentViewResponseImageComplete_of_globalResponseImageIncluded
      included targetExtensional
  exact
    observationOnly_responseImageComplete_forces_unalignedSkeletonInterfaces
      A B sourceState adverseAction recoveryAction response_ne
      localComplete hview target_eq

/--
Fixed trace-behavior preservation gives the current trace-aligned skeleton
surface.

This is the first Gate-5 shape: from an observation-only source response
separation and a role-free finite-trace behavior relation to a target
calculation, construct source and target current skeleton interfaces whose
generated two-channel composition trace languages agree.

Scope is explicit and intentionally strong: the action translator and
`traceBehaviorRelated` evidence are hypotheses.  Therefore this is not
arbitrary adapter discovery and not full same-interface uniqueness.  It is the
current aligned-skeleton theorem under a fixed observational translator.
-/
theorem observationOnly_traceBehavior_forces_traceAlignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (toAction : Action -> AlternativeAction)
    (hbehavior :
      traceBehaviorRelated A.process B.process toAction
        sourceState targetInitialState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        I.TraceAligned J := by
  let source : ResponseSeparatedCompositionSource A.process :=
    { initialState := sourceState
      burdenAction := adverseAction
      supportAction := recoveryAction
      burdenUnit := 1
      supportUnit := 1
      burdenUnit_pos := by decide
      supportUnit_pos := by decide
      response_ne := response_ne }
  let mapped :=
    source.toGeneratedPrefixMappedResponseSeparatedCompositionSource_of_traceBehaviorRelated
      toAction hbehavior
  let targetSource : ResponseSeparatedCompositionSource B.process :=
    targetResponseSeparatedSourceOfGeneratedPrefixMappedSource mapped
  let I : CurrentInevitabilitySkeletonInterface A :=
    { core := A.coreInterface
      viable_agrees := fun s => A.core_inducedViableState_iff s
      nonCollapse := A.nonCollapse_of_responseSeparated
        ⟨sourceState, adverseAction, recoveryAction, response_ne⟩
      mlSource := source
      mlSeparation :=
        responseSeparated_forces_scopedAdditiveMLSeparation source }
  let J : CurrentInevitabilitySkeletonInterface B :=
    { core := B.coreInterface
      viable_agrees := fun s => B.core_inducedViableState_iff s
      nonCollapse := B.nonCollapse_of_responseSeparated
        ⟨targetSource.initialState,
          targetSource.burdenAction,
          targetSource.supportAction,
          targetSource.response_ne⟩
      mlSource := targetSource
      mlSeparation :=
        generatedPrefixMapped_forces_target_scopedAdditiveMLSeparation
          mapped }
  refine ⟨I, J, I.factorsThroughCurrentSkeleton, J.factorsThroughCurrentSkeleton, ?_⟩
  refine
    { target_eq := target_eq
      traceLogOfCounts_eq := ?_ }
  intro burdenCount supportCount
  exact mapped.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
Fixed current-view action translation upgrades the unaligned skeleton route to
the trace-aligned skeleton route.

The hypothesis is still a visible wall: a fixed `toAction` is supplied together
with the role-free one-step law saying it preserves observable responses at
every same-current-view state pair.  The theorem does not discover arbitrary
adapters, but it no longer takes `traceBehaviorRelated` itself as an input; the
finite-prefix behavior relation is derived by induction.
-/
theorem observationOnly_fixedActionTranslator_forces_traceAlignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (toAction : Action -> AlternativeAction)
    (translator :
      CurrentViewFixedActionTranslator A.process B.process toAction)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        I.TraceAligned J := by
  exact
    observationOnly_traceBehavior_forces_traceAlignedSkeletonInterfaces
      A B sourceState adverseAction recoveryAction response_ne
      toAction
      (CurrentViewFixedActionTranslator.toTraceBehaviorRelated
        translator hview)
      target_eq

/--
Existence of a fixed current-view action translator is enough to enter the
trace-aligned skeleton route.

This removes the concrete `toAction` from the theorem surface, but it still
keeps the fixed-translator existence wall explicit.  It does not discover that
wall from arbitrary alternatives.
-/
theorem observationOnly_fixedActionTranslatorExists_forces_traceAlignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (translatorExists :
      CurrentViewFixedActionTranslatorExists A.process B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        I.TraceAligned J := by
  rcases translatorExists with ⟨toAction, translator⟩
  exact
    observationOnly_fixedActionTranslator_forces_traceAlignedSkeletonInterfaces
      A B sourceState adverseAction recoveryAction response_ne
      toAction translator hview target_eq

/--
Fixed action coverage enters the trace-aligned skeleton route through the
fixed-translator existence wall.

The antecedent is still observation-only, but this general form crosses the
expected choice boundary when selecting one uniform target action per source
action.  It is therefore a scoped general route, not a finite computable
adapter-discovery theorem.
-/
theorem observationOnly_fixedActionCoverage_forces_traceAlignedSkeletonInterfaces
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (coverage :
      CurrentViewFixedActionCoverage A.process B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.FactorsThroughCurrentSkeleton ∧
        J.FactorsThroughCurrentSkeleton ∧
        I.TraceAligned J := by
  exact
    observationOnly_fixedActionTranslatorExists_forces_traceAlignedSkeletonInterfaces
      A B sourceState adverseAction recoveryAction response_ne
      (CurrentViewFixedActionCoverage.toCurrentViewFixedActionTranslatorExists
        coverage)
      hview target_eq

/--
Canonical scoped G1 inevitability skeleton under fixed action coverage.

This is the current folded no-alternative skeleton surface: if a competing
observation-only calculation has fixed action coverage for the source actions,
then the source and competitor both factor through output-only current
skeleton interfaces and their generated two-channel composition traces align.

The scope is explicit.  `CurrentViewFixedActionCoverage` is the named
observation-only wall equivalent to fixed translator existence, and the general
route crosses `Classical.choice` when choosing one uniform target action per
source action.  This theorem is still not full native `L/B` recovery, not
qualified-support `M`, and not adapter discovery from weaker response-image or
trace-language inclusion alone.
-/
theorem g1_scopedInevitabilitySkeleton_of_fixedActionCoverage
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (coverage :
      CurrentViewFixedActionCoverage A.process B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.SameCurrentSkeletonSurface J := by
  rcases
    observationOnly_fixedActionCoverage_forces_traceAlignedSkeletonInterfaces
      A B sourceState adverseAction recoveryAction response_ne
      coverage hview target_eq with
    ⟨I, J, hI, hJ, haligned⟩
  exact ⟨I, J, hI, hJ, haligned⟩

/--
Canonical scoped G1 inevitability skeleton under the adopted current-view
observational same-calculation condition.

`CurrentViewObservationalSameCalculation` is definitionally fixed action
coverage: for each source action, a single target action preserves its
observable one-step response uniformly over all same-current-view state pairs.
The red tests show why this scope is explicit: response-image completeness,
trace-log language inclusion, and pair-local finite search are each too weak.

This is the current scoped G1 skeleton closure, not full native `L/B` recovery,
not qualified-support `M`, and not an unscoped theorem for hidden-state or
weaker adapter notions.  The general route inherits the `Classical.choice`
boundary from choosing one uniform target action per source action.
-/
theorem g1_scopedInevitabilitySkeleton_of_currentViewSameCalculation
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type x}
    {AlternativeState : Type y} {AlternativeAction : Type z}
    (A : ObservationallyRigorousCalc State Action Observation Target)
    (B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target)
    (sourceState : State)
    (adverseAction recoveryAction : Action)
    (response_ne :
      A.response sourceState adverseAction ≠
        A.response sourceState recoveryAction)
    {targetInitialState : AlternativeState}
    (sameCalculation :
      CurrentViewObservationalSameCalculation A.process B.process)
    (hview :
      B.process.currentView targetInitialState =
        A.process.currentView sourceState)
    (target_eq : B.maintainedTarget = A.maintainedTarget) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      ∃ J : CurrentInevitabilitySkeletonInterface B,
        I.SameCurrentSkeletonSurface J :=
  g1_scopedInevitabilitySkeleton_of_fixedActionCoverage
    A B sourceState adverseAction recoveryAction response_ne
    sameCalculation hview target_eq

end G1SemanticSpine
end Persistence.StructuralPersistence
