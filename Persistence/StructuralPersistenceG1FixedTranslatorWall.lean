import Persistence.StructuralPersistenceG1ObservationalCore

/-!
# G1 Fixed Translator Wall

This file records the small red test behind the current Gate-5 boundary:
current-view response-image completeness can produce target-side skeletons
without a fixed action translator, but it does not by itself produce
`traceBehaviorRelated`.

The toy target process realizes every one-step response image of the source at
same-current-view states, while swapping the meaning of one action after a
`low` step.  The formalized point is deliberately one-step: this completeness
is still not enough to produce a single global `toAction` preserving all finite
prefix logs from the initial state.
-/

namespace Persistence.StructuralPersistence

universe u v w x y

/--
Fixed current-view action translation.

This is the current observation-only sufficient wall exposed by the red test
below, not a minimal characterization.  A single translator `toAction` must
preserve every one-step observable response at every same-current-view state
pair.  It mentions only current views, one-step responses, and the fixed action
translator; no Structural Persistence roles are fields of this predicate.
-/
def CurrentViewFixedActionTranslator
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (toAction : ActionA -> ActionB) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      forall action : ActionA,
        B.response sB (toAction action) = A.response sA action

/--
Existence form of fixed current-view action translation.

This still does not discover an adapter from arbitrary alternatives.  It only
moves the fixed translator itself behind an observation-only existential
predicate, making the remaining wall explicit.
-/
def CurrentViewFixedActionTranslatorExists
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) :
    Prop :=
  ∃ toAction : ActionA -> ActionB,
    CurrentViewFixedActionTranslator A B toAction

/--
Fixed current-view action coverage.

This is one step below fixed translator existence: every source action has
some target action that preserves its one-step observable response uniformly
over all same-current-view state pairs.  It still mentions only current views,
one-step responses, and actions; no Structural Persistence roles are fields.
-/
def CurrentViewFixedActionCoverage
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) :
    Prop :=
  forall action : ActionA,
    ∃ targetAction : ActionB,
      forall {sA : StateA} {sB : StateB},
        B.currentView sB = A.currentView sA ->
          B.response sB targetAction = A.response sA action

/--
The adopted current-view observational same-calculation condition for the
scoped G1 skeleton.

This is a definitional alias for fixed action coverage.  The name records the
semantic decision forced by the red tests: weaker response-image,
trace-language, or pair-local finite-search conditions do not choose one
uniform target action per source action.  The predicate remains
observation-only and contains no Structural Persistence roles.
-/
def CurrentViewObservationalSameCalculation
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) :
    Prop :=
  CurrentViewFixedActionCoverage A B

namespace CurrentViewFixedActionTranslator

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {toAction : ActionA -> ActionB}

/--
A fixed current-view action translator yields canonical trace behavior by
finite-prefix induction.
-/
theorem toTraceBehaviorRelated
    (translator : CurrentViewFixedActionTranslator A B toAction)
    {sA : StateA} {sB : StateB}
    (hview : B.currentView sB = A.currentView sA) :
    traceBehaviorRelated A B toAction sA sB := by
  constructor
  · exact hview
  · intro actions
    induction actions generalizing sA sB with
    | nil => rfl
    | cons action actions ih =>
        have hhead :
            B.response sB (toAction action) = A.response sA action :=
          translator hview action
        have htail :
            A.traceLog (A.step sA action) actions =
              B.traceLog
                (B.step sB (toAction action))
                (actions.map toAction) :=
          ih hhead
        change
          A.response sA action ::
              A.traceLog (A.step sA action) actions =
            B.response sB (toAction action) ::
              B.traceLog
                (B.step sB (toAction action))
                (actions.map toAction)
        exact congrArg₂ List.cons hhead.symm htail

/--
The same fixed translator also gives a trace simulation whose relation is
equality of current observable views.
-/
def toTraceSimulation
    (translator : CurrentViewFixedActionTranslator A B toAction) :
    ObservationalTraceSimulation A B where
  related := fun sA sB => B.currentView sB = A.currentView sA
  toAction := toAction
  preserves_observation := by
    intro sA sB hview
    exact congrArg Prod.fst hview
  preserves_readout := by
    intro sA sB hview
    exact congrArg Prod.snd hview
  step_related := by
    intro sA sB hview action
    exact translator hview action

end CurrentViewFixedActionTranslator

namespace CurrentViewFixedActionTranslatorExists

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
The existential fixed-translator wall yields canonical trace behavior from any
same-current-view initial pair.
-/
theorem toTraceBehaviorRelated
    (translatorExists : CurrentViewFixedActionTranslatorExists A B)
    {sA : StateA} {sB : StateB}
    (hview : B.currentView sB = A.currentView sA) :
    ∃ toAction : ActionA -> ActionB,
      traceBehaviorRelated A B toAction sA sB := by
  rcases translatorExists with ⟨toAction, translator⟩
  exact ⟨toAction,
    CurrentViewFixedActionTranslator.toTraceBehaviorRelated
      translator hview⟩

/--
The existential fixed-translator wall yields some trace simulation.
-/
theorem toTraceSimulation
    (translatorExists : CurrentViewFixedActionTranslatorExists A B) :
    Nonempty (ObservationalTraceSimulation A B) := by
  rcases translatorExists with ⟨_toAction, translator⟩
  exact ⟨CurrentViewFixedActionTranslator.toTraceSimulation translator⟩

end CurrentViewFixedActionTranslatorExists

namespace CurrentViewFixedActionCoverage

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Fixed action coverage gives fixed translator existence.

The general form crosses the expected choice boundary: it chooses one uniform
target action for each source action.  Finite/decidable refinements should
replace this when a computable adapter is required.
-/
theorem toCurrentViewFixedActionTranslatorExists
    (coverage : CurrentViewFixedActionCoverage A B) :
    CurrentViewFixedActionTranslatorExists A B := by
  refine ⟨fun action => Classical.choose (coverage action), ?_⟩
  intro sA sB hview action
  exact Classical.choose_spec (coverage action) hview

/--
Any fixed translator gives fixed action coverage by taking its translated
target actions.
-/
theorem ofCurrentViewFixedActionTranslatorExists
    (translatorExists : CurrentViewFixedActionTranslatorExists A B) :
    CurrentViewFixedActionCoverage A B := by
  rcases translatorExists with ⟨toAction, translator⟩
  intro action
  exact ⟨toAction action, fun hview => translator hview action⟩

/--
Fixed action coverage is exactly the observation-only wall for fixed translator
existence.

The forward direction has the same general `Classical.choice` cost as
`toCurrentViewFixedActionTranslatorExists`: it chooses one uniform target action
for each source action.  The reverse direction is choice-free.
-/
theorem iff_currentViewFixedActionTranslatorExists :
    CurrentViewFixedActionCoverage A B ↔
      CurrentViewFixedActionTranslatorExists A B := by
  constructor
  · exact toCurrentViewFixedActionTranslatorExists
  · exact ofCurrentViewFixedActionTranslatorExists

end CurrentViewFixedActionCoverage

namespace CurrentViewObservationalSameCalculation

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/-- The adopted same-calculation predicate is fixed action coverage by definition. -/
theorem iff_currentViewFixedActionCoverage :
    CurrentViewObservationalSameCalculation A B ↔
      CurrentViewFixedActionCoverage A B :=
  Iff.rfl

/--
The adopted same-calculation predicate is equivalent to fixed translator
existence, with the same general `Classical.choice` cost in the forward
direction as fixed action coverage.
-/
theorem iff_currentViewFixedActionTranslatorExists :
    CurrentViewObservationalSameCalculation A B ↔
      CurrentViewFixedActionTranslatorExists A B :=
  CurrentViewFixedActionCoverage.iff_currentViewFixedActionTranslatorExists

end CurrentViewObservationalSameCalculation

namespace G1FixedTranslatorWall

inductive SwapState where
  | start
  | low
  | high
  deriving DecidableEq

inductive SwapAction where
  | low
  | high
  deriving DecidableEq

inductive SwapObservation where
  | low
  | high
  deriving DecidableEq

def observe : SwapState -> SwapObservation
  | SwapState.start => SwapObservation.low
  | SwapState.low => SwapObservation.low
  | SwapState.high => SwapObservation.high

def sourceStep : SwapState -> SwapAction -> SwapState
  | _, SwapAction.low => SwapState.low
  | _, SwapAction.high => SwapState.high

def targetStep : SwapState -> SwapAction -> SwapState
  | SwapState.start, SwapAction.low => SwapState.low
  | SwapState.start, SwapAction.high => SwapState.high
  | SwapState.low, SwapAction.low => SwapState.high
  | SwapState.low, SwapAction.high => SwapState.low
  | SwapState.high, SwapAction.low => SwapState.low
  | SwapState.high, SwapAction.high => SwapState.high

def sourceProcess :
    ObservationalPersistenceProcess SwapState SwapAction SwapObservation where
  observe := observe
  step := sourceStep
  readout := fun _ => BoundaryStatus.viable

def targetProcess :
    ObservationalPersistenceProcess SwapState SwapAction SwapObservation where
  observe := observe
  step := targetStep
  readout := fun _ => BoundaryStatus.viable

/--
The target process realizes every one-step response image of the source at
same-current-view states.
-/
theorem target_currentViewResponseImageComplete :
    CurrentViewResponseImageComplete sourceProcess targetProcess := by
  intro _sA sB _hview response hsource
  rcases hsource with ⟨action, hresponse⟩
  subst response
  cases sB <;> cases action
  · exact ⟨SwapAction.low, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩
  · exact ⟨SwapAction.high, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩
  · exact ⟨SwapAction.high, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩
  · exact ⟨SwapAction.low, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩
  · exact ⟨SwapAction.low, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩
  · exact ⟨SwapAction.high, by
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep]⟩

/--
Therefore the toy target also has current-view trace-log language inclusion:
each finite source log can be realized by some target action list.

The point of the red test below is that this language-level inclusion still
does not choose one fixed action translator.
-/
theorem target_currentViewTraceLogLanguageIncluded :
    CurrentViewTraceLogLanguageIncluded sourceProcess targetProcess :=
  CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
    target_currentViewResponseImageComplete

/-- The toy target action space is explicitly finite. -/
def swapActionEnumeration : FiniteActionEnumeration SwapAction where
  candidates := [SwapAction.low, SwapAction.high]
  fallback := SwapAction.low
  complete := by
    intro action
    cases action <;> simp

/--
With the explicit finite target-action enumeration, the toy target even has
current-view finite action-response search.

The red test below therefore rules out a tempting shortcut: pair-local finite
search is still weaker than fixed action coverage.
-/
def target_currentViewFiniteActionResponseSearch :
    CurrentViewFiniteActionResponseSearch sourceProcess targetProcess :=
  CurrentViewResponseImageComplete.toCurrentViewFiniteActionResponseSearch
    swapActionEnumeration target_currentViewResponseImageComplete

/--
Nevertheless, no fixed action translator preserves all finite prefix logs from
the initial state.

The singleton trace `[low]` forces `low` to translate to `low` at `start`, but
then the trace `[low, low]` fails after the target process swaps the action
meaning at the reached `low` state.
-/
theorem no_fixedTraceBehaviorRelated_from_responseImageComplete :
    ¬
      ∃ toAction : SwapAction -> SwapAction,
        traceBehaviorRelated sourceProcess targetProcess toAction
          SwapState.start SwapState.start := by
  rintro ⟨toAction, hbehavior⟩
  cases hlow : toAction SwapAction.low with
  | low =>
      have htwo := hbehavior.2 [SwapAction.low, SwapAction.low]
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.traceLog,
        observe, sourceStep, targetStep, hlow] at htwo
  | high =>
      have hone := hbehavior.2 [SwapAction.low]
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.traceLog,
        observe, sourceStep, targetStep, hlow] at hone

/--
Consequently, the toy process has no fixed current-view action translator.

This sharpens the wall: pointwise one-step response-image completeness gives
target-side one-step witnesses, but not one fixed translator that supports
finite-prefix trace behavior.
-/
theorem not_currentViewFixedActionTranslatorExists :
    ¬ CurrentViewFixedActionTranslatorExists sourceProcess targetProcess := by
  intro translatorExists
  rcases CurrentViewFixedActionTranslatorExists.toTraceBehaviorRelated
      translatorExists (sA := SwapState.start) (sB := SwapState.start) rfl with
    ⟨toAction, hbehavior⟩
  exact no_fixedTraceBehaviorRelated_from_responseImageComplete
    ⟨toAction, hbehavior⟩

/--
The toy process also fails fixed action coverage itself.

For the source `low` action, a target `high` action already fails at `start`;
a target `low` action fails after moving to the `low` current view, where the
target swaps the action meaning.
-/
theorem not_currentViewFixedActionCoverage :
    ¬ CurrentViewFixedActionCoverage sourceProcess targetProcess := by
  intro coverage
  rcases coverage SwapAction.low with ⟨targetAction, htarget⟩
  cases htarget_low : targetAction with
  | low =>
      have h := htarget (sA := SwapState.low) (sB := SwapState.low) rfl
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep, htarget_low] at h
  | high =>
      have h := htarget (sA := SwapState.start) (sB := SwapState.start) rfl
      simp [sourceProcess, targetProcess,
        ObservationalPersistenceProcess.response,
        observe, sourceStep, targetStep, htarget_low] at h

end G1FixedTranslatorWall
end Persistence.StructuralPersistence
