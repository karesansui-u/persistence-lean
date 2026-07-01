import Persistence.StructuralPersistenceG1SemanticCore
import Persistence.RepresentationTheorem

/-!
# G1 Observational Core

This module starts the G1c proof-substance track.  It deliberately avoids the
internal role vocabulary of realization carriers, viable regions, loss,
burden, or support.  The only primitive data here are observable states,
actions, observations, one-step responses, and boundary readouts.

The first test theorem is negative: if two actions have observably different
responses, then any response-preserving one-coordinate action model must assign
them different coordinates.  This is not the full burden/support separation
theorem.  It is the small observational anti-collapse lemma that such a theorem
should consume.
-/

namespace Persistence.StructuralPersistence

universe u v w x y z t r p q a b c

/--
An observational persistence process.

No structural-persistence roles are fields of this object.  It only records
what can be observed before and after an action, together with a boundary
readout.
-/
structure ObservationalPersistenceProcess
    (State : Type u) (Action : Type v) (Observation : Type w) where
  observe : State -> Observation
  step : State -> Action -> State
  readout : State -> BoundaryStatus

namespace ObservationalPersistenceProcess

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable (P : ObservationalPersistenceProcess State Action Observation)

/-- The observable one-step response to an action at a state. -/
def response (s : State) (a : Action) : Observation × BoundaryStatus :=
  (P.observe (P.step s a), P.readout (P.step s a))

/-- Run a finite action trace from an initial state. -/
def run (s : State) (actions : List Action) : State :=
  actions.foldl P.step s

/-- Log the observable post-action view at every prefix of a finite trace. -/
def traceLog : State -> List Action -> List (Observation × BoundaryStatus)
  | _, [] => []
  | s, action :: actions =>
      let nextState := P.step s action
      (P.observe nextState, P.readout nextState) ::
        traceLog nextState actions

/-- Boundary statuses at every post-action prefix of a finite trace. -/
def prefixBoundaryReadout (s : State) (actions : List Action) :
    List BoundaryStatus :=
  (P.traceLog s actions).map Prod.snd

/-- The observable response after a finite action trace. -/
def traceResponse (s : State) (actions : List Action) :
    Observation × BoundaryStatus :=
  let finalState := P.run s actions
  (P.observe finalState, P.readout finalState)

/-- The current observable view before an action is applied. -/
def currentView (s : State) : Observation × BoundaryStatus :=
  (P.observe s, P.readout s)

end ObservationalPersistenceProcess

/--
The current observable view determines all future finite prefix logs.

This is a scope condition, not an arbitrary-alternative theorem: it says that
there is no hidden same-current-view state that can later produce a different
trace log under the same action trace.
-/
def CurrentViewTraceLogExtensional
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) : Prop :=
  forall {sourceState targetState : State},
    P.currentView sourceState = P.currentView targetState ->
      forall actions : List Action,
        P.traceLog sourceState actions = P.traceLog targetState actions

/--
One-step responses are determined by the current observable view.

This is a local, role-free condition: hidden states with the same current view
are allowed, but they must have the same observable post-action response for
each action.  It is weaker than requiring the current view to determine the
state, and stronger than merely asking for equal one-step response images.
-/
def CurrentViewOneStepExtensional
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) : Prop :=
  forall {sourceState targetState : State},
    P.currentView sourceState = P.currentView targetState ->
      forall action : Action,
        P.response sourceState action = P.response targetState action

/--
Local current-view one-step extensionality determines every future finite
prefix log.

The proof is the finite-prefix induction that the semantic G1 route needs:
same current view gives the same first observable response, and that first
response is exactly the next current view needed for the induction tail.
-/
theorem currentViewTraceLogExtensional_of_oneStepExtensional
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (oneStep : CurrentViewOneStepExtensional P) :
    CurrentViewTraceLogExtensional P := by
  intro sourceState targetState hview actions
  induction actions generalizing sourceState targetState with
  | nil => rfl
  | cons action actions ih =>
      have hhead :
          P.response sourceState action =
            P.response targetState action :=
        oneStep hview action
      have htail :
          P.traceLog (P.step sourceState action) actions =
            P.traceLog (P.step targetState action) actions :=
        ih hhead
      exact congrArg₂ List.cons hhead htail

/--
If the current observable view determines the state, then it determines every
future finite prefix log.

This is the visible-state route into trace-log extensionality.  It does not
say that arbitrary alternatives are trace-log extensional; it records a simple
sufficient condition where no hidden same-current-view state remains.
-/
theorem currentViewTraceLogExtensional_of_currentView_injective
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (hinjective : Function.Injective P.currentView) :
    CurrentViewTraceLogExtensional P := by
  intro sourceState targetState hview actions
  have hstate : sourceState = targetState := hinjective hview
  subst targetState
  rfl

/--
One-state action-response coverage for an alternative process.

This is the local obstruction behind the arbitrary-alternative G1 target:
before an action translation can be constructed, every source action response
at the selected source state must be realized by some target action at the
selected target state.  This definition is purely observational; it mentions
only one-step responses, not burden/support roles or viability structure.
-/
def ActionResponseCoverageAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  forall action : ActionA,
    ∃ targetAction : ActionB,
      B.response sB targetAction = A.response sA action

namespace ActionResponseCoverageAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Choose an action translation from observational response coverage.

The use of `Classical.choose` is intentional: in the general, non-finite
setting, pointwise existence of matching target actions does not by itself
provide a computable canonical translator.
-/
noncomputable def toAction
    (coverage : ActionResponseCoverageAt A B sA sB) :
    ActionA -> ActionB :=
  fun action => Classical.choose (coverage action)

/-- The chosen action translation preserves one-step responses. -/
theorem toAction_preserves_response
    (coverage : ActionResponseCoverageAt A B sA sB)
    (action : ActionA) :
    B.response sB (coverage.toAction action) =
      A.response sA action :=
  Classical.choose_spec (coverage action)

/--
Action-response coverage is sufficient to produce a response-preserving
action translation at the selected state.
-/
theorem exists_responsePreserving_toAction
    (coverage : ActionResponseCoverageAt A B sA sB) :
    ∃ toAction : ActionA -> ActionB,
      forall action,
        B.response sB (toAction action) =
          A.response sA action :=
  ⟨coverage.toAction, coverage.toAction_preserves_response⟩

end ActionResponseCoverageAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Any response-preserving action translation supplies action-response coverage.
-/
theorem actionResponseCoverageAt_of_exists_responsePreserving_toAction
    (h :
      ∃ toAction : ActionA -> ActionB,
        forall action,
          B.response sB (toAction action) =
            A.response sA action) :
    ActionResponseCoverageAt A B sA sB := by
  rcases h with ⟨toAction, htoAction⟩
  intro action
  exact ⟨toAction action, htoAction action⟩

/--
If some source action response is not realized by any target action, no
response-preserving action translation can exist.
-/
theorem no_responsePreserving_toAction_without_actionResponseCoverage
    (hmissing :
      ∃ action : ActionA,
        forall targetAction : ActionB,
          B.response sB targetAction ≠ A.response sA action) :
    ¬
      ∃ toAction : ActionA -> ActionB,
        forall action,
          B.response sB (toAction action) =
            A.response sA action := by
  intro htranslator
  rcases hmissing with ⟨action, hmissing_action⟩
  rcases htranslator with ⟨toAction, htoAction⟩
  exact hmissing_action (toAction action) (htoAction action)

/--
At a selected state pair, action-response coverage is exactly the condition
for the existence of a response-preserving action translation.  The forward
direction chooses one matching target action per source action.
-/
theorem actionResponseCoverageAt_iff_exists_responsePreserving_toAction :
    ActionResponseCoverageAt A B sA sB ↔
      ∃ toAction : ActionA -> ActionB,
        forall action,
          B.response sB (toAction action) =
            A.response sA action := by
  constructor
  · intro coverage
    exact coverage.exists_responsePreserving_toAction
  · intro h
    exact actionResponseCoverageAt_of_exists_responsePreserving_toAction h

/--
Observational response-image preservation at a selected state pair.

This is the role-free observational condition immediately below
`ActionResponseCoverageAt`: every one-step response observed from the source
state is also realized by some target action at the target state.  It does not
supply an action translator and does not mention viability, burden, support, or
other G1 roles.
-/
def ResponseImagePreservationAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  forall response : Observation × BoundaryStatus,
    (∃ action : ActionA,
      A.response sA action = response) ->
      ∃ targetAction : ActionB,
        B.response sB targetAction = response

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Response-image preservation gives action-response coverage without choosing a
global action translator.  The target witness is selected only inside the proof
of the local coverage proposition.
-/
theorem actionResponseCoverageAt_of_responseImagePreservationAt
    (himage : ResponseImagePreservationAt A B sA sB) :
    ActionResponseCoverageAt A B sA sB := by
  intro action
  exact himage (A.response sA action) ⟨action, rfl⟩

/--
Action-response coverage is exactly response-image preservation: coverage
realizes every source response, while image preservation is the same statement
phrased without naming source actions in the conclusion.
-/
theorem responseImagePreservationAt_of_actionResponseCoverageAt
    (coverage : ActionResponseCoverageAt A B sA sB) :
    ResponseImagePreservationAt A B sA sB := by
  intro response hsource
  rcases hsource with ⟨action, hresponse⟩
  rcases coverage action with ⟨targetAction, htarget⟩
  exact ⟨targetAction, htarget.trans hresponse⟩

/--
At a selected state pair, observational response-image preservation is
equivalent to action-response coverage.  This equivalence is still local; it
does not construct a global `toAction`.
-/
theorem responseImagePreservationAt_iff_actionResponseCoverageAt :
    ResponseImagePreservationAt A B sA sB ↔
      ActionResponseCoverageAt A B sA sB := by
  constructor
  · exact actionResponseCoverageAt_of_responseImagePreservationAt
  · exact responseImagePreservationAt_of_actionResponseCoverageAt

/--
If a source one-step response is missing from the target response image, then
observational response-image preservation fails.
-/
theorem no_responseImagePreservationAt_without_actionResponseCoverage
    (hmissing :
      ∃ action : ActionA,
        forall targetAction : ActionB,
          B.response sB targetAction ≠ A.response sA action) :
    ¬ ResponseImagePreservationAt A B sA sB := by
  intro himage
  rcases hmissing with ⟨action, hmissing_action⟩
  rcases himage (A.response sA action) ⟨action, rfl⟩ with
    ⟨targetAction, htarget⟩
  exact hmissing_action targetAction htarget

/--
Role-free trace-log image preservation at a selected state pair.

Every finite source prefix log must be realized by some target action trace,
but no action translator is supplied.  This is weaker than a
`traceBehaviorRelated` witness: each source trace may be matched by a different
target trace.
-/
def TraceLogImagePreservationAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  forall actions : List ActionA,
    ∃ targetActions : List ActionB,
      B.traceLog sB targetActions = A.traceLog sA actions

/--
Trace-log image preservation implies one-step response-image preservation:
apply the trace-image hypothesis to singleton source traces and read the head
of the matching target trace.
-/
theorem responseImagePreservationAt_of_traceLogImagePreservationAt
    (htrace : TraceLogImagePreservationAt A B sA sB) :
    ResponseImagePreservationAt A B sA sB := by
  intro response hsource
  rcases hsource with ⟨action, hresponse⟩
  rcases htrace [action] with ⟨targetActions, hlog⟩
  cases targetActions with
  | nil =>
      change [] = [A.response sA action] at hlog
      cases hlog
  | cons targetAction rest =>
      change
        B.response sB targetAction ::
            B.traceLog (B.step sB targetAction) rest =
          [A.response sA action] at hlog
      have hhead :
          B.response sB targetAction = A.response sA action :=
        (List.cons.inj hlog).1
      exact ⟨targetAction, hhead.trans hresponse⟩

/-- Trace-log image preservation is sufficient for local action-response coverage. -/
theorem actionResponseCoverageAt_of_traceLogImagePreservationAt
    (htrace : TraceLogImagePreservationAt A B sA sB) :
    ActionResponseCoverageAt A B sA sB :=
  actionResponseCoverageAt_of_responseImagePreservationAt
    (responseImagePreservationAt_of_traceLogImagePreservationAt htrace)

/--
If a one-step source response is missing from the target response image, then
even trace-log image preservation cannot hold: the singleton source trace has
no possible target trace with the same prefix log.
-/
theorem no_traceLogImagePreservationAt_without_actionResponseCoverage
    (hmissing :
      ∃ action : ActionA,
        forall targetAction : ActionB,
          B.response sB targetAction ≠ A.response sA action) :
    ¬ TraceLogImagePreservationAt A B sA sB := by
  intro htrace
  rcases hmissing with ⟨action, hmissing_action⟩
  rcases htrace [action] with ⟨targetActions, hlog⟩
  cases targetActions with
  | nil =>
      change [] = [A.response sA action] at hlog
      simp at hlog
  | cons targetAction rest =>
      change
        B.response sB targetAction ::
            B.traceLog (B.step sB targetAction) rest =
          [A.response sA action] at hlog
      have hhead :
          B.response sB targetAction = A.response sA action :=
        (List.cons.inj hlog).1
      exact hmissing_action targetAction hhead

/--
Finite-search action-response coverage at a selected state pair.

This is a stricter, choice-bounded version of `ActionResponseCoverageAt`: every
source action response must be realized by some member of an explicit target
candidate list.  The list and fallback remain supplied data; this is not
automatic target-action discovery for arbitrary alternatives.
-/
structure FiniteActionResponseSearchAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) where
  candidates : List ActionB
  fallback : ActionB
  complete :
    forall action : ActionA,
      ∃ targetAction : ActionB,
        targetAction ∈ candidates ∧
          B.response sB targetAction = A.response sA action

namespace FiniteActionResponseSearchAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

section Search

variable [DecidableEq Observation]

/-- Search an explicit target-action list for the first matching response. -/
def firstMatchingActionIn? :
    List ActionB -> ActionA -> Option ActionB
  | [], _ => none
  | targetAction :: rest, action =>
      if B.response sB targetAction = A.response sA action then
        some targetAction
      else
        firstMatchingActionIn? rest action

/-- Any action returned by finite response search preserves the selected one-step response. -/
theorem firstMatchingActionIn?_sound
    (candidates : List ActionB)
    (action : ActionA)
    {targetAction : ActionB}
    (hfind :
      firstMatchingActionIn?
        (A := A) (B := B) (sA := sA) (sB := sB)
        candidates action = some targetAction) :
    B.response sB targetAction = A.response sA action := by
  induction candidates with
  | nil =>
      change none = some targetAction at hfind
      cases hfind
  | cons candidate rest ih =>
      by_cases hmatch :
          B.response sB candidate = A.response sA action
      · have hsome : some candidate = some targetAction := by
          rw [firstMatchingActionIn?, if_pos hmatch] at hfind
          exact hfind
        cases hsome
        exact hmatch
      · have hfind_tail :
            firstMatchingActionIn?
                (A := A) (B := B) (sA := sA) (sB := sB)
                rest action = some targetAction := by
          rw [firstMatchingActionIn?, if_neg hmatch] at hfind
          exact hfind
        exact ih hfind_tail

/-- Any action returned by finite response search belongs to the supplied candidate list. -/
theorem firstMatchingActionIn?_mem
    (candidates : List ActionB)
    (action : ActionA)
    {targetAction : ActionB}
    (hfind :
      firstMatchingActionIn?
        (A := A) (B := B) (sA := sA) (sB := sB)
        candidates action = some targetAction) :
    targetAction ∈ candidates := by
  induction candidates with
  | nil =>
      change none = some targetAction at hfind
      cases hfind
  | cons candidate rest ih =>
      by_cases hmatch :
          B.response sB candidate = A.response sA action
      · have hsome : some candidate = some targetAction := by
          rw [firstMatchingActionIn?, if_pos hmatch] at hfind
          exact hfind
        cases hsome
        exact List.Mem.head rest
      · have hfind_tail :
            firstMatchingActionIn?
                (A := A) (B := B) (sA := sA) (sB := sB)
                rest action = some targetAction := by
          rw [firstMatchingActionIn?, if_neg hmatch] at hfind
          exact hfind
        exact List.mem_cons_of_mem candidate (ih hfind_tail)

/--
If a matching candidate exists in the list, finite response search returns a
matching candidate.
-/
theorem firstMatchingActionIn?_complete
    (candidates : List ActionB)
    (action : ActionA)
    (hcomplete :
      ∃ targetAction : ActionB,
        targetAction ∈ candidates ∧
          B.response sB targetAction = A.response sA action) :
    ∃ targetAction : ActionB,
      firstMatchingActionIn?
          (A := A) (B := B) (sA := sA) (sB := sB)
          candidates action = some targetAction ∧
        B.response sB targetAction = A.response sA action ∧
        targetAction ∈ candidates := by
  induction candidates with
  | nil =>
      rcases hcomplete with ⟨targetAction, hmem, _⟩
      cases hmem
  | cons candidate rest ih =>
      by_cases hmatch :
          B.response sB candidate = A.response sA action
      · refine ⟨candidate, ?_, hmatch, ?_⟩
        · rw [firstMatchingActionIn?, if_pos hmatch]
        · exact List.Mem.head rest
      · rcases hcomplete with ⟨targetAction, hmem, hresponse⟩
        have hrest_complete :
            ∃ targetAction : ActionB,
              targetAction ∈ rest ∧
                B.response sB targetAction = A.response sA action := by
          cases hmem with
          | head =>
              exact False.elim (hmatch hresponse)
          | tail _ htail =>
              exact ⟨targetAction, htail, hresponse⟩
        rcases ih hrest_complete with
          ⟨foundAction, hfind, hfound_response, hfound_mem⟩
        refine ⟨foundAction, ?_, hfound_response, ?_⟩
        · rw [firstMatchingActionIn?, if_neg hmatch]
          exact hfind
        · exact List.mem_cons_of_mem candidate hfound_mem

variable (search : FiniteActionResponseSearchAt A B sA sB)

/-- The finite search result for one source action. -/
def firstMatchingAction? (action : ActionA) : Option ActionB :=
  firstMatchingActionIn?
    (A := A) (B := B) (sA := sA) (sB := sB)
    search.candidates action

/-- A total action translator produced by explicit finite response search. -/
def toAction (action : ActionA) : ActionB :=
  (search.firstMatchingAction? action).getD search.fallback

/-- The finite search returns a matching target action for every source action. -/
theorem firstMatchingAction?_complete
    (action : ActionA) :
    ∃ targetAction : ActionB,
      search.firstMatchingAction? action = some targetAction ∧
        B.response sB targetAction = A.response sA action ∧
        targetAction ∈ search.candidates :=
  firstMatchingActionIn?_complete
    (A := A) (B := B) (sA := sA) (sB := sB)
    search.candidates action (search.complete action)

/--
The finite-search translator preserves selected one-step responses without
using `Classical.choice`; the fallback is unreachable under `complete`.
-/
theorem toAction_preserves_response
    (action : ActionA) :
    B.response sB (search.toAction action) =
      A.response sA action := by
  rcases search.firstMatchingAction?_complete action with
    ⟨targetAction, hfind, hresponse, _⟩
  unfold toAction
  rw [hfind]
  exact hresponse

/-- The finite-search translator always selects from the supplied candidate list. -/
theorem toAction_mem_candidates
    (action : ActionA) :
    search.toAction action ∈ search.candidates := by
  rcases search.firstMatchingAction?_complete action with
    ⟨targetAction, hfind, _, hmem⟩
  unfold toAction
  rw [hfind]
  exact hmem

end Search

/-- Finite search gives the ordinary action-response coverage property. -/
theorem toAction_coverage
    [DecidableEq Observation]
    (search : FiniteActionResponseSearchAt A B sA sB) :
    ActionResponseCoverageAt A B sA sB ∧
      forall action,
        B.response sB (search.toAction action) =
          A.response sA action := by
  refine ⟨?_, toAction_preserves_response search⟩
  intro action
  exact ⟨search.toAction action, toAction_preserves_response search action⟩

/-- Finite search gives an explicit response-preserving action translation. -/
theorem exists_responsePreserving_toAction
    [DecidableEq Observation]
    (search : FiniteActionResponseSearchAt A B sA sB) :
    ∃ toAction : ActionA -> ActionB,
      toAction = search.toAction ∧
        forall action,
          B.response sB (toAction action) =
            A.response sA action :=
  ⟨toAction search, rfl, toAction_preserves_response search⟩

end FiniteActionResponseSearchAt

/--
A finite exhaustive action enumeration.

This is weaker than supplying a separate candidate list at every state pair:
one global list contains every action of the target action type.  A fallback is
kept because `FiniteActionResponseSearchAt` produces total translators by
`Option.getD`, even though completeness makes the fallback unreachable.
-/
structure FiniteActionEnumeration (Action : Type u) where
  candidates : List Action
  fallback : Action
  complete : forall action : Action, action ∈ candidates

namespace FiniteActionEnumeration

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Global finite target-action enumeration turns ordinary local coverage into a
finite-search object, without supplying a state-specific candidate list.
-/
def toFiniteActionResponseSearchAt
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (coverage : ActionResponseCoverageAt A B sA sB) :
    FiniteActionResponseSearchAt A B sA sB where
  candidates := targetEnumeration.candidates
  fallback := targetEnumeration.fallback
  complete := by
    intro action
    rcases coverage action with ⟨targetAction, hresponse⟩
    exact
      ⟨targetAction, targetEnumeration.complete targetAction, hresponse⟩

end FiniteActionEnumeration

/--
An observational response-preserving map between processes.

This is the observational version of "same calculation": it preserves current
observations, current boundary readouts, and one-step action responses.  It
does not mention target carriers, viable regions, burden, or support.
-/
structure ObservationalResponseMap
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  toState : StateA -> StateB
  toAction : ActionA -> ActionB
  preserves_observation :
    forall s, B.observe (toState s) = A.observe s
  preserves_readout :
    forall s, B.readout (toState s) = A.readout s
  preserves_response :
    forall s a, B.response (toState s) (toAction a) = A.response s a

namespace ObservationalResponseMap

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (phi : ObservationalResponseMap A B)

/-- Current observation/readout views are preserved by an observational map. -/
theorem preserves_currentView
    (s : StateA) :
    B.currentView (phi.toState s) = A.currentView s := by
  exact Prod.ext (phi.preserves_observation s) (phi.preserves_readout s)

/--
Observed response distinctions cannot disappear under a response-preserving
map.
-/
theorem preserves_distinguished_response
    {s : StateA} {a₁ a₂ : ActionA}
    (h : A.response s a₁ ≠ A.response s a₂) :
    B.response (phi.toState s) (phi.toAction a₁) ≠
      B.response (phi.toState s) (phi.toAction a₂) := by
  intro hB
  apply h
  calc
    A.response s a₁ =
        B.response (phi.toState s) (phi.toAction a₁) :=
      (phi.preserves_response s a₁).symm
    _ = B.response (phi.toState s) (phi.toAction a₂) := hB
    _ = A.response s a₂ := phi.preserves_response s a₂

/--
A response-preserving map preserves one-step prefix logs.

This is deliberately weaker than full `traceLog` preservation: it uses only
the one-step response preservation field, not transition commutation.
-/
theorem preserves_singleton_traceLog
    (s : StateA) (a : ActionA) :
    A.traceLog s [a] =
      B.traceLog (phi.toState s) [phi.toAction a] := by
  change [A.response s a] =
    [B.response (phi.toState s) (phi.toAction a)]
  exact congrArg (fun response => [response])
    (phi.preserves_response s a).symm

/--
If the target process has no hidden same-current-view continuation behavior,
then a one-step response-preserving map preserves full finite prefix logs.

This is a scoped upgrade from response maps to trace maps.  Without the target
trace-log extensionality condition, `ResponseMapFullTraceDeletionTest` below
shows that preserving every one-step response is still not enough.
-/
theorem preserves_traceLog_of_target_currentViewTraceLogExtensional
    (targetExtensional : CurrentViewTraceLogExtensional B)
    (s : StateA) (actions : List ActionA) :
    A.traceLog s actions =
      B.traceLog (phi.toState s) (actions.map phi.toAction) := by
  induction actions generalizing s with
  | nil => rfl
  | cons action actions ih =>
      have hnextView :
          B.currentView (phi.toState (A.step s action)) =
            B.currentView
              (B.step (phi.toState s) (phi.toAction action)) := by
        calc
          B.currentView (phi.toState (A.step s action)) =
              A.currentView (A.step s action) :=
            phi.preserves_currentView (A.step s action)
          _ = A.response s action := rfl
          _ = B.response (phi.toState s) (phi.toAction action) :=
            (phi.preserves_response s action).symm
          _ = B.currentView
                (B.step (phi.toState s) (phi.toAction action)) := rfl
      have htail :
          A.traceLog (A.step s action) actions =
            B.traceLog
              (B.step (phi.toState s) (phi.toAction action))
              (actions.map phi.toAction) := by
        calc
          A.traceLog (A.step s action) actions =
              B.traceLog
                (phi.toState (A.step s action))
                (actions.map phi.toAction) :=
            ih (A.step s action)
          _ = B.traceLog
                (B.step (phi.toState s) (phi.toAction action))
                (actions.map phi.toAction) :=
            targetExtensional hnextView (actions.map phi.toAction)
      exact
        congrArg₂ List.cons
          (phi.preserves_response s action).symm
          htail

end ObservationalResponseMap

/--
An observational transition-preserving map between processes.

This is a stronger, still role-free, preservation surface: it preserves current
observations and boundary readouts, and it commutes with the one-step
transition.  From those fields the one-step response map and full prefix-log
preservation are derived; burden, support, viable regions, and target carriers
are not fields of this object.
-/
structure ObservationalTransitionMap
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  toState : StateA -> StateB
  toAction : ActionA -> ActionB
  preserves_observation :
    forall s, B.observe (toState s) = A.observe s
  preserves_readout :
    forall s, B.readout (toState s) = A.readout s
  step_commutes :
    forall s a, toState (A.step s a) = B.step (toState s) (toAction a)

namespace ObservationalTransitionMap

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (phi : ObservationalTransitionMap A B)

/-- A transition-preserving map induces a one-step response-preserving map. -/
def toResponseMap : ObservationalResponseMap A B where
  toState := phi.toState
  toAction := phi.toAction
  preserves_observation := phi.preserves_observation
  preserves_readout := phi.preserves_readout
  preserves_response := by
    intro s a
    have hstep :
        B.step (phi.toState s) (phi.toAction a) =
          phi.toState (A.step s a) :=
      (phi.step_commutes s a).symm
    exact
      Prod.ext
        (calc
          B.observe (B.step (phi.toState s) (phi.toAction a)) =
              B.observe (phi.toState (A.step s a)) := by
            rw [hstep]
          _ = A.observe (A.step s a) :=
            phi.preserves_observation (A.step s a))
        (calc
          B.readout (B.step (phi.toState s) (phi.toAction a)) =
              B.readout (phi.toState (A.step s a)) := by
            rw [hstep]
          _ = A.readout (A.step s a) :=
            phi.preserves_readout (A.step s a))

/-- A transition-preserving map preserves the full finite prefix log. -/
theorem preserves_traceLog
    (s : StateA) (actions : List ActionA) :
    A.traceLog s actions =
      B.traceLog (phi.toState s) (actions.map phi.toAction) := by
  induction actions generalizing s with
  | nil => rfl
  | cons action actions ih =>
      have hstep :
          B.step (phi.toState s) (phi.toAction action) =
            phi.toState (A.step s action) :=
        (phi.step_commutes s action).symm
      have hhead :
          (A.observe (A.step s action), A.readout (A.step s action)) =
            (B.observe (B.step (phi.toState s) (phi.toAction action)),
              B.readout (B.step (phi.toState s) (phi.toAction action))) := by
        exact
          Prod.ext
            (calc
              A.observe (A.step s action) =
                  B.observe (phi.toState (A.step s action)) :=
                (phi.preserves_observation (A.step s action)).symm
              _ = B.observe
                    (B.step (phi.toState s) (phi.toAction action)) := by
                rw [hstep])
            (calc
              A.readout (A.step s action) =
                  B.readout (phi.toState (A.step s action)) :=
                (phi.preserves_readout (A.step s action)).symm
              _ = B.readout
                    (B.step (phi.toState s) (phi.toAction action)) := by
                rw [hstep])
      have htail :
          A.traceLog (A.step s action) actions =
            B.traceLog
              (B.step (phi.toState s) (phi.toAction action))
              (actions.map phi.toAction) := by
        calc
          A.traceLog (A.step s action) actions =
              B.traceLog
                (phi.toState (A.step s action))
                (actions.map phi.toAction) :=
            ih (A.step s action)
          _ = B.traceLog
                (B.step (phi.toState s) (phi.toAction action))
                (actions.map phi.toAction) := by
            rw [hstep]
      exact congrArg₂ List.cons hhead htail

end ObservationalTransitionMap

/-
Toy deletion test for the transition-commutation hypothesis.

The map below preserves current views and every one-step response, so it is an
`ObservationalResponseMap`.  It deliberately fails to commute with `step`: the
target's first step lands in a hidden state with the same first response but a
different continuation.  Thus singleton logs are preserved, while the two-step
prefix log is not.  This keeps the boundary around
`ObservationalTransitionMap.preserves_traceLog` visible: full finite-prefix-log
preservation needs step closure or a separate trace/simulation hypothesis.
-/
namespace ResponseMapFullTraceDeletionTest

inductive SourceState where
  | start
  | mid
  | final
  deriving DecidableEq, Repr

inductive TargetState where
  | start
  | mappedMid
  | hiddenMid
  | final
  deriving DecidableEq, Repr

def sourceObserve : SourceState -> Bool
  | .start => false
  | .mid => false
  | .final => true

def sourceStep : SourceState -> Unit -> SourceState
  | .start, _ => .mid
  | .mid, _ => .final
  | .final, _ => .final

def sourceProcess :
    ObservationalPersistenceProcess SourceState Unit Bool where
  observe := sourceObserve
  step := sourceStep
  readout := fun _ => BoundaryStatus.viable

def targetObserve : TargetState -> Bool
  | .start => false
  | .mappedMid => false
  | .hiddenMid => false
  | .final => true

def targetStep : TargetState -> Unit -> TargetState
  | .start, _ => .hiddenMid
  | .mappedMid, _ => .final
  | .hiddenMid, _ => .hiddenMid
  | .final, _ => .final

def targetProcess :
    ObservationalPersistenceProcess TargetState Unit Bool where
  observe := targetObserve
  step := targetStep
  readout := fun _ => BoundaryStatus.viable

def toState : SourceState -> TargetState
  | .start => .start
  | .mid => .mappedMid
  | .final => .final

def toAction : Unit -> Unit
  | () => ()

/--
The map preserves current observations, readouts, and one-step responses.
-/
def responseMap : ObservationalResponseMap sourceProcess targetProcess where
  toState := toState
  toAction := toAction
  preserves_observation := by
    intro s
    cases s <;> rfl
  preserves_readout := by
    intro s
    cases s <;> rfl
  preserves_response := by
    intro s a
    cases s <;> cases a <;> rfl

/-- The same map does not commute with the first source transition. -/
theorem responseMap_step_commutes_fails :
    toState (sourceProcess.step SourceState.start ()) ≠
      targetProcess.step (toState SourceState.start) (toAction ()) := by
  decide

/-- One-step prefix logs are preserved by the response-preserving map. -/
theorem responseMap_preserves_singleton_traceLog :
    sourceProcess.traceLog SourceState.start [()] =
      targetProcess.traceLog (toState SourceState.start) ([()].map toAction) :=
  responseMap.preserves_singleton_traceLog SourceState.start ()

/--
Full finite prefix-log preservation fails without step commutation, even
though the selected map preserves every one-step response at mapped states.
-/
theorem responseMap_does_not_preserve_two_step_traceLog :
    sourceProcess.traceLog SourceState.start [(), ()] ≠
      targetProcess.traceLog
        (toState SourceState.start) ([(), ()].map toAction) := by
  decide

/--
The target process has hidden same-current-view continuation behavior: mapped
and hidden mid-states have the same current view but different future logs.
-/
theorem target_not_currentViewTraceLogExtensional :
    ¬ CurrentViewTraceLogExtensional targetProcess := by
  intro targetExtensional
  have hview :
      targetProcess.currentView TargetState.mappedMid =
        targetProcess.currentView TargetState.hiddenMid := rfl
  have hlogs :
      targetProcess.traceLog TargetState.mappedMid [()] =
        targetProcess.traceLog TargetState.hiddenMid [()] :=
    targetExtensional hview [()]
  have hne :
      targetProcess.traceLog TargetState.mappedMid [()] ≠
        targetProcess.traceLog TargetState.hiddenMid [()] := by
    decide
  exact hne hlogs

end ResponseMapFullTraceDeletionTest

/--
A role-free trace simulation between observational processes.

Unlike `ObservationalTransitionMap`, this does not require a function on source
states whose image commutes with the target step.  It only requires a relation
between source and target states that preserves the current observable view and
is closed under paired actions.  From that relation, one-step responses and
finite prefix logs are preserved along related states.
-/
structure ObservationalTraceSimulation
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  related : StateA -> StateB -> Prop
  toAction : ActionA -> ActionB
  preserves_observation :
    forall {sA sB}, related sA sB -> B.observe sB = A.observe sA
  preserves_readout :
    forall {sA sB}, related sA sB -> B.readout sB = A.readout sA
  step_related :
    forall {sA sB}, related sA sB -> forall a,
      related (A.step sA a) (B.step sB (toAction a))

namespace ObservationalTraceSimulation

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (simulation : ObservationalTraceSimulation A B)

/-- Related states have the same current observable view. -/
theorem preserves_currentView
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    B.currentView sB = A.currentView sA := by
  exact
    Prod.ext
      (simulation.preserves_observation h)
      (simulation.preserves_readout h)

/-- A trace simulation preserves one-step responses along related states. -/
theorem preserves_response
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB)
    (a : ActionA) :
    B.response sB (simulation.toAction a) = A.response sA a := by
  have hnext :
      simulation.related
        (A.step sA a)
        (B.step sB (simulation.toAction a)) :=
    simulation.step_related h a
  exact
    Prod.ext
      (simulation.preserves_observation hnext)
      (simulation.preserves_readout hnext)

/-- A trace simulation preserves the full finite prefix log along related states. -/
theorem preserves_traceLog
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB)
    (actions : List ActionA) :
    A.traceLog sA actions =
      B.traceLog sB (actions.map simulation.toAction) := by
  induction actions generalizing sA sB with
  | nil => rfl
  | cons action actions ih =>
      have hnext :
          simulation.related
            (A.step sA action)
            (B.step sB (simulation.toAction action)) :=
        simulation.step_related h action
      have hhead :
          (A.observe (A.step sA action), A.readout (A.step sA action)) =
            (B.observe (B.step sB (simulation.toAction action)),
              B.readout (B.step sB (simulation.toAction action))) := by
        exact
          Prod.ext
            (simulation.preserves_observation hnext).symm
            (simulation.preserves_readout hnext).symm
      have htail :
          A.traceLog (A.step sA action) actions =
            B.traceLog
              (B.step sB (simulation.toAction action))
              (actions.map simulation.toAction) :=
        ih hnext
      exact congrArg₂ List.cons hhead htail

/--
A trace simulation gives trace-log image preservation on related states.  The
image statement forgets the supplied action translator and keeps only the
existence of a target trace with the same observed prefix log.
-/
theorem traceLogImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    TraceLogImagePreservationAt A B sA sB := by
  intro actions
  exact ⟨actions.map simulation.toAction,
    (simulation.preserves_traceLog h actions).symm⟩

/-- A transition-preserving map induces a relational trace simulation. -/
def ofTransitionMap
    (phi : ObservationalTransitionMap A B) :
    ObservationalTraceSimulation A B where
  related := fun sA sB => sB = phi.toState sA
  toAction := phi.toAction
  preserves_observation := by
    intro sA sB h
    rw [h]
    exact phi.preserves_observation sA
  preserves_readout := by
    intro sA sB h
    rw [h]
    exact phi.preserves_readout sA
  step_related := by
    intro sA sB h action
    rw [h]
    exact (phi.step_commutes sA action).symm

end ObservationalTraceSimulation

/--
A role-free response-image simulation between observational processes.

This is weaker than `ObservationalTraceSimulation`: it does not provide a
global `toAction`.  Instead, for each related source/target state pair and each
source action, it requires only the existence of some target action whose
post-action state remains related.  From that observable relation, selected
state-pair response-image preservation is derived below.
-/
structure ObservationalResponseImageSimulation
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  related : StateA -> StateB -> Prop
  preserves_observation :
    forall {sA sB}, related sA sB -> B.observe sB = A.observe sA
  preserves_readout :
    forall {sA sB}, related sA sB -> B.readout sB = A.readout sA
  step_response_related :
    forall {sA sB}, related sA sB -> forall action : ActionA,
      ∃ targetAction : ActionB,
        related (A.step sA action) (B.step sB targetAction)

namespace ObservationalResponseImageSimulation

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (simulation : ObservationalResponseImageSimulation A B)

/-- Related states have the same current observable view. -/
theorem preserves_currentView
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    B.currentView sB = A.currentView sA := by
  exact
    Prod.ext
      (simulation.preserves_observation h)
      (simulation.preserves_readout h)

/--
A response-image simulation derives selected-state response-image preservation.

This is the first construction layer below a supplied action translator: the
target action is obtained from existential step-relatedness, and the matching
response is read only through observation/readout preservation on the related
post-action states.
-/
theorem responseImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    ResponseImagePreservationAt A B sA sB := by
  intro response hsource
  rcases hsource with ⟨action, hresponse⟩
  rcases simulation.step_response_related h action with
    ⟨targetAction, hnext⟩
  refine ⟨targetAction, ?_⟩
  have htarget_response :
      B.response sB targetAction = A.response sA action := by
    change
      (B.observe (B.step sB targetAction),
        B.readout (B.step sB targetAction)) =
        (A.observe (A.step sA action), A.readout (A.step sA action))
    exact
      Prod.ext
        (simulation.preserves_observation hnext)
        (simulation.preserves_readout hnext)
  exact htarget_response.trans hresponse

/--
A response-image simulation also supplies action-response coverage at related
state pairs, without choosing a global action translator.
-/
theorem actionResponseCoverageAt
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    ActionResponseCoverageAt A B sA sB :=
  actionResponseCoverageAt_of_responseImagePreservationAt
    (simulation.responseImagePreservationAt h)

/--
A response-image simulation gives finite trace-log image preservation.

The construction is by induction over the source action trace.  It does not
choose a global action translator: each source trace is matched by a target
trace whose next action witnesses the current related step.
-/
theorem traceLogImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    TraceLogImagePreservationAt A B sA sB := by
  intro actions
  induction actions generalizing sA sB with
  | nil =>
      exact ⟨[], rfl⟩
  | cons action actions ih =>
      rcases simulation.step_response_related h action with
        ⟨targetAction, hnext⟩
      rcases ih hnext with ⟨targetActions, htail⟩
      refine ⟨targetAction :: targetActions, ?_⟩
      have hhead :
          B.response sB targetAction = A.response sA action := by
        change
          (B.observe (B.step sB targetAction),
            B.readout (B.step sB targetAction)) =
            (A.observe (A.step sA action), A.readout (A.step sA action))
        exact
          Prod.ext
            (simulation.preserves_observation hnext)
            (simulation.preserves_readout hnext)
      exact congrArg₂ List.cons hhead htail

/--
Every trace simulation induces a response-image simulation by forgetting its
global action translator after using it to witness each one-step target action.
-/
def ofTraceSimulation
    (simulation : ObservationalTraceSimulation A B) :
    ObservationalResponseImageSimulation A B where
  related := simulation.related
  preserves_observation := simulation.preserves_observation
  preserves_readout := simulation.preserves_readout
  step_response_related := by
    intro sA sB h action
    exact ⟨simulation.toAction action, simulation.step_related h action⟩

/-- A transition-preserving map induces a response-image simulation. -/
def ofTransitionMap
    (phi : ObservationalTransitionMap A B) :
    ObservationalResponseImageSimulation A B :=
  ofTraceSimulation (ObservationalTraceSimulation.ofTransitionMap phi)

end ObservationalResponseImageSimulation

/--
Canonical trace-language image relatedness.

Two states are related when their current observable views agree and every
finite source prefix log can be realized by some target trace.  This relation
is defined only from observable views and trace-log images; it does not include
a supplied action translator or Structural Persistence roles.
-/
def traceLanguageImageRelated
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  B.currentView sB = A.currentView sA ∧
    TraceLogImagePreservationAt A B sA sB

namespace TraceLanguageImageRelated

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/-- Trace-language image related states preserve current observations. -/
theorem preserves_observation
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    B.observe sB = A.observe sA :=
  congrArg Prod.fst h.1

/-- Trace-language image related states preserve current boundary readouts. -/
theorem preserves_readout
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    B.readout sB = A.readout sA :=
  congrArg Prod.snd h.1

/-- Trace-language image relatedness exposes its trace-log image component. -/
theorem traceLogImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    TraceLogImagePreservationAt A B sA sB :=
  h.2

/-- Trace-language image relatedness yields selected-state response-image preservation. -/
theorem responseImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    ResponseImagePreservationAt A B sA sB :=
  responseImagePreservationAt_of_traceLogImagePreservationAt h.2

/-- Trace-language image relatedness yields selected-state action-response coverage. -/
theorem actionResponseCoverageAt
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    ActionResponseCoverageAt A B sA sB :=
  actionResponseCoverageAt_of_traceLogImagePreservationAt h.2

end TraceLanguageImageRelated

/--
Global current-view trace-image completeness.

Whenever a target state has the same observable current view as a source state,
every finite source prefix log can be realized by some target trace.  This is
still a role-free observational hypothesis: it mentions only current views and
finite trace-log images, not `F/K/V_K/L/B/M` roles or certificates.
-/
def CurrentViewTraceImageComplete
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      TraceLogImagePreservationAt A B sA sB

/--
The observable finite trace-log language generated from a selected state.

This is a role-free language view: a log belongs to the language of a state
when some finite action trace from that state produces it.
-/
def TraceLogLanguageAt
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (s : State) (log : List (Observation × BoundaryStatus)) : Prop :=
  ∃ actions : List Action,
    P.traceLog s actions = log

/--
Selected-state trace-log language inclusion.

Every finite observable trace log from the source state is also generated from
the target state.  This is the state-pair language form of
`TraceLogImagePreservationAt`.
-/
def TraceLogLanguageIncludedAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  forall log : List (Observation × BoundaryStatus),
    TraceLogLanguageAt A sA log ->
      TraceLogLanguageAt B sB log

/--
Selected-state trace-log language equivalence.

This is still purely observational: it compares only the finite prefix-log
languages available at a selected source/target state pair.
-/
def TraceLogLanguageEquivalentAt
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (sA : StateA) (sB : StateB) : Prop :=
  forall log : List (Observation × BoundaryStatus),
    TraceLogLanguageAt A sA log ↔
      TraceLogLanguageAt B sB log

namespace TraceLogLanguageIncludedAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Trace-log language inclusion is the language-level form of trace-log image
preservation.
-/
theorem toTraceLogImagePreservationAt
    (included : TraceLogLanguageIncludedAt A B sA sB) :
    TraceLogImagePreservationAt A B sA sB := by
  intro actions
  exact included (A.traceLog sA actions) ⟨actions, rfl⟩

end TraceLogLanguageIncludedAt

namespace TraceLogImagePreservationAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/--
Trace-log image preservation gives trace-log language inclusion.

The target trace supplied for a source action trace realizes the same observable
log in the target state's finite trace-log language.
-/
theorem toTraceLogLanguageIncludedAt
    (htrace : TraceLogImagePreservationAt A B sA sB) :
    TraceLogLanguageIncludedAt A B sA sB := by
  intro log hsource
  rcases hsource with ⟨actions, hlog⟩
  rcases htrace actions with ⟨targetActions, htarget⟩
  exact ⟨targetActions, htarget.trans hlog⟩

end TraceLogImagePreservationAt

/--
Trace-log language inclusion is equivalent to trace-log image preservation.

This pins down the two role-free formulations of the same selected-state
observable bottleneck: one quantifies over source traces, the other over
observable logs in the source language.
-/
theorem traceLogLanguageIncludedAt_iff_traceLogImagePreservationAt :
    TraceLogLanguageIncludedAt A B sA sB ↔
      TraceLogImagePreservationAt A B sA sB := by
  constructor
  · exact TraceLogLanguageIncludedAt.toTraceLogImagePreservationAt
  · exact TraceLogImagePreservationAt.toTraceLogLanguageIncludedAt

namespace TraceLogLanguageEquivalentAt

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {sA : StateA} {sB : StateB}

/-- Trace-log language equivalence gives the forward inclusion. -/
theorem toIncluded
    (equivalent : TraceLogLanguageEquivalentAt A B sA sB) :
    TraceLogLanguageIncludedAt A B sA sB := by
  intro log hlog
  exact (equivalent log).1 hlog

/-- Trace-log language equivalence also gives the reverse inclusion. -/
theorem toReverseIncluded
    (equivalent : TraceLogLanguageEquivalentAt A B sA sB) :
    TraceLogLanguageIncludedAt B A sB sA := by
  intro log hlog
  exact (equivalent log).2 hlog

/--
Trace-log language equivalence gives trace-log image preservation by forgetting
the reverse inclusion.
-/
theorem toTraceLogImagePreservationAt
    (equivalent : TraceLogLanguageEquivalentAt A B sA sB) :
    TraceLogImagePreservationAt A B sA sB :=
  TraceLogLanguageIncludedAt.toTraceLogImagePreservationAt
    (toIncluded equivalent)

/--
Trace-log language equivalence gives reverse trace-log image preservation by
forgetting to the reverse inclusion.
-/
theorem toReverseTraceLogImagePreservationAt
    (equivalent : TraceLogLanguageEquivalentAt A B sA sB) :
    TraceLogImagePreservationAt B A sB sA :=
  TraceLogLanguageIncludedAt.toTraceLogImagePreservationAt
    (toReverseIncluded equivalent)

end TraceLogLanguageEquivalentAt

/--
Current-view trace-log language inclusion.

For every source/target state pair with the same current observable view, the
target state can realize every finite source prefix log.  This is a candidate
"same observable calculation" hypothesis for the semantic G1 track; it still
does not mention `F/K/V_K/L/B/M`.
-/
def CurrentViewTraceLogLanguageIncluded
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      TraceLogLanguageIncludedAt A B sA sB

/--
Current-view trace-log language equivalence.

This is the bidirectional observable-language version of "same calculation" at
the current-view level.  The forward direction is enough for the G1 image
construction below.
-/
def CurrentViewTraceLogLanguageEquivalent
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      TraceLogLanguageEquivalentAt A B sA sB

namespace CurrentViewTraceLogLanguageIncluded

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language inclusion implies current-view trace-image
completeness.
-/
theorem toCurrentViewTraceImageComplete
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewTraceImageComplete A B := by
  intro sA sB hview
  exact TraceLogLanguageIncludedAt.toTraceLogImagePreservationAt
    (included hview)

end CurrentViewTraceLogLanguageIncluded

namespace CurrentViewTraceImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-image completeness gives current-view trace-log language
inclusion.
-/
theorem toCurrentViewTraceLogLanguageIncluded
    (complete : CurrentViewTraceImageComplete A B) :
    CurrentViewTraceLogLanguageIncluded A B := by
  intro sA sB hview
  exact TraceLogImagePreservationAt.toTraceLogLanguageIncludedAt
    (complete hview)

end CurrentViewTraceImageComplete

/--
Current-view trace-log language inclusion is equivalent to current-view
trace-image completeness.
-/
theorem currentViewTraceLogLanguageIncluded_iff_currentViewTraceImageComplete :
    CurrentViewTraceLogLanguageIncluded A B ↔
      CurrentViewTraceImageComplete A B := by
  constructor
  · exact CurrentViewTraceLogLanguageIncluded.toCurrentViewTraceImageComplete
  · exact CurrentViewTraceImageComplete.toCurrentViewTraceLogLanguageIncluded

/--
Current-view response-image completeness.

This is the one-step observable-image version of current-view trace-language
inclusion: whenever current views agree, every one-step source response is
realized by some target action.  It still mentions only observable responses,
not `F/K/V_K/L/B/M`, certificates, or a fixed action translator.
-/
def CurrentViewResponseImageComplete
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      ResponseImagePreservationAt A B sA sB

/--
A current-view one-step response-image gap.

This is the local obstruction to the current-view completeness lane: at some
same-current-view state pair, a source action has no target action with the
same observable post-action response.  It is stated only in observable terms
and carries no Structural Persistence roles.
-/
def CurrentViewResponseImageGap
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  ∃ sA : StateA,
    ∃ sB : StateB,
      B.currentView sB = A.currentView sA ∧
        ∃ action : ActionA,
          forall targetAction : ActionB,
            B.response sB targetAction ≠ A.response sA action

/--
Current-view action-response coverage.

This names the same one-step bottleneck in action-indexed form: at every
same-current-view state pair, each source action response is realized by some
target action response.  It still does not choose a fixed global action
translator.
-/
def CurrentViewActionResponseCoverage
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      ActionResponseCoverageAt A B sA sB

/--
Current-view response-preserving translator existence.

This is the chosen-translator form of the same one-step bottleneck.  In the
general non-finite setting, deriving this from pointwise coverage uses the
same `Classical.choice` boundary as `ActionResponseCoverageAt.toAction`.
-/
def CurrentViewResponseTranslatorExists
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      ∃ toAction : ActionA -> ActionB,
        forall action,
          B.response sB (toAction action) =
            A.response sA action

namespace CurrentViewActionResponseCoverage

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view action-response coverage gives current-view response-image
completeness by forgetting the source action in the conclusion.
-/
theorem toCurrentViewResponseImageComplete
    (coverage : CurrentViewActionResponseCoverage A B) :
    CurrentViewResponseImageComplete A B := by
  intro sA sB hview
  exact responseImagePreservationAt_of_actionResponseCoverageAt
    (coverage hview)

/--
Pointwise current-view action-response coverage gives a response-preserving
action translator at each same-current-view state pair.

The construction inherits the general non-finite `Classical.choice` cost from
the selected-state coverage theorem.
-/
theorem toCurrentViewResponseTranslatorExists
    (coverage : CurrentViewActionResponseCoverage A B) :
    CurrentViewResponseTranslatorExists A B := by
  intro sA sB hview
  exact (coverage hview).exists_responsePreserving_toAction

end CurrentViewActionResponseCoverage

namespace CurrentViewResponseImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view response-image completeness gives action-response coverage at
every same-current-view state pair, without choosing a translator.
-/
theorem toCurrentViewActionResponseCoverage
    (complete : CurrentViewResponseImageComplete A B) :
    CurrentViewActionResponseCoverage A B := by
  intro sA sB hview
  exact actionResponseCoverageAt_of_responseImagePreservationAt
    (complete hview)

end CurrentViewResponseImageComplete

/--
Current-view response-image completeness and current-view action-response
coverage are the same one-step bottleneck before a translator is chosen.
-/
theorem currentViewResponseImageComplete_iff_currentViewActionResponseCoverage :
    CurrentViewResponseImageComplete A B ↔
      CurrentViewActionResponseCoverage A B := by
  constructor
  · exact CurrentViewResponseImageComplete.toCurrentViewActionResponseCoverage
  · exact CurrentViewActionResponseCoverage.toCurrentViewResponseImageComplete

namespace CurrentViewResponseTranslatorExists

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
If translators exist at every same-current-view state pair, then the
action-response coverage condition follows by taking their values.
-/
theorem toCurrentViewActionResponseCoverage
    (existsTranslator : CurrentViewResponseTranslatorExists A B) :
    CurrentViewActionResponseCoverage A B := by
  intro sA sB hview
  exact actionResponseCoverageAt_of_exists_responsePreserving_toAction
    (existsTranslator hview)

end CurrentViewResponseTranslatorExists

/--
Current-view action-response coverage is equivalent to selected-state
translator existence at every same-current-view state pair.

The forward direction chooses one matching target action per source action at
each pair; in general this is a `Classical.choice` boundary, not automatic
computable adapter discovery.
-/
theorem currentViewActionResponseCoverage_iff_currentViewResponseTranslatorExists :
    CurrentViewActionResponseCoverage A B ↔
      CurrentViewResponseTranslatorExists A B := by
  constructor
  · exact CurrentViewActionResponseCoverage.toCurrentViewResponseTranslatorExists
  · exact CurrentViewResponseTranslatorExists.toCurrentViewActionResponseCoverage

/--
Current-view finite action-response search.

This is the finite/decidable version of the current-view translator boundary:
for every same-current-view source/target state pair, an explicit finite
target-action candidate list realizes every source one-step response.  The
candidate lists and fallbacks are still supplied per state pair; the point is
that, once supplied, translators are obtained by finite search rather than by
the general non-finite `Classical.choice` route.
-/
structure CurrentViewFiniteActionResponseSearch
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  search :
    forall {sA : StateA} {sB : StateB},
      B.currentView sB = A.currentView sA ->
        FiniteActionResponseSearchAt A B sA sB

namespace CurrentViewFiniteActionResponseSearch

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view finite search yields current-view action-response coverage before
any translator is chosen.
-/
theorem toCurrentViewActionResponseCoverage
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    CurrentViewActionResponseCoverage A B := by
  intro sA sB hview action
  rcases (finiteSearch.search hview).complete action with
    ⟨targetAction, _, hresponse⟩
  exact ⟨targetAction, hresponse⟩

/--
Current-view finite search yields response-image completeness by forgetting the
searched target action witnesses.
-/
theorem toCurrentViewResponseImageComplete
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    CurrentViewResponseImageComplete A B :=
  CurrentViewActionResponseCoverage.toCurrentViewResponseImageComplete
    (toCurrentViewActionResponseCoverage finiteSearch)

/--
Current-view finite search yields a response-preserving translator at each
same-current-view state pair by list search, not by the general non-finite
choice route.
-/
theorem toCurrentViewResponseTranslatorExists
    (responseDecidable : DecidableEq Observation)
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    CurrentViewResponseTranslatorExists A B := by
  letI := responseDecidable
  intro sA sB hview
  rcases
    FiniteActionResponseSearchAt.exists_responsePreserving_toAction
      (finiteSearch.search hview) with
    ⟨toAction, _, hpreserves⟩
  exact ⟨toAction, hpreserves⟩

end CurrentViewFiniteActionResponseSearch

namespace CurrentViewActionResponseCoverage

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
With a global finite target-action enumeration, current-view action-response
coverage yields current-view finite search without supplying per-state
candidate lists.
-/
def toCurrentViewFiniteActionResponseSearch
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (coverage : CurrentViewActionResponseCoverage A B) :
    CurrentViewFiniteActionResponseSearch A B where
  search := by
    intro sA sB hview
    exact
      FiniteActionEnumeration.toFiniteActionResponseSearchAt
        targetEnumeration (coverage hview)

end CurrentViewActionResponseCoverage

namespace CurrentViewResponseImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
With a global finite target-action enumeration, current-view response-image
completeness yields current-view finite search through action-response
coverage.
-/
def toCurrentViewFiniteActionResponseSearch
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (complete : CurrentViewResponseImageComplete A B) :
    CurrentViewFiniteActionResponseSearch A B :=
  CurrentViewActionResponseCoverage.toCurrentViewFiniteActionResponseSearch
    targetEnumeration (toCurrentViewActionResponseCoverage complete)

end CurrentViewResponseImageComplete

namespace CurrentViewTraceLogLanguageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/-- Current-view trace-log language equivalence gives the forward inclusion. -/
theorem toIncluded
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewTraceLogLanguageIncluded A B := by
  intro sA sB hview
  exact TraceLogLanguageEquivalentAt.toIncluded (equivalent hview)

/-- Current-view trace-log language equivalence also gives the reverse inclusion. -/
theorem toReverseIncluded
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewTraceLogLanguageIncluded B A := by
  intro sB sA hview
  exact TraceLogLanguageEquivalentAt.toReverseIncluded
    (equivalent hview.symm)

/--
Current-view trace-log language equivalence implies current-view trace-image
completeness.
-/
theorem toCurrentViewTraceImageComplete
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewTraceImageComplete A B :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewTraceImageComplete
    (toIncluded equivalent)

/--
Current-view trace-log language equivalence also implies reverse current-view
trace-image completeness.
-/
theorem toReverseCurrentViewTraceImageComplete
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewTraceImageComplete B A :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewTraceImageComplete
    (toReverseIncluded equivalent)

end CurrentViewTraceLogLanguageEquivalent

/--
A residual simulation over the canonical trace-language image relation.

The relation itself is not supplied as an arbitrary field; it is fixed to
`traceLanguageImageRelated`.  The remaining input is the residual/step closure:
from related states and a source action, some target action reaches related
next states.
-/
structure TraceLanguageImageSimulation
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  step_image_related :
    forall {sA sB},
      traceLanguageImageRelated A B sA sB ->
        forall action : ActionA,
          ∃ targetAction : ActionB,
            traceLanguageImageRelated A B
              (A.step sA action) (B.step sB targetAction)

namespace TraceLanguageImageSimulation

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (simulation : TraceLanguageImageSimulation A B)

/--
Canonical trace-language residual closure induces a response-image simulation.

This removes the arbitrary related-state relation from the input; the induced
simulation relates exactly the states with the same current view and target
realizability of all finite source prefix logs.
-/
def toResponseImageSimulation :
    ObservationalResponseImageSimulation A B where
  related := traceLanguageImageRelated A B
  preserves_observation := by
    intro sA sB h
    exact TraceLanguageImageRelated.preserves_observation h
  preserves_readout := by
    intro sA sB h
    exact TraceLanguageImageRelated.preserves_readout h
  step_response_related := by
    intro sA sB h action
    exact simulation.step_image_related h action

/--
Canonical trace-language image related states expose trace-log image
preservation directly.
-/
theorem traceLogImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    TraceLogImagePreservationAt A B sA sB :=
  TraceLanguageImageRelated.traceLogImagePreservationAt h

/--
A trace-language image simulation gives selected-state response-image
preservation on its canonical related states.
-/
theorem responseImagePreservationAt
    (simulation : TraceLanguageImageSimulation A B)
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    ResponseImagePreservationAt A B sA sB :=
  (toResponseImageSimulation simulation).responseImagePreservationAt h

/--
A trace-language image simulation gives selected-state action-response coverage
on its canonical related states.
-/
theorem actionResponseCoverageAt
    (simulation : TraceLanguageImageSimulation A B)
    {sA : StateA} {sB : StateB}
    (h : traceLanguageImageRelated A B sA sB) :
    ActionResponseCoverageAt A B sA sB :=
  (toResponseImageSimulation simulation).actionResponseCoverageAt h

end TraceLanguageImageSimulation

namespace CurrentViewTraceImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-image completeness makes the canonical trace-language image
relation step-closed.

The proof extracts the next target action from the singleton source trace and
uses the global current-view completeness hypothesis to recover the tail
trace-image property at the next state pair.  No fixed action translator,
burden/support role, or supplied step-closure field is used.
-/
def toTraceLanguageImageSimulation
    (complete : CurrentViewTraceImageComplete A B) :
    TraceLanguageImageSimulation A B where
  step_image_related := by
    intro sA sB hrelated action
    rcases hrelated.2 [action] with ⟨targetActions, hlog⟩
    cases targetActions with
    | nil =>
        change [] = [A.response sA action] at hlog
        cases hlog
    | cons targetAction rest =>
        change
          B.response sB targetAction ::
              B.traceLog (B.step sB targetAction) rest =
            [A.response sA action] at hlog
        have hhead :
            B.response sB targetAction = A.response sA action :=
          (List.cons.inj hlog).1
        have hnextView :
            B.currentView (B.step sB targetAction) =
              A.currentView (A.step sA action) := by
          change
            B.response sB targetAction =
              A.response sA action
          exact hhead
        exact ⟨targetAction, hnextView, complete hnextView⟩

end CurrentViewTraceImageComplete

namespace CurrentViewTraceLogLanguageIncluded

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language inclusion constructs the canonical
trace-language image simulation.

This factors through `CurrentViewTraceImageComplete`: language inclusion is
the observable-language form, and trace-image completeness is the image form
consumed by the step-closure construction.
-/
def toTraceLanguageImageSimulation
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    TraceLanguageImageSimulation A B :=
  CurrentViewTraceImageComplete.toTraceLanguageImageSimulation
    (toCurrentViewTraceImageComplete included)

end CurrentViewTraceLogLanguageIncluded

namespace CurrentViewTraceLogLanguageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language equivalence constructs the canonical
trace-language image simulation by forgetting to the forward inclusion.
-/
def toTraceLanguageImageSimulation
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    TraceLanguageImageSimulation A B :=
  CurrentViewTraceLogLanguageIncluded.toTraceLanguageImageSimulation
    (toIncluded equivalent)

end CurrentViewTraceLogLanguageEquivalent

/--
Local current-view step-image completeness.

This is the one-step, role-free source for current-view trace-image
completeness: whenever the current observable views agree, every source action
has some target action whose next observable view agrees.  It mentions only
observable current views and one-step transitions, not a fixed action
translator or Structural Persistence roles.
-/
def CurrentViewStepImageComplete
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  forall {sA : StateA} {sB : StateB},
    B.currentView sB = A.currentView sA ->
      forall action : ActionA,
        ∃ targetAction : ActionB,
          B.currentView (B.step sB targetAction) =
            A.currentView (A.step sA action)

namespace CurrentViewStepImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Local current-view step images iterate to finite trace-log image completeness.

The construction chooses target actions trace-by-trace, not a single global
translator.  Each chosen target action preserves the next current view, and
the induction continues from that reached state pair.
-/
theorem toCurrentViewTraceImageComplete
    (complete : CurrentViewStepImageComplete A B) :
    CurrentViewTraceImageComplete A B := by
  intro sA sB hview actions
  induction actions generalizing sA sB with
  | nil =>
      exact ⟨[], rfl⟩
  | cons action actions ih =>
      rcases complete hview action with ⟨targetAction, hnextView⟩
      rcases ih hnextView with ⟨targetActions, htail⟩
      exact ⟨targetAction :: targetActions,
        congrArg₂ List.cons hnextView htail⟩

/--
Local current-view step images construct the canonical trace-language image
simulation through finite trace-image completeness.
-/
def toTraceLanguageImageSimulation
    (complete : CurrentViewStepImageComplete A B) :
    TraceLanguageImageSimulation A B :=
  CurrentViewTraceImageComplete.toTraceLanguageImageSimulation
    (toCurrentViewTraceImageComplete complete)

/--
Local current-view step images therefore induce the role-free response-image
simulation boundary.
-/
def toResponseImageSimulation
    (complete : CurrentViewStepImageComplete A B) :
    ObservationalResponseImageSimulation A B :=
  TraceLanguageImageSimulation.toResponseImageSimulation
    (toTraceLanguageImageSimulation complete)

end CurrentViewStepImageComplete

namespace CurrentViewResponseImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view response-image completeness is the one-step source of local
current-view step images.
-/
theorem toCurrentViewStepImageComplete
    (complete : CurrentViewResponseImageComplete A B) :
    CurrentViewStepImageComplete A B := by
  intro sA sB hview action
  rcases complete hview (A.response sA action) ⟨action, rfl⟩ with
    ⟨targetAction, htarget⟩
  exact ⟨targetAction, htarget⟩

/--
Current-view response-image completeness iterates to finite trace-image
completeness through local current-view step images.
-/
theorem toCurrentViewTraceImageComplete
    (complete : CurrentViewResponseImageComplete A B) :
    CurrentViewTraceImageComplete A B :=
  CurrentViewStepImageComplete.toCurrentViewTraceImageComplete
    (toCurrentViewStepImageComplete complete)

/--
Current-view response-image completeness also gives current-view trace-log
language inclusion by the trace-image/language equivalence.
-/
theorem toCurrentViewTraceLogLanguageIncluded
    (complete : CurrentViewResponseImageComplete A B) :
    CurrentViewTraceLogLanguageIncluded A B :=
  CurrentViewTraceImageComplete.toCurrentViewTraceLogLanguageIncluded
    (toCurrentViewTraceImageComplete complete)

/--
Current-view response-image completeness directly constructs the role-free
response-image simulation whose relation is equality of current observable
views.

This removes one arbitrary supplied relation from the path: the remaining
hypothesis is still the local one-step response-image condition, not arbitrary
alternative admissibility or a recovered `F/K/V_K/L/B/M` interface.
-/
def toResponseImageSimulation
    (complete : CurrentViewResponseImageComplete A B) :
    ObservationalResponseImageSimulation A B where
  related := fun sA sB => B.currentView sB = A.currentView sA
  preserves_observation := by
    intro sA sB hview
    exact congrArg Prod.fst hview
  preserves_readout := by
    intro sA sB hview
    exact congrArg Prod.snd hview
  step_response_related := by
    intro sA sB hview action
    rcases complete hview (A.response sA action) ⟨action, rfl⟩ with
      ⟨targetAction, htarget⟩
    exact ⟨targetAction, htarget⟩

/--
The direct same-current-view simulation recovers the selected-state
action-response coverage consequence.
-/
theorem toResponseImageSimulation_actionResponseCoverageAt
    (complete : CurrentViewResponseImageComplete A B)
    {sA : StateA} {sB : StateB}
    (hview : B.currentView sB = A.currentView sA) :
    ActionResponseCoverageAt A B sA sB :=
  (toResponseImageSimulation complete).actionResponseCoverageAt hview

end CurrentViewResponseImageComplete

namespace CurrentViewStepImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Local current-view step images are exactly current-view response-image
completeness in one-step form.
-/
theorem toCurrentViewResponseImageComplete
    (complete : CurrentViewStepImageComplete A B) :
    CurrentViewResponseImageComplete A B := by
  intro sA sB hview response hsource
  rcases hsource with ⟨action, hresponse⟩
  rcases complete hview action with ⟨targetAction, htarget⟩
  exact ⟨targetAction, htarget.trans hresponse⟩

end CurrentViewStepImageComplete

/--
Current-view response-image completeness and local current-view step-image
completeness are the same role-free one-step bottleneck.
-/
theorem currentViewResponseImageComplete_iff_currentViewStepImageComplete :
    CurrentViewResponseImageComplete A B ↔
      CurrentViewStepImageComplete A B := by
  constructor
  · exact CurrentViewResponseImageComplete.toCurrentViewStepImageComplete
  · exact CurrentViewStepImageComplete.toCurrentViewResponseImageComplete

namespace CurrentViewTraceImageComplete

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-image completeness already contains the one-step
response-image condition: read the singleton source trace.
-/
theorem toCurrentViewResponseImageComplete
    (complete : CurrentViewTraceImageComplete A B) :
    CurrentViewResponseImageComplete A B := by
  intro sA sB hview
  exact responseImagePreservationAt_of_traceLogImagePreservationAt
    (complete hview)

/--
Current-view trace-image completeness therefore gives the action-response
coverage bottleneck without choosing a translator.
-/
theorem toCurrentViewActionResponseCoverage
    (complete : CurrentViewTraceImageComplete A B) :
    CurrentViewActionResponseCoverage A B :=
  CurrentViewResponseImageComplete.toCurrentViewActionResponseCoverage
    (toCurrentViewResponseImageComplete complete)

end CurrentViewTraceImageComplete

/--
Current-view trace-image completeness is equivalent to current-view
response-image completeness.  The forward direction takes singleton traces;
the reverse direction iterates one-step response images through current-view
step images.
-/
theorem currentViewTraceImageComplete_iff_currentViewResponseImageComplete :
    CurrentViewTraceImageComplete A B ↔
      CurrentViewResponseImageComplete A B := by
  constructor
  · exact CurrentViewTraceImageComplete.toCurrentViewResponseImageComplete
  · exact CurrentViewResponseImageComplete.toCurrentViewTraceImageComplete

namespace CurrentViewTraceLogLanguageIncluded

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language inclusion gives current-view response-image
completeness by passing through trace-image completeness and reading singleton
traces.
-/
theorem toCurrentViewResponseImageComplete
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewResponseImageComplete A B :=
  CurrentViewTraceImageComplete.toCurrentViewResponseImageComplete
    (toCurrentViewTraceImageComplete included)

/--
Current-view trace-log language inclusion gives current-view action-response
coverage before any translator is chosen.
-/
theorem toCurrentViewActionResponseCoverage
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewActionResponseCoverage A B :=
  CurrentViewTraceImageComplete.toCurrentViewActionResponseCoverage
    (toCurrentViewTraceImageComplete included)

end CurrentViewTraceLogLanguageIncluded

/--
Current-view trace-log language inclusion is equivalent to current-view
response-image completeness.
-/
theorem currentViewTraceLogLanguageIncluded_iff_currentViewResponseImageComplete :
    CurrentViewTraceLogLanguageIncluded A B ↔
      CurrentViewResponseImageComplete A B := by
  constructor
  · exact CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
  · exact CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded

/--
A current-view one-step response-image gap blocks current-view response-image
completeness.
-/
theorem not_currentViewResponseImageComplete_of_currentViewResponseImageGap
    (gap : CurrentViewResponseImageGap A B) :
    ¬ CurrentViewResponseImageComplete A B := by
  intro complete
  rcases gap with ⟨sA, sB, hview, action, hmissing⟩
  rcases complete hview (A.response sA action) ⟨action, rfl⟩ with
    ⟨targetAction, htarget⟩
  exact hmissing targetAction htarget

/--
Current-view response-image completeness rules out a one-step response-image
gap.
-/
theorem no_currentViewResponseImageGap_of_currentViewResponseImageComplete
    (complete : CurrentViewResponseImageComplete A B) :
    ¬ CurrentViewResponseImageGap A B := by
  intro gap
  exact
    not_currentViewResponseImageComplete_of_currentViewResponseImageGap
      gap complete

/--
Absence of a current-view response-image gap recovers current-view
response-image completeness in the general, non-finite setting.

The reverse direction is intentionally marked by `classical`: it extracts a
target action from the negation of a missing-response statement.  Finite-search
routes remain the constructive/computable route when explicit target-action
enumerations are supplied.
-/
theorem currentViewResponseImageComplete_of_not_currentViewResponseImageGap
    (noGap : ¬ CurrentViewResponseImageGap A B) :
    CurrentViewResponseImageComplete A B := by
  classical
  intro sA sB hview response hsource
  rcases hsource with ⟨action, hresponse⟩
  by_contra hmissing_response
  have hmissing_action :
      forall targetAction : ActionB,
        B.response sB targetAction ≠ A.response sA action := by
    intro targetAction htarget
    apply hmissing_response
    exact ⟨targetAction, htarget.trans hresponse⟩
  exact noGap ⟨sA, sB, hview, action, hmissing_action⟩

/--
Current-view response-image completeness is equivalent to the absence of a
current-view response-image gap.

The forward direction is constructive; the reverse direction inherits the
general classical boundary documented in
`currentViewResponseImageComplete_of_not_currentViewResponseImageGap`.
-/
theorem currentViewResponseImageComplete_iff_not_currentViewResponseImageGap :
    CurrentViewResponseImageComplete A B ↔
      ¬ CurrentViewResponseImageGap A B := by
  constructor
  · exact no_currentViewResponseImageGap_of_currentViewResponseImageComplete
  · exact currentViewResponseImageComplete_of_not_currentViewResponseImageGap

/--
A current-view one-step response-image gap blocks current-view step-image
completeness.
-/
theorem not_currentViewStepImageComplete_of_currentViewResponseImageGap
    (gap : CurrentViewResponseImageGap A B) :
    ¬ CurrentViewStepImageComplete A B := by
  intro complete
  exact
    not_currentViewResponseImageComplete_of_currentViewResponseImageGap
      gap
      (CurrentViewStepImageComplete.toCurrentViewResponseImageComplete
        complete)

/--
A current-view one-step response-image gap blocks current-view trace-image
completeness.
-/
theorem not_currentViewTraceImageComplete_of_currentViewResponseImageGap
    (gap : CurrentViewResponseImageGap A B) :
    ¬ CurrentViewTraceImageComplete A B := by
  intro complete
  exact
    not_currentViewResponseImageComplete_of_currentViewResponseImageGap
      gap
      (CurrentViewTraceImageComplete.toCurrentViewResponseImageComplete
        complete)

/--
A current-view one-step response-image gap blocks current-view trace-log
language inclusion.
-/
theorem not_currentViewTraceLogLanguageIncluded_of_currentViewResponseImageGap
    (gap : CurrentViewResponseImageGap A B) :
    ¬ CurrentViewTraceLogLanguageIncluded A B := by
  intro included
  exact
    not_currentViewResponseImageComplete_of_currentViewResponseImageGap
      gap
      (CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
        included)

/--
Current-view trace-log language inclusion is equivalent to current-view
action-response coverage.  Both directions stay before the general
translator-choice boundary.
-/
theorem currentViewTraceLogLanguageIncluded_iff_currentViewActionResponseCoverage :
    CurrentViewTraceLogLanguageIncluded A B ↔
      CurrentViewActionResponseCoverage A B := by
  constructor
  · exact CurrentViewTraceLogLanguageIncluded.toCurrentViewActionResponseCoverage
  · intro coverage
    exact
      CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
        (CurrentViewActionResponseCoverage.toCurrentViewResponseImageComplete
          coverage)

namespace CurrentViewTraceLogLanguageIncluded

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language inclusion gives selected-state response
translators only after passing through the general action-coverage choice
boundary.
-/
theorem toCurrentViewResponseTranslatorExists
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewResponseTranslatorExists A B :=
  CurrentViewActionResponseCoverage.toCurrentViewResponseTranslatorExists
    (toCurrentViewActionResponseCoverage included)

end CurrentViewTraceLogLanguageIncluded

namespace CurrentViewResponseTranslatorExists

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Selected-state response translators imply current-view trace-log language
inclusion by forgetting to action-response coverage and then to the
response-image/trace-image path.
-/
theorem toCurrentViewTraceLogLanguageIncluded
    (existsTranslator : CurrentViewResponseTranslatorExists A B) :
    CurrentViewTraceLogLanguageIncluded A B :=
  CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
    (CurrentViewActionResponseCoverage.toCurrentViewResponseImageComplete
      (toCurrentViewActionResponseCoverage existsTranslator))

end CurrentViewResponseTranslatorExists

/--
Current-view trace-log language inclusion is equivalent to selected-state
response-translator existence, but the forward direction crosses the general
non-finite `Classical.choice` boundary for choosing target actions.
-/
theorem currentViewTraceLogLanguageIncluded_iff_currentViewResponseTranslatorExists :
    CurrentViewTraceLogLanguageIncluded A B ↔
      CurrentViewResponseTranslatorExists A B := by
  constructor
  · exact CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseTranslatorExists
  · exact CurrentViewResponseTranslatorExists.toCurrentViewTraceLogLanguageIncluded

namespace CurrentViewTraceLogLanguageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view trace-log language equivalence yields the current-view
response-image condition by forgetting to forward language inclusion.
-/
theorem toCurrentViewResponseImageComplete
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseImageComplete A B :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
    (toIncluded equivalent)

/--
Current-view trace-log language equivalence also yields the reverse
current-view response-image condition.
-/
theorem toReverseCurrentViewResponseImageComplete
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseImageComplete B A :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
    (toReverseIncluded equivalent)

/--
Current-view trace-log language equivalence yields current-view action-response
coverage before a translator is chosen.
-/
theorem toCurrentViewActionResponseCoverage
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewActionResponseCoverage A B :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewActionResponseCoverage
    (toIncluded equivalent)

/--
Current-view trace-log language equivalence also yields reverse current-view
action-response coverage before a translator is chosen.
-/
theorem toReverseCurrentViewActionResponseCoverage
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewActionResponseCoverage B A :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewActionResponseCoverage
    (toReverseIncluded equivalent)

/--
Current-view trace-log language equivalence yields selected-state response
translators only through the same general target-action choice boundary.
-/
theorem toCurrentViewResponseTranslatorExists
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseTranslatorExists A B :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseTranslatorExists
    (toIncluded equivalent)

/--
Current-view trace-log language equivalence also yields reverse selected-state
response translators through the same general target-action choice boundary.
-/
theorem toReverseCurrentViewResponseTranslatorExists
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseTranslatorExists B A :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseTranslatorExists
    (toReverseIncluded equivalent)

end CurrentViewTraceLogLanguageEquivalent

/--
Bidirectional current-view response-image completeness.

This is the response-image formulation of observable equivalence before any
global action translator is chosen.  It is still role-free: it mentions only
same-current-view one-step observable response images.
-/
def CurrentViewResponseImageEquivalent
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) : Prop :=
  CurrentViewResponseImageComplete A B ∧
    CurrentViewResponseImageComplete B A

namespace CurrentViewResponseImageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/-- Forward response-image completeness from bidirectional equivalence. -/
theorem toCurrentViewResponseImageComplete
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewResponseImageComplete A B :=
  equivalent.1

/-- Reverse response-image completeness from bidirectional equivalence. -/
theorem toReverseCurrentViewResponseImageComplete
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewResponseImageComplete B A :=
  equivalent.2

/--
Bidirectional response-image equivalence gives forward trace-log language
inclusion.
-/
theorem toCurrentViewTraceLogLanguageIncluded
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewTraceLogLanguageIncluded A B :=
  CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
    equivalent.1

/--
Bidirectional response-image equivalence gives reverse trace-log language
inclusion.
-/
theorem toReverseCurrentViewTraceLogLanguageIncluded
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewTraceLogLanguageIncluded B A :=
  CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
    equivalent.2

/--
Bidirectional response-image equivalence gives current-view trace-log language
equivalence.
-/
theorem toCurrentViewTraceLogLanguageEquivalent
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewTraceLogLanguageEquivalent A B := by
  intro sA sB hview log
  constructor
  · intro hlog
    exact
      (toCurrentViewTraceLogLanguageIncluded equivalent hview)
        log hlog
  · intro hlog
    exact
      (toReverseCurrentViewTraceLogLanguageIncluded equivalent hview.symm)
        log hlog

/--
Bidirectional response-image equivalence constructs the forward canonical
role-free response-image simulation.
-/
def toResponseImageSimulation
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    ObservationalResponseImageSimulation A B :=
  CurrentViewResponseImageComplete.toResponseImageSimulation
    (toCurrentViewResponseImageComplete equivalent)

/--
Bidirectional response-image equivalence also constructs the reverse canonical
role-free response-image simulation.
-/
def toReverseResponseImageSimulation
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    ObservationalResponseImageSimulation B A :=
  CurrentViewResponseImageComplete.toResponseImageSimulation
    (toReverseCurrentViewResponseImageComplete equivalent)

end CurrentViewResponseImageEquivalent

/--
Current-view trace-log language equivalence is equivalent to bidirectional
current-view response-image completeness.

This pins the latest "completeness" bottleneck to a purely observational
bidirectional response-image condition.  No `F/K/V_K/L/B/M` roles or action
translator are introduced here.
-/
theorem currentViewTraceLogLanguageEquivalent_iff_currentViewResponseImageEquivalent :
    CurrentViewTraceLogLanguageEquivalent A B ↔
      CurrentViewResponseImageEquivalent A B := by
  constructor
  · intro equivalent
    exact
      ⟨CurrentViewTraceLogLanguageEquivalent.toCurrentViewResponseImageComplete
          equivalent,
        CurrentViewTraceLogLanguageEquivalent.toReverseCurrentViewResponseImageComplete
          equivalent⟩
  · exact
      CurrentViewResponseImageEquivalent.toCurrentViewTraceLogLanguageEquivalent

namespace CurrentViewFiniteActionResponseSearch

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Current-view finite search yields current-view trace-log language inclusion by
first forgetting to response-image completeness and then iterating one-step
images.
-/
theorem toCurrentViewTraceLogLanguageIncluded
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    CurrentViewTraceLogLanguageIncluded A B :=
  CurrentViewResponseImageComplete.toCurrentViewTraceLogLanguageIncluded
    (toCurrentViewResponseImageComplete finiteSearch)

/--
Current-view finite search constructs the canonical trace-language image
simulation through the response-image/language path.
-/
def toTraceLanguageImageSimulation
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    TraceLanguageImageSimulation A B :=
  CurrentViewTraceLogLanguageIncluded.toTraceLanguageImageSimulation
    (toCurrentViewTraceLogLanguageIncluded finiteSearch)

/--
Current-view finite search also constructs the canonical role-free
response-image simulation.

This removes one supplied simulation-relation layer from the finite-search
route.  The finite candidate lists remain inputs; this still does not discover
arbitrary adapters.
-/
def toResponseImageSimulation
    (finiteSearch : CurrentViewFiniteActionResponseSearch A B) :
    ObservationalResponseImageSimulation A B :=
  TraceLanguageImageSimulation.toResponseImageSimulation
    (toTraceLanguageImageSimulation finiteSearch)

end CurrentViewFiniteActionResponseSearch

/--
Bidirectional current-view finite action-response search.

This is the finite-search analogue of current-view response-image equivalence:
the finite candidate lists are still supplied in both directions, but no
Structural Persistence roles or global action translator are assumed.
-/
structure CurrentViewBidirectionalFiniteActionResponseSearch
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  forward : CurrentViewFiniteActionResponseSearch A B
  reverse : CurrentViewFiniteActionResponseSearch B A

namespace CurrentViewBidirectionalFiniteActionResponseSearch

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
Bidirectional finite search gives bidirectional response-image equivalence.
-/
theorem toCurrentViewResponseImageEquivalent
    (bidirectional : CurrentViewBidirectionalFiniteActionResponseSearch A B) :
    CurrentViewResponseImageEquivalent A B :=
  ⟨CurrentViewFiniteActionResponseSearch.toCurrentViewResponseImageComplete
      bidirectional.forward,
    CurrentViewFiniteActionResponseSearch.toCurrentViewResponseImageComplete
      bidirectional.reverse⟩

/--
Bidirectional finite search gives current-view trace-log language equivalence.
-/
theorem toCurrentViewTraceLogLanguageEquivalent
    (bidirectional : CurrentViewBidirectionalFiniteActionResponseSearch A B) :
    CurrentViewTraceLogLanguageEquivalent A B :=
  CurrentViewResponseImageEquivalent.toCurrentViewTraceLogLanguageEquivalent
    (toCurrentViewResponseImageEquivalent bidirectional)

/--
The forward finite search also constructs the forward canonical
trace-language image simulation.
-/
def toTraceLanguageImageSimulation
    (bidirectional : CurrentViewBidirectionalFiniteActionResponseSearch A B) :
    TraceLanguageImageSimulation A B :=
  CurrentViewFiniteActionResponseSearch.toTraceLanguageImageSimulation
    bidirectional.forward

/--
The forward finite-search side constructs the forward role-free
response-image simulation.
-/
def toResponseImageSimulation
    (bidirectional : CurrentViewBidirectionalFiniteActionResponseSearch A B) :
    ObservationalResponseImageSimulation A B :=
  CurrentViewFiniteActionResponseSearch.toResponseImageSimulation
    bidirectional.forward

/--
The reverse finite-search side constructs the reverse role-free response-image
simulation.
-/
def toReverseResponseImageSimulation
    (bidirectional : CurrentViewBidirectionalFiniteActionResponseSearch A B) :
    ObservationalResponseImageSimulation B A :=
  CurrentViewFiniteActionResponseSearch.toResponseImageSimulation
    bidirectional.reverse

end CurrentViewBidirectionalFiniteActionResponseSearch

namespace CurrentViewResponseImageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
If both action types have global finite enumerations, bidirectional
current-view response-image equivalence constructs the bidirectional
finite-search boundary.

The enumerations are still supplied, but the state-specific candidate lists are
not: they are obtained by reusing the global exhaustive lists.
-/
def toCurrentViewBidirectionalFiniteActionResponseSearch
    (sourceEnumeration : FiniteActionEnumeration ActionA)
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (equivalent : CurrentViewResponseImageEquivalent A B) :
    CurrentViewBidirectionalFiniteActionResponseSearch A B where
  forward :=
    CurrentViewResponseImageComplete.toCurrentViewFiniteActionResponseSearch
      targetEnumeration equivalent.1
  reverse :=
    CurrentViewResponseImageComplete.toCurrentViewFiniteActionResponseSearch
      sourceEnumeration equivalent.2

end CurrentViewResponseImageEquivalent

namespace CurrentViewTraceLogLanguageIncluded

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
With a global finite target-action enumeration, current-view trace-log
language inclusion constructs current-view finite search by descending through
the one-step response-image boundary.
-/
def toCurrentViewFiniteActionResponseSearch
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewFiniteActionResponseSearch A B :=
  CurrentViewResponseImageComplete.toCurrentViewFiniteActionResponseSearch
    targetEnumeration
    (toCurrentViewResponseImageComplete included)

/--
With decidable observable responses and a global finite target-action
enumeration, current-view trace-log language inclusion yields selected-state
response translators through finite search rather than through the general
coverage-choice route.
-/
theorem toCurrentViewResponseTranslatorExists_ofFiniteEnumeration
    (responseDecidable : DecidableEq Observation)
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (included : CurrentViewTraceLogLanguageIncluded A B) :
    CurrentViewResponseTranslatorExists A B :=
  CurrentViewFiniteActionResponseSearch.toCurrentViewResponseTranslatorExists
    responseDecidable
    (toCurrentViewFiniteActionResponseSearch targetEnumeration included)

end CurrentViewTraceLogLanguageIncluded

namespace CurrentViewTraceLogLanguageEquivalent

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}

/--
With global finite enumerations for both action types, current-view trace-log
language equivalence constructs the bidirectional finite-search boundary.

The finite enumerations remain explicit inputs; this is not automatic adapter
or action-space discovery for arbitrary alternatives.
-/
def toCurrentViewBidirectionalFiniteActionResponseSearch
    (sourceEnumeration : FiniteActionEnumeration ActionA)
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewBidirectionalFiniteActionResponseSearch A B :=
  CurrentViewResponseImageEquivalent.toCurrentViewBidirectionalFiniteActionResponseSearch
    sourceEnumeration
    targetEnumeration
    ⟨toCurrentViewResponseImageComplete equivalent,
      toReverseCurrentViewResponseImageComplete equivalent⟩

/--
With decidable observable responses and a global finite target-action
enumeration, current-view trace-log language equivalence yields forward
selected-state response translators by the finite-search route.
-/
theorem toCurrentViewResponseTranslatorExists_ofFiniteEnumeration
    (responseDecidable : DecidableEq Observation)
    (targetEnumeration : FiniteActionEnumeration ActionB)
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseTranslatorExists A B :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseTranslatorExists_ofFiniteEnumeration
    responseDecidable targetEnumeration (toIncluded equivalent)

/--
With decidable observable responses and a global finite source-action
enumeration, current-view trace-log language equivalence also yields reverse
selected-state response translators by the finite-search route.
-/
theorem toReverseCurrentViewResponseTranslatorExists_ofFiniteEnumeration
    (responseDecidable : DecidableEq Observation)
    (sourceEnumeration : FiniteActionEnumeration ActionA)
    (equivalent : CurrentViewTraceLogLanguageEquivalent A B) :
    CurrentViewResponseTranslatorExists B A :=
  CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseTranslatorExists_ofFiniteEnumeration
    responseDecidable sourceEnumeration (toReverseIncluded equivalent)

end CurrentViewTraceLogLanguageEquivalent

/--
Canonical trace-behavior relation induced by an action translation.

Two states are related when their current observable views agree and every
finite source action trace has the same prefix log as the translated target
trace.  This definition mentions only observations, boundary readouts, finite
action traces, and the action translation; it does not mention maintained
targets, viable regions, burden, support, or certificates.
-/
def traceBehaviorRelated
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation)
    (toAction : ActionA -> ActionB)
    (sA : StateA) (sB : StateB) : Prop :=
  B.currentView sB = A.currentView sA ∧
    forall actions : List ActionA,
      A.traceLog sA actions =
        B.traceLog sB (actions.map toAction)

namespace TraceBehaviorRelated

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (toAction : ActionA -> ActionB)

/-- Trace-behavior related states preserve current observations. -/
theorem preserves_observation
    {sA : StateA} {sB : StateB}
    (h : traceBehaviorRelated A B toAction sA sB) :
    B.observe sB = A.observe sA :=
  congrArg Prod.fst h.1

/-- Trace-behavior related states preserve current boundary readouts. -/
theorem preserves_readout
    {sA : StateA} {sB : StateB}
    (h : traceBehaviorRelated A B toAction sA sB) :
    B.readout sB = A.readout sA :=
  congrArg Prod.snd h.1

/--
Trace-behavior related states are closed under paired source/target actions.
-/
theorem step_related
    {sA : StateA} {sB : StateB}
    (h : traceBehaviorRelated A B toAction sA sB)
    (action : ActionA) :
    traceBehaviorRelated A B toAction
      (A.step sA action)
      (B.step sB (toAction action)) := by
  constructor
  · have hsingle := h.2 [action]
    change
      [(A.observe (A.step sA action), A.readout (A.step sA action))] =
        [(B.observe (B.step sB (toAction action)),
          B.readout (B.step sB (toAction action)))] at hsingle
    exact (List.cons.inj hsingle).1.symm
  · intro actions
    have htrace := h.2 (action :: actions)
    change
      (A.observe (A.step sA action), A.readout (A.step sA action)) ::
          A.traceLog (A.step sA action) actions =
        (B.observe (B.step sB (toAction action)),
          B.readout (B.step sB (toAction action))) ::
          B.traceLog
            (B.step sB (toAction action))
            (actions.map toAction) at htrace
    exact (List.cons.inj htrace).2

/--
The canonical trace-behavior relation yields a role-free trace simulation.

This is the scoped construction that removes one supplied-simulation layer:
given only an action translation, relatedness is defined by observable current
views and finite prefix-log preservation, and the simulation laws follow.
-/
def toTraceSimulation :
    ObservationalTraceSimulation A B where
  related := traceBehaviorRelated A B toAction
  toAction := toAction
  preserves_observation := by
    intro sA sB h
    exact preserves_observation toAction h
  preserves_readout := by
    intro sA sB h
    exact preserves_readout toAction h
  step_related := by
    intro sA sB h action
    exact step_related toAction h action

/--
Any step-closed observational trace simulation induces the canonical
trace-behavior relation on related states.

This is the reverse bookkeeping direction from `toTraceSimulation`: instead
of supplying all finite prefix-log equalities directly, they are obtained from
the local simulation laws by `ObservationalTraceSimulation.preserves_traceLog`.
-/
theorem ofTraceSimulation
    (simulation : ObservationalTraceSimulation A B)
    {sA : StateA} {sB : StateB}
    (h : simulation.related sA sB) :
    traceBehaviorRelated A B simulation.toAction sA sB := by
  constructor
  · exact simulation.preserves_currentView h
  · intro actions
    exact simulation.preserves_traceLog h actions

/--
A transition-preserving observational map induces canonical trace behavior at
each mapped state.
-/
theorem ofTransitionMap
    (phi : ObservationalTransitionMap A B)
    (sA : StateA) :
    traceBehaviorRelated A B phi.toAction sA (phi.toState sA) := by
  exact ofTraceSimulation (ObservationalTraceSimulation.ofTransitionMap phi)
    (by rfl)

/--
Canonical trace behavior gives trace-log image preservation at the related
state pair.  The image statement forgets the fixed action translator and keeps
only the target trace that realizes each source prefix log.
-/
theorem traceLogImagePreservationAt
    {sA : StateA} {sB : StateB}
    (h : traceBehaviorRelated A B toAction sA sB) :
    TraceLogImagePreservationAt A B sA sB := by
  intro actions
  exact ⟨actions.map toAction, (h.2 actions).symm⟩

end TraceBehaviorRelated

namespace ObservationalResponseMap

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (phi : ObservationalResponseMap A B)

/--
A response-preserving map plus an explicit selected-state full trace-log law
enters the canonical trace-behavior relation at that selected state.

This is the positive counterpart to the deletion test above.  The
`ObservationalResponseMap` fields supply only the current view and one-step
responses; the all-prefix trace-log equality remains a visible hypothesis.
-/
theorem traceBehaviorRelated_of_preserves_traceLog
    (s : StateA)
    (htrace :
      forall actions : List ActionA,
        A.traceLog s actions =
          B.traceLog (phi.toState s) (actions.map phi.toAction)) :
    traceBehaviorRelated A B phi.toAction s (phi.toState s) :=
  ⟨phi.preserves_currentView s, htrace⟩

/--
The same selected-state full trace-log law gives trace-log image preservation
after forgetting the fixed action translator.
-/
theorem traceLogImagePreservationAt_of_preserves_traceLog
    (s : StateA)
    (htrace :
      forall actions : List ActionA,
        A.traceLog s actions =
          B.traceLog (phi.toState s) (actions.map phi.toAction)) :
    TraceLogImagePreservationAt A B s (phi.toState s) :=
  TraceBehaviorRelated.traceLogImagePreservationAt phi.toAction
    (phi.traceBehaviorRelated_of_preserves_traceLog s htrace)

end ObservationalResponseMap

/--
A one-coordinate model for action responses.

The coordinate can be any type; the point is not to ban one-coordinate models
by fiat.  The theorem below says only that a faithful model cannot identify
actions that have different observable responses.
-/
structure SingleCoordinateActionModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (Coordinate : Type x) where
  coordinate : Action -> Coordinate
  responseOfCoordinate : State -> Coordinate -> Observation × BoundaryStatus
  preserves_response :
    forall s a, P.response s a = responseOfCoordinate s (coordinate a)

/--
A coordinate model for finite action traces.

This is the trace-level analogue of `SingleCoordinateActionModel`: the model
sees only the coordinate trace, not the original action trace.
-/
structure TraceCoordinateActionModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (Coordinate : Type x) where
  coordinate : Action -> Coordinate
  traceResponseOfCoordinate :
    State -> List Coordinate -> Observation × BoundaryStatus
  preserves_traceResponse :
    forall s actions,
      P.traceResponse s actions =
        traceResponseOfCoordinate s (actions.map coordinate)

/--
A coordinate model for prefix-sensitive finite action traces.

The model sees only the coordinate trace, but must preserve the full
post-action observation/readout log, not just the final response.
-/
structure TraceLogCoordinateActionModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (Coordinate : Type x) where
  coordinate : Action -> Coordinate
  traceLogOfCoordinate :
    State -> List Coordinate -> List (Observation × BoundaryStatus)
  preserves_traceLog :
    forall s actions,
      P.traceLog s actions =
        traceLogOfCoordinate s (actions.map coordinate)

/--
A coordinate model for initial contexts/states and finite action traces.

The model sees the coordinate of the initial state and the original action
trace.  It is meant to test whether a collapsed context aggregate can preserve
intervention/recovery responses.
-/
structure StateCoordinateTraceModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (Coordinate : Type x) where
  coordinate : State -> Coordinate
  traceResponseOfCoordinate :
    Coordinate -> List Action -> Observation × BoundaryStatus
  preserves_traceResponse :
    forall s actions,
      P.traceResponse s actions =
        traceResponseOfCoordinate (coordinate s) actions

/--
A joint coordinate model for initial states and action traces.

The model sees only a coordinate of the initial state and a coordinate trace of
the actions.  It is the collapsed joint context/action model used in the next
anti-collapse tests.
-/
structure JointCoordinateTraceModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  traceResponseOfCoordinates :
    StateCoordinate -> List ActionCoordinate -> Observation × BoundaryStatus
  preserves_traceResponse :
    forall s actions,
      P.traceResponse s actions =
        traceResponseOfCoordinates
          (stateCoordinate s)
          (actions.map actionCoordinate)

/--
A joint coordinate model for prefix-sensitive finite action traces.

The model sees only a coordinate of the initial state and a coordinate trace of
the actions, but it must preserve every post-action observation/readout.
-/
structure JointCoordinateTraceLogModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  traceLogOfCoordinates :
    StateCoordinate -> List ActionCoordinate ->
      List (Observation × BoundaryStatus)
  preserves_traceLog :
    forall s actions,
      P.traceLog s actions =
        traceLogOfCoordinates
          (stateCoordinate s)
          (actions.map actionCoordinate)

/--
A joint coordinate model with decoders back to the original state and action
types.
-/
structure DecodedJointCoordinateModel
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  stateOfCoordinate : StateCoordinate -> State
  actionOfCoordinate : ActionCoordinate -> Action
  state_decode : forall s, stateOfCoordinate (stateCoordinate s) = s
  action_decode : forall a, actionOfCoordinate (actionCoordinate a) = a

namespace DecodedJointCoordinateModel

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

def traceResponseOfCoordinates
    (D : DecodedJointCoordinateModel P StateCoordinate ActionCoordinate)
    (stateCoordinate : StateCoordinate)
    (actionCoordinates : List ActionCoordinate) :
    Observation × BoundaryStatus :=
  P.traceResponse
    (D.stateOfCoordinate stateCoordinate)
    (actionCoordinates.map D.actionOfCoordinate)

def traceLogOfCoordinates
    (D : DecodedJointCoordinateModel P StateCoordinate ActionCoordinate)
    (stateCoordinate : StateCoordinate)
    (actionCoordinates : List ActionCoordinate) :
    List (Observation × BoundaryStatus) :=
  P.traceLog
    (D.stateOfCoordinate stateCoordinate)
    (actionCoordinates.map D.actionOfCoordinate)

theorem map_action_decode
    (D : DecodedJointCoordinateModel P StateCoordinate ActionCoordinate)
    (actions : List Action) :
    (actions.map D.actionCoordinate).map D.actionOfCoordinate =
      actions := by
  induction actions with
  | nil => rfl
  | cons action actions ih =>
      change
        D.actionOfCoordinate (D.actionCoordinate action) ::
            ((actions.map D.actionCoordinate).map D.actionOfCoordinate) =
          action :: actions
      rw [D.action_decode action, ih]

def toJointCoordinateTraceModel
    (D : DecodedJointCoordinateModel P StateCoordinate ActionCoordinate) :
    JointCoordinateTraceModel P StateCoordinate ActionCoordinate where
  stateCoordinate := D.stateCoordinate
  actionCoordinate := D.actionCoordinate
  traceResponseOfCoordinates := D.traceResponseOfCoordinates
  preserves_traceResponse := by
    intro s actions
    unfold traceResponseOfCoordinates
    rw [D.state_decode s]
    rw [D.map_action_decode actions]

def toJointCoordinateTraceLogModel
    (D : DecodedJointCoordinateModel P StateCoordinate ActionCoordinate) :
    JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate where
  stateCoordinate := D.stateCoordinate
  actionCoordinate := D.actionCoordinate
  traceLogOfCoordinates := D.traceLogOfCoordinates
  preserves_traceLog := by
    intro s actions
    unfold traceLogOfCoordinates
    rw [D.state_decode s]
    rw [D.map_action_decode actions]

end DecodedJointCoordinateModel

/--
If a response-preserving one-coordinate model assigns the same coordinate to
two actions, those actions have the same observable response at every state.
-/
theorem same_coordinate_forces_same_response
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : SingleCoordinateActionModel P Coordinate)
    (s : State) {a₁ a₂ : Action}
    (h : R.coordinate a₁ = R.coordinate a₂) :
    P.response s a₁ = P.response s a₂ := by
  calc
    P.response s a₁ = R.responseOfCoordinate s (R.coordinate a₁) :=
      R.preserves_response s a₁
    _ = R.responseOfCoordinate s (R.coordinate a₂) := by
      rw [h]
    _ = P.response s a₂ := (R.preserves_response s a₂).symm

/--
If two actions are observably distinguished, a response-preserving
one-coordinate model must keep their coordinates distinct.
-/
theorem distinguished_responses_force_distinct_coordinates
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : SingleCoordinateActionModel P Coordinate)
    {s : State} {a₁ a₂ : Action}
    (h : P.response s a₁ ≠ P.response s a₂) :
    R.coordinate a₁ ≠ R.coordinate a₂ := by
  intro hcoord
  exact h (same_coordinate_forces_same_response R s hcoord)

/--
If a trace-coordinate model assigns the same coordinate trace to two action
traces, those traces have the same observable trace response.
-/
theorem same_coordinateTrace_forces_same_traceResponse
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : TraceCoordinateActionModel P Coordinate)
    (s : State) {actions₁ actions₂ : List Action}
    (h :
      actions₁.map R.coordinate =
        actions₂.map R.coordinate) :
    P.traceResponse s actions₁ = P.traceResponse s actions₂ := by
  calc
    P.traceResponse s actions₁ =
        R.traceResponseOfCoordinate s (actions₁.map R.coordinate) :=
      R.preserves_traceResponse s actions₁
    _ = R.traceResponseOfCoordinate s (actions₂.map R.coordinate) := by
      rw [h]
    _ = P.traceResponse s actions₂ :=
      (R.preserves_traceResponse s actions₂).symm

/--
Observably different trace responses force a faithful trace-coordinate model
to assign different coordinate traces.
-/
theorem distinguished_traceResponses_force_distinct_coordinateTrace
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : TraceCoordinateActionModel P Coordinate)
    {s : State} {actions₁ actions₂ : List Action}
    (h : P.traceResponse s actions₁ ≠ P.traceResponse s actions₂) :
    actions₁.map R.coordinate ≠ actions₂.map R.coordinate := by
  intro hcoord
  exact h (same_coordinateTrace_forces_same_traceResponse R s hcoord)

/--
If a prefix-log coordinate model assigns the same coordinate trace to two
action traces, those traces have the same full trace log.
-/
theorem same_coordinateTrace_forces_same_traceLog
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : TraceLogCoordinateActionModel P Coordinate)
    (s : State) {actions₁ actions₂ : List Action}
    (h :
      actions₁.map R.coordinate =
        actions₂.map R.coordinate) :
    P.traceLog s actions₁ = P.traceLog s actions₂ := by
  calc
    P.traceLog s actions₁ =
        R.traceLogOfCoordinate s (actions₁.map R.coordinate) :=
      R.preserves_traceLog s actions₁
    _ = R.traceLogOfCoordinate s (actions₂.map R.coordinate) := by
      rw [h]
    _ = P.traceLog s actions₂ :=
      (R.preserves_traceLog s actions₂).symm

/--
Different prefix logs force a faithful prefix-log coordinate model to assign
different coordinate traces.
-/
theorem distinguished_traceLogs_force_distinct_coordinateTrace
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : TraceLogCoordinateActionModel P Coordinate)
    {s : State} {actions₁ actions₂ : List Action}
    (h : P.traceLog s actions₁ ≠ P.traceLog s actions₂) :
    actions₁.map R.coordinate ≠ actions₂.map R.coordinate := by
  intro hcoord
  exact h (same_coordinateTrace_forces_same_traceLog R s hcoord)

/--
If a state-coordinate trace model assigns the same coordinate to two initial
states, those states have the same observable trace response for any fixed
action trace.
-/
theorem same_stateCoordinate_forces_same_traceResponse
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : StateCoordinateTraceModel P Coordinate)
    {s₁ s₂ : State} (actions : List Action)
    (h : R.coordinate s₁ = R.coordinate s₂) :
    P.traceResponse s₁ actions = P.traceResponse s₂ actions := by
  calc
    P.traceResponse s₁ actions =
        R.traceResponseOfCoordinate (R.coordinate s₁) actions :=
      R.preserves_traceResponse s₁ actions
    _ = R.traceResponseOfCoordinate (R.coordinate s₂) actions := by
      rw [h]
    _ = P.traceResponse s₂ actions :=
      (R.preserves_traceResponse s₂ actions).symm

/--
Observably different context trace responses force a faithful state-coordinate
trace model to distinguish the initial state coordinates.
-/
theorem distinguished_contextTraceResponses_force_distinct_stateCoordinate
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {Coordinate : Type x}
    (R : StateCoordinateTraceModel P Coordinate)
    {s₁ s₂ : State} {actions : List Action}
    (h : P.traceResponse s₁ actions ≠ P.traceResponse s₂ actions) :
    R.coordinate s₁ ≠ R.coordinate s₂ := by
  intro hcoord
  exact h (same_stateCoordinate_forces_same_traceResponse R actions hcoord)

/--
If a joint coordinate model assigns the same initial-state coordinate and the
same action-coordinate trace to two runs, those runs have the same observed
trace response.
-/
theorem same_jointCoordinates_forces_same_traceResponse
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {StateCoordinate : Type x} {ActionCoordinate : Type y}
    (R : JointCoordinateTraceModel P StateCoordinate ActionCoordinate)
    {s₁ s₂ : State} {actions₁ actions₂ : List Action}
    (hs : R.stateCoordinate s₁ = R.stateCoordinate s₂)
    (ha :
      actions₁.map R.actionCoordinate =
        actions₂.map R.actionCoordinate) :
    P.traceResponse s₁ actions₁ = P.traceResponse s₂ actions₂ := by
  calc
    P.traceResponse s₁ actions₁ =
        R.traceResponseOfCoordinates
          (R.stateCoordinate s₁)
          (actions₁.map R.actionCoordinate) :=
      R.preserves_traceResponse s₁ actions₁
    _ = R.traceResponseOfCoordinates
          (R.stateCoordinate s₂)
          (actions₂.map R.actionCoordinate) := by
      rw [hs, ha]
    _ = P.traceResponse s₂ actions₂ :=
      (R.preserves_traceResponse s₂ actions₂).symm

/--
Observed trace distinction contradicts simultaneous equality of the collapsed
state coordinate and action-coordinate trace.
-/
theorem joint_coordinate_equalities_contradict_distinguished_traceResponses
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {StateCoordinate : Type x} {ActionCoordinate : Type y}
    (R : JointCoordinateTraceModel P StateCoordinate ActionCoordinate)
    {s₁ s₂ : State} {actions₁ actions₂ : List Action}
    (h : P.traceResponse s₁ actions₁ ≠ P.traceResponse s₂ actions₂)
    (hs : R.stateCoordinate s₁ = R.stateCoordinate s₂)
    (ha :
      actions₁.map R.actionCoordinate =
        actions₂.map R.actionCoordinate) :
    False :=
  h (same_jointCoordinates_forces_same_traceResponse R hs ha)

/--
If a joint prefix-log coordinate model assigns the same initial-state
coordinate and the same action-coordinate trace to two runs, those runs have
the same full prefix log.
-/
theorem same_jointCoordinates_forces_same_traceLog
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {StateCoordinate : Type x} {ActionCoordinate : Type y}
    (R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate)
    {s₁ s₂ : State} {actions₁ actions₂ : List Action}
    (hs : R.stateCoordinate s₁ = R.stateCoordinate s₂)
    (ha :
      actions₁.map R.actionCoordinate =
        actions₂.map R.actionCoordinate) :
    P.traceLog s₁ actions₁ = P.traceLog s₂ actions₂ := by
  calc
    P.traceLog s₁ actions₁ =
        R.traceLogOfCoordinates
          (R.stateCoordinate s₁)
          (actions₁.map R.actionCoordinate) :=
      R.preserves_traceLog s₁ actions₁
    _ = R.traceLogOfCoordinates
          (R.stateCoordinate s₂)
          (actions₂.map R.actionCoordinate) := by
      rw [hs, ha]
    _ = P.traceLog s₂ actions₂ :=
      (R.preserves_traceLog s₂ actions₂).symm

/--
Observed prefix-log distinction contradicts simultaneous equality of the
collapsed state coordinate and action-coordinate trace.
-/
theorem joint_coordinate_equalities_contradict_distinguished_traceLogs
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {StateCoordinate : Type x} {ActionCoordinate : Type y}
    (R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate)
    {s₁ s₂ : State} {actions₁ actions₂ : List Action}
    (h : P.traceLog s₁ actions₁ ≠ P.traceLog s₂ actions₂)
    (hs : R.stateCoordinate s₁ = R.stateCoordinate s₂)
    (ha :
      actions₁.map R.actionCoordinate =
        actions₂.map R.actionCoordinate) :
    False :=
  h (same_jointCoordinates_forces_same_traceLog R hs ha)

/-- A pair of runs distinguished only by their observed trace responses. -/
structure ObservedJointTraceSplit
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  leftState : State
  rightState : State
  leftActions : List Action
  rightActions : List Action
  traceResponse_ne :
    P.traceResponse leftState leftActions ≠
      P.traceResponse rightState rightActions

namespace ObservedJointTraceSplit

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

/--
Any preserving joint-coordinate model cannot identify both sides of an
observed split.
-/
theorem preserving_model_cannot_collapse_both
    (split : ObservedJointTraceSplit P)
    (R : JointCoordinateTraceModel P StateCoordinate ActionCoordinate) :
    ¬
      (R.stateCoordinate split.leftState =
          R.stateCoordinate split.rightState ∧
        split.leftActions.map R.actionCoordinate =
          split.rightActions.map R.actionCoordinate) := by
  intro h
  exact
    split.traceResponse_ne
      (same_jointCoordinates_forces_same_traceResponse R h.1 h.2)

end ObservedJointTraceSplit

/-- A pair of runs distinguished by their full observed prefix logs. -/
structure ObservedJointTraceLogSplit
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  leftState : State
  rightState : State
  leftActions : List Action
  rightActions : List Action
  traceLog_ne :
    P.traceLog leftState leftActions ≠
      P.traceLog rightState rightActions

namespace ObservedJointTraceLogSplit

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

/--
Any prefix-log preserving joint-coordinate model cannot identify both sides of
an observed prefix-log split.
-/
theorem preserving_model_cannot_collapse_both
    (split : ObservedJointTraceLogSplit P)
    (R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate) :
    ¬
      (R.stateCoordinate split.leftState =
          R.stateCoordinate split.rightState ∧
        split.leftActions.map R.actionCoordinate =
          split.rightActions.map R.actionCoordinate) := by
  intro h
  exact
    split.traceLog_ne
      (same_jointCoordinates_forces_same_traceLog R h.1 h.2)

end ObservedJointTraceLogSplit

/--
A collapsed-coordinate gap where final responses agree but prefix logs do not.

This is a hypothesis-deletion witness for the G1c track: if prefix-log
preservation is weakened to final-response preservation, this local collapse
is no longer detected by the final readout.
-/
structure CollapsedFinalResponsePrefixLogGap
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  leftState : State
  rightState : State
  leftActions : List Action
  rightActions : List Action
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  sameState :
    stateCoordinate leftState = stateCoordinate rightState
  sameTrace :
    leftActions.map actionCoordinate = rightActions.map actionCoordinate
  traceResponse_eq :
    P.traceResponse leftState leftActions =
      P.traceResponse rightState rightActions
  traceLog_ne :
    P.traceLog leftState leftActions ≠
      P.traceLog rightState rightActions

namespace CollapsedFinalResponsePrefixLogGap

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

def observedJointTraceLogSplit
    (gap :
      CollapsedFinalResponsePrefixLogGap
        P StateCoordinate ActionCoordinate) :
    ObservedJointTraceLogSplit P where
  leftState := gap.leftState
  rightState := gap.rightState
  leftActions := gap.leftActions
  rightActions := gap.rightActions
  traceLog_ne := gap.traceLog_ne

/--
The final-response readout itself does not reject the collapsed witness.
This is the local deletion test: final-response equality survives the
coordinate identification recorded in `sameState` and `sameTrace`.
-/
theorem final_response_deletion_witness
    (gap :
      CollapsedFinalResponsePrefixLogGap
        P StateCoordinate ActionCoordinate) :
    P.traceResponse gap.leftState gap.leftActions =
        P.traceResponse gap.rightState gap.rightActions ∧
      gap.stateCoordinate gap.leftState =
        gap.stateCoordinate gap.rightState ∧
      gap.leftActions.map gap.actionCoordinate =
        gap.rightActions.map gap.actionCoordinate :=
  ⟨gap.traceResponse_eq, gap.sameState, gap.sameTrace⟩

/--
Prefix-log preservation still rejects the same collapsed witness.
This is why the alternative-quantified G1 statement must keep prefix-sensitive
observational preservation rather than only a final-response readout.
-/
theorem no_preserving_prefix_log_coordinate_model
    (gap :
      CollapsedFinalResponsePrefixLogGap
        P StateCoordinate ActionCoordinate) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        StateCoordinate -> List ActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (gap.stateCoordinate s)
                (actions.map gap.actionCoordinate)) := by
  intro h
  rcases h with ⟨traceLogOfCoordinates, hpreserve⟩
  let R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate :=
    { stateCoordinate := gap.stateCoordinate
      actionCoordinate := gap.actionCoordinate
      traceLogOfCoordinates := traceLogOfCoordinates
      preserves_traceLog := hpreserve }
  exact
    gap.traceLog_ne
      (same_jointCoordinates_forces_same_traceLog
        R gap.sameState gap.sameTrace)

end CollapsedFinalResponsePrefixLogGap

/--
A two-channel trace law that yields an observed split without naming internal
Structural Persistence roles.
-/
structure TwoChannelTraceLaw
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  adverseContext : State
  restorativeContext : State
  restorativeIntervention : Action
  adverseIntervention : Action
  restorativeResponse : Observation × BoundaryStatus
  adverseResponse : Observation × BoundaryStatus
  restorative_law :
    P.traceResponse adverseContext [restorativeIntervention] =
      restorativeResponse
  adverse_law :
    P.traceResponse restorativeContext [adverseIntervention] =
      adverseResponse
  response_ne : restorativeResponse ≠ adverseResponse

namespace TwoChannelTraceLaw

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

def restorativeTrace (law : TwoChannelTraceLaw P) : List Action :=
  [law.restorativeIntervention]

def adverseTrace (law : TwoChannelTraceLaw P) : List Action :=
  [law.adverseIntervention]

theorem traceResponse_ne (law : TwoChannelTraceLaw P) :
    P.traceResponse law.adverseContext law.restorativeTrace ≠
      P.traceResponse law.restorativeContext law.adverseTrace := by
  intro h
  exact
    law.response_ne
      (calc
        law.restorativeResponse =
            P.traceResponse law.adverseContext law.restorativeTrace :=
          law.restorative_law.symm
        _ = P.traceResponse law.restorativeContext law.adverseTrace := h
        _ = law.adverseResponse := law.adverse_law)

/-- A one-action trace log is the singleton final trace response. -/
theorem traceLog_singleton
    (s : State) (a : Action) :
    P.traceLog s [a] = [P.traceResponse s [a]] :=
  rfl

/-- The two-channel law also yields a prefix-log distinction. -/
theorem traceLog_ne (law : TwoChannelTraceLaw P) :
    P.traceLog law.adverseContext law.restorativeTrace ≠
      P.traceLog law.restorativeContext law.adverseTrace := by
  intro h
  apply law.traceResponse_ne
  have hleft :
      P.traceLog law.adverseContext law.restorativeTrace =
        [P.traceResponse law.adverseContext law.restorativeTrace] := by
    unfold restorativeTrace
    rfl
  have hright :
      P.traceLog law.restorativeContext law.adverseTrace =
        [P.traceResponse law.restorativeContext law.adverseTrace] := by
    unfold adverseTrace
    rfl
  rw [hleft, hright] at h
  exact (List.cons.inj h).1

def observedJointTraceSplit
    (law : TwoChannelTraceLaw P) :
    ObservedJointTraceSplit P where
  leftState := law.adverseContext
  rightState := law.restorativeContext
  leftActions := law.restorativeTrace
  rightActions := law.adverseTrace
  traceResponse_ne := law.traceResponse_ne

def observedJointTraceLogSplit
    (law : TwoChannelTraceLaw P) :
    ObservedJointTraceLogSplit P where
  leftState := law.adverseContext
  rightState := law.restorativeContext
  leftActions := law.restorativeTrace
  rightActions := law.adverseTrace
  traceLog_ne := law.traceLog_ne

theorem preserving_model_cannot_collapse_both
    (law : TwoChannelTraceLaw P)
    (R : JointCoordinateTraceModel P StateCoordinate ActionCoordinate) :
    ¬
      (R.stateCoordinate law.adverseContext =
          R.stateCoordinate law.restorativeContext ∧
        law.restorativeTrace.map R.actionCoordinate =
          law.adverseTrace.map R.actionCoordinate) :=
  law.observedJointTraceSplit.preserving_model_cannot_collapse_both R

/--
Any prefix-log preserving joint-coordinate model cannot collapse both sides of
the two-channel law.
-/
theorem prefix_log_model_cannot_collapse_both
    (law : TwoChannelTraceLaw P)
    (R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate) :
    ¬
      (R.stateCoordinate law.adverseContext =
          R.stateCoordinate law.restorativeContext ∧
        law.restorativeTrace.map R.actionCoordinate =
          law.adverseTrace.map R.actionCoordinate) :=
  law.observedJointTraceLogSplit.preserving_model_cannot_collapse_both R

end TwoChannelTraceLaw

namespace ObservationalResponseMap

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (phi : ObservationalResponseMap A B)

/--
Transport a one-step two-channel observational law across a response-preserving
map.

This is a fixed-probe consequence of observational preservation.  It does not
claim full trace preservation, transition commutation, or any recovery of
internal Structural Persistence roles.
-/
def toTwoChannelTraceLaw (law : TwoChannelTraceLaw A) :
    TwoChannelTraceLaw B where
  adverseContext := phi.toState law.adverseContext
  restorativeContext := phi.toState law.restorativeContext
  restorativeIntervention := phi.toAction law.restorativeIntervention
  adverseIntervention := phi.toAction law.adverseIntervention
  restorativeResponse := law.restorativeResponse
  adverseResponse := law.adverseResponse
  restorative_law := by
    calc
      B.traceResponse
          (phi.toState law.adverseContext)
          [phi.toAction law.restorativeIntervention] =
          B.response
            (phi.toState law.adverseContext)
            (phi.toAction law.restorativeIntervention) := rfl
      _ = A.response law.adverseContext law.restorativeIntervention :=
          phi.preserves_response
            law.adverseContext law.restorativeIntervention
      _ = A.traceResponse law.adverseContext
            [law.restorativeIntervention] := rfl
      _ = law.restorativeResponse := law.restorative_law
  adverse_law := by
    calc
      B.traceResponse
          (phi.toState law.restorativeContext)
          [phi.toAction law.adverseIntervention] =
          B.response
            (phi.toState law.restorativeContext)
            (phi.toAction law.adverseIntervention) := rfl
      _ = A.response law.restorativeContext law.adverseIntervention :=
          phi.preserves_response
            law.restorativeContext law.adverseIntervention
      _ = A.traceResponse law.restorativeContext
            [law.adverseIntervention] := rfl
      _ = law.adverseResponse := law.adverse_law
  response_ne := law.response_ne

/--
The transported two-channel probes remain final-response separated in the
target process.
-/
theorem transported_twoChannel_traceResponse_ne
    (law : TwoChannelTraceLaw A) :
    B.traceResponse
        (phi.toState law.adverseContext)
        [phi.toAction law.restorativeIntervention] ≠
      B.traceResponse
        (phi.toState law.restorativeContext)
        [phi.toAction law.adverseIntervention] :=
  (phi.toTwoChannelTraceLaw law).traceResponse_ne

/--
The transported two-channel probes remain prefix-log separated in the target
process.

Because the probes are one-step traces, this follows from response
preservation alone.  Full finite-prefix preservation still requires the
stronger transition-commuting map above.
-/
theorem transported_twoChannel_traceLog_ne
    (law : TwoChannelTraceLaw A) :
    B.traceLog
        (phi.toState law.adverseContext)
        [phi.toAction law.restorativeIntervention] ≠
      B.traceLog
        (phi.toState law.restorativeContext)
        [phi.toAction law.adverseIntervention] :=
  (phi.toTwoChannelTraceLaw law).traceLog_ne

end ObservationalResponseMap

namespace ObservationalTraceSimulation

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (simulation : ObservationalTraceSimulation A B)

/--
Transport a one-step two-channel observational law across a trace simulation.

The target contexts are not images of a supplied state function.  They are only
required to be related to the two source contexts by the simulation relation.
The simulation itself is still an input, so this is not yet an
arbitrary-alternative construction theorem.
-/
def toTwoChannelTraceLaw
    (law : TwoChannelTraceLaw A)
    (targetAdverseContext targetRestorativeContext : StateB)
    (adverse_related :
      simulation.related law.adverseContext targetAdverseContext)
    (restorative_related :
      simulation.related law.restorativeContext targetRestorativeContext) :
    TwoChannelTraceLaw B where
  adverseContext := targetAdverseContext
  restorativeContext := targetRestorativeContext
  restorativeIntervention := simulation.toAction law.restorativeIntervention
  adverseIntervention := simulation.toAction law.adverseIntervention
  restorativeResponse := law.restorativeResponse
  adverseResponse := law.adverseResponse
  restorative_law := by
    calc
      B.traceResponse targetAdverseContext
          [simulation.toAction law.restorativeIntervention] =
          B.response
            targetAdverseContext
            (simulation.toAction law.restorativeIntervention) := rfl
      _ = A.response law.adverseContext law.restorativeIntervention :=
          simulation.preserves_response adverse_related
            law.restorativeIntervention
      _ = A.traceResponse law.adverseContext
            [law.restorativeIntervention] := rfl
      _ = law.restorativeResponse := law.restorative_law
  adverse_law := by
    calc
      B.traceResponse targetRestorativeContext
          [simulation.toAction law.adverseIntervention] =
          B.response
            targetRestorativeContext
            (simulation.toAction law.adverseIntervention) := rfl
      _ = A.response law.restorativeContext law.adverseIntervention :=
          simulation.preserves_response restorative_related
            law.adverseIntervention
      _ = A.traceResponse law.restorativeContext
            [law.adverseIntervention] := rfl
      _ = law.adverseResponse := law.adverse_law
  response_ne := law.response_ne

/--
The transported two-channel probes remain final-response separated in the
target process.
-/
theorem transported_twoChannel_traceResponse_ne
    (law : TwoChannelTraceLaw A)
    {targetAdverseContext targetRestorativeContext : StateB}
    (adverse_related :
      simulation.related law.adverseContext targetAdverseContext)
    (restorative_related :
      simulation.related law.restorativeContext targetRestorativeContext) :
    B.traceResponse
        targetAdverseContext
        [simulation.toAction law.restorativeIntervention] ≠
      B.traceResponse
        targetRestorativeContext
        [simulation.toAction law.adverseIntervention] :=
  (simulation.toTwoChannelTraceLaw
    law targetAdverseContext targetRestorativeContext
    adverse_related restorative_related).traceResponse_ne

/--
The transported two-channel probes remain prefix-log separated in the target
process.
-/
theorem transported_twoChannel_traceLog_ne
    (law : TwoChannelTraceLaw A)
    {targetAdverseContext targetRestorativeContext : StateB}
    (adverse_related :
      simulation.related law.adverseContext targetAdverseContext)
    (restorative_related :
      simulation.related law.restorativeContext targetRestorativeContext) :
    B.traceLog
        targetAdverseContext
        [simulation.toAction law.restorativeIntervention] ≠
      B.traceLog
        targetRestorativeContext
        [simulation.toAction law.adverseIntervention] :=
  (simulation.toTwoChannelTraceLaw
    law targetAdverseContext targetRestorativeContext
    adverse_related restorative_related).traceLog_ne

end ObservationalTraceSimulation

/--
A fixed decisive-log transport for a two-channel law.

This is weaker than a full transition map or trace simulation.  It only says
that the two one-step decisive target logs are the corresponding source logs.
From those two observable equalities we can reconstruct the target two-channel
law, including the response separation, without naming internal roles.
-/
structure TwoChannelFixedTraceLogTransport
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  law : TwoChannelTraceLaw A
  targetAdverseContext : StateB
  targetRestorativeContext : StateB
  targetRestorativeIntervention : ActionB
  targetAdverseIntervention : ActionB
  target_restorativeTraceLog_eq_source :
    B.traceLog targetAdverseContext [targetRestorativeIntervention] =
      A.traceLog law.adverseContext law.restorativeTrace
  target_adverseTraceLog_eq_source :
    B.traceLog targetRestorativeContext [targetAdverseIntervention] =
      A.traceLog law.restorativeContext law.adverseTrace

namespace TwoChannelFixedTraceLogTransport

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (transport : TwoChannelFixedTraceLogTransport A B)

theorem target_restorative_law :
    B.traceResponse
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] =
      transport.law.restorativeResponse := by
  have hlist :
      [B.traceResponse
          transport.targetAdverseContext
          [transport.targetRestorativeIntervention]] =
        [transport.law.restorativeResponse] := by
    calc
      [B.traceResponse
          transport.targetAdverseContext
          [transport.targetRestorativeIntervention]] =
          B.traceLog
            transport.targetAdverseContext
            [transport.targetRestorativeIntervention] := rfl
      _ = A.traceLog
            transport.law.adverseContext
            transport.law.restorativeTrace :=
          transport.target_restorativeTraceLog_eq_source
      _ = [A.traceResponse
            transport.law.adverseContext
            transport.law.restorativeTrace] := by
          unfold TwoChannelTraceLaw.restorativeTrace
          rfl
      _ = [transport.law.restorativeResponse] :=
          congrArg (fun response => [response])
            transport.law.restorative_law
  exact (List.cons.inj hlist).1

theorem target_adverse_law :
    B.traceResponse
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] =
      transport.law.adverseResponse := by
  have hlist :
      [B.traceResponse
          transport.targetRestorativeContext
          [transport.targetAdverseIntervention]] =
        [transport.law.adverseResponse] := by
    calc
      [B.traceResponse
          transport.targetRestorativeContext
          [transport.targetAdverseIntervention]] =
          B.traceLog
            transport.targetRestorativeContext
            [transport.targetAdverseIntervention] := rfl
      _ = A.traceLog
            transport.law.restorativeContext
            transport.law.adverseTrace :=
          transport.target_adverseTraceLog_eq_source
      _ = [A.traceResponse
            transport.law.restorativeContext
            transport.law.adverseTrace] := by
          unfold TwoChannelTraceLaw.adverseTrace
          rfl
      _ = [transport.law.adverseResponse] :=
          congrArg (fun response => [response])
            transport.law.adverse_law
  exact (List.cons.inj hlist).1

/-- The target two-channel law reconstructed from two fixed-log equalities. -/
def targetLaw : TwoChannelTraceLaw B where
  adverseContext := transport.targetAdverseContext
  restorativeContext := transport.targetRestorativeContext
  restorativeIntervention := transport.targetRestorativeIntervention
  adverseIntervention := transport.targetAdverseIntervention
  restorativeResponse := transport.law.restorativeResponse
  adverseResponse := transport.law.adverseResponse
  restorative_law := transport.target_restorative_law
  adverse_law := transport.target_adverse_law
  response_ne := transport.law.response_ne

theorem target_traceResponse_ne :
    B.traceResponse
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      B.traceResponse
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.targetLaw.traceResponse_ne

theorem target_traceLog_ne :
    B.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      B.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.targetLaw.traceLog_ne

end TwoChannelFixedTraceLogTransport

/--
A fixed one-step response transport for a two-channel law.

This is weaker than `TwoChannelFixedTraceLogTransport`: it supplies only the
two one-step intervention-response equalities.  Since the decisive traces in a
`TwoChannelTraceLaw` are singletons, those response equalities derive the
fixed-log transport needed by the event-score layer.
-/
structure TwoChannelFixedResponseTransport
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (A : ObservationalPersistenceProcess StateA ActionA Observation)
    (B : ObservationalPersistenceProcess StateB ActionB Observation) where
  law : TwoChannelTraceLaw A
  targetAdverseContext : StateB
  targetRestorativeContext : StateB
  targetRestorativeIntervention : ActionB
  targetAdverseIntervention : ActionB
  target_restorativeResponse_eq_source :
    B.response targetAdverseContext targetRestorativeIntervention =
      A.response law.adverseContext law.restorativeIntervention
  target_adverseResponse_eq_source :
    B.response targetRestorativeContext targetAdverseIntervention =
      A.response law.restorativeContext law.adverseIntervention

namespace TwoChannelFixedResponseTransport

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable (transport : TwoChannelFixedResponseTransport A B)

theorem target_restorativeTraceLog_eq_source :
    B.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] =
      A.traceLog transport.law.adverseContext transport.law.restorativeTrace := by
  calc
    B.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] =
        [B.response
          transport.targetAdverseContext
          transport.targetRestorativeIntervention] := rfl
    _ =
        [A.response
          transport.law.adverseContext
          transport.law.restorativeIntervention] :=
        congrArg (fun response => [response])
          transport.target_restorativeResponse_eq_source
    _ = A.traceLog
          transport.law.adverseContext
          transport.law.restorativeTrace := by
        unfold TwoChannelTraceLaw.restorativeTrace
        rfl

theorem target_adverseTraceLog_eq_source :
    B.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] =
      A.traceLog transport.law.restorativeContext transport.law.adverseTrace := by
  calc
    B.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] =
        [B.response
          transport.targetRestorativeContext
          transport.targetAdverseIntervention] := rfl
    _ =
        [A.response
          transport.law.restorativeContext
          transport.law.adverseIntervention] :=
        congrArg (fun response => [response])
          transport.target_adverseResponse_eq_source
    _ = A.traceLog
          transport.law.restorativeContext
          transport.law.adverseTrace := by
        unfold TwoChannelTraceLaw.adverseTrace
        rfl

/-- Forget a fixed-response transport into the fixed-log transport it implies. -/
def toFixedTraceLogTransport :
    TwoChannelFixedTraceLogTransport A B where
  law := transport.law
  targetAdverseContext := transport.targetAdverseContext
  targetRestorativeContext := transport.targetRestorativeContext
  targetRestorativeIntervention := transport.targetRestorativeIntervention
  targetAdverseIntervention := transport.targetAdverseIntervention
  target_restorativeTraceLog_eq_source :=
    transport.target_restorativeTraceLog_eq_source
  target_adverseTraceLog_eq_source :=
    transport.target_adverseTraceLog_eq_source

def targetLaw : TwoChannelTraceLaw B :=
  transport.toFixedTraceLogTransport.targetLaw

theorem target_traceResponse_ne :
    B.traceResponse
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      B.traceResponse
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.toFixedTraceLogTransport.target_traceResponse_ne

theorem target_traceLog_ne :
    B.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      B.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.toFixedTraceLogTransport.target_traceLog_ne

end TwoChannelFixedResponseTransport

/--
A witness that a chosen pair of state/action coordinates collapses two
observationally different runs.
-/
structure CollapsedJointTraceSplit
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  leftState : State
  rightState : State
  leftActions : List Action
  rightActions : List Action
  same_stateCoordinate :
    stateCoordinate leftState = stateCoordinate rightState
  same_actionCoordinateTrace :
    leftActions.map actionCoordinate = rightActions.map actionCoordinate
  traceResponse_ne :
    P.traceResponse leftState leftActions ≠
      P.traceResponse rightState rightActions

namespace CollapsedJointTraceSplit

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

/--
No preserving joint-coordinate response rule can use coordinates that collapse
an observed split witness.
-/
theorem no_preserving_joint_coordinate_model
    (split :
      CollapsedJointTraceSplit P StateCoordinate ActionCoordinate) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        StateCoordinate -> List ActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (split.stateCoordinate s)
                (actions.map split.actionCoordinate)) := by
  intro h
  rcases h with ⟨traceResponseOfCoordinates, hpreserve⟩
  let R : JointCoordinateTraceModel P StateCoordinate ActionCoordinate :=
    { stateCoordinate := split.stateCoordinate
      actionCoordinate := split.actionCoordinate
      traceResponseOfCoordinates := traceResponseOfCoordinates
      preserves_traceResponse := hpreserve }
  exact
    joint_coordinate_equalities_contradict_distinguished_traceResponses R
      split.traceResponse_ne
      split.same_stateCoordinate
      split.same_actionCoordinateTrace

end CollapsedJointTraceSplit

/--
A witness that chosen state/action coordinates collapse two runs with distinct
prefix logs.
-/
structure CollapsedJointTraceLogSplit
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  leftState : State
  rightState : State
  leftActions : List Action
  rightActions : List Action
  same_stateCoordinate :
    stateCoordinate leftState = stateCoordinate rightState
  same_actionCoordinateTrace :
    leftActions.map actionCoordinate = rightActions.map actionCoordinate
  traceLog_ne :
    P.traceLog leftState leftActions ≠
      P.traceLog rightState rightActions

namespace CollapsedJointTraceLogSplit

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

/--
No prefix-log preserving joint-coordinate rule can use coordinates that
collapse a prefix-log split witness.
-/
theorem no_preserving_joint_coordinate_traceLog_model
    (split :
      CollapsedJointTraceLogSplit P StateCoordinate ActionCoordinate) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        StateCoordinate -> List ActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (split.stateCoordinate s)
                (actions.map split.actionCoordinate)) := by
  intro h
  rcases h with ⟨traceLogOfCoordinates, hpreserve⟩
  let R : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate :=
    { stateCoordinate := split.stateCoordinate
      actionCoordinate := split.actionCoordinate
      traceLogOfCoordinates := traceLogOfCoordinates
      preserves_traceLog := hpreserve }
  exact
    joint_coordinate_equalities_contradict_distinguished_traceLogs R
      split.traceLog_ne
      split.same_stateCoordinate
      split.same_actionCoordinateTrace

end CollapsedJointTraceLogSplit

namespace TwoChannelTraceLaw

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

def collapsedJointTraceSplit
    (law : TwoChannelTraceLaw P)
    (stateCoordinate : State -> StateCoordinate)
    (actionCoordinate : Action -> ActionCoordinate)
    (sameState :
      stateCoordinate law.adverseContext =
        stateCoordinate law.restorativeContext)
    (sameTrace :
      law.restorativeTrace.map actionCoordinate =
        law.adverseTrace.map actionCoordinate) :
    CollapsedJointTraceSplit P StateCoordinate ActionCoordinate where
  stateCoordinate := stateCoordinate
  actionCoordinate := actionCoordinate
  leftState := law.adverseContext
  rightState := law.restorativeContext
  leftActions := law.restorativeTrace
  rightActions := law.adverseTrace
  same_stateCoordinate := sameState
  same_actionCoordinateTrace := sameTrace
  traceResponse_ne := law.traceResponse_ne

def collapsedJointTraceLogSplit
    (law : TwoChannelTraceLaw P)
    (stateCoordinate : State -> StateCoordinate)
    (actionCoordinate : Action -> ActionCoordinate)
    (sameState :
      stateCoordinate law.adverseContext =
        stateCoordinate law.restorativeContext)
    (sameTrace :
      law.restorativeTrace.map actionCoordinate =
        law.adverseTrace.map actionCoordinate) :
    CollapsedJointTraceLogSplit P StateCoordinate ActionCoordinate where
  stateCoordinate := stateCoordinate
  actionCoordinate := actionCoordinate
  leftState := law.adverseContext
  rightState := law.restorativeContext
  leftActions := law.restorativeTrace
  rightActions := law.adverseTrace
  same_stateCoordinate := sameState
  same_actionCoordinateTrace := sameTrace
  traceLog_ne := law.traceLog_ne

end TwoChannelTraceLaw

structure TwoChannelAggregateIdentification
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  law : TwoChannelTraceLaw P
  stateCoordinate : State -> StateCoordinate
  actionCoordinate : Action -> ActionCoordinate
  sameState :
    stateCoordinate law.adverseContext =
      stateCoordinate law.restorativeContext
  sameTrace :
    law.restorativeTrace.map actionCoordinate =
      law.adverseTrace.map actionCoordinate

namespace TwoChannelAggregateIdentification

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

def collapsedSplit
    (agg :
      TwoChannelAggregateIdentification P StateCoordinate ActionCoordinate) :
    CollapsedJointTraceSplit P StateCoordinate ActionCoordinate :=
  agg.law.collapsedJointTraceSplit
    agg.stateCoordinate
    agg.actionCoordinate
    agg.sameState
    agg.sameTrace

def collapsedTraceLogSplit
    (agg :
      TwoChannelAggregateIdentification P StateCoordinate ActionCoordinate) :
    CollapsedJointTraceLogSplit P StateCoordinate ActionCoordinate :=
  agg.law.collapsedJointTraceLogSplit
    agg.stateCoordinate
    agg.actionCoordinate
    agg.sameState
    agg.sameTrace

theorem no_traceResponse_model
    (agg :
      TwoChannelAggregateIdentification P StateCoordinate ActionCoordinate) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        StateCoordinate -> List ActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (agg.stateCoordinate s)
                (actions.map agg.actionCoordinate)) :=
  CollapsedJointTraceSplit.no_preserving_joint_coordinate_model
    agg.collapsedSplit

theorem no_traceLog_model
    (agg :
      TwoChannelAggregateIdentification P StateCoordinate ActionCoordinate) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        StateCoordinate -> List ActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (agg.stateCoordinate s)
                (actions.map agg.actionCoordinate)) :=
  CollapsedJointTraceLogSplit.no_preserving_joint_coordinate_traceLog_model
    agg.collapsedTraceLogSplit

end TwoChannelAggregateIdentification

structure TwoChannelSplitPackage
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (CollapsedStateCoordinate : Type x)
    (CollapsedActionCoordinate : Type y)
    (DecodedStateCoordinate : Type z)
    (DecodedActionCoordinate : Type t) where
  law : TwoChannelTraceLaw P
  collapsedStateCoordinate : State -> CollapsedStateCoordinate
  collapsedActionCoordinate : Action -> CollapsedActionCoordinate
  sameCollapsedState :
    collapsedStateCoordinate law.adverseContext =
      collapsedStateCoordinate law.restorativeContext
  sameCollapsedTrace :
    law.restorativeTrace.map collapsedActionCoordinate =
      law.adverseTrace.map collapsedActionCoordinate
  decodedModel :
    DecodedJointCoordinateModel
      P DecodedStateCoordinate DecodedActionCoordinate

namespace TwoChannelSplitPackage

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}

def collapsedSplit
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    CollapsedJointTraceSplit
      P CollapsedStateCoordinate CollapsedActionCoordinate :=
  pkg.law.collapsedJointTraceSplit
    pkg.collapsedStateCoordinate
    pkg.collapsedActionCoordinate
    pkg.sameCollapsedState
    pkg.sameCollapsedTrace

def collapsedTraceLogSplit
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    CollapsedJointTraceLogSplit
      P CollapsedStateCoordinate CollapsedActionCoordinate :=
  pkg.law.collapsedJointTraceLogSplit
    pkg.collapsedStateCoordinate
    pkg.collapsedActionCoordinate
    pkg.sameCollapsedState
    pkg.sameCollapsedTrace

theorem no_collapsed_traceResponse_model
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (pkg.collapsedStateCoordinate s)
                (actions.map pkg.collapsedActionCoordinate)) :=
  CollapsedJointTraceSplit.no_preserving_joint_coordinate_model
    pkg.collapsedSplit

theorem no_collapsed_traceLog_model
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (pkg.collapsedStateCoordinate s)
                (actions.map pkg.collapsedActionCoordinate)) :=
  CollapsedJointTraceLogSplit.no_preserving_joint_coordinate_traceLog_model
    pkg.collapsedTraceLogSplit

def decodedJointCoordinateTraceModel
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    JointCoordinateTraceModel
      P DecodedStateCoordinate DecodedActionCoordinate :=
  pkg.decodedModel.toJointCoordinateTraceModel

def decodedJointCoordinateTraceLogModel
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    JointCoordinateTraceLogModel
      P DecodedStateCoordinate DecodedActionCoordinate :=
  pkg.decodedModel.toJointCoordinateTraceLogModel

theorem decoded_preserves_traceResponse
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate)
    (s : State) (actions : List Action) :
    P.traceResponse s actions =
      pkg.decodedModel.traceResponseOfCoordinates
        (pkg.decodedModel.stateCoordinate s)
        (actions.map pkg.decodedModel.actionCoordinate) :=
  pkg.decodedJointCoordinateTraceModel.preserves_traceResponse s actions

theorem decoded_preserves_traceLog
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate)
    (s : State) (actions : List Action) :
    P.traceLog s actions =
      pkg.decodedModel.traceLogOfCoordinates
        (pkg.decodedModel.stateCoordinate s)
        (actions.map pkg.decodedModel.actionCoordinate) :=
  pkg.decodedJointCoordinateTraceLogModel.preserves_traceLog s actions

def ofAggregateIdentification
    (agg :
      TwoChannelAggregateIdentification
        P CollapsedStateCoordinate CollapsedActionCoordinate)
    (decodedModel :
      DecodedJointCoordinateModel
        P DecodedStateCoordinate DecodedActionCoordinate) :
    TwoChannelSplitPackage
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate where
  law := agg.law
  collapsedStateCoordinate := agg.stateCoordinate
  collapsedActionCoordinate := agg.actionCoordinate
  sameCollapsedState := agg.sameState
  sameCollapsedTrace := agg.sameTrace
  decodedModel := decodedModel

end TwoChannelSplitPackage

structure ChannelRoleBridgeInputs
    {State : Type u} {Action : Type v} {Observation : Type w}
    {P : ObservationalPersistenceProcess State Action Observation}
    {CollapsedStateCoordinate : Type x}
    {CollapsedActionCoordinate : Type y}
    {DecodedStateCoordinate : Type z}
    {DecodedActionCoordinate : Type t}
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate)
    (BurdenRole : Type r) (SupportRole : Type p) where
  burdenOfRun : DecodedStateCoordinate -> List DecodedActionCoordinate -> BurdenRole
  supportOfRun : DecodedStateCoordinate -> List DecodedActionCoordinate -> SupportRole
  adverseBurden : BurdenRole
  restorativeSupport : SupportRole
  adverseTrace_burden :
    burdenOfRun
        (pkg.decodedModel.stateCoordinate pkg.law.restorativeContext)
        (pkg.law.adverseTrace.map pkg.decodedModel.actionCoordinate) =
      adverseBurden
  restorativeTrace_support :
    supportOfRun
        (pkg.decodedModel.stateCoordinate pkg.law.adverseContext)
        (pkg.law.restorativeTrace.map pkg.decodedModel.actionCoordinate) =
      restorativeSupport

namespace TwoChannelSplitPackage

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}

def decodedTraceLog
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate)
    (stateCoordinate : DecodedStateCoordinate)
    (actionCoordinates : List DecodedActionCoordinate) :
    List (Observation × BoundaryStatus) :=
  P.traceLog
    (pkg.decodedModel.stateOfCoordinate stateCoordinate)
    (actionCoordinates.map pkg.decodedModel.actionOfCoordinate)

def decodedTraceResponse
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate)
    (stateCoordinate : DecodedStateCoordinate)
    (actionCoordinates : List DecodedActionCoordinate) :
    Observation × BoundaryStatus :=
  P.traceResponse
    (pkg.decodedModel.stateOfCoordinate stateCoordinate)
    (actionCoordinates.map pkg.decodedModel.actionOfCoordinate)

def hasCollapsedPrefix : List (Observation × BoundaryStatus) -> Bool
  | [] => false
  | (_, BoundaryStatus.collapsed) :: _ => true
  | _ :: rest => hasCollapsedPrefix rest

def finalLogReadoutViable : List (Observation × BoundaryStatus) -> Bool
  | [] => false
  | (_, BoundaryStatus.viable) :: [] => true
  | _ :: [] => false
  | _ :: rest => finalLogReadoutViable rest

def finalResponseViable : Observation × BoundaryStatus -> Bool
  | (_, BoundaryStatus.viable) => true
  | _ => false

def observedCollapsedPrefixRole
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Bool :=
  fun stateCoordinate actionCoordinates =>
    hasCollapsedPrefix (pkg.decodedTraceLog stateCoordinate actionCoordinates)

def observedViableFinalRole
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Bool :=
  fun stateCoordinate actionCoordinates =>
    finalResponseViable
      (pkg.decodedTraceResponse stateCoordinate actionCoordinates)

/--
Construct the smallest current role bridge from observations alone.

This does not derive `L/B` or `M`.  It constructs only two Boolean readouts:
whether a decoded run has a collapsed prefix, and whether its final response
is viable.
-/
def observedBoundaryEventRoleInputs
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    ChannelRoleBridgeInputs pkg Bool Bool where
  burdenOfRun := pkg.observedCollapsedPrefixRole
  supportOfRun := pkg.observedViableFinalRole
  adverseBurden :=
    pkg.observedCollapsedPrefixRole
      (pkg.decodedModel.stateCoordinate pkg.law.restorativeContext)
      (pkg.law.adverseTrace.map pkg.decodedModel.actionCoordinate)
  restorativeSupport :=
    pkg.observedViableFinalRole
      (pkg.decodedModel.stateCoordinate pkg.law.adverseContext)
      (pkg.law.restorativeTrace.map pkg.decodedModel.actionCoordinate)
  adverseTrace_burden := rfl
  restorativeTrace_support := rfl

end TwoChannelSplitPackage

structure ChannelRoleBridgeBoundary
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (CollapsedStateCoordinate : Type x)
    (CollapsedActionCoordinate : Type y)
    (DecodedStateCoordinate : Type z)
    (DecodedActionCoordinate : Type t)
    (BurdenRole : Type r) (SupportRole : Type p) where
  package :
    TwoChannelSplitPackage
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
  roleInputs : ChannelRoleBridgeInputs package BurdenRole SupportRole

namespace ChannelRoleBridgeBoundary

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}
variable {BurdenRole : Type r} {SupportRole : Type p}

theorem no_collapsed_traceResponse_model
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (bridge.package.collapsedStateCoordinate s)
                (actions.map bridge.package.collapsedActionCoordinate)) :=
  bridge.package.no_collapsed_traceResponse_model

theorem no_collapsed_traceLog_model
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (bridge.package.collapsedStateCoordinate s)
                (actions.map bridge.package.collapsedActionCoordinate)) :=
  bridge.package.no_collapsed_traceLog_model

theorem decoded_preserves_traceResponse
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole)
    (s : State) (actions : List Action) :
    P.traceResponse s actions =
      bridge.package.decodedModel.traceResponseOfCoordinates
        (bridge.package.decodedModel.stateCoordinate s)
        (actions.map bridge.package.decodedModel.actionCoordinate) :=
  bridge.package.decoded_preserves_traceResponse s actions

theorem decoded_preserves_traceLog
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole)
    (s : State) (actions : List Action) :
    P.traceLog s actions =
      bridge.package.decodedModel.traceLogOfCoordinates
        (bridge.package.decodedModel.stateCoordinate s)
        (actions.map bridge.package.decodedModel.actionCoordinate) :=
  bridge.package.decoded_preserves_traceLog s actions

theorem adverseTrace_burden
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    bridge.roleInputs.burdenOfRun
        (bridge.package.decodedModel.stateCoordinate
          bridge.package.law.restorativeContext)
        (bridge.package.law.adverseTrace.map
          bridge.package.decodedModel.actionCoordinate) =
      bridge.roleInputs.adverseBurden :=
  bridge.roleInputs.adverseTrace_burden

theorem restorativeTrace_support
    (bridge :
      ChannelRoleBridgeBoundary
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    bridge.roleInputs.supportOfRun
        (bridge.package.decodedModel.stateCoordinate
          bridge.package.law.adverseContext)
        (bridge.package.law.restorativeTrace.map
          bridge.package.decodedModel.actionCoordinate) =
      bridge.roleInputs.restorativeSupport :=
  bridge.roleInputs.restorativeTrace_support

end ChannelRoleBridgeBoundary

namespace TwoChannelSplitPackage

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}

def observedBoundaryEventBridgeBoundary
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    ChannelRoleBridgeBoundary
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      Bool Bool where
  package := pkg
  roleInputs := pkg.observedBoundaryEventRoleInputs

end TwoChannelSplitPackage

structure PrefixSensitiveRoleSeparationCandidate
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (CollapsedStateCoordinate : Type x)
    (CollapsedActionCoordinate : Type y)
    (DecodedStateCoordinate : Type z)
    (DecodedActionCoordinate : Type t)
    (BurdenRole : Type r) (SupportRole : Type p) where
  bridge :
    ChannelRoleBridgeBoundary
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      BurdenRole SupportRole

namespace PrefixSensitiveRoleSeparationCandidate

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}
variable {BurdenRole : Type r} {SupportRole : Type p}

theorem no_collapsed_traceResponse_model
    (candidate :
      PrefixSensitiveRoleSeparationCandidate
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (candidate.bridge.package.collapsedStateCoordinate s)
                (actions.map candidate.bridge.package.collapsedActionCoordinate)) :=
  candidate.bridge.no_collapsed_traceResponse_model

theorem no_collapsed_traceLog_model
    (candidate :
      PrefixSensitiveRoleSeparationCandidate
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (candidate.bridge.package.collapsedStateCoordinate s)
                (actions.map
                  candidate.bridge.package.collapsedActionCoordinate)) :=
  candidate.bridge.no_collapsed_traceLog_model

theorem decoded_preserves_traceLog
    (candidate :
      PrefixSensitiveRoleSeparationCandidate
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole)
    (s : State) (actions : List Action) :
    P.traceLog s actions =
      candidate.bridge.package.decodedModel.traceLogOfCoordinates
        (candidate.bridge.package.decodedModel.stateCoordinate s)
        (actions.map candidate.bridge.package.decodedModel.actionCoordinate) :=
  candidate.bridge.decoded_preserves_traceLog s actions

theorem adverseTrace_burden
    (candidate :
      PrefixSensitiveRoleSeparationCandidate
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    candidate.bridge.roleInputs.burdenOfRun
        (candidate.bridge.package.decodedModel.stateCoordinate
          candidate.bridge.package.law.restorativeContext)
        (candidate.bridge.package.law.adverseTrace.map
          candidate.bridge.package.decodedModel.actionCoordinate) =
      candidate.bridge.roleInputs.adverseBurden :=
  candidate.bridge.adverseTrace_burden

theorem restorativeTrace_support
    (candidate :
      PrefixSensitiveRoleSeparationCandidate
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole) :
    candidate.bridge.roleInputs.supportOfRun
        (candidate.bridge.package.decodedModel.stateCoordinate
          candidate.bridge.package.law.adverseContext)
        (candidate.bridge.package.law.restorativeTrace.map
          candidate.bridge.package.decodedModel.actionCoordinate) =
      candidate.bridge.roleInputs.restorativeSupport :=
  candidate.bridge.restorativeTrace_support

end PrefixSensitiveRoleSeparationCandidate

namespace TwoChannelSplitPackage

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {CollapsedStateCoordinate : Type x}
variable {CollapsedActionCoordinate : Type y}
variable {DecodedStateCoordinate : Type z}
variable {DecodedActionCoordinate : Type t}

def observedBoundaryEventRoleSeparationCandidate
    (pkg :
      TwoChannelSplitPackage
        P CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate) :
    PrefixSensitiveRoleSeparationCandidate
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      Bool Bool where
  bridge := pkg.observedBoundaryEventBridgeBoundary

end TwoChannelSplitPackage

/--
Target semantics for an observational process.

This is the guarded boundary where the `F` claim enters the observational
track.  It does not put `K`, `V_K`, burden, or support into the observational
process itself; it only says which target is maintained and why a viable
readout entails maintenance of that target.
-/
structure ObservationalTargetSemantics
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (Target : Type q) where
  maintainedTarget : Target
  maintains : State -> Target -> Prop
  viable_implies_maintained :
    forall s, P.readout s = BoundaryStatus.viable ->
      maintains s maintainedTarget

namespace ObservationalTargetSemantics

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {Target : Type q}

/-- Forget the action/observation layer and expose the semantic G1 kernel. -/
def toAlternativeCalculation
    (S : ObservationalTargetSemantics P Target) :
    AlternativePersistenceCalculation State Target where
  maintainedTarget := S.maintainedTarget
  maintains := S.maintains
  boundaryReadout := P.readout
  viable_implies_maintained := S.viable_implies_maintained

/-- Nontriviality for the observational target semantics. -/
def NontrivialReadout
    (_S : ObservationalTargetSemantics P Target) : Prop :=
  exists s, P.readout s = BoundaryStatus.viable

/-- Observational nontriviality becomes semantic nontriviality. -/
theorem nontrivial_toAlternativeCalculation
    (S : ObservationalTargetSemantics P Target)
    (h : S.NontrivialReadout) :
    S.toAlternativeCalculation.NontrivialReadout := by
  rcases h with ⟨s, hs⟩
  exact ⟨⟨s, hs⟩⟩

/--
The raw viable region in the semantic kernel is the viable readout preimage of
the observational process.
-/
theorem stateViableRegion_eq
    (S : ObservationalTargetSemantics P Target) :
    S.toAlternativeCalculation.stateViableRegion =
      {s | P.readout s = BoundaryStatus.viable} :=
  rfl

end ObservationalTargetSemantics

/--
A target-aware observational map.

The observational map preserves readouts and responses.  These two extra
fields say that the maintained target itself and its maintenance predicate are
preserved, which is exactly the information needed to enter the semantic core.
-/
structure ObservationalTargetMap
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y} {Target : Type q}
    {A : ObservationalPersistenceProcess StateA ActionA Observation}
    {B : ObservationalPersistenceProcess StateB ActionB Observation}
    (SA : ObservationalTargetSemantics A Target)
    (SB : ObservationalTargetSemantics B Target)
    (phi : ObservationalResponseMap A B) where
  target_eq : SA.maintainedTarget = SB.maintainedTarget
  preserves_maintained_target :
    forall s, SA.maintains s SA.maintainedTarget ->
      SB.maintains (phi.toState s) SB.maintainedTarget

namespace ObservationalTargetMap

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y} {Target : Type q}
variable {A : ObservationalPersistenceProcess StateA ActionA Observation}
variable {B : ObservationalPersistenceProcess StateB ActionB Observation}
variable {SA : ObservationalTargetSemantics A Target}
variable {SB : ObservationalTargetSemantics B Target}
variable {phi : ObservationalResponseMap A B}

/-- A target-aware observational map is a semantic same-calculation map. -/
def toSameCalculationMap
    (targetMap : ObservationalTargetMap SA SB phi) :
    SameCalculationMap
      SA.toAlternativeCalculation
      SB.toAlternativeCalculation where
  toFun := phi.toState
  target_eq := targetMap.target_eq
  preserves_boundary := phi.preserves_readout
  preserves_maintained_target :=
    targetMap.preserves_maintained_target

/-- Recover the semantic `K`/`V_K` scaffold from the target-aware map. -/
def recoverStateRealizationAndViability
    (targetMap : ObservationalTargetMap SA SB phi)
    (h : SA.NontrivialReadout) :
    StateRealizationViabilityRecovery
      SA.toAlternativeCalculation
      SB.toAlternativeCalculation
      targetMap.toSameCalculationMap :=
  Persistence.StructuralPersistence.recoverStateRealizationAndViability
    targetMap.toSameCalculationMap
    (SA.nontrivial_toAlternativeCalculation h)

end ObservationalTargetMap

/--
Scoped bridge from a prefix-sensitive observational candidate to the semantic
`F/K/V_K` recovery kernel.

The bridge keeps the two pieces separate: the candidate contributes the
prefix-log anti-collapse side, while the target semantics and target-aware map
contribute the maintained-target and viable-region recovery side.
-/
structure PrefixSensitiveSemanticBridge
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (CollapsedStateCoordinate : Type z)
    (CollapsedActionCoordinate : Type t)
    (DecodedStateCoordinate : Type r)
    (DecodedActionCoordinate : Type p)
    (BurdenRole : Type q) (SupportRole : Type a)
    (Target : Type b) where
  candidate :
    PrefixSensitiveRoleSeparationCandidate
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      BurdenRole SupportRole
  sourceSemantics : ObservationalTargetSemantics P Target
  targetSemantics : ObservationalTargetSemantics Q Target
  observationMap : ObservationalResponseMap P Q
  targetMap :
    ObservationalTargetMap
      sourceSemantics targetSemantics observationMap
  sourceNontrivial : sourceSemantics.NontrivialReadout

namespace PrefixSensitiveSemanticBridge

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {BurdenRole : Type q} {SupportRole : Type a}
variable {Target : Type b}

/-- The semantic same-calculation map exposed by the bridge. -/
def sameCalculationMap
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    SameCalculationMap
      bridge.sourceSemantics.toAlternativeCalculation
      bridge.targetSemantics.toAlternativeCalculation :=
  bridge.targetMap.toSameCalculationMap

/-- The recovered state-based `K`/`V_K` scaffold. -/
def stateRealizationViability
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    StateRealizationViabilityRecovery
      bridge.sourceSemantics.toAlternativeCalculation
      bridge.targetSemantics.toAlternativeCalculation
      bridge.sameCalculationMap :=
  bridge.targetMap.recoverStateRealizationAndViability
    bridge.sourceNontrivial

/-- The recovered viable region is nonempty under the supplied nontrivial readout. -/
theorem viableRegion_nonempty
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    bridge.stateRealizationViability.viableRegion.Nonempty :=
  bridge.stateRealizationViability.viableRegion_nonempty

/-- Viable membership in the recovered region realizes the maintained target. -/
theorem viable_implies_maintained_target
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target)
    (k : bridge.stateRealizationViability.K)
    (hk : k ∈ bridge.stateRealizationViability.viableRegion) :
    bridge.sourceSemantics.maintains
      (bridge.stateRealizationViability.carrier k)
      bridge.sourceSemantics.maintainedTarget :=
  bridge.stateRealizationViability.viable_implies_carrier_realizes k hk

/-- The prefix-sensitive decoded model still preserves the observational log. -/
theorem decoded_preserves_traceLog
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target)
    (s : StateA) (actions : List ActionA) :
    P.traceLog s actions =
      bridge.candidate.bridge.package.decodedModel.traceLogOfCoordinates
        (bridge.candidate.bridge.package.decodedModel.stateCoordinate s)
        (actions.map
          bridge.candidate.bridge.package.decodedModel.actionCoordinate) :=
  bridge.candidate.decoded_preserves_traceLog s actions

/--
The collapsed aggregate still cannot preserve the candidate's trace response.
This is kept separate from the semantic `F/K/V_K` recovery theorem.
-/
theorem no_collapsed_traceResponse_model
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ¬ Exists
      (fun traceResponseOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          Observation × BoundaryStatus =>
          forall s actions,
            P.traceResponse s actions =
              traceResponseOfCoordinates
                (bridge.candidate.bridge.package.collapsedStateCoordinate s)
                (actions.map
                  bridge.candidate.bridge.package.collapsedActionCoordinate)) :=
  bridge.candidate.no_collapsed_traceResponse_model

/--
The collapsed aggregate also cannot preserve the candidate's prefix log.  This
is the prefix-sensitive no-collapse side used before connecting to `F/K/V_K`.
-/
theorem no_collapsed_traceLog_model
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (bridge.candidate.bridge.package.collapsedStateCoordinate s)
                (actions.map
                  bridge.candidate.bridge.package.collapsedActionCoordinate)) :=
  bridge.candidate.no_collapsed_traceLog_model

end PrefixSensitiveSemanticBridge

/--
Alternative construction boundary for the observation-derived event bridge.

Unlike `AlternativeQuantifiedFactorizationStatementBoundary`, this does not
take a finished semantic bridge as an input.  It constructs the current Boolean
boundary-event bridge from the split package's decoded prefix logs and final
responses, then connects that constructed candidate to the target-aware
semantic `F/K/V_K` scaffold.

This is still not the full G1 no-alternative theorem: it constructs only the
`collapsed-prefix` / `viable-final` event bridge, not the full `L/B` and `M`
roles or log-accounting certificate.
-/
structure ObservationDerivedAlternativeConstructionBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (CollapsedStateCoordinate : Type z)
    (CollapsedActionCoordinate : Type t)
    (DecodedStateCoordinate : Type r)
    (DecodedActionCoordinate : Type p)
    (Target : Type b) where
  package :
    TwoChannelSplitPackage
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
  sourceSemantics : ObservationalTargetSemantics P Target
  targetSemantics : ObservationalTargetSemantics Q Target
  observationMap : ObservationalResponseMap P Q
  targetMap :
    ObservationalTargetMap
      sourceSemantics targetSemantics observationMap
  sourceNontrivial : sourceSemantics.NontrivialReadout

namespace ObservationDerivedAlternativeConstructionBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}

def constructedCandidate
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    PrefixSensitiveRoleSeparationCandidate
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      Bool Bool :=
  boundary.package.observedBoundaryEventRoleSeparationCandidate

def toSemanticBridge
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    PrefixSensitiveSemanticBridge
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      Bool Bool Target where
  candidate := boundary.constructedCandidate
  sourceSemantics := boundary.sourceSemantics
  targetSemantics := boundary.targetSemantics
  observationMap := boundary.observationMap
  targetMap := boundary.targetMap
  sourceNontrivial := boundary.sourceNontrivial

theorem no_collapsed_traceLog_model
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (boundary.package.collapsedStateCoordinate s)
                (actions.map boundary.package.collapsedActionCoordinate)) :=
  boundary.toSemanticBridge.no_collapsed_traceLog_model

theorem decoded_preserves_traceLog
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target)
    (s : StateA) (actions : List ActionA) :
    P.traceLog s actions =
      boundary.package.decodedModel.traceLogOfCoordinates
        (boundary.package.decodedModel.stateCoordinate s)
        (actions.map boundary.package.decodedModel.actionCoordinate) :=
  boundary.toSemanticBridge.decoded_preserves_traceLog s actions

theorem viableRegion_nonempty
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    boundary.toSemanticBridge.stateRealizationViability.viableRegion.Nonempty :=
  boundary.toSemanticBridge.viableRegion_nonempty

theorem adverseTrace_collapsedPrefix_law
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    boundary.package.observedCollapsedPrefixRole
        (boundary.package.decodedModel.stateCoordinate
          boundary.package.law.restorativeContext)
        (boundary.package.law.adverseTrace.map
          boundary.package.decodedModel.actionCoordinate) =
      boundary.toSemanticBridge.candidate.bridge.roleInputs.adverseBurden :=
  boundary.toSemanticBridge.candidate.adverseTrace_burden

theorem restorativeTrace_viableFinal_law
    (boundary :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) :
    boundary.package.observedViableFinalRole
        (boundary.package.decodedModel.stateCoordinate
          boundary.package.law.adverseContext)
        (boundary.package.law.restorativeTrace.map
          boundary.package.decodedModel.actionCoordinate) =
      boundary.toSemanticBridge.candidate.bridge.roleInputs.restorativeSupport :=
  boundary.toSemanticBridge.candidate.restorativeTrace_support

end ObservationDerivedAlternativeConstructionBoundary

/--
Scoped log-accounting bridge for the prefix-sensitive semantic track.

This is the boundary where a burden/loss interpretation is supplied.  The
observational candidate does not derive `L/B`: the bridge requires an explicit
loss functional, ratio readout, ratio-domain certificates, and a law saying
that the supplied burden readout agrees with that loss functional.
-/
structure PrefixSensitiveLogAccountingBridge
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {BurdenRole : Type q} {SupportRole : Type a}
    {Target : Type b}
    (bridge :
      PrefixSensitiveSemanticBridge
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) where
  accountingFunctional : Persistence.RepresentationTheorem.PersistenceFunctional
  ratioOfRun : DecodedStateCoordinate -> List DecodedActionCoordinate -> ℝ
  ratio_pos :
    forall stateCoordinate actionCoordinates,
      0 < ratioOfRun stateCoordinate actionCoordinates
  ratio_le_one :
    forall stateCoordinate actionCoordinates,
      ratioOfRun stateCoordinate actionCoordinates ≤ 1
  burdenLossValue : BurdenRole -> ℝ
  burden_matches_lossFn :
    forall stateCoordinate actionCoordinates,
      burdenLossValue
          (bridge.candidate.bridge.roleInputs.burdenOfRun
            stateCoordinate actionCoordinates) =
        accountingFunctional.lossFn
          (ratioOfRun stateCoordinate actionCoordinates)

namespace PrefixSensitiveLogAccountingBridge

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {BurdenRole : Type q} {SupportRole : Type a}
variable {Target : Type b}
variable {bridge :
  PrefixSensitiveSemanticBridge
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate
    BurdenRole SupportRole Target}

/-- The supplied accounting functional has the log-ratio representation. -/
theorem functional_loss_has_log_form
    (accounting : PrefixSensitiveLogAccountingBridge bridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ r, 0 < r -> r ≤ 1 ->
        accounting.accountingFunctional.lossFn r = -k * Real.log r :=
  Persistence.RepresentationTheorem.loss_must_be_log
    accounting.accountingFunctional

/--
The supplied burden readout inherits log form only through the explicit
matching law to the supplied accounting functional.
-/
theorem burden_loss_has_log_form
    (accounting : PrefixSensitiveLogAccountingBridge bridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        accounting.burdenLossValue
            (bridge.candidate.bridge.roleInputs.burdenOfRun
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (accounting.ratioOfRun stateCoordinate actionCoordinates) := by
  obtain ⟨k, hk, hform⟩ :=
    accounting.functional_loss_has_log_form
  refine ⟨k, hk, ?_⟩
  intro stateCoordinate actionCoordinates
  rw [accounting.burden_matches_lossFn]
  exact
    hform
      (accounting.ratioOfRun stateCoordinate actionCoordinates)
      (accounting.ratio_pos stateCoordinate actionCoordinates)
      (accounting.ratio_le_one stateCoordinate actionCoordinates)

/--
Specialized log form for the candidate's adverse trace.  This is still
certificate-relative: the loss functional, ratio readout, and matching law are
all supplied by `accounting`.
-/
theorem adverseTrace_burden_loss_has_log_form
    (accounting : PrefixSensitiveLogAccountingBridge bridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      accounting.burdenLossValue
          (bridge.candidate.bridge.roleInputs.burdenOfRun
            (bridge.candidate.bridge.package.decodedModel.stateCoordinate
              bridge.candidate.bridge.package.law.restorativeContext)
            (bridge.candidate.bridge.package.law.adverseTrace.map
              bridge.candidate.bridge.package.decodedModel.actionCoordinate)) =
        -k * Real.log
          (accounting.ratioOfRun
            (bridge.candidate.bridge.package.decodedModel.stateCoordinate
              bridge.candidate.bridge.package.law.restorativeContext)
            (bridge.candidate.bridge.package.law.adverseTrace.map
              bridge.candidate.bridge.package.decodedModel.actionCoordinate)) := by
  obtain ⟨k, hk, hform⟩ := accounting.burden_loss_has_log_form
  exact
    ⟨k, hk,
      hform
        (bridge.candidate.bridge.package.decodedModel.stateCoordinate
          bridge.candidate.bridge.package.law.restorativeContext)
        (bridge.candidate.bridge.package.law.adverseTrace.map
          bridge.candidate.bridge.package.decodedModel.actionCoordinate)⟩

end PrefixSensitiveLogAccountingBridge

/--
Scoped canonical factorization boundary for the current G1 semantic track.

This is not the final no-alternative theorem and it does not quantify over all
alternative representations.  It packages the currently proved ingredients:
prefix-log anti-collapse, supplied-target `F/K/V_K` recovery, supplied
burden/support bridge laws, and certificate-relative log accounting.
-/
structure PrefixSensitiveCanonicalFactorizationBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (CollapsedStateCoordinate : Type z)
    (CollapsedActionCoordinate : Type t)
    (DecodedStateCoordinate : Type r)
    (DecodedActionCoordinate : Type p)
    (BurdenRole : Type q) (SupportRole : Type a)
    (Target : Type b) where
  semanticBridge :
    PrefixSensitiveSemanticBridge
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      BurdenRole SupportRole Target
  logAccounting :
    PrefixSensitiveLogAccountingBridge semanticBridge

namespace PrefixSensitiveCanonicalFactorizationBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {BurdenRole : Type q} {SupportRole : Type a}
variable {Target : Type b}

def stateRealizationViability
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    StateRealizationViabilityRecovery
      factorization.semanticBridge.sourceSemantics.toAlternativeCalculation
      factorization.semanticBridge.targetSemantics.toAlternativeCalculation
      factorization.semanticBridge.sameCalculationMap :=
  factorization.semanticBridge.stateRealizationViability

def splitPackage
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    TwoChannelSplitPackage
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate :=
  factorization.semanticBridge.candidate.bridge.package

def decodedModel
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    DecodedJointCoordinateModel
      P DecodedStateCoordinate DecodedActionCoordinate :=
  factorization.splitPackage.decodedModel

def collapsedStateCoordinate
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    StateA -> CollapsedStateCoordinate :=
  factorization.splitPackage.collapsedStateCoordinate

def collapsedActionCoordinate
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ActionA -> CollapsedActionCoordinate :=
  factorization.splitPackage.collapsedActionCoordinate

def burdenOfRun
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> BurdenRole :=
  factorization.semanticBridge.candidate.bridge.roleInputs.burdenOfRun

def supportOfRun
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> SupportRole :=
  factorization.semanticBridge.candidate.bridge.roleInputs.supportOfRun

def adverseTraceStateCoordinate
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    DecodedStateCoordinate :=
  factorization.decodedModel.stateCoordinate
    factorization.splitPackage.law.restorativeContext

def adverseTraceActionCoordinates
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    List DecodedActionCoordinate :=
  factorization.splitPackage.law.adverseTrace.map
    factorization.decodedModel.actionCoordinate

def restorativeTraceStateCoordinate
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    DecodedStateCoordinate :=
  factorization.decodedModel.stateCoordinate
    factorization.splitPackage.law.adverseContext

def restorativeTraceActionCoordinates
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    List DecodedActionCoordinate :=
  factorization.splitPackage.law.restorativeTrace.map
    factorization.decodedModel.actionCoordinate

/-- Prefix-log aggregate collapse is ruled out by the packaged candidate. -/
theorem no_collapsed_traceLog_model
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (factorization.collapsedStateCoordinate s)
                (actions.map factorization.collapsedActionCoordinate)) :=
  factorization.semanticBridge.no_collapsed_traceLog_model

/-- The decoded coordinate interface preserves the prefix log. -/
theorem decoded_preserves_traceLog
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target)
    (s : StateA) (actions : List ActionA) :
    P.traceLog s actions =
      factorization.decodedModel.traceLogOfCoordinates
        (factorization.decodedModel.stateCoordinate s)
        (actions.map factorization.decodedModel.actionCoordinate) :=
  factorization.semanticBridge.decoded_preserves_traceLog s actions

/-- The semantic `F/K/V_K` recovery side has a nonempty viable region. -/
theorem viableRegion_nonempty
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    factorization.stateRealizationViability.viableRegion.Nonempty :=
  factorization.semanticBridge.viableRegion_nonempty

/-- Viable membership realizes the supplied maintained target. -/
theorem viable_implies_maintained_target
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target)
    (k : factorization.stateRealizationViability.K)
    (hk : k ∈ factorization.stateRealizationViability.viableRegion) :
    factorization.semanticBridge.sourceSemantics.maintains
      (factorization.stateRealizationViability.carrier k)
      factorization.semanticBridge.sourceSemantics.maintainedTarget :=
  factorization.semanticBridge.viable_implies_maintained_target k hk

/-- The supplied adverse trace burden law remains visible on the package. -/
theorem adverseTrace_burden
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    factorization.burdenOfRun
        factorization.adverseTraceStateCoordinate
        factorization.adverseTraceActionCoordinates =
      factorization.semanticBridge.candidate.bridge.roleInputs.adverseBurden :=
  factorization.semanticBridge.candidate.adverseTrace_burden

/-- The supplied restorative trace support law remains visible on the package. -/
theorem restorativeTrace_support
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    factorization.supportOfRun
        factorization.restorativeTraceStateCoordinate
        factorization.restorativeTraceActionCoordinates =
      factorization.semanticBridge.candidate.bridge.roleInputs.restorativeSupport :=
  factorization.semanticBridge.candidate.restorativeTrace_support

/-- The supplied burden/loss accounting inherits log form from the log theorem. -/
theorem burden_loss_has_log_form
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        factorization.logAccounting.burdenLossValue
            (factorization.semanticBridge.candidate.bridge.roleInputs.burdenOfRun
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (factorization.logAccounting.ratioOfRun
              stateCoordinate actionCoordinates) :=
  factorization.logAccounting.burden_loss_has_log_form

/-- The adverse trace has the same certificate-relative log-accounting readout. -/
theorem adverseTrace_burden_loss_has_log_form
    (factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ∃ k : ℝ, 0 ≤ k ∧
      factorization.logAccounting.burdenLossValue
          (factorization.burdenOfRun
            factorization.adverseTraceStateCoordinate
            factorization.adverseTraceActionCoordinates) =
        -k * Real.log
          (factorization.logAccounting.ratioOfRun
            factorization.adverseTraceStateCoordinate
            factorization.adverseTraceActionCoordinates) :=
  factorization.logAccounting.adverseTrace_burden_loss_has_log_form

end PrefixSensitiveCanonicalFactorizationBoundary

/--
Factorization boundary built from the observation-derived construction track.

The semantic bridge is constructed from observable prefix-log/final-response
events by `ObservationDerivedAlternativeConstructionBoundary`.  The
log-accounting certificate remains a visible supplied field; this surface does
not claim to derive the full `L/B` coordinate or qualified support `M`.
-/
structure ObservationDerivedFactorizationBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    (construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) where
  logAccounting :
    PrefixSensitiveLogAccountingBridge construction.toSemanticBridge

namespace ObservationDerivedFactorizationBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}

def toCanonicalFactorization
    (surface : ObservationDerivedFactorizationBoundary construction) :
    PrefixSensitiveCanonicalFactorizationBoundary
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      Bool Bool Target where
  semanticBridge := construction.toSemanticBridge
  logAccounting := surface.logAccounting

theorem no_collapsed_traceLog_model
    (surface : ObservationDerivedFactorizationBoundary construction) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (construction.package.collapsedStateCoordinate s)
                (actions.map construction.package.collapsedActionCoordinate)) :=
  (toCanonicalFactorization surface).no_collapsed_traceLog_model

theorem decoded_preserves_traceLog
    (surface : ObservationDerivedFactorizationBoundary construction)
    (s : StateA) (actions : List ActionA) :
    P.traceLog s actions =
      construction.package.decodedModel.traceLogOfCoordinates
        (construction.package.decodedModel.stateCoordinate s)
        (actions.map construction.package.decodedModel.actionCoordinate) :=
  (toCanonicalFactorization surface).decoded_preserves_traceLog s actions

theorem viableRegion_nonempty
    (surface : ObservationDerivedFactorizationBoundary construction) :
    (PrefixSensitiveCanonicalFactorizationBoundary.stateRealizationViability
      (toCanonicalFactorization surface)).viableRegion.Nonempty :=
  (toCanonicalFactorization surface).viableRegion_nonempty

theorem observed_adverseTrace_collapsedPrefix_law
    (_surface : ObservationDerivedFactorizationBoundary construction) :
    construction.package.observedCollapsedPrefixRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.restorativeContext)
        (construction.package.law.adverseTrace.map
          construction.package.decodedModel.actionCoordinate) =
      construction.toSemanticBridge.candidate.bridge.roleInputs.adverseBurden :=
  construction.adverseTrace_collapsedPrefix_law

theorem observed_restorativeTrace_viableFinal_law
    (_surface : ObservationDerivedFactorizationBoundary construction) :
    construction.package.observedViableFinalRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.adverseContext)
        (construction.package.law.restorativeTrace.map
          construction.package.decodedModel.actionCoordinate) =
      construction.toSemanticBridge.candidate.bridge.roleInputs.restorativeSupport :=
  construction.restorativeTrace_viableFinal_law

theorem burden_loss_has_log_form
    (surface : ObservationDerivedFactorizationBoundary construction) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        surface.logAccounting.burdenLossValue
            (construction.package.observedCollapsedPrefixRole
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (surface.logAccounting.ratioOfRun
              stateCoordinate actionCoordinates) :=
  (toCanonicalFactorization surface).burden_loss_has_log_form

theorem adverseTrace_burden_loss_has_log_form
    (surface : ObservationDerivedFactorizationBoundary construction) :
    ∃ k : ℝ, 0 ≤ k ∧
      surface.logAccounting.burdenLossValue
          (construction.package.observedCollapsedPrefixRole
            ((toCanonicalFactorization surface).adverseTraceStateCoordinate)
            ((toCanonicalFactorization surface).adverseTraceActionCoordinates)) =
        -k * Real.log
          (surface.logAccounting.ratioOfRun
            ((toCanonicalFactorization surface).adverseTraceStateCoordinate)
            ((toCanonicalFactorization surface).adverseTraceActionCoordinates)) :=
  (toCanonicalFactorization surface).adverseTrace_burden_loss_has_log_form

end ObservationDerivedFactorizationBoundary

/--
A coordinate model for a Boolean role read out from decoded runs.

The role can be any observation-derived event.  The model sees only a run
coordinate and must preserve the role value.  This is a small anti-collapse
test for the next burden/support-candidate layer: if the observed role differs
on two decoded runs, a role-preserving coordinate model cannot identify those
runs.
-/
structure RunRoleCoordinateModel
    {StateCoordinate : Type u} {ActionCoordinate : Type v}
    (role : StateCoordinate -> List ActionCoordinate -> Bool)
    (RunCoordinate : Type w) where
  coordinate : StateCoordinate -> List ActionCoordinate -> RunCoordinate
  roleOfCoordinate : RunCoordinate -> Bool
  preserves_role :
    forall stateCoordinate actionCoordinates,
      role stateCoordinate actionCoordinates =
        roleOfCoordinate (coordinate stateCoordinate actionCoordinates)

namespace RunRoleCoordinateModel

variable {StateCoordinate : Type u} {ActionCoordinate : Type v}
variable {role : StateCoordinate -> List ActionCoordinate -> Bool}
variable {RunCoordinate : Type c}

theorem distinguished_roles_force_distinct_coordinates
    (model : RunRoleCoordinateModel role RunCoordinate)
    {stateCoordinate₁ stateCoordinate₂ : StateCoordinate}
    {actionCoordinates₁ actionCoordinates₂ : List ActionCoordinate}
    (h :
      role stateCoordinate₁ actionCoordinates₁ ≠
        role stateCoordinate₂ actionCoordinates₂) :
    model.coordinate stateCoordinate₁ actionCoordinates₁ ≠
      model.coordinate stateCoordinate₂ actionCoordinates₂ := by
  intro hcoord
  apply h
  calc
    role stateCoordinate₁ actionCoordinates₁ =
        model.roleOfCoordinate
          (model.coordinate stateCoordinate₁ actionCoordinates₁) :=
      model.preserves_role stateCoordinate₁ actionCoordinates₁
    _ =
        model.roleOfCoordinate
          (model.coordinate stateCoordinate₂ actionCoordinates₂) := by
      rw [hcoord]
    _ = role stateCoordinate₂ actionCoordinates₂ :=
      (model.preserves_role
        stateCoordinate₂ actionCoordinates₂).symm

end RunRoleCoordinateModel

/--
A coordinate model for a pair of Boolean run roles.

This is the first paired candidate surface for the burden/support direction:
the model may compress runs, but it must preserve the two observable candidate
roles together.
-/
structure RunRolePairCoordinateModel
    {StateCoordinate : Type u} {ActionCoordinate : Type v}
    (leftRole rightRole : StateCoordinate -> List ActionCoordinate -> Bool)
    (RunCoordinate : Type w) where
  coordinate : StateCoordinate -> List ActionCoordinate -> RunCoordinate
  rolePairOfCoordinate : RunCoordinate -> Bool × Bool
  preserves_rolePair :
    forall stateCoordinate actionCoordinates,
      (leftRole stateCoordinate actionCoordinates,
          rightRole stateCoordinate actionCoordinates) =
        rolePairOfCoordinate (coordinate stateCoordinate actionCoordinates)

namespace RunRolePairCoordinateModel

variable {StateCoordinate : Type u} {ActionCoordinate : Type v}
variable {leftRole rightRole :
  StateCoordinate -> List ActionCoordinate -> Bool}
variable {RunCoordinate : Type w}

theorem distinguished_rolePairs_force_distinct_coordinates
    (model :
      RunRolePairCoordinateModel leftRole rightRole RunCoordinate)
    {stateCoordinate₁ stateCoordinate₂ : StateCoordinate}
    {actionCoordinates₁ actionCoordinates₂ : List ActionCoordinate}
    (h :
      (leftRole stateCoordinate₁ actionCoordinates₁,
          rightRole stateCoordinate₁ actionCoordinates₁) ≠
        (leftRole stateCoordinate₂ actionCoordinates₂,
          rightRole stateCoordinate₂ actionCoordinates₂)) :
    model.coordinate stateCoordinate₁ actionCoordinates₁ ≠
      model.coordinate stateCoordinate₂ actionCoordinates₂ := by
  intro hcoord
  apply h
  calc
    (leftRole stateCoordinate₁ actionCoordinates₁,
        rightRole stateCoordinate₁ actionCoordinates₁) =
        model.rolePairOfCoordinate
          (model.coordinate stateCoordinate₁ actionCoordinates₁) :=
      model.preserves_rolePair stateCoordinate₁ actionCoordinates₁
    _ =
        model.rolePairOfCoordinate
          (model.coordinate stateCoordinate₂ actionCoordinates₂) := by
      rw [hcoord]
    _ =
        (leftRole stateCoordinate₂ actionCoordinates₂,
          rightRole stateCoordinate₂ actionCoordinates₂) :=
      (model.preserves_rolePair
        stateCoordinate₂ actionCoordinates₂).symm

end RunRolePairCoordinateModel

/--
A coordinate model for a pair of typed run roles.

This generalizes the Boolean candidate-pair model.  It is used only after a
separate promotion boundary explains how Boolean candidate events are read as
stronger typed roles.
-/
structure RunTypedRolePairCoordinateModel
    {StateCoordinate : Type u} {ActionCoordinate : Type v}
    {LeftRole : Type w} {RightRole : Type x}
    (leftRole : StateCoordinate -> List ActionCoordinate -> LeftRole)
    (rightRole : StateCoordinate -> List ActionCoordinate -> RightRole)
    (RunCoordinate : Type y) where
  coordinate : StateCoordinate -> List ActionCoordinate -> RunCoordinate
  rolePairOfCoordinate : RunCoordinate -> LeftRole × RightRole
  preserves_rolePair :
    forall stateCoordinate actionCoordinates,
      (leftRole stateCoordinate actionCoordinates,
          rightRole stateCoordinate actionCoordinates) =
        rolePairOfCoordinate (coordinate stateCoordinate actionCoordinates)

namespace RunTypedRolePairCoordinateModel

variable {StateCoordinate : Type u} {ActionCoordinate : Type v}
variable {LeftRole : Type w} {RightRole : Type x}
variable {leftRole : StateCoordinate -> List ActionCoordinate -> LeftRole}
variable {rightRole : StateCoordinate -> List ActionCoordinate -> RightRole}
variable {RunCoordinate : Type y}

theorem distinguished_rolePairs_force_distinct_coordinates
    (model :
      RunTypedRolePairCoordinateModel leftRole rightRole RunCoordinate)
    {stateCoordinate₁ stateCoordinate₂ : StateCoordinate}
    {actionCoordinates₁ actionCoordinates₂ : List ActionCoordinate}
    (h :
      (leftRole stateCoordinate₁ actionCoordinates₁,
          rightRole stateCoordinate₁ actionCoordinates₁) ≠
        (leftRole stateCoordinate₂ actionCoordinates₂,
          rightRole stateCoordinate₂ actionCoordinates₂)) :
    model.coordinate stateCoordinate₁ actionCoordinates₁ ≠
      model.coordinate stateCoordinate₂ actionCoordinates₂ := by
  intro hcoord
  apply h
  calc
    (leftRole stateCoordinate₁ actionCoordinates₁,
        rightRole stateCoordinate₁ actionCoordinates₁) =
        model.rolePairOfCoordinate
          (model.coordinate stateCoordinate₁ actionCoordinates₁) :=
      model.preserves_rolePair stateCoordinate₁ actionCoordinates₁
    _ =
        model.rolePairOfCoordinate
          (model.coordinate stateCoordinate₂ actionCoordinates₂) := by
      rw [hcoord]
    _ =
        (leftRole stateCoordinate₂ actionCoordinates₂,
          rightRole stateCoordinate₂ actionCoordinates₂) :=
      (model.preserves_rolePair
        stateCoordinate₂ actionCoordinates₂).symm

end RunTypedRolePairCoordinateModel

/--
A coordinate model for a two-component numeric run score.

This is the positive-side companion for total-scalar deletion tests: a
coordinate may compress runs only if it can still recover the two-component
score readout.
-/
structure RunComponentScoreCoordinateModel
    {StateCoordinate : Type u} {ActionCoordinate : Type v}
    (componentScore : StateCoordinate -> List ActionCoordinate -> Nat × Nat)
    (RunCoordinate : Type w) where
  coordinate : StateCoordinate -> List ActionCoordinate -> RunCoordinate
  componentOfCoordinate : RunCoordinate -> Nat × Nat
  preserves_componentScore :
    forall stateCoordinate actionCoordinates,
      componentScore stateCoordinate actionCoordinates =
        componentOfCoordinate (coordinate stateCoordinate actionCoordinates)

namespace RunComponentScoreCoordinateModel

variable {StateCoordinate : Type u} {ActionCoordinate : Type v}
variable {componentScore :
  StateCoordinate -> List ActionCoordinate -> Nat × Nat}
variable {RunCoordinate : Type w}

def identity
    (componentScore :
      StateCoordinate -> List ActionCoordinate -> Nat × Nat) :
    RunComponentScoreCoordinateModel componentScore (Nat × Nat) where
  coordinate := componentScore
  componentOfCoordinate := id
  preserves_componentScore := by
    intro _stateCoordinate _actionCoordinates
    rfl

theorem distinguished_componentScores_force_distinct_coordinates
    (model :
      RunComponentScoreCoordinateModel componentScore RunCoordinate)
    {stateCoordinate₁ stateCoordinate₂ : StateCoordinate}
    {actionCoordinates₁ actionCoordinates₂ : List ActionCoordinate}
    (h :
      componentScore stateCoordinate₁ actionCoordinates₁ ≠
        componentScore stateCoordinate₂ actionCoordinates₂) :
    model.coordinate stateCoordinate₁ actionCoordinates₁ ≠
      model.coordinate stateCoordinate₂ actionCoordinates₂ := by
  intro hcoord
  apply h
  calc
    componentScore stateCoordinate₁ actionCoordinates₁ =
        model.componentOfCoordinate
          (model.coordinate stateCoordinate₁ actionCoordinates₁) :=
      model.preserves_componentScore
        stateCoordinate₁ actionCoordinates₁
    _ =
        model.componentOfCoordinate
          (model.coordinate stateCoordinate₂ actionCoordinates₂) := by
      rw [hcoord]
    _ =
        componentScore stateCoordinate₂ actionCoordinates₂ :=
      (model.preserves_componentScore
        stateCoordinate₂ actionCoordinates₂).symm

end RunComponentScoreCoordinateModel

/--
Observation-derived Boolean burden/support candidate boundary.

This is not a derivation of the full `L/B` coordinate or qualified support
`M`.  It records the weakest current observation-derived candidate roles:

* burden-side candidate: a decoded run has a collapsed prefix;
* support-side candidate: a decoded run ends viable.

The four Boolean laws are explicit observational hypotheses.  With them, the
two candidate roles separate the adverse and restorative runs without
mentioning `BurdenRole` or `SupportRole`.
-/
structure ObservationDerivedBurdenSupportCandidateBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    (construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target) where
  adverseCollapsedPrefixActive :
    construction.package.observedCollapsedPrefixRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.restorativeContext)
        (construction.package.law.adverseTrace.map
          construction.package.decodedModel.actionCoordinate) =
      true
  adverseViableFinalInactive :
    construction.package.observedViableFinalRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.restorativeContext)
        (construction.package.law.adverseTrace.map
          construction.package.decodedModel.actionCoordinate) =
      false
  restorativeCollapsedPrefixInactive :
    construction.package.observedCollapsedPrefixRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.adverseContext)
        (construction.package.law.restorativeTrace.map
          construction.package.decodedModel.actionCoordinate) =
      false
  restorativeViableFinalActive :
    construction.package.observedViableFinalRole
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.adverseContext)
        (construction.package.law.restorativeTrace.map
          construction.package.decodedModel.actionCoordinate) =
      true

namespace ObservationDerivedBurdenSupportCandidateBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {RunCoordinate : Type q}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}

def adverseTraceStateCoordinate
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    DecodedStateCoordinate :=
  construction.package.decodedModel.stateCoordinate
    construction.package.law.restorativeContext

def adverseTraceActionCoordinates
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    List DecodedActionCoordinate :=
  construction.package.law.adverseTrace.map
    construction.package.decodedModel.actionCoordinate

def restorativeTraceStateCoordinate
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    DecodedStateCoordinate :=
  construction.package.decodedModel.stateCoordinate
    construction.package.law.adverseContext

def restorativeTraceActionCoordinates
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    List DecodedActionCoordinate :=
  construction.package.law.restorativeTrace.map
    construction.package.decodedModel.actionCoordinate

def burdenCandidate
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Bool :=
  construction.package.observedCollapsedPrefixRole

def supportCandidate
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Bool :=
  construction.package.observedViableFinalRole

def candidateRolePair
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Bool × Bool :=
  fun stateCoordinate actionCoordinates =>
    (candidate.burdenCandidate stateCoordinate actionCoordinates,
      candidate.supportCandidate stateCoordinate actionCoordinates)

theorem burdenCandidate_adverse_active
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.burdenCandidate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      true :=
  candidate.adverseCollapsedPrefixActive

theorem burdenCandidate_restorative_inactive
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.burdenCandidate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      false :=
  candidate.restorativeCollapsedPrefixInactive

theorem supportCandidate_adverse_inactive
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.supportCandidate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      false :=
  candidate.adverseViableFinalInactive

theorem supportCandidate_restorative_active
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.supportCandidate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      true :=
  candidate.restorativeViableFinalActive

theorem candidateRolePair_adverse
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.candidateRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      (true, false) := by
  rw [candidateRolePair, candidate.burdenCandidate_adverse_active,
    candidate.supportCandidate_adverse_inactive]

theorem candidateRolePair_restorative
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.candidateRolePair
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      (false, true) := by
  rw [candidateRolePair, candidate.burdenCandidate_restorative_inactive,
    candidate.supportCandidate_restorative_active]

theorem burdenCandidate_distinguishes_runs
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.burdenCandidate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      candidate.burdenCandidate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  rw [candidate.burdenCandidate_adverse_active,
    candidate.burdenCandidate_restorative_inactive]
  decide

theorem supportCandidate_distinguishes_runs
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.supportCandidate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      candidate.supportCandidate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  rw [candidate.supportCandidate_adverse_inactive,
    candidate.supportCandidate_restorative_active]
  decide

theorem candidateRolePair_distinguishes_runs
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction) :
    candidate.candidateRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      candidate.candidateRolePair
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  rw [candidate.candidateRolePair_adverse,
    candidate.candidateRolePair_restorative]
  decide

theorem burden_candidate_coordinate_must_distinguish
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    (model :
      RunRoleCoordinateModel candidate.burdenCandidate RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  model.distinguished_roles_force_distinct_coordinates
    candidate.burdenCandidate_distinguishes_runs

theorem support_candidate_coordinate_must_distinguish
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    (model :
      RunRoleCoordinateModel candidate.supportCandidate RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  model.distinguished_roles_force_distinct_coordinates
    candidate.supportCandidate_distinguishes_runs

theorem candidate_pair_coordinate_must_distinguish
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    (model :
      RunRolePairCoordinateModel
        candidate.burdenCandidate candidate.supportCandidate RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  model.distinguished_rolePairs_force_distinct_coordinates
    candidate.candidateRolePair_distinguishes_runs

end ObservationDerivedBurdenSupportCandidateBoundary

/--
Promotion boundary from Boolean candidate roles to stronger typed roles.

This is a certificate boundary, not a derivation of `L/B` or `M`: the maps
from Boolean candidate events to typed roles are supplied.  The important
non-collapse requirement is explicit: the promoted image of the adverse
candidate pair must differ from the promoted image of the restorative candidate
pair.
-/
structure ObservationDerivedPromotedRoleBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    (PromotedBurdenRole : Type q) (PromotedSupportRole : Type a) where
  promoteBurden : Bool -> PromotedBurdenRole
  promoteSupport : Bool -> PromotedSupportRole
  promoted_adverse_ne_restorative :
    (promoteBurden true, promoteSupport false) ≠
      (promoteBurden false, promoteSupport true)

namespace ObservationDerivedPromotedRoleBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {RunCoordinate : Type c}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}

def promotedBurden
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    DecodedStateCoordinate -> List DecodedActionCoordinate ->
      PromotedBurdenRole :=
  fun stateCoordinate actionCoordinates =>
    boundary.promoteBurden
      (candidate.burdenCandidate stateCoordinate actionCoordinates)

def promotedSupport
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    DecodedStateCoordinate -> List DecodedActionCoordinate ->
      PromotedSupportRole :=
  fun stateCoordinate actionCoordinates =>
    boundary.promoteSupport
      (candidate.supportCandidate stateCoordinate actionCoordinates)

def promotedRolePair
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    DecodedStateCoordinate -> List DecodedActionCoordinate ->
      PromotedBurdenRole × PromotedSupportRole :=
  fun stateCoordinate actionCoordinates =>
    (boundary.promotedBurden stateCoordinate actionCoordinates,
      boundary.promotedSupport stateCoordinate actionCoordinates)

theorem promotedRolePair_adverse
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      (boundary.promoteBurden true, boundary.promoteSupport false) := by
  rw [promotedRolePair, promotedBurden, promotedSupport,
    candidate.burdenCandidate_adverse_active,
    candidate.supportCandidate_adverse_inactive]

theorem promotedRolePair_restorative
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedRolePair
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      (boundary.promoteBurden false, boundary.promoteSupport true) := by
  rw [promotedRolePair, promotedBurden, promotedSupport,
    candidate.burdenCandidate_restorative_inactive,
    candidate.supportCandidate_restorative_active]

theorem promotedRolePair_distinguishes_runs
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      boundary.promotedRolePair
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  rw [boundary.promotedRolePair_adverse,
    boundary.promotedRolePair_restorative]
  exact boundary.promoted_adverse_ne_restorative

theorem promoted_pair_coordinate_must_distinguish
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole)
    (model :
      RunTypedRolePairCoordinateModel
        boundary.promotedBurden boundary.promotedSupport RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  model.distinguished_rolePairs_force_distinct_coordinates
    boundary.promotedRolePair_distinguishes_runs

def promotedRoleInputs
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    ChannelRoleBridgeInputs
      construction.package PromotedBurdenRole PromotedSupportRole where
  burdenOfRun := boundary.promotedBurden
  supportOfRun := boundary.promotedSupport
  adverseBurden := boundary.promoteBurden true
  restorativeSupport := boundary.promoteSupport true
  adverseTrace_burden := by
    change
      boundary.promoteBurden
          (candidate.burdenCandidate
            (construction.package.decodedModel.stateCoordinate
              construction.package.law.restorativeContext)
            (construction.package.law.adverseTrace.map
              construction.package.decodedModel.actionCoordinate)) =
        boundary.promoteBurden true
    simpa [
      ObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate,
      ObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates
    ] using
      congrArg boundary.promoteBurden
        candidate.burdenCandidate_adverse_active
  restorativeTrace_support := by
    change
      boundary.promoteSupport
          (candidate.supportCandidate
            (construction.package.decodedModel.stateCoordinate
              construction.package.law.adverseContext)
            (construction.package.law.restorativeTrace.map
              construction.package.decodedModel.actionCoordinate)) =
        boundary.promoteSupport true
    simpa [
      ObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate,
      ObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates
    ] using
      congrArg boundary.promoteSupport
        candidate.supportCandidate_restorative_active

def promotedBridgeBoundary
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    ChannelRoleBridgeBoundary
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      PromotedBurdenRole PromotedSupportRole where
  package := construction.package
  roleInputs := boundary.promotedRoleInputs

def promotedRoleSeparationCandidate
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    PrefixSensitiveRoleSeparationCandidate
      P CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      PromotedBurdenRole PromotedSupportRole where
  bridge := boundary.promotedBridgeBoundary

theorem promotedBridge_adverseTrace_burden
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedRoleInputs.burdenOfRun
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.restorativeContext)
        (construction.package.law.adverseTrace.map
          construction.package.decodedModel.actionCoordinate) =
      boundary.promotedRoleInputs.adverseBurden :=
  boundary.promotedRoleInputs.adverseTrace_burden

theorem promotedBridge_restorativeTrace_support
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedRoleInputs.supportOfRun
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.adverseContext)
        (construction.package.law.restorativeTrace.map
          construction.package.decodedModel.actionCoordinate) =
      boundary.promotedRoleInputs.restorativeSupport :=
  boundary.promotedRoleInputs.restorativeTrace_support

theorem promotedBridge_no_collapsed_traceLog_model
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (construction.package.collapsedStateCoordinate s)
                (actions.map construction.package.collapsedActionCoordinate)) :=
  boundary.promotedRoleSeparationCandidate.no_collapsed_traceLog_model

/--
Semantic bridge for observation-derived promoted roles.

The promoted role candidate is constructed from observed Boolean events plus
supplied promotion maps.  Target semantics and the nontrivial readout are
still supplied by the observation-derived construction boundary.
-/
def promotedSemanticBridge
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    PrefixSensitiveSemanticBridge
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      PromotedBurdenRole PromotedSupportRole Target where
  candidate := boundary.promotedRoleSeparationCandidate
  sourceSemantics := construction.sourceSemantics
  targetSemantics := construction.targetSemantics
  observationMap := construction.observationMap
  targetMap := construction.targetMap
  sourceNontrivial := construction.sourceNontrivial

theorem promotedSemantic_no_collapsed_traceLog_model
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (construction.package.collapsedStateCoordinate s)
                (actions.map construction.package.collapsedActionCoordinate)) :=
  boundary.promotedSemanticBridge.no_collapsed_traceLog_model

theorem promotedSemantic_viableRegion_nonempty
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.promotedSemanticBridge.stateRealizationViability.viableRegion.Nonempty :=
  boundary.promotedSemanticBridge.viableRegion_nonempty

theorem promotedSemantic_viable_implies_maintained_target
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole)
    (k : boundary.promotedSemanticBridge.stateRealizationViability.K)
    (hk :
      k ∈ boundary.promotedSemanticBridge.stateRealizationViability.viableRegion) :
    construction.sourceSemantics.maintains
      (boundary.promotedSemanticBridge.stateRealizationViability.carrier k)
      construction.sourceSemantics.maintainedTarget :=
  boundary.promotedSemanticBridge.viable_implies_maintained_target k hk

end ObservationDerivedPromotedRoleBoundary

/--
Factorization boundary for observation-derived promoted roles.

This packages the promoted semantic bridge with an explicit log-accounting
certificate.  It does not derive the full additive `L/B` coordinate or
qualified support `M`; the promoted roles and the accounting certificate remain
visible inputs.
-/
structure ObservationDerivedPromotedFactorizationBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  logAccounting :
    PrefixSensitiveLogAccountingBridge boundary.promotedSemanticBridge

namespace ObservationDerivedPromotedFactorizationBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}

def toCanonicalFactorization
    (surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    PrefixSensitiveCanonicalFactorizationBoundary
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      PromotedBurdenRole PromotedSupportRole Target where
  semanticBridge := boundary.promotedSemanticBridge
  logAccounting := surface.logAccounting

theorem no_collapsed_traceLog_model
    (surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    ¬ Exists
      (fun traceLogOfCoordinates :
        CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
          List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfCoordinates
                (construction.package.collapsedStateCoordinate s)
                (actions.map construction.package.collapsedActionCoordinate)) :=
  surface.toCanonicalFactorization.no_collapsed_traceLog_model

theorem viableRegion_nonempty
    (surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    surface.toCanonicalFactorization
      |>.stateRealizationViability.viableRegion.Nonempty :=
  surface.toCanonicalFactorization.viableRegion_nonempty

theorem promoted_adverseTrace_burden
    (_surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    boundary.promotedRoleInputs.burdenOfRun
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.restorativeContext)
        (construction.package.law.adverseTrace.map
          construction.package.decodedModel.actionCoordinate) =
      boundary.promotedRoleInputs.adverseBurden :=
  boundary.promotedBridge_adverseTrace_burden

theorem promoted_restorativeTrace_support
    (_surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    boundary.promotedRoleInputs.supportOfRun
        (construction.package.decodedModel.stateCoordinate
          construction.package.law.adverseContext)
        (construction.package.law.restorativeTrace.map
          construction.package.decodedModel.actionCoordinate) =
      boundary.promotedRoleInputs.restorativeSupport :=
  boundary.promotedBridge_restorativeTrace_support

theorem burden_loss_has_log_form
    (surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        surface.logAccounting.burdenLossValue
            (boundary.promotedRoleInputs.burdenOfRun
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (surface.logAccounting.ratioOfRun
              stateCoordinate actionCoordinates) :=
  surface.toCanonicalFactorization.burden_loss_has_log_form

theorem adverseTrace_burden_loss_has_log_form
    (surface :
      ObservationDerivedPromotedFactorizationBoundary boundary) :
    ∃ k : ℝ, 0 ≤ k ∧
      surface.logAccounting.burdenLossValue
          (boundary.promotedRoleInputs.burdenOfRun
            (construction.package.decodedModel.stateCoordinate
              construction.package.law.restorativeContext)
            (construction.package.law.adverseTrace.map
              construction.package.decodedModel.actionCoordinate)) =
        -k * Real.log
          (surface.logAccounting.ratioOfRun
            (construction.package.decodedModel.stateCoordinate
              construction.package.law.restorativeContext)
            (construction.package.law.adverseTrace.map
              construction.package.decodedModel.actionCoordinate)) :=
  surface.toCanonicalFactorization.adverseTrace_burden_loss_has_log_form

end ObservationDerivedPromotedFactorizationBoundary

/--
Component-wise promotion boundary for the Boolean candidate roles.

This is stronger and more auditable than supplying a single promoted-pair
non-collapse certificate.  It says each promoted role map keeps its relevant
Boolean distinction alive.  The full `L/B` and `M` roles are still not derived;
the maps remain supplied promotion data.
-/
structure ObservationDerivedComponentwisePromotionBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    (PromotedBurdenRole : Type q) (PromotedSupportRole : Type a) where
  promoteBurden : Bool -> PromotedBurdenRole
  promoteSupport : Bool -> PromotedSupportRole
  burden_true_ne_false : promoteBurden true ≠ promoteBurden false
  support_false_ne_true : promoteSupport false ≠ promoteSupport true

namespace ObservationDerivedComponentwisePromotionBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {RunCoordinate : Type c}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}

theorem promoted_adverse_ne_restorative
    (boundary :
      ObservationDerivedComponentwisePromotionBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    (boundary.promoteBurden true, boundary.promoteSupport false) ≠
      (boundary.promoteBurden false, boundary.promoteSupport true) := by
  intro h
  exact boundary.burden_true_ne_false (congrArg Prod.fst h)

def toPromotedRoleBoundary
    (boundary :
      ObservationDerivedComponentwisePromotionBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    ObservationDerivedPromotedRoleBoundary
      candidate PromotedBurdenRole PromotedSupportRole where
  promoteBurden := boundary.promoteBurden
  promoteSupport := boundary.promoteSupport
  promoted_adverse_ne_restorative :=
    boundary.promoted_adverse_ne_restorative

theorem promotedRolePair_distinguishes_runs
    (boundary :
      ObservationDerivedComponentwisePromotionBoundary
        candidate PromotedBurdenRole PromotedSupportRole) :
    boundary.toPromotedRoleBoundary.promotedRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      boundary.toPromotedRoleBoundary.promotedRolePair
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  boundary.toPromotedRoleBoundary.promotedRolePair_distinguishes_runs

theorem promoted_pair_coordinate_must_distinguish
    (boundary :
      ObservationDerivedComponentwisePromotionBoundary
        candidate PromotedBurdenRole PromotedSupportRole)
    (model :
      RunTypedRolePairCoordinateModel
        boundary.toPromotedRoleBoundary.promotedBurden
        boundary.toPromotedRoleBoundary.promotedSupport
        RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  boundary.toPromotedRoleBoundary.promoted_pair_coordinate_must_distinguish
    model

end ObservationDerivedComponentwisePromotionBoundary

/--
Constant promotion erases the candidate distinction.

This is a hypothesis-deletion witness for the promotion layer: without a
non-collapse law on the promotion maps, the Boolean candidate split can be
mapped to a single promoted pair.
-/
def constantPromotedRolePair
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    (_candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (burdenValue : PromotedBurdenRole)
    (supportValue : PromotedSupportRole) :
    DecodedStateCoordinate -> List DecodedActionCoordinate ->
      PromotedBurdenRole × PromotedSupportRole :=
  fun _stateCoordinate _actionCoordinates => (burdenValue, supportValue)

theorem constantPromotedRolePair_identifies_adverse_restorative
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    (candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction)
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (burdenValue : PromotedBurdenRole)
    (supportValue : PromotedSupportRole) :
    constantPromotedRolePair candidate burdenValue supportValue
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      constantPromotedRolePair candidate burdenValue supportValue
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  rfl

/--
Additive score boundary for promoted burden/support candidates.

This is a deletion-test surface for the next G1c step.  It supplies numeric
component scores for the promoted roles and records the key situation where
the adverse and restorative runs have the same total score but different
two-component scores.  It does not derive full additive `L/B` or `M`.
-/
structure PromotedRoleAdditiveScoreBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_separates_adverse_restorative :
    burdenScore (boundary.promoteBurden true) ≠
      burdenScore (boundary.promoteBurden false)
  supportScore_separates_adverse_restorative :
    supportScore (boundary.promoteSupport false) ≠
      supportScore (boundary.promoteSupport true)
  adverse_total_eq_restorative :
    burdenScore (boundary.promoteBurden true) +
        supportScore (boundary.promoteSupport false) =
      burdenScore (boundary.promoteBurden false) +
        supportScore (boundary.promoteSupport true)

namespace PromotedRoleAdditiveScoreBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}

def burdenScoreOfRun
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat :=
  fun stateCoordinate actionCoordinates =>
    score.burdenScore
      (boundary.promotedBurden stateCoordinate actionCoordinates)

def supportScoreOfRun
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat :=
  fun stateCoordinate actionCoordinates =>
    score.supportScore
      (boundary.promotedSupport stateCoordinate actionCoordinates)

def componentScoreOfRun
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat × Nat :=
  fun stateCoordinate actionCoordinates =>
    (score.burdenScoreOfRun stateCoordinate actionCoordinates,
      score.supportScoreOfRun stateCoordinate actionCoordinates)

def totalScoreOfRun
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat :=
  fun stateCoordinate actionCoordinates =>
    score.burdenScoreOfRun stateCoordinate actionCoordinates +
      score.supportScoreOfRun stateCoordinate actionCoordinates

theorem adverseTrace_burdenScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.burdenScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      score.burdenScore (boundary.promoteBurden true) := by
  rw [burdenScoreOfRun,
    ObservationDerivedPromotedRoleBoundary.promotedBurden,
    candidate.burdenCandidate_adverse_active]

theorem adverseTrace_supportScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.supportScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      score.supportScore (boundary.promoteSupport false) := by
  rw [supportScoreOfRun,
    ObservationDerivedPromotedRoleBoundary.promotedSupport,
    candidate.supportCandidate_adverse_inactive]

theorem restorativeTrace_burdenScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.burdenScoreOfRun
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      score.burdenScore (boundary.promoteBurden false) := by
  rw [burdenScoreOfRun,
    ObservationDerivedPromotedRoleBoundary.promotedBurden,
    candidate.burdenCandidate_restorative_inactive]

theorem restorativeTrace_supportScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.supportScoreOfRun
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      score.supportScore (boundary.promoteSupport true) := by
  rw [supportScoreOfRun,
    ObservationDerivedPromotedRoleBoundary.promotedSupport,
    candidate.supportCandidate_restorative_active]

theorem adverseTrace_componentScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.componentScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      (score.burdenScore (boundary.promoteBurden true),
        score.supportScore (boundary.promoteSupport false)) := by
  rw [componentScoreOfRun, score.adverseTrace_burdenScore,
    score.adverseTrace_supportScore]

theorem restorativeTrace_componentScore
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.componentScoreOfRun
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      (score.burdenScore (boundary.promoteBurden false),
        score.supportScore (boundary.promoteSupport true)) := by
  rw [componentScoreOfRun, score.restorativeTrace_burdenScore,
    score.restorativeTrace_supportScore]

theorem adverseTrace_totalScore_eq_restorativeTrace
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.totalScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      score.totalScoreOfRun
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  simpa [totalScoreOfRun, score.adverseTrace_burdenScore,
    score.adverseTrace_supportScore, score.restorativeTrace_burdenScore,
    score.restorativeTrace_supportScore] using
    score.adverse_total_eq_restorative

theorem componentScore_distinguishes_runs
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    score.componentScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      score.componentScoreOfRun
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  rw [score.adverseTrace_componentScore,
    score.restorativeTrace_componentScore]
  intro h
  exact score.burdenScore_separates_adverse_restorative
    (congrArg Prod.fst h)

theorem no_totalScore_componentScore_model
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          score.componentScoreOfRun stateCoordinate actionCoordinates =
            componentOfTotal
              (score.totalScoreOfRun stateCoordinate actionCoordinates)) := by
  rintro ⟨componentOfTotal, hpreserves⟩
  apply score.componentScore_distinguishes_runs
  calc
    score.componentScoreOfRun
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
        componentOfTotal
          (score.totalScoreOfRun
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates) :=
      hpreserves
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates
    _ =
        componentOfTotal
          (score.totalScoreOfRun
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates) := by
      rw [score.adverseTrace_totalScore_eq_restorativeTrace]
    _ =
        score.componentScoreOfRun
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates :=
      (hpreserves
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates).symm

def componentScoreCoordinateModel
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    RunComponentScoreCoordinateModel score.componentScoreOfRun (Nat × Nat) :=
  RunComponentScoreCoordinateModel.identity score.componentScoreOfRun

theorem componentScore_coordinate_must_distinguish
    {RunCoordinate : Type c}
    (score : PromotedRoleAdditiveScoreBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel score.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  model.distinguished_componentScores_force_distinct_coordinates
    score.componentScore_distinguishes_runs

theorem no_totalScore_promotedRolePair_model
    (score : PromotedRoleAdditiveScoreBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (score.totalScoreOfRun stateCoordinate actionCoordinates)) := by
  rintro ⟨rolePairOfTotal, hpreserves⟩
  apply boundary.promotedRolePair_distinguishes_runs
  calc
    boundary.promotedRolePair
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
        rolePairOfTotal
          (score.totalScoreOfRun
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates) :=
      hpreserves
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates
    _ =
        rolePairOfTotal
          (score.totalScoreOfRun
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates) := by
      rw [score.adverseTrace_totalScore_eq_restorativeTrace]
    _ =
        boundary.promotedRolePair
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates :=
      (hpreserves
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates).symm

end PromotedRoleAdditiveScoreBoundary

/--
Indicator score laws for promoted roles.

This strengthens the previous additive score boundary by requiring that the
promoted burden/support roles read the underlying Boolean candidate events as
standard inactive/active scores `0` and `1`.  The scoring functions are still
explicit inputs; the full `L/B` and `M` coordinates are not derived here.
-/
structure PromotedRoleIndicatorScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_active : burdenScore (boundary.promoteBurden true) = 1
  burdenScore_inactive : burdenScore (boundary.promoteBurden false) = 0
  supportScore_active : supportScore (boundary.promoteSupport true) = 1
  supportScore_inactive : supportScore (boundary.promoteSupport false) = 0

namespace PromotedRoleIndicatorScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def toAdditiveScoreBoundary
    (law : PromotedRoleIndicatorScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary where
  burdenScore := law.burdenScore
  supportScore := law.supportScore
  burdenScore_separates_adverse_restorative := by
    rw [law.burdenScore_active, law.burdenScore_inactive]
    decide
  supportScore_separates_adverse_restorative := by
    rw [law.supportScore_inactive, law.supportScore_active]
    decide
  adverse_total_eq_restorative := by
    rw [law.burdenScore_active, law.supportScore_inactive,
      law.burdenScore_inactive, law.supportScore_active]

theorem no_totalScore_componentScore_model
    (law : PromotedRoleIndicatorScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          law.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toAdditiveScoreBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (law : PromotedRoleIndicatorScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toAdditiveScoreBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (law : PromotedRoleIndicatorScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        law.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  law.toAdditiveScoreBoundary.componentScore_coordinate_must_distinguish model

end PromotedRoleIndicatorScoreLawBoundary

/--
Common-unit score laws for promoted roles.

This weakens the exact indicator law: active burden/support candidates need
not be read as `1`, only as the same nonzero unit, while inactive candidates
are read as `0`.  The resulting additive boundary still has the same total
score on the adverse/restorative runs and still rules out total-only
preservation of the two-component or role-pair readouts.
-/
structure PromotedRoleCommonUnitScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  scoreUnit : Nat
  scoreUnit_ne_zero : scoreUnit ≠ 0
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_active : burdenScore (boundary.promoteBurden true) = scoreUnit
  burdenScore_inactive : burdenScore (boundary.promoteBurden false) = 0
  supportScore_active : supportScore (boundary.promoteSupport true) = scoreUnit
  supportScore_inactive : supportScore (boundary.promoteSupport false) = 0

namespace PromotedRoleCommonUnitScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def toAdditiveScoreBoundary
    (law : PromotedRoleCommonUnitScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary where
  burdenScore := law.burdenScore
  supportScore := law.supportScore
  burdenScore_separates_adverse_restorative := by
    rw [law.burdenScore_active, law.burdenScore_inactive]
    exact law.scoreUnit_ne_zero
  supportScore_separates_adverse_restorative := by
    rw [law.supportScore_inactive, law.supportScore_active]
    exact Ne.symm law.scoreUnit_ne_zero
  adverse_total_eq_restorative := by
    rw [law.burdenScore_active, law.supportScore_inactive,
      law.burdenScore_inactive, law.supportScore_active]
    calc
      law.scoreUnit + 0 = law.scoreUnit := Nat.add_zero law.scoreUnit
      _ = 0 + law.scoreUnit := (Nat.zero_add law.scoreUnit).symm

theorem no_totalScore_componentScore_model
    (law : PromotedRoleCommonUnitScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          law.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toAdditiveScoreBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (law : PromotedRoleCommonUnitScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toAdditiveScoreBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (law : PromotedRoleCommonUnitScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        law.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  law.toAdditiveScoreBoundary.componentScore_coordinate_must_distinguish model

end PromotedRoleCommonUnitScoreLawBoundary

/--
Balanced-zero score laws for promoted roles.

This weakens the common-unit boundary one step further.  Instead of supplying
the shared active score as a named unit, the source law only says that inactive
promoted roles read as zero, the active burden/support scores agree, and the
active score is nonzero.  The common unit is then recovered from the active
burden score.
-/
structure PromotedRoleBalancedZeroScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_inactive : burdenScore (boundary.promoteBurden false) = 0
  supportScore_inactive : supportScore (boundary.promoteSupport false) = 0
  active_scores_match :
    burdenScore (boundary.promoteBurden true) =
      supportScore (boundary.promoteSupport true)
  active_score_ne_zero : burdenScore (boundary.promoteBurden true) ≠ 0

namespace PromotedRoleBalancedZeroScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def toCommonUnitScoreLawBoundary
    (law : PromotedRoleBalancedZeroScoreLawBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary where
  scoreUnit := law.burdenScore (boundary.promoteBurden true)
  scoreUnit_ne_zero := law.active_score_ne_zero
  burdenScore := law.burdenScore
  supportScore := law.supportScore
  burdenScore_active := rfl
  burdenScore_inactive := law.burdenScore_inactive
  supportScore_active := law.active_scores_match.symm
  supportScore_inactive := law.supportScore_inactive

def toAdditiveScoreBoundary
    (law : PromotedRoleBalancedZeroScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  law.toCommonUnitScoreLawBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (law : PromotedRoleBalancedZeroScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          law.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toCommonUnitScoreLawBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (law : PromotedRoleBalancedZeroScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (law.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  law.toCommonUnitScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (law : PromotedRoleBalancedZeroScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        law.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  law.toCommonUnitScoreLawBoundary.componentScore_coordinate_must_distinguish model

end PromotedRoleBalancedZeroScoreLawBoundary

/--
Observable score probes for promoted role scoring.

This moves the balanced-zero laws one layer closer to observations: the
zero/matching/nonzero facts are stated for run-level probe scores, and the
role scores are required to read those probe scores on promoted runs.  The
probe-score compatibility laws are still explicit inputs, so this is not yet a
derivation of the numeric `L/B` and `M` accounting laws from observations
alone.
-/
structure PromotedRoleObservableScoreProbeBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_reads_probe :
    forall stateCoordinate actionCoordinates,
      burdenScore (boundary.promotedBurden stateCoordinate actionCoordinates) =
        burdenProbeScore stateCoordinate actionCoordinates
  supportScore_reads_probe :
    forall stateCoordinate actionCoordinates,
      supportScore (boundary.promotedSupport stateCoordinate actionCoordinates) =
        supportProbeScore stateCoordinate actionCoordinates
  burdenInactive_probe_zero :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates = 0
  supportInactive_probe_zero :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates = 0
  active_probe_scores_match :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates
  active_probe_ne_zero :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠ 0

namespace PromotedRoleObservableScoreProbeBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

theorem burdenScore_inactive_from_probe
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden false) = 0 := by
  have hread :=
    source.burdenScore_reads_probe
      candidate.restorativeTraceStateCoordinate
      candidate.restorativeTraceActionCoordinates
  rw [ObservationDerivedPromotedRoleBoundary.promotedBurden,
    candidate.burdenCandidate_restorative_inactive] at hread
  exact hread.trans source.burdenInactive_probe_zero

theorem supportScore_inactive_from_probe
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    source.supportScore (boundary.promoteSupport false) = 0 := by
  have hread :=
    source.supportScore_reads_probe
      candidate.adverseTraceStateCoordinate
      candidate.adverseTraceActionCoordinates
  rw [ObservationDerivedPromotedRoleBoundary.promotedSupport,
    candidate.supportCandidate_adverse_inactive] at hread
  exact hread.trans source.supportInactive_probe_zero

theorem active_scores_match_from_probe
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden true) =
      source.supportScore (boundary.promoteSupport true) := by
  have hburden :=
    source.burdenScore_reads_probe
      candidate.adverseTraceStateCoordinate
      candidate.adverseTraceActionCoordinates
  rw [ObservationDerivedPromotedRoleBoundary.promotedBurden,
    candidate.burdenCandidate_adverse_active] at hburden
  have hsupport :=
    source.supportScore_reads_probe
      candidate.restorativeTraceStateCoordinate
      candidate.restorativeTraceActionCoordinates
  rw [ObservationDerivedPromotedRoleBoundary.promotedSupport,
    candidate.supportCandidate_restorative_active] at hsupport
  calc
    source.burdenScore (boundary.promoteBurden true) =
        source.burdenProbeScore
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates :=
      hburden
    _ =
        source.supportProbeScore
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates :=
      source.active_probe_scores_match
    _ = source.supportScore (boundary.promoteSupport true) :=
      hsupport.symm

theorem active_score_ne_zero_from_probe
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden true) ≠ 0 := by
  have hread :=
    source.burdenScore_reads_probe
      candidate.adverseTraceStateCoordinate
      candidate.adverseTraceActionCoordinates
  rw [ObservationDerivedPromotedRoleBoundary.promotedBurden,
    candidate.burdenCandidate_adverse_active] at hread
  intro hzero
  exact source.active_probe_ne_zero (hread.symm.trans hzero)

def toBalancedZeroScoreLawBoundary
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary where
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_inactive := source.burdenScore_inactive_from_probe
  supportScore_inactive := source.supportScore_inactive_from_probe
  active_scores_match := source.active_scores_match_from_probe
  active_score_ne_zero := source.active_score_ne_zero_from_probe

def toCommonUnitScoreLawBoundary
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toBalancedZeroScoreLawBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toBalancedZeroScoreLawBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toBalancedZeroScoreLawBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRoleObservableScoreProbeBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toBalancedZeroScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRoleObservableScoreProbeBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toBalancedZeroScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRoleObservableScoreProbeBoundary

/--
Decisive-trace score probes for promoted role scoring.

This weakens the observable score-probe boundary: the role scores do not need
to read the run-level probes on every decoded run.  To recover the current
balanced-zero score law, it is enough to require probe compatibility on the
four decisive traces used by the adverse/restorative split.  This is still a
guarded source boundary, not a derivation of full `L/B` and `M` accounting.
-/
structure PromotedRoleDecisiveTraceScoreProbeBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_adverse_reads_probe :
    burdenScore (boundary.promoteBurden true) =
      burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates
  burdenScore_restorative_reads_probe :
    burdenScore (boundary.promoteBurden false) =
      burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates
  supportScore_adverse_reads_probe :
    supportScore (boundary.promoteSupport false) =
      supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates
  supportScore_restorative_reads_probe :
    supportScore (boundary.promoteSupport true) =
      supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates
  burdenInactive_probe_zero :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates = 0
  supportInactive_probe_zero :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates = 0
  active_probe_scores_match :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates
  active_probe_ne_zero :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠ 0

namespace PromotedRoleDecisiveTraceScoreProbeBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

theorem burdenScore_inactive_from_decisive_probe
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden false) = 0 :=
  source.burdenScore_restorative_reads_probe.trans
    source.burdenInactive_probe_zero

theorem supportScore_inactive_from_decisive_probe
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    source.supportScore (boundary.promoteSupport false) = 0 :=
  source.supportScore_adverse_reads_probe.trans
    source.supportInactive_probe_zero

theorem active_scores_match_from_decisive_probe
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden true) =
      source.supportScore (boundary.promoteSupport true) := by
  calc
    source.burdenScore (boundary.promoteBurden true) =
        source.burdenProbeScore
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates :=
      source.burdenScore_adverse_reads_probe
    _ =
        source.supportProbeScore
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates :=
      source.active_probe_scores_match
    _ = source.supportScore (boundary.promoteSupport true) :=
      source.supportScore_restorative_reads_probe.symm

theorem active_score_ne_zero_from_decisive_probe
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    source.burdenScore (boundary.promoteBurden true) ≠ 0 := by
  intro hzero
  exact source.active_probe_ne_zero
    (source.burdenScore_adverse_reads_probe.symm.trans hzero)

def toBalancedZeroScoreLawBoundary
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary where
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_inactive := source.burdenScore_inactive_from_decisive_probe
  supportScore_inactive := source.supportScore_inactive_from_decisive_probe
  active_scores_match := source.active_scores_match_from_decisive_probe
  active_score_ne_zero := source.active_score_ne_zero_from_decisive_probe

def toCommonUnitScoreLawBoundary
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toBalancedZeroScoreLawBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toBalancedZeroScoreLawBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toBalancedZeroScoreLawBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toBalancedZeroScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRoleDecisiveTraceScoreProbeBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toBalancedZeroScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRoleDecisiveTraceScoreProbeBoundary

/--
Prefix-log score readouts for the decisive trace probes.

This is one layer weaker than direct role-score/probe compatibility.  The
source laws say that, on the decisive traces, both the promoted role score and
the run-level probe score read the same score from the decoded prefix log.
The trace-score laws themselves remain explicit inputs; the point is to make
the remaining compatibility surface prefix-log based and visible.
-/
structure PromotedRoleTraceLocalScoreReadoutBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenTraceScore : List (Observation × BoundaryStatus) -> Nat
  supportTraceScore : List (Observation × BoundaryStatus) -> Nat
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_adverse_reads_trace :
    burdenScore (boundary.promoteBurden true) =
      burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates)
  burdenProbe_adverse_reads_trace :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates)
  burdenScore_restorative_reads_trace :
    burdenScore (boundary.promoteBurden false) =
      burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates)
  burdenProbe_restorative_reads_trace :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates)
  supportScore_adverse_reads_trace :
    supportScore (boundary.promoteSupport false) =
      supportTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates)
  supportProbe_adverse_reads_trace :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      supportTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates)
  supportScore_restorative_reads_trace :
    supportScore (boundary.promoteSupport true) =
      supportTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates)
  supportProbe_restorative_reads_trace :
    supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      supportTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates)
  burdenInactive_trace_zero :
    burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = 0
  supportInactive_trace_zero :
    supportTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = 0
  active_trace_scores_match :
    burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) =
      supportTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates)
  active_trace_score_ne_zero :
    burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) ≠ 0

namespace PromotedRoleTraceLocalScoreReadoutBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

theorem burdenScore_adverse_reads_probe
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.burdenScore (boundary.promoteBurden true) =
      source.burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates :=
  source.burdenScore_adverse_reads_trace.trans
    source.burdenProbe_adverse_reads_trace.symm

theorem burdenScore_restorative_reads_probe
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.burdenScore (boundary.promoteBurden false) =
      source.burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.burdenScore_restorative_reads_trace.trans
    source.burdenProbe_restorative_reads_trace.symm

theorem supportScore_adverse_reads_probe
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.supportScore (boundary.promoteSupport false) =
      source.supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates :=
  source.supportScore_adverse_reads_trace.trans
    source.supportProbe_adverse_reads_trace.symm

theorem supportScore_restorative_reads_probe
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.supportScore (boundary.promoteSupport true) =
      source.supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.supportScore_restorative_reads_trace.trans
    source.supportProbe_restorative_reads_trace.symm

theorem burdenInactive_probe_zero
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates = 0 :=
  source.burdenProbe_restorative_reads_trace.trans
    source.burdenInactive_trace_zero

theorem supportInactive_probe_zero
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates = 0 :=
  source.supportProbe_adverse_reads_trace.trans
    source.supportInactive_trace_zero

theorem active_probe_scores_match
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      source.supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates := by
  calc
    source.burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
        source.burdenTraceScore
          (construction.package.decodedTraceLog
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates) :=
      source.burdenProbe_adverse_reads_trace
    _ =
        source.supportTraceScore
          (construction.package.decodedTraceLog
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates) :=
      source.active_trace_scores_match
    _ =
        source.supportProbeScore
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates :=
      source.supportProbe_restorative_reads_trace.symm

theorem active_probe_ne_zero
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    source.burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠ 0 := by
  intro hzero
  exact source.active_trace_score_ne_zero
    (source.burdenProbe_adverse_reads_trace.symm.trans hzero)

def toDecisiveTraceScoreProbeBoundary
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    PromotedRoleDecisiveTraceScoreProbeBoundary boundary where
  burdenProbeScore := source.burdenProbeScore
  supportProbeScore := source.supportProbeScore
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_adverse_reads_probe := source.burdenScore_adverse_reads_probe
  burdenScore_restorative_reads_probe :=
    source.burdenScore_restorative_reads_probe
  supportScore_adverse_reads_probe := source.supportScore_adverse_reads_probe
  supportScore_restorative_reads_probe :=
    source.supportScore_restorative_reads_probe
  burdenInactive_probe_zero := source.burdenInactive_probe_zero
  supportInactive_probe_zero := source.supportInactive_probe_zero
  active_probe_scores_match := source.active_probe_scores_match
  active_probe_ne_zero := source.active_probe_ne_zero

def toBalancedZeroScoreLawBoundary
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary :=
  source.toDecisiveTraceScoreProbeBoundary.toBalancedZeroScoreLawBoundary

def toCommonUnitScoreLawBoundary
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toDecisiveTraceScoreProbeBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toDecisiveTraceScoreProbeBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toDecisiveTraceScoreProbeBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toDecisiveTraceScoreProbeBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRoleTraceLocalScoreReadoutBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toDecisiveTraceScoreProbeBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRoleTraceLocalScoreReadoutBoundary

/--
Prefix-log event score laws for the decisive trace scores.

This weakens the trace-local score boundary one more step: the decisive
trace-score laws are obtained from Boolean prefix-log events read with a
shared nonzero unit.  The event laws are still explicit inputs, so this is
not a derivation of full additive `L/B` and `M` accounting from observations
alone.
-/
def boolEventScore (scoreUnit : Nat) : Bool -> Nat
  | true => scoreUnit
  | false => 0

structure PromotedRoleTraceEventScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  scoreUnit : Nat
  scoreUnit_ne_zero : scoreUnit ≠ 0
  burdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  supportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_adverse_reads_eventScore :
    burdenScore (boundary.promoteBurden true) =
      boolEventScore scoreUnit
        (burdenTraceEvent
          (construction.package.decodedTraceLog
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates))
  burdenProbe_adverse_reads_eventScore :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (burdenTraceEvent
          (construction.package.decodedTraceLog
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates))
  burdenScore_restorative_reads_eventScore :
    burdenScore (boundary.promoteBurden false) =
      boolEventScore scoreUnit
        (burdenTraceEvent
          (construction.package.decodedTraceLog
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates))
  burdenProbe_restorative_reads_eventScore :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (burdenTraceEvent
          (construction.package.decodedTraceLog
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates))
  supportScore_adverse_reads_eventScore :
    supportScore (boundary.promoteSupport false) =
      boolEventScore scoreUnit
        (supportTraceEvent
          (construction.package.decodedTraceLog
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates))
  supportProbe_adverse_reads_eventScore :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (supportTraceEvent
          (construction.package.decodedTraceLog
            candidate.adverseTraceStateCoordinate
            candidate.adverseTraceActionCoordinates))
  supportScore_restorative_reads_eventScore :
    supportScore (boundary.promoteSupport true) =
      boolEventScore scoreUnit
        (supportTraceEvent
          (construction.package.decodedTraceLog
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates))
  supportProbe_restorative_reads_eventScore :
    supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (supportTraceEvent
          (construction.package.decodedTraceLog
            candidate.restorativeTraceStateCoordinate
            candidate.restorativeTraceActionCoordinates))
  burdenTraceEvent_adverse_active :
    burdenTraceEvent
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = true
  burdenTraceEvent_restorative_inactive :
    burdenTraceEvent
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = false
  supportTraceEvent_adverse_inactive :
    supportTraceEvent
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = false
  supportTraceEvent_restorative_active :
    supportTraceEvent
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = true

namespace PromotedRoleTraceEventScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def burdenTraceScore
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    List (Observation × BoundaryStatus) -> Nat :=
  fun traceLog =>
    boolEventScore source.scoreUnit (source.burdenTraceEvent traceLog)

def supportTraceScore
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    List (Observation × BoundaryStatus) -> Nat :=
  fun traceLog =>
    boolEventScore source.scoreUnit (source.supportTraceEvent traceLog)

theorem burdenInactive_trace_zero
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    source.burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = 0 := by
  rw [burdenTraceScore, source.burdenTraceEvent_restorative_inactive,
    boolEventScore]

theorem supportInactive_trace_zero
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    source.supportTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = 0 := by
  rw [supportTraceScore, source.supportTraceEvent_adverse_inactive,
    boolEventScore]

theorem active_trace_scores_match
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    source.burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) =
      source.supportTraceScore
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) := by
  rw [burdenTraceScore, supportTraceScore,
    source.burdenTraceEvent_adverse_active,
    source.supportTraceEvent_restorative_active, boolEventScore]

theorem active_trace_score_ne_zero
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    source.burdenTraceScore
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) ≠ 0 := by
  rw [burdenTraceScore, source.burdenTraceEvent_adverse_active]
  rw [boolEventScore]
  exact source.scoreUnit_ne_zero

def toTraceLocalScoreReadoutBoundary
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    PromotedRoleTraceLocalScoreReadoutBoundary boundary where
  burdenTraceScore := source.burdenTraceScore
  supportTraceScore := source.supportTraceScore
  burdenProbeScore := source.burdenProbeScore
  supportProbeScore := source.supportProbeScore
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_adverse_reads_trace := by
    simpa [burdenTraceScore] using
      source.burdenScore_adverse_reads_eventScore
  burdenProbe_adverse_reads_trace := by
    simpa [burdenTraceScore] using
      source.burdenProbe_adverse_reads_eventScore
  burdenScore_restorative_reads_trace := by
    simpa [burdenTraceScore] using
      source.burdenScore_restorative_reads_eventScore
  burdenProbe_restorative_reads_trace := by
    simpa [burdenTraceScore] using
      source.burdenProbe_restorative_reads_eventScore
  supportScore_adverse_reads_trace := by
    simpa [supportTraceScore] using
      source.supportScore_adverse_reads_eventScore
  supportProbe_adverse_reads_trace := by
    simpa [supportTraceScore] using
      source.supportProbe_adverse_reads_eventScore
  supportScore_restorative_reads_trace := by
    simpa [supportTraceScore] using
      source.supportScore_restorative_reads_eventScore
  supportProbe_restorative_reads_trace := by
    simpa [supportTraceScore] using
      source.supportProbe_restorative_reads_eventScore
  burdenInactive_trace_zero := source.burdenInactive_trace_zero
  supportInactive_trace_zero := source.supportInactive_trace_zero
  active_trace_scores_match := source.active_trace_scores_match
  active_trace_score_ne_zero := source.active_trace_score_ne_zero

def toDecisiveTraceScoreProbeBoundary
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    PromotedRoleDecisiveTraceScoreProbeBoundary boundary :=
  source.toTraceLocalScoreReadoutBoundary.toDecisiveTraceScoreProbeBoundary

def toBalancedZeroScoreLawBoundary
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary :=
  source.toTraceLocalScoreReadoutBoundary.toBalancedZeroScoreLawBoundary

def toCommonUnitScoreLawBoundary
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toTraceLocalScoreReadoutBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toTraceLocalScoreReadoutBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toTraceLocalScoreReadoutBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRoleTraceEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toTraceLocalScoreReadoutBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRoleTraceEventScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toTraceLocalScoreReadoutBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRoleTraceEventScoreLawBoundary

/--
Prefix-log witnesses for the decisive event activity laws.

This separates the event activity facts from the score laws.  Instead of
directly asserting that the adverse/restorative decoded traces make the
burden/support events active or inactive, this boundary names the decoded
prefix logs and checks the Boolean events on those logs.  The event readouts
are still explicit source inputs; this is a prefix-log activity boundary, not
the full burden/support role recovery theorem.
-/
structure PromotedRolePrefixLogEventActivityBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (_boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  supportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  adverseTraceLog : List (Observation × BoundaryStatus)
  restorativeTraceLog : List (Observation × BoundaryStatus)
  adverseTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      adverseTraceLog
  restorativeTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      restorativeTraceLog
  burdenTraceEvent_adverse_log_active :
    burdenTraceEvent adverseTraceLog = true
  burdenTraceEvent_restorative_log_inactive :
    burdenTraceEvent restorativeTraceLog = false
  supportTraceEvent_adverse_log_inactive :
    supportTraceEvent adverseTraceLog = false
  supportTraceEvent_restorative_log_active :
    supportTraceEvent restorativeTraceLog = true

namespace PromotedRolePrefixLogEventActivityBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}

theorem burdenTraceEvent_adverse_active
    (source : PromotedRolePrefixLogEventActivityBoundary boundary) :
    source.burdenTraceEvent
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = true := by
  rw [source.adverseTraceLog_eq]
  exact source.burdenTraceEvent_adverse_log_active

theorem burdenTraceEvent_restorative_inactive
    (source : PromotedRolePrefixLogEventActivityBoundary boundary) :
    source.burdenTraceEvent
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = false := by
  rw [source.restorativeTraceLog_eq]
  exact source.burdenTraceEvent_restorative_log_inactive

theorem supportTraceEvent_adverse_inactive
    (source : PromotedRolePrefixLogEventActivityBoundary boundary) :
    source.supportTraceEvent
        (construction.package.decodedTraceLog
          candidate.adverseTraceStateCoordinate
          candidate.adverseTraceActionCoordinates) = false := by
  rw [source.adverseTraceLog_eq]
  exact source.supportTraceEvent_adverse_log_inactive

theorem supportTraceEvent_restorative_active
    (source : PromotedRolePrefixLogEventActivityBoundary boundary) :
    source.supportTraceEvent
        (construction.package.decodedTraceLog
          candidate.restorativeTraceStateCoordinate
          candidate.restorativeTraceActionCoordinates) = true := by
  rw [source.restorativeTraceLog_eq]
  exact source.supportTraceEvent_restorative_log_active

end PromotedRolePrefixLogEventActivityBoundary

/--
Prefix-log event score laws using a separate activity witness.

The activity witness derives the decisive active/inactive event facts from
named prefix logs.  The role/probe score read laws are still explicit; this
boundary only prevents those score laws from carrying the event activity facts
implicitly.
-/
structure PromotedRolePrefixLogEventScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  activity : PromotedRolePrefixLogEventActivityBoundary boundary
  scoreUnit : Nat
  scoreUnit_ne_zero : scoreUnit ≠ 0
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_adverse_reads_eventScore :
    burdenScore (boundary.promoteBurden true) =
      boolEventScore scoreUnit
        (activity.burdenTraceEvent activity.adverseTraceLog)
  burdenProbe_adverse_reads_eventScore :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (activity.burdenTraceEvent activity.adverseTraceLog)
  burdenScore_restorative_reads_eventScore :
    burdenScore (boundary.promoteBurden false) =
      boolEventScore scoreUnit
        (activity.burdenTraceEvent activity.restorativeTraceLog)
  burdenProbe_restorative_reads_eventScore :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (activity.burdenTraceEvent activity.restorativeTraceLog)
  supportScore_adverse_reads_eventScore :
    supportScore (boundary.promoteSupport false) =
      boolEventScore scoreUnit
        (activity.supportTraceEvent activity.adverseTraceLog)
  supportProbe_adverse_reads_eventScore :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (activity.supportTraceEvent activity.adverseTraceLog)
  supportScore_restorative_reads_eventScore :
    supportScore (boundary.promoteSupport true) =
      boolEventScore scoreUnit
        (activity.supportTraceEvent activity.restorativeTraceLog)
  supportProbe_restorative_reads_eventScore :
    supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (activity.supportTraceEvent activity.restorativeTraceLog)

namespace PromotedRolePrefixLogEventScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def toTraceEventScoreLawBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleTraceEventScoreLawBoundary boundary where
  scoreUnit := source.scoreUnit
  scoreUnit_ne_zero := source.scoreUnit_ne_zero
  burdenTraceEvent := source.activity.burdenTraceEvent
  supportTraceEvent := source.activity.supportTraceEvent
  burdenProbeScore := source.burdenProbeScore
  supportProbeScore := source.supportProbeScore
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_adverse_reads_eventScore := by
    rw [source.activity.adverseTraceLog_eq]
    exact source.burdenScore_adverse_reads_eventScore
  burdenProbe_adverse_reads_eventScore := by
    rw [source.activity.adverseTraceLog_eq]
    exact source.burdenProbe_adverse_reads_eventScore
  burdenScore_restorative_reads_eventScore := by
    rw [source.activity.restorativeTraceLog_eq]
    exact source.burdenScore_restorative_reads_eventScore
  burdenProbe_restorative_reads_eventScore := by
    rw [source.activity.restorativeTraceLog_eq]
    exact source.burdenProbe_restorative_reads_eventScore
  supportScore_adverse_reads_eventScore := by
    rw [source.activity.adverseTraceLog_eq]
    exact source.supportScore_adverse_reads_eventScore
  supportProbe_adverse_reads_eventScore := by
    rw [source.activity.adverseTraceLog_eq]
    exact source.supportProbe_adverse_reads_eventScore
  supportScore_restorative_reads_eventScore := by
    rw [source.activity.restorativeTraceLog_eq]
    exact source.supportScore_restorative_reads_eventScore
  supportProbe_restorative_reads_eventScore := by
    rw [source.activity.restorativeTraceLog_eq]
    exact source.supportProbe_restorative_reads_eventScore
  burdenTraceEvent_adverse_active :=
    source.activity.burdenTraceEvent_adverse_active
  burdenTraceEvent_restorative_inactive :=
    source.activity.burdenTraceEvent_restorative_inactive
  supportTraceEvent_adverse_inactive :=
    source.activity.supportTraceEvent_adverse_inactive
  supportTraceEvent_restorative_active :=
    source.activity.supportTraceEvent_restorative_active

def toTraceLocalScoreReadoutBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleTraceLocalScoreReadoutBoundary boundary :=
  source.toTraceEventScoreLawBoundary.toTraceLocalScoreReadoutBoundary

def toDecisiveTraceScoreProbeBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleDecisiveTraceScoreProbeBoundary boundary :=
  source.toTraceEventScoreLawBoundary.toDecisiveTraceScoreProbeBoundary

def toBalancedZeroScoreLawBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary :=
  source.toTraceEventScoreLawBoundary.toBalancedZeroScoreLawBoundary

def toCommonUnitScoreLawBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toTraceEventScoreLawBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toTraceEventScoreLawBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toTraceEventScoreLawBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toTraceEventScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRolePrefixLogEventScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toTraceEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRolePrefixLogEventScoreLawBoundary

/--
Agreement between candidate event readouts and canonical prefix-log events.

The previous activity boundary accepts event activity on the decisive logs.
This boundary factors those activity facts through canonical event readouts:
the supplied burden/support event readouts only need to agree with the
canonical prefix-log events on the two decisive logs.  This is still scoped to
the named logs and does not prove that every admissible alternative must use
these events globally.
-/
structure PromotedRoleCanonicalPrefixEventAgreementBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (_boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  supportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  adverseTraceLog : List (Observation × BoundaryStatus)
  restorativeTraceLog : List (Observation × BoundaryStatus)
  adverseTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      adverseTraceLog
  restorativeTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      restorativeTraceLog
  burdenEvent_agrees_adverse :
    burdenTraceEvent adverseTraceLog =
      canonicalBurdenTraceEvent adverseTraceLog
  burdenEvent_agrees_restorative :
    burdenTraceEvent restorativeTraceLog =
      canonicalBurdenTraceEvent restorativeTraceLog
  supportEvent_agrees_adverse :
    supportTraceEvent adverseTraceLog =
      canonicalSupportTraceEvent adverseTraceLog
  supportEvent_agrees_restorative :
    supportTraceEvent restorativeTraceLog =
      canonicalSupportTraceEvent restorativeTraceLog
  canonicalBurden_adverse_active :
    canonicalBurdenTraceEvent adverseTraceLog = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenTraceEvent restorativeTraceLog = false
  canonicalSupport_adverse_inactive :
    canonicalSupportTraceEvent adverseTraceLog = false
  canonicalSupport_restorative_active :
    canonicalSupportTraceEvent restorativeTraceLog = true

namespace PromotedRoleCanonicalPrefixEventAgreementBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}

theorem burdenTraceEvent_adverse_log_active
    (source : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary) :
    source.burdenTraceEvent source.adverseTraceLog = true :=
  source.burdenEvent_agrees_adverse.trans
    source.canonicalBurden_adverse_active

theorem burdenTraceEvent_restorative_log_inactive
    (source : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary) :
    source.burdenTraceEvent source.restorativeTraceLog = false :=
  source.burdenEvent_agrees_restorative.trans
    source.canonicalBurden_restorative_inactive

theorem supportTraceEvent_adverse_log_inactive
    (source : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary) :
    source.supportTraceEvent source.adverseTraceLog = false :=
  source.supportEvent_agrees_adverse.trans
    source.canonicalSupport_adverse_inactive

theorem supportTraceEvent_restorative_log_active
    (source : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary) :
    source.supportTraceEvent source.restorativeTraceLog = true :=
  source.supportEvent_agrees_restorative.trans
    source.canonicalSupport_restorative_active

def toPrefixLogEventActivityBoundary
    (source : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary) :
    PromotedRolePrefixLogEventActivityBoundary boundary where
  burdenTraceEvent := source.burdenTraceEvent
  supportTraceEvent := source.supportTraceEvent
  adverseTraceLog := source.adverseTraceLog
  restorativeTraceLog := source.restorativeTraceLog
  adverseTraceLog_eq := source.adverseTraceLog_eq
  restorativeTraceLog_eq := source.restorativeTraceLog_eq
  burdenTraceEvent_adverse_log_active :=
    source.burdenTraceEvent_adverse_log_active
  burdenTraceEvent_restorative_log_inactive :=
    source.burdenTraceEvent_restorative_log_inactive
  supportTraceEvent_adverse_log_inactive :=
    source.supportTraceEvent_adverse_log_inactive
  supportTraceEvent_restorative_log_active :=
    source.supportTraceEvent_restorative_log_active

end PromotedRoleCanonicalPrefixEventAgreementBoundary

/--
Local preservation of a Boolean prefix-log event on the decisive logs.

This is deliberately small: it does not say that two event readouts agree on
all logs, only that a candidate event readout preserves a canonical event
readout on the adverse/restorative logs used by the split.
-/
structure PrefixLogEventPreservation
    {Observation : Type w}
    (candidateEvent canonicalEvent :
      List (Observation × BoundaryStatus) -> Bool)
    (adverseTraceLog restorativeTraceLog :
      List (Observation × BoundaryStatus)) where
  preserves_adverse :
    candidateEvent adverseTraceLog = canonicalEvent adverseTraceLog
  preserves_restorative :
    candidateEvent restorativeTraceLog = canonicalEvent restorativeTraceLog

namespace PrefixLogEventPreservation

variable {Observation : Type w}
variable {candidateEvent canonicalEvent :
  List (Observation × BoundaryStatus) -> Bool}
variable {adverseTraceLog restorativeTraceLog :
  List (Observation × BoundaryStatus)}

theorem candidate_distinguishes_of_canonical_true_false
    (preservation :
      PrefixLogEventPreservation
        candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog)
    (canonical_adverse_active : canonicalEvent adverseTraceLog = true)
    (canonical_restorative_inactive :
      canonicalEvent restorativeTraceLog = false) :
    candidateEvent adverseTraceLog ≠
      candidateEvent restorativeTraceLog := by
  intro h
  have htf : true = false := by
    calc
      true = canonicalEvent adverseTraceLog :=
        canonical_adverse_active.symm
      _ = candidateEvent adverseTraceLog :=
        preservation.preserves_adverse.symm
      _ = candidateEvent restorativeTraceLog := h
      _ = canonicalEvent restorativeTraceLog :=
        preservation.preserves_restorative
      _ = false := canonical_restorative_inactive
  nomatch htf

theorem candidate_distinguishes_of_canonical_false_true
    (preservation :
      PrefixLogEventPreservation
        candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog)
    (canonical_adverse_inactive : canonicalEvent adverseTraceLog = false)
    (canonical_restorative_active :
      canonicalEvent restorativeTraceLog = true) :
    candidateEvent adverseTraceLog ≠
      candidateEvent restorativeTraceLog := by
  intro h
  have hft : false = true := by
    calc
      false = canonicalEvent adverseTraceLog :=
        canonical_adverse_inactive.symm
      _ = candidateEvent adverseTraceLog :=
        preservation.preserves_adverse.symm
      _ = candidateEvent restorativeTraceLog := h
      _ = canonicalEvent restorativeTraceLog :=
        preservation.preserves_restorative
      _ = true := canonical_restorative_active
  nomatch hft

end PrefixLogEventPreservation

/--
Canonical prefix-event preservation boundary.

The previous agreement boundary accepted the decisive candidate/canonical
event equalities directly.  This boundary takes local preservation certificates
for the burden and support event readouts, then constructs the agreement
surface and the corresponding non-collapse facts.  It is still scoped to the
two decisive logs and does not prove global event uniqueness.
-/
structure PromotedRoleCanonicalPrefixEventPreservationBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (_boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  burdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  supportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurdenTraceEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportTraceEvent : List (Observation × BoundaryStatus) -> Bool
  adverseTraceLog : List (Observation × BoundaryStatus)
  restorativeTraceLog : List (Observation × BoundaryStatus)
  adverseTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      adverseTraceLog
  restorativeTraceLog_eq :
    construction.package.decodedTraceLog
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      restorativeTraceLog
  burdenEvent_preservation :
    PrefixLogEventPreservation
      burdenTraceEvent canonicalBurdenTraceEvent
      adverseTraceLog restorativeTraceLog
  supportEvent_preservation :
    PrefixLogEventPreservation
      supportTraceEvent canonicalSupportTraceEvent
      adverseTraceLog restorativeTraceLog
  canonicalBurden_adverse_active :
    canonicalBurdenTraceEvent adverseTraceLog = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenTraceEvent restorativeTraceLog = false
  canonicalSupport_adverse_inactive :
    canonicalSupportTraceEvent adverseTraceLog = false
  canonicalSupport_restorative_active :
    canonicalSupportTraceEvent restorativeTraceLog = true

namespace PromotedRoleCanonicalPrefixEventPreservationBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}

theorem burdenEvent_agrees_adverse
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.burdenTraceEvent source.adverseTraceLog =
      source.canonicalBurdenTraceEvent source.adverseTraceLog :=
  source.burdenEvent_preservation.preserves_adverse

theorem burdenEvent_agrees_restorative
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.burdenTraceEvent source.restorativeTraceLog =
      source.canonicalBurdenTraceEvent source.restorativeTraceLog :=
  source.burdenEvent_preservation.preserves_restorative

theorem supportEvent_agrees_adverse
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.supportTraceEvent source.adverseTraceLog =
      source.canonicalSupportTraceEvent source.adverseTraceLog :=
  source.supportEvent_preservation.preserves_adverse

theorem supportEvent_agrees_restorative
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.supportTraceEvent source.restorativeTraceLog =
      source.canonicalSupportTraceEvent source.restorativeTraceLog :=
  source.supportEvent_preservation.preserves_restorative

theorem burdenEvent_decisive_logs_distinguish
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.burdenTraceEvent source.adverseTraceLog ≠
      source.burdenTraceEvent source.restorativeTraceLog :=
  source.burdenEvent_preservation
    |>.candidate_distinguishes_of_canonical_true_false
      source.canonicalBurden_adverse_active
      source.canonicalBurden_restorative_inactive

theorem supportEvent_decisive_logs_distinguish
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    source.supportTraceEvent source.adverseTraceLog ≠
      source.supportTraceEvent source.restorativeTraceLog :=
  source.supportEvent_preservation
    |>.candidate_distinguishes_of_canonical_false_true
      source.canonicalSupport_adverse_inactive
      source.canonicalSupport_restorative_active

def toCanonicalPrefixEventAgreementBoundary
    (source :
      PromotedRoleCanonicalPrefixEventPreservationBoundary boundary) :
    PromotedRoleCanonicalPrefixEventAgreementBoundary boundary where
  burdenTraceEvent := source.burdenTraceEvent
  supportTraceEvent := source.supportTraceEvent
  canonicalBurdenTraceEvent := source.canonicalBurdenTraceEvent
  canonicalSupportTraceEvent := source.canonicalSupportTraceEvent
  adverseTraceLog := source.adverseTraceLog
  restorativeTraceLog := source.restorativeTraceLog
  adverseTraceLog_eq := source.adverseTraceLog_eq
  restorativeTraceLog_eq := source.restorativeTraceLog_eq
  burdenEvent_agrees_adverse := source.burdenEvent_agrees_adverse
  burdenEvent_agrees_restorative := source.burdenEvent_agrees_restorative
  supportEvent_agrees_adverse := source.supportEvent_agrees_adverse
  supportEvent_agrees_restorative := source.supportEvent_agrees_restorative
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

end PromotedRoleCanonicalPrefixEventPreservationBoundary

/--
Canonical-prefix-event score laws.

This boundary reads role/probe scores from canonical prefix-log event scores
on the decisive logs, then uses the agreement boundary to pass through the
existing prefix-log event score surface.  It removes one more direct source:
scores no longer need to read the candidate event readouts themselves, only
the canonical events that the candidate readouts agree with on the decisive
logs.
-/
structure PromotedRoleCanonicalPrefixEventScoreLawBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    {CollapsedStateCoordinate : Type z}
    {CollapsedActionCoordinate : Type t}
    {DecodedStateCoordinate : Type r}
    {DecodedActionCoordinate : Type p}
    {Target : Type b}
    {construction :
      ObservationDerivedAlternativeConstructionBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate Target}
    {candidate :
      ObservationDerivedBurdenSupportCandidateBoundary construction}
    {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
    (boundary :
      ObservationDerivedPromotedRoleBoundary
        candidate PromotedBurdenRole PromotedSupportRole) where
  agreement : PromotedRoleCanonicalPrefixEventAgreementBoundary boundary
  scoreUnit : Nat
  scoreUnit_ne_zero : scoreUnit ≠ 0
  burdenProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  supportProbeScore :
    DecodedStateCoordinate -> List DecodedActionCoordinate -> Nat
  burdenScore : PromotedBurdenRole -> Nat
  supportScore : PromotedSupportRole -> Nat
  burdenScore_adverse_reads_canonicalScore :
    burdenScore (boundary.promoteBurden true) =
      boolEventScore scoreUnit
        (agreement.canonicalBurdenTraceEvent agreement.adverseTraceLog)
  burdenProbe_adverse_reads_canonicalScore :
    burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (agreement.canonicalBurdenTraceEvent agreement.adverseTraceLog)
  burdenScore_restorative_reads_canonicalScore :
    burdenScore (boundary.promoteBurden false) =
      boolEventScore scoreUnit
        (agreement.canonicalBurdenTraceEvent agreement.restorativeTraceLog)
  burdenProbe_restorative_reads_canonicalScore :
    burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (agreement.canonicalBurdenTraceEvent agreement.restorativeTraceLog)
  supportScore_adverse_reads_canonicalScore :
    supportScore (boundary.promoteSupport false) =
      boolEventScore scoreUnit
        (agreement.canonicalSupportTraceEvent agreement.adverseTraceLog)
  supportProbe_adverse_reads_canonicalScore :
    supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore scoreUnit
        (agreement.canonicalSupportTraceEvent agreement.adverseTraceLog)
  supportScore_restorative_reads_canonicalScore :
    supportScore (boundary.promoteSupport true) =
      boolEventScore scoreUnit
        (agreement.canonicalSupportTraceEvent agreement.restorativeTraceLog)
  supportProbe_restorative_reads_canonicalScore :
    supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore scoreUnit
        (agreement.canonicalSupportTraceEvent agreement.restorativeTraceLog)

namespace PromotedRoleCanonicalPrefixEventScoreLawBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {Target : Type b}
variable {construction :
  ObservationDerivedAlternativeConstructionBoundary
    P Q CollapsedStateCoordinate CollapsedActionCoordinate
    DecodedStateCoordinate DecodedActionCoordinate Target}
variable {candidate :
  ObservationDerivedBurdenSupportCandidateBoundary construction}
variable {PromotedBurdenRole : Type q} {PromotedSupportRole : Type a}
variable {boundary :
  ObservationDerivedPromotedRoleBoundary
    candidate PromotedBurdenRole PromotedSupportRole}
variable {RunCoordinate : Type c}

def toPrefixLogEventScoreLawBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRolePrefixLogEventScoreLawBoundary boundary where
  activity := source.agreement.toPrefixLogEventActivityBoundary
  scoreUnit := source.scoreUnit
  scoreUnit_ne_zero := source.scoreUnit_ne_zero
  burdenProbeScore := source.burdenProbeScore
  supportProbeScore := source.supportProbeScore
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  burdenScore_adverse_reads_eventScore := by
    change source.burdenScore (boundary.promoteBurden true) =
      boolEventScore source.scoreUnit
        (source.agreement.burdenTraceEvent source.agreement.adverseTraceLog)
    rw [source.agreement.burdenEvent_agrees_adverse]
    exact source.burdenScore_adverse_reads_canonicalScore
  burdenProbe_adverse_reads_eventScore := by
    change source.burdenProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore source.scoreUnit
        (source.agreement.burdenTraceEvent source.agreement.adverseTraceLog)
    rw [source.agreement.burdenEvent_agrees_adverse]
    exact source.burdenProbe_adverse_reads_canonicalScore
  burdenScore_restorative_reads_eventScore := by
    change source.burdenScore (boundary.promoteBurden false) =
      boolEventScore source.scoreUnit
        (source.agreement.burdenTraceEvent
          source.agreement.restorativeTraceLog)
    rw [source.agreement.burdenEvent_agrees_restorative]
    exact source.burdenScore_restorative_reads_canonicalScore
  burdenProbe_restorative_reads_eventScore := by
    change source.burdenProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore source.scoreUnit
        (source.agreement.burdenTraceEvent
          source.agreement.restorativeTraceLog)
    rw [source.agreement.burdenEvent_agrees_restorative]
    exact source.burdenProbe_restorative_reads_canonicalScore
  supportScore_adverse_reads_eventScore := by
    change source.supportScore (boundary.promoteSupport false) =
      boolEventScore source.scoreUnit
        (source.agreement.supportTraceEvent source.agreement.adverseTraceLog)
    rw [source.agreement.supportEvent_agrees_adverse]
    exact source.supportScore_adverse_reads_canonicalScore
  supportProbe_adverse_reads_eventScore := by
    change source.supportProbeScore
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates =
      boolEventScore source.scoreUnit
        (source.agreement.supportTraceEvent source.agreement.adverseTraceLog)
    rw [source.agreement.supportEvent_agrees_adverse]
    exact source.supportProbe_adverse_reads_canonicalScore
  supportScore_restorative_reads_eventScore := by
    change source.supportScore (boundary.promoteSupport true) =
      boolEventScore source.scoreUnit
        (source.agreement.supportTraceEvent
          source.agreement.restorativeTraceLog)
    rw [source.agreement.supportEvent_agrees_restorative]
    exact source.supportScore_restorative_reads_canonicalScore
  supportProbe_restorative_reads_eventScore := by
    change source.supportProbeScore
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates =
      boolEventScore source.scoreUnit
        (source.agreement.supportTraceEvent
          source.agreement.restorativeTraceLog)
    rw [source.agreement.supportEvent_agrees_restorative]
    exact source.supportProbe_restorative_reads_canonicalScore

def toTraceEventScoreLawBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleTraceEventScoreLawBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toTraceEventScoreLawBoundary

def toTraceLocalScoreReadoutBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleTraceLocalScoreReadoutBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toTraceLocalScoreReadoutBoundary

def toDecisiveTraceScoreProbeBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleDecisiveTraceScoreProbeBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toDecisiveTraceScoreProbeBoundary

def toBalancedZeroScoreLawBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleBalancedZeroScoreLawBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toBalancedZeroScoreLawBoundary

def toCommonUnitScoreLawBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleCommonUnitScoreLawBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toCommonUnitScoreLawBoundary

def toAdditiveScoreBoundary
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    PromotedRoleAdditiveScoreBoundary boundary :=
  source.toPrefixLogEventScoreLawBoundary.toAdditiveScoreBoundary

theorem no_totalScore_componentScore_model
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          source.toAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toPrefixLogEventScoreLawBoundary.no_totalScore_componentScore_model

theorem no_totalScore_promotedRolePair_model
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary) :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> PromotedBurdenRole × PromotedSupportRole =>
        forall stateCoordinate actionCoordinates,
          boundary.promotedRolePair stateCoordinate actionCoordinates =
            rolePairOfTotal
              (source.toAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  source.toPrefixLogEventScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem componentScore_coordinate_must_distinguish
    (source : PromotedRoleCanonicalPrefixEventScoreLawBoundary boundary)
    (model :
      RunComponentScoreCoordinateModel
        source.toAdditiveScoreBoundary.componentScoreOfRun RunCoordinate) :
    model.coordinate
        candidate.adverseTraceStateCoordinate
        candidate.adverseTraceActionCoordinates ≠
      model.coordinate
        candidate.restorativeTraceStateCoordinate
        candidate.restorativeTraceActionCoordinates :=
  source.toPrefixLogEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

end PromotedRoleCanonicalPrefixEventScoreLawBoundary

/--
Alternative-quantified factorization statement boundary.

This is the next theorem statement shape: for arbitrary observational
source/target processes, if the preservation, target-semantics, role-bridge,
and accounting certificates are supplied, the current scoped factorization
surface can be produced.  It is deliberately not a uniqueness theorem and not
a proof that every possible alternative representation has already supplied
the required preservation/equivalence data.
-/
structure AlternativeQuantifiedFactorizationStatementBoundary
    {StateA : Type u} {ActionA : Type v} {Observation : Type w}
    {StateB : Type x} {ActionB : Type y}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (CollapsedStateCoordinate : Type z)
    (CollapsedActionCoordinate : Type t)
    (DecodedStateCoordinate : Type r)
    (DecodedActionCoordinate : Type p)
    (BurdenRole : Type q) (SupportRole : Type a)
    (Target : Type b) where
  semanticBridge :
    PrefixSensitiveSemanticBridge
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      BurdenRole SupportRole Target
  logAccounting :
    PrefixSensitiveLogAccountingBridge semanticBridge

namespace AlternativeQuantifiedFactorizationStatementBoundary

variable {StateA : Type u} {ActionA : Type v} {Observation : Type w}
variable {StateB : Type x} {ActionB : Type y}
variable {P : ObservationalPersistenceProcess StateA ActionA Observation}
variable {Q : ObservationalPersistenceProcess StateB ActionB Observation}
variable {CollapsedStateCoordinate : Type z}
variable {CollapsedActionCoordinate : Type t}
variable {DecodedStateCoordinate : Type r}
variable {DecodedActionCoordinate : Type p}
variable {BurdenRole : Type q} {SupportRole : Type a}
variable {Target : Type b}

def toCanonicalFactorization
    (statement :
      AlternativeQuantifiedFactorizationStatementBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    PrefixSensitiveCanonicalFactorizationBoundary
      P Q CollapsedStateCoordinate CollapsedActionCoordinate
      DecodedStateCoordinate DecodedActionCoordinate
      BurdenRole SupportRole Target where
  semanticBridge := statement.semanticBridge
  logAccounting := statement.logAccounting

/--
The statement boundary exposes the current scoped factorization package and
the three currently checked consequences.  The first conjunct is the negative
anti-collapse test; the second is the `F/K/V_K` recovery witness; the third is
the certificate-relative log-accounting readout.
-/
theorem produces_factorization_surface
    (statement :
      AlternativeQuantifiedFactorizationStatementBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ∃ factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target,
      (¬ Exists
        (fun traceLogOfCoordinates :
          CollapsedStateCoordinate -> List CollapsedActionCoordinate ->
            List (Observation × BoundaryStatus) =>
            forall s actions,
              P.traceLog s actions =
                traceLogOfCoordinates
                  (factorization.collapsedStateCoordinate s)
                  (actions.map factorization.collapsedActionCoordinate))) ∧
      factorization.stateRealizationViability.viableRegion.Nonempty ∧
      (∃ k : ℝ, 0 ≤ k ∧
        ∀ stateCoordinate actionCoordinates,
          factorization.logAccounting.burdenLossValue
              (factorization.burdenOfRun
                stateCoordinate actionCoordinates) =
            -k * Real.log
              (factorization.logAccounting.ratioOfRun
                stateCoordinate actionCoordinates)) := by
  let factorization := statement.toCanonicalFactorization
  refine
    ⟨factorization,
      factorization.no_collapsed_traceLog_model,
      factorization.viableRegion_nonempty,
      ?_⟩
  exact factorization.burden_loss_has_log_form

theorem produces_adverse_trace_log_accounting
    (statement :
      AlternativeQuantifiedFactorizationStatementBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target) :
    ∃ factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        P Q CollapsedStateCoordinate CollapsedActionCoordinate
        DecodedStateCoordinate DecodedActionCoordinate
        BurdenRole SupportRole Target,
      ∃ k : ℝ, 0 ≤ k ∧
        factorization.logAccounting.burdenLossValue
            (factorization.burdenOfRun
              factorization.adverseTraceStateCoordinate
              factorization.adverseTraceActionCoordinates) =
          -k * Real.log
            (factorization.logAccounting.ratioOfRun
              factorization.adverseTraceStateCoordinate
              factorization.adverseTraceActionCoordinates) := by
  let factorization := statement.toCanonicalFactorization
  exact
    ⟨factorization,
      factorization.adverseTrace_burden_loss_has_log_form⟩

end AlternativeQuantifiedFactorizationStatementBoundary

/--
An observed split between two actions, stated only in response terms.
-/
structure ObservableActionSplit
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  left : Action
  right : Action
  witness : State
  response_ne : P.response witness left ≠ P.response witness right

namespace ObservableActionSplit

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable (split : ObservableActionSplit P)

/--
An observed split forces any faithful one-coordinate response model to separate
the two action coordinates.
-/
theorem forces_distinct_coordinates
    {Coordinate : Type x}
    (R : SingleCoordinateActionModel P Coordinate) :
    R.coordinate split.left ≠ R.coordinate split.right :=
  distinguished_responses_force_distinct_coordinates R split.response_ne

end ObservableActionSplit

namespace ToyObservationProcess

/-- A tiny process state for the observational anti-collapse test. -/
inductive ToyState where
  | ok
  | failed
  deriving DecidableEq, Repr

/-- Two observable actions with opposite one-step effects. -/
inductive ToyAction where
  | degrade
  | repair
  deriving DecidableEq, Repr

/-- The observable state label in the toy process. -/
inductive ToyObservation where
  | green
  | red
  deriving DecidableEq, Repr

def observe : ToyState -> ToyObservation
  | ToyState.ok => ToyObservation.green
  | ToyState.failed => ToyObservation.red

def readout : ToyState -> BoundaryStatus
  | ToyState.ok => BoundaryStatus.viable
  | ToyState.failed => BoundaryStatus.collapsed

def step : ToyState -> ToyAction -> ToyState
  | _, ToyAction.degrade => ToyState.failed
  | _, ToyAction.repair => ToyState.ok

/--
A concrete observational process where the two actions have different observed
responses from the same state.
-/
def process :
    ObservationalPersistenceProcess ToyState ToyAction ToyObservation where
  observe := observe
  step := step
  readout := readout

/-- The toy actions are observationally distinguished at the ok state. -/
theorem degrade_repair_distinguished :
    process.response ToyState.ok ToyAction.degrade ≠
      process.response ToyState.ok ToyAction.repair := by
  decide

/-- The observed split for the toy process. -/
def degradeRepairSplit : ObservableActionSplit process where
  left := ToyAction.degrade
  right := ToyAction.repair
  witness := ToyState.ok
  response_ne := degrade_repair_distinguished

/--
Any response-preserving one-coordinate model of the toy process must separate
the degrade and repair coordinates.
-/
theorem degrade_repair_forces_distinct_coordinates
    {Coordinate : Type u}
    (R : SingleCoordinateActionModel process Coordinate) :
    R.coordinate ToyAction.degrade ≠ R.coordinate ToyAction.repair :=
  degradeRepairSplit.forces_distinct_coordinates R

/--
A response-preserving coordinate model cannot collapse the two toy actions to
the same coordinate.
-/
theorem no_collapsed_degrade_repair_coordinate
    {Coordinate : Type u}
    (R : SingleCoordinateActionModel process Coordinate)
    (hcollapse :
      R.coordinate ToyAction.degrade = R.coordinate ToyAction.repair) :
    False :=
  degrade_repair_forces_distinct_coordinates R hcollapse

/--
There is no response-preserving model whose action coordinate has only one
available value.
-/
theorem no_unit_coordinate_model :
    ¬ Nonempty (SingleCoordinateActionModel process Unit) := by
  intro h
  rcases h with ⟨R⟩
  apply degrade_repair_forces_distinct_coordinates R
  cases R.coordinate ToyAction.degrade
  cases R.coordinate ToyAction.repair
  rfl

/--
A bare action code has no response-preservation requirement.  This is used as
the hypothesis-deletion check: once preservation is deleted, the collapsed
Unit-valued action code exists immediately.
-/
structure BareActionCode (Coordinate : Type u) where
  coordinate : ToyAction -> Coordinate

def collapsedUnitActionCode : BareActionCode Unit where
  coordinate := fun _ => ()

/-- Without the response-preservation field, the two toy actions can be collapsed. -/
theorem collapsedUnitActionCode_identifies_actions :
    collapsedUnitActionCode.coordinate ToyAction.degrade =
      collapsedUnitActionCode.coordinate ToyAction.repair :=
  rfl

/-- A two-channel observational action code for the toy process. -/
structure TwoChannelCoordinate where
  adverse : Bool
  restorative : Bool
  deriving DecidableEq, Repr

/--
The two-channel code is deliberately observational: it records an adverse and
a restorative action channel, without importing the full burden/support role
vocabulary.
-/
def twoChannelCoordinate : ToyAction -> TwoChannelCoordinate
  | ToyAction.degrade => { adverse := true, restorative := false }
  | ToyAction.repair => { adverse := false, restorative := true }

/--
The aggregate activity score forgets which channel was active.  Both toy
actions have total activity one.
-/
def totalActivityOfTwoChannel (c : TwoChannelCoordinate) : Nat :=
  (if c.adverse then 1 else 0) + (if c.restorative then 1 else 0)

def totalActivityCoordinate (a : ToyAction) : Nat :=
  totalActivityOfTwoChannel (twoChannelCoordinate a)

/-- The total-activity aggregate identifies the two toy actions. -/
theorem totalActivityCoordinate_identifies_actions :
    totalActivityCoordinate ToyAction.degrade =
      totalActivityCoordinate ToyAction.repair :=
  rfl

/--
No response rule depending only on the total-activity aggregate can preserve
the toy process.  This is the sharper anti-collapse test: the failed model is
not every one-coordinate model, but the specific aggregate that forgets the
adverse/restorative distinction.
-/
theorem no_totalActivity_response_model :
    ¬ Exists
      (fun responseOfTotal :
        ToyState -> Nat -> ToyObservation × BoundaryStatus =>
          forall s a,
            process.response s a =
              responseOfTotal s (totalActivityCoordinate a)) := by
  intro h
  rcases h with ⟨responseOfTotal, hpreserve⟩
  let R : SingleCoordinateActionModel process Nat :=
    { coordinate := totalActivityCoordinate
      responseOfCoordinate := responseOfTotal
      preserves_response := hpreserve }
  exact
    degrade_repair_forces_distinct_coordinates R
      totalActivityCoordinate_identifies_actions

def degradeThenRepair : List ToyAction :=
  [ToyAction.degrade, ToyAction.repair]

def repairThenDegrade : List ToyAction :=
  [ToyAction.repair, ToyAction.degrade]

def repairThenRepair : List ToyAction :=
  [ToyAction.repair, ToyAction.repair]

/--
The total-activity aggregate also identifies the two action traces: each trace
has coordinate trace `[1, 1]`.
-/
theorem totalActivityTrace_identifies_order :
    degradeThenRepair.map totalActivityCoordinate =
      repairThenDegrade.map totalActivityCoordinate :=
  rfl

/--
The two same-aggregate traces have different observed outcomes from the same
initial state.
-/
theorem totalActivityTrace_order_distinguished :
    process.traceResponse ToyState.ok degradeThenRepair ≠
      process.traceResponse ToyState.ok repairThenDegrade := by
  decide

/--
The total-activity aggregate identifies a recovered trace and a never-collapsed
trace.
-/
theorem totalActivityTrace_identifies_recoveredPrefix :
    degradeThenRepair.map totalActivityCoordinate =
      repairThenRepair.map totalActivityCoordinate :=
  rfl

/-- The recovered-prefix pair has the same final observed response. -/
theorem recoveredPrefix_traceResponse_equal :
    process.traceResponse ToyState.ok degradeThenRepair =
      process.traceResponse ToyState.ok repairThenRepair :=
  rfl

/--
The recovered-prefix pair has different prefix logs: the first trace crosses
the collapsed boundary before repair.
-/
theorem recoveredPrefix_traceLog_distinguished :
    process.traceLog ToyState.ok degradeThenRepair ≠
      process.traceLog ToyState.ok repairThenRepair := by
  decide

/-- The boundary-only prefix readout also distinguishes the recovered prefix. -/
theorem recoveredPrefix_boundaryReadout_distinguished :
    process.prefixBoundaryReadout ToyState.ok degradeThenRepair ≠
      process.prefixBoundaryReadout ToyState.ok repairThenRepair := by
  decide

def recoveredPrefixFinalResponsePrefixLogGap :
    CollapsedFinalResponsePrefixLogGap process ToyState Nat where
  leftState := ToyState.ok
  rightState := ToyState.ok
  leftActions := degradeThenRepair
  rightActions := repairThenRepair
  stateCoordinate := fun s => s
  actionCoordinate := totalActivityCoordinate
  sameState := rfl
  sameTrace := totalActivityTrace_identifies_recoveredPrefix
  traceResponse_eq := recoveredPrefix_traceResponse_equal
  traceLog_ne := recoveredPrefix_traceLog_distinguished

theorem recoveredPrefix_finalResponse_deletion_witness :
    process.traceResponse ToyState.ok degradeThenRepair =
        process.traceResponse ToyState.ok repairThenRepair ∧
      ToyState.ok = ToyState.ok ∧
      degradeThenRepair.map totalActivityCoordinate =
        repairThenRepair.map totalActivityCoordinate :=
  CollapsedFinalResponsePrefixLogGap.final_response_deletion_witness
    recoveredPrefixFinalResponsePrefixLogGap

theorem recoveredPrefix_gap_no_prefixLog_model :
    ¬ Exists
      (fun traceLogOfTotal :
        ToyState -> List Nat -> List (ToyObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfTotal s
                (actions.map totalActivityCoordinate)) :=
  CollapsedFinalResponsePrefixLogGap.no_preserving_prefix_log_coordinate_model
    recoveredPrefixFinalResponsePrefixLogGap

/--
No trace response rule depending only on the total-activity aggregate trace can
preserve the toy process.  This is the trace-level anti-collapse test for the
next G1c loop.
-/
theorem no_totalActivity_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfTotal :
        ToyState -> List Nat -> ToyObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfTotal s
                (actions.map totalActivityCoordinate)) := by
  intro h
  rcases h with ⟨traceResponseOfTotal, hpreserve⟩
  let R : TraceCoordinateActionModel process Nat :=
    { coordinate := totalActivityCoordinate
      traceResponseOfCoordinate := traceResponseOfTotal
      preserves_traceResponse := hpreserve }
  exact
    distinguished_traceResponses_force_distinct_coordinateTrace R
      totalActivityTrace_order_distinguished
      totalActivityTrace_identifies_order

/--
No prefix-log rule depending only on the total-activity aggregate trace can
preserve the toy process: it would miss a collapsed prefix that later repairs.
-/
theorem no_totalActivity_traceLog_model :
    ¬ Exists
      (fun traceLogOfTotal :
        ToyState -> List Nat -> List (ToyObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfTotal s
                (actions.map totalActivityCoordinate)) := by
  intro h
  rcases h with ⟨traceLogOfTotal, hpreserve⟩
  let R : TraceLogCoordinateActionModel process Nat :=
    { coordinate := totalActivityCoordinate
      traceLogOfCoordinate := traceLogOfTotal
      preserves_traceLog := hpreserve }
  exact
    distinguished_traceLogs_force_distinct_coordinateTrace R
      recoveredPrefix_traceLog_distinguished
      totalActivityTrace_identifies_recoveredPrefix

def responseOfTwoChannel
    (s : ToyState) (c : TwoChannelCoordinate) :
    ToyObservation × BoundaryStatus :=
  let next :=
    if c.restorative then ToyState.ok
    else if c.adverse then ToyState.failed
    else s
  (observe next, readout next)

/-- The two-channel code preserves the toy process's observed action response. -/
def twoChannelModel :
    SingleCoordinateActionModel process TwoChannelCoordinate where
  coordinate := twoChannelCoordinate
  responseOfCoordinate := responseOfTwoChannel
  preserves_response := by
    intro s a
    cases s <;> cases a <;> rfl

/-- The two-channel model separates the two toy action coordinates. -/
theorem twoChannelModel_distinguishes_actions :
    twoChannelModel.coordinate ToyAction.degrade ≠
      twoChannelModel.coordinate ToyAction.repair := by
  exact degrade_repair_forces_distinct_coordinates twoChannelModel

def stepOfTwoChannel (s : ToyState) (c : TwoChannelCoordinate) : ToyState :=
  if c.restorative then ToyState.ok
  else if c.adverse then ToyState.failed
  else s

def traceLogOfTwoChannel :
    ToyState -> List TwoChannelCoordinate ->
      List (ToyObservation × BoundaryStatus)
  | _, [] => []
  | s, coordinate :: coordinates =>
      let nextState := stepOfTwoChannel s coordinate
      (observe nextState, readout nextState) ::
        traceLogOfTwoChannel nextState coordinates

/-- The two-channel code preserves prefix logs, not only final trace response. -/
def twoChannelTraceLogModel :
    TraceLogCoordinateActionModel process TwoChannelCoordinate where
  coordinate := twoChannelCoordinate
  traceLogOfCoordinate := traceLogOfTwoChannel
  preserves_traceLog := by
    intro s actions
    induction actions generalizing s with
    | nil => rfl
    | cons action actions ih =>
        cases s with
        | ok =>
            cases action with
            | degrade =>
                change
                  (ToyObservation.red, BoundaryStatus.collapsed) ::
                      process.traceLog ToyState.failed actions =
                    (ToyObservation.red, BoundaryStatus.collapsed) ::
                      traceLogOfTwoChannel ToyState.failed
                        (actions.map twoChannelCoordinate)
                rw [ih ToyState.failed]
            | repair =>
                change
                  (ToyObservation.green, BoundaryStatus.viable) ::
                      process.traceLog ToyState.ok actions =
                    (ToyObservation.green, BoundaryStatus.viable) ::
                      traceLogOfTwoChannel ToyState.ok
                        (actions.map twoChannelCoordinate)
                rw [ih ToyState.ok]
        | failed =>
            cases action with
            | degrade =>
                change
                  (ToyObservation.red, BoundaryStatus.collapsed) ::
                      process.traceLog ToyState.failed actions =
                    (ToyObservation.red, BoundaryStatus.collapsed) ::
                      traceLogOfTwoChannel ToyState.failed
                        (actions.map twoChannelCoordinate)
                rw [ih ToyState.failed]
            | repair =>
                change
                  (ToyObservation.green, BoundaryStatus.viable) ::
                      process.traceLog ToyState.ok actions =
                    (ToyObservation.green, BoundaryStatus.viable) ::
                      traceLogOfTwoChannel ToyState.ok
                        (actions.map twoChannelCoordinate)
                rw [ih ToyState.ok]

def runTwoChannel (s : ToyState) (coordinates : List TwoChannelCoordinate) :
    ToyState :=
  coordinates.foldl stepOfTwoChannel s

def traceResponseOfTwoChannel
    (s : ToyState) (coordinates : List TwoChannelCoordinate) :
    ToyObservation × BoundaryStatus :=
  let finalState := runTwoChannel s coordinates
  (observe finalState, readout finalState)

/-- The two-channel trace response preserves the degrade-then-repair trace. -/
theorem twoChannelTrace_preserves_degradeThenRepair :
    process.traceResponse ToyState.ok degradeThenRepair =
      traceResponseOfTwoChannel ToyState.ok
        (degradeThenRepair.map twoChannelCoordinate) :=
  rfl

/-- The two-channel trace response preserves the repair-then-degrade trace. -/
theorem twoChannelTrace_preserves_repairThenDegrade :
    process.traceResponse ToyState.ok repairThenDegrade =
      traceResponseOfTwoChannel ToyState.ok
        (repairThenDegrade.map twoChannelCoordinate) :=
  rfl

/-- The two-channel log preserves the recovered-prefix trace. -/
theorem twoChannelTraceLog_preserves_degradeThenRepair :
    process.traceLog ToyState.ok degradeThenRepair =
      traceLogOfTwoChannel ToyState.ok
        (degradeThenRepair.map twoChannelCoordinate) :=
  rfl

/-- The two-channel log preserves the never-collapsed comparison trace. -/
theorem twoChannelTraceLog_preserves_repairThenRepair :
    process.traceLog ToyState.ok repairThenRepair =
      traceLogOfTwoChannel ToyState.ok
        (repairThenRepair.map twoChannelCoordinate) :=
  rfl

end ToyObservationProcess

namespace ToyContextProcess

/-- A latent context can resolve to a viable or collapsed outcome. -/
inductive ContextState where
  | latent (adverse : Bool) (restorative : Bool)
  | ok
  | failed
  deriving DecidableEq, Repr

/-- A recovery probe exposes how the latent context responds. -/
inductive ContextAction where
  | probeRecovery
  deriving DecidableEq, Repr

/-- Observations deliberately hide latent channel details. -/
inductive ContextObservation where
  | latent
  | green
  | red
  deriving DecidableEq, Repr

def observe : ContextState -> ContextObservation
  | ContextState.latent _ _ => ContextObservation.latent
  | ContextState.ok => ContextObservation.green
  | ContextState.failed => ContextObservation.red

def readout : ContextState -> BoundaryStatus
  | ContextState.latent _ _ => BoundaryStatus.stopped
  | ContextState.ok => BoundaryStatus.viable
  | ContextState.failed => BoundaryStatus.collapsed

def resolveLatent (adverse restorative : Bool) : ContextState :=
  if restorative && !adverse then ContextState.ok else ContextState.failed

def step : ContextState -> ContextAction -> ContextState
  | ContextState.latent adverse restorative, ContextAction.probeRecovery =>
      resolveLatent adverse restorative
  | s, ContextAction.probeRecovery => s

/--
A context process whose initial observation hides the two latent channels.
-/
def process :
    ObservationalPersistenceProcess
      ContextState ContextAction ContextObservation where
  observe := observe
  step := step
  readout := readout

def adverseOnlyContext : ContextState :=
  ContextState.latent true false

def restorativeOnlyContext : ContextState :=
  ContextState.latent false true

def recoveryProbeTrace : List ContextAction :=
  [ContextAction.probeRecovery]

/--
The aggregate context score forgets which latent channel is active.
-/
def contextAggregate : ContextState -> Nat
  | ContextState.latent adverse restorative =>
      (if adverse then 1 else 0) + (if restorative then 1 else 0)
  | ContextState.ok => 1
  | ContextState.failed => 1

/-- The aggregate identifies the adverse-only and restorative-only contexts. -/
theorem contextAggregate_identifies_contexts :
    contextAggregate adverseOnlyContext =
      contextAggregate restorativeOnlyContext :=
  rfl

/--
The same recovery probe has different observed trace responses in the two
same-aggregate contexts.
-/
theorem contextAggregateTrace_distinguished :
    process.traceResponse adverseOnlyContext recoveryProbeTrace ≠
      process.traceResponse restorativeOnlyContext recoveryProbeTrace := by
  decide

/--
No trace response rule depending only on the collapsed context aggregate can
preserve both latent contexts.
-/
theorem no_contextAggregate_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List ContextAction -> ContextObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate (contextAggregate s) actions) := by
  intro h
  rcases h with ⟨traceResponseOfAggregate, hpreserve⟩
  let R : StateCoordinateTraceModel process Nat :=
    { coordinate := contextAggregate
      traceResponseOfCoordinate := traceResponseOfAggregate
      preserves_traceResponse := hpreserve }
  exact
    distinguished_contextTraceResponses_force_distinct_stateCoordinate R
      contextAggregateTrace_distinguished
      contextAggregate_identifies_contexts

inductive ContextResolution where
  | latent
  | ok
  | failed
  deriving DecidableEq, Repr

/-- A non-collapsed context coordinate keeps the two latent channels separate. -/
structure TwoChannelContextCoordinate where
  adverse : Bool
  restorative : Bool
  resolution : ContextResolution
  deriving DecidableEq, Repr

def twoChannelContextCoordinate :
    ContextState -> TwoChannelContextCoordinate
  | ContextState.latent adverse restorative =>
      { adverse := adverse
        restorative := restorative
        resolution := ContextResolution.latent }
  | ContextState.ok =>
      { adverse := false
        restorative := true
        resolution := ContextResolution.ok }
  | ContextState.failed =>
      { adverse := true
        restorative := false
        resolution := ContextResolution.failed }

def stateOfTwoChannelContext :
    TwoChannelContextCoordinate -> ContextState
  | { adverse, restorative, resolution := ContextResolution.latent } =>
      ContextState.latent adverse restorative
  | { resolution := ContextResolution.ok, .. } => ContextState.ok
  | { resolution := ContextResolution.failed, .. } => ContextState.failed

def traceResponseOfTwoChannelContext
    (c : TwoChannelContextCoordinate) (actions : List ContextAction) :
    ContextObservation × BoundaryStatus :=
  process.traceResponse (stateOfTwoChannelContext c) actions

/-- The non-collapsed two-channel context coordinate preserves trace response. -/
def twoChannelContextModel :
    StateCoordinateTraceModel process TwoChannelContextCoordinate where
  coordinate := twoChannelContextCoordinate
  traceResponseOfCoordinate := traceResponseOfTwoChannelContext
  preserves_traceResponse := by
    intro s actions
    cases s <;> rfl

/-- The two-channel context model preserves the adverse-only recovery trace. -/
theorem twoChannelContext_preserves_adverseOnlyTrace :
    process.traceResponse adverseOnlyContext recoveryProbeTrace =
      traceResponseOfTwoChannelContext
        (twoChannelContextCoordinate adverseOnlyContext)
        recoveryProbeTrace :=
  rfl

/-- The two-channel context model preserves the restorative-only recovery trace. -/
theorem twoChannelContext_preserves_restorativeOnlyTrace :
    process.traceResponse restorativeOnlyContext recoveryProbeTrace =
      traceResponseOfTwoChannelContext
        (twoChannelContextCoordinate restorativeOnlyContext)
        recoveryProbeTrace :=
  rfl

end ToyContextProcess

namespace ToyJointProcess

/-- A latent joint context can resolve under a two-channel intervention. -/
inductive JointState where
  | latent (contextAdverse : Bool) (contextRestorative : Bool)
  | ok
  | failed
  deriving DecidableEq, Repr

/-- A joint intervention can carry adverse and restorative channels. -/
inductive JointAction where
  | pulse (actionAdverse : Bool) (actionRestorative : Bool)
  deriving DecidableEq, Repr

/-- Observations hide the latent channel split. -/
inductive JointObservation where
  | latent
  | green
  | red
  deriving DecidableEq, Repr

def observe : JointState -> JointObservation
  | JointState.latent _ _ => JointObservation.latent
  | JointState.ok => JointObservation.green
  | JointState.failed => JointObservation.red

def readout : JointState -> BoundaryStatus
  | JointState.latent _ _ => BoundaryStatus.stopped
  | JointState.ok => BoundaryStatus.viable
  | JointState.failed => BoundaryStatus.collapsed

def resolveLatent
    (contextAdverse contextRestorative actionAdverse actionRestorative :
      Bool) :
    JointState :=
  if actionRestorative && contextAdverse && !contextRestorative &&
      !actionAdverse then
    JointState.ok
  else if actionAdverse && contextRestorative && !contextAdverse &&
      !actionRestorative then
    JointState.failed
  else if (contextRestorative || actionRestorative) &&
      !(contextAdverse || actionAdverse) then
    JointState.ok
  else
    JointState.failed

def step : JointState -> JointAction -> JointState
  | JointState.latent contextAdverse contextRestorative,
      JointAction.pulse actionAdverse actionRestorative =>
      resolveLatent
        contextAdverse contextRestorative actionAdverse actionRestorative
  | JointState.ok, JointAction.pulse actionAdverse actionRestorative =>
      if actionAdverse && !actionRestorative then
        JointState.failed
      else
        JointState.ok
  | JointState.failed, JointAction.pulse actionAdverse actionRestorative =>
      if actionRestorative && !actionAdverse then
        JointState.ok
      else
        JointState.failed

def process :
    ObservationalPersistenceProcess
      JointState JointAction JointObservation where
  observe := observe
  step := step
  readout := readout

/--
A deliberately collapsed one-action alternative that cannot realize every
one-step response of the joint process at `failed`.
-/
def unitFrozenFailedProcess :
    ObservationalPersistenceProcess
      JointState Unit JointObservation where
  observe := observe
  step := fun _ _ => JointState.failed
  readout := readout

def contextAdverseOnly : JointState :=
  JointState.latent true false

def contextRestorativeOnly : JointState :=
  JointState.latent false true

def restorativePulse : JointAction :=
  JointAction.pulse false true

def adversePulse : JointAction :=
  JointAction.pulse true false

/--
The collapsed unit-action alternative misses the restorative response from
the failed state.
-/
theorem unitFrozenFailedProcess_misses_restorativeResponse_at_failed
    (targetAction : Unit) :
    unitFrozenFailedProcess.response JointState.failed targetAction ≠
      process.response JointState.failed restorativePulse := by
  cases targetAction
  decide

/--
Unit action collapse cannot provide the action translation needed to preserve
all one-step responses at the failed state.  This is the local red test for
the final `toAction` bottleneck: without response coverage, no translator can
be constructed.
-/
theorem no_unitAction_responsePreserving_toAction_at_failed :
    ¬
      ∃ toAction : JointAction -> Unit,
        forall action,
          unitFrozenFailedProcess.response
              JointState.failed (toAction action) =
            process.response JointState.failed action :=
  no_responsePreserving_toAction_without_actionResponseCoverage
    (A := process) (B := unitFrozenFailedProcess)
    (sA := JointState.failed) (sB := JointState.failed)
    ⟨restorativePulse,
      unitFrozenFailedProcess_misses_restorativeResponse_at_failed⟩

/--
The same collapsed alternative already fails the weaker role-free
response-image preservation condition.  This red test keeps the coverage layer
observational: the target action space simply lacks a one-step response that
the source process can observe at `failed`.
-/
theorem unitFrozenFailedProcess_not_responseImagePreserving_at_failed :
    ¬
      ResponseImagePreservationAt
        process unitFrozenFailedProcess
        JointState.failed JointState.failed :=
  no_responseImagePreservationAt_without_actionResponseCoverage
    (A := process) (B := unitFrozenFailedProcess)
    (sA := JointState.failed) (sB := JointState.failed)
    ⟨restorativePulse,
      unitFrozenFailedProcess_misses_restorativeResponse_at_failed⟩

/--
The collapsed unit-action alternative cannot even relate the failed state by a
role-free response-image simulation.  If it did, the simulation would derive
the response-image preservation already refuted above.
-/
theorem no_unitFrozenFailedProcess_responseImageSimulation_at_failed
    (simulation :
      ObservationalResponseImageSimulation
        process unitFrozenFailedProcess) :
    ¬ simulation.related JointState.failed JointState.failed := by
  intro hrelated
  exact unitFrozenFailedProcess_not_responseImagePreserving_at_failed
    (simulation.responseImagePreservationAt hrelated)

/--
The same collapse fails current-view response-image completeness at the failed
state pair.  The obstruction is still purely observational: the restorative
one-step response is missing from the collapsed target image.
-/
theorem unitFrozenFailedProcess_not_currentViewResponseImageComplete :
    ¬ CurrentViewResponseImageComplete process unitFrozenFailedProcess := by
  intro hcomplete
  exact unitFrozenFailedProcess_not_responseImagePreserving_at_failed
    (hcomplete (sA := JointState.failed) (sB := JointState.failed) rfl)

/--
The collapsed unit-action alternative also fails the finite-search boundary.
Finite candidate lists cannot repair a missing response image: any such search
would imply current-view response-image completeness, already refuted above.
-/
theorem unitFrozenFailedProcess_not_currentViewFiniteActionResponseSearch :
    CurrentViewFiniteActionResponseSearch process unitFrozenFailedProcess ->
      False := by
  intro finiteSearch
  exact unitFrozenFailedProcess_not_currentViewResponseImageComplete
    (CurrentViewFiniteActionResponseSearch.toCurrentViewResponseImageComplete
      finiteSearch)

/--
Bidirectional finite search is impossible for the collapsed alternative as
well, because its forward finite-search side is already red.
-/
theorem unitFrozenFailedProcess_not_currentViewBidirectionalFiniteActionResponseSearch :
    CurrentViewBidirectionalFiniteActionResponseSearch
        process unitFrozenFailedProcess ->
      False := by
  intro bidirectional
  exact unitFrozenFailedProcess_not_currentViewFiniteActionResponseSearch
    bidirectional.forward

/--
The collapsed alternative also fails the action-free trace-log image condition:
the singleton restorative source trace from `failed` has no target trace with
the same observed prefix log.
-/
theorem unitFrozenFailedProcess_not_traceLogImagePreserving_at_failed :
    ¬
      TraceLogImagePreservationAt
        process unitFrozenFailedProcess
        JointState.failed JointState.failed :=
  no_traceLogImagePreservationAt_without_actionResponseCoverage
    (A := process) (B := unitFrozenFailedProcess)
    (sA := JointState.failed) (sB := JointState.failed)
    ⟨restorativePulse,
      unitFrozenFailedProcess_misses_restorativeResponse_at_failed⟩

/--
The same collapse cannot satisfy the canonical trace-language image relation
at the failed state pair, because that relation includes trace-log image
preservation.
-/
theorem unitFrozenFailedProcess_not_traceLanguageImageRelated_at_failed :
    ¬
      traceLanguageImageRelated
        process unitFrozenFailedProcess
        JointState.failed JointState.failed := by
  intro hrelated
  exact unitFrozenFailedProcess_not_traceLogImagePreserving_at_failed
    (TraceLanguageImageRelated.traceLogImagePreservationAt hrelated)

/--
The same collapse cannot satisfy current-view trace-log language inclusion:
inclusion would imply trace-log image preservation at the failed state pair.
-/
theorem unitFrozenFailedProcess_not_currentViewTraceLogLanguageIncluded :
    ¬ CurrentViewTraceLogLanguageIncluded process unitFrozenFailedProcess := by
  intro hincluded
  have hcomplete :
      CurrentViewTraceImageComplete process unitFrozenFailedProcess :=
    CurrentViewTraceLogLanguageIncluded.toCurrentViewTraceImageComplete
      hincluded
  have htrace :
      TraceLogImagePreservationAt
        process unitFrozenFailedProcess
        JointState.failed JointState.failed :=
    hcomplete (sA := JointState.failed) (sB := JointState.failed) rfl
  exact unitFrozenFailedProcess_not_traceLogImagePreserving_at_failed htrace

/--
Current-view trace-log language equivalence is also impossible for the
collapsed alternative, since equivalence implies the failed inclusion above.
-/
theorem unitFrozenFailedProcess_not_currentViewTraceLogLanguageEquivalent :
    ¬ CurrentViewTraceLogLanguageEquivalent process unitFrozenFailedProcess := by
  intro hequivalent
  exact unitFrozenFailedProcess_not_currentViewTraceLogLanguageIncluded
    (CurrentViewTraceLogLanguageEquivalent.toIncluded hequivalent)

/--
The collapsed alternative also fails the local current-view step-image source:
from the same failed current view, no unit target action realizes the
restorative next view.
-/
theorem unitFrozenFailedProcess_not_currentViewStepImageComplete :
    ¬ CurrentViewStepImageComplete process unitFrozenFailedProcess := by
  intro hcomplete
  rcases hcomplete (sA := JointState.failed) (sB := JointState.failed)
      rfl restorativePulse with
    ⟨targetAction, hnextView⟩
  change
    unitFrozenFailedProcess.response JointState.failed targetAction =
      process.response JointState.failed restorativePulse at hnextView
  exact unitFrozenFailedProcess_misses_restorativeResponse_at_failed
    targetAction hnextView

/-- Explicit finite target-action candidates for the joint toy process. -/
def jointActionCandidates : List JointAction :=
  [JointAction.pulse false false,
    JointAction.pulse false true,
    JointAction.pulse true false,
    JointAction.pulse true true]

/-- Every joint action is present in the explicit finite candidate list. -/
theorem jointAction_mem_candidates
    (action : JointAction) :
    action ∈ jointActionCandidates := by
  cases action with
  | pulse actionAdverse actionRestorative =>
      cases actionAdverse <;> cases actionRestorative <;>
        simp [jointActionCandidates]

/--
The self joint process has finite action-response search coverage at `failed`.
This is the positive side of the previous `Unit` collapse red test.
-/
def jointFiniteActionResponseSearchAtFailed :
    FiniteActionResponseSearchAt
      process process JointState.failed JointState.failed where
  candidates := jointActionCandidates
  fallback := restorativePulse
  complete := by
    intro action
    exact ⟨action, jointAction_mem_candidates action, rfl⟩

/-- Finite search preserves every one-step response in the joint self-process. -/
theorem jointFiniteSearchToAction_preserves_response
    (action : JointAction) :
    process.response JointState.failed
        (FiniteActionResponseSearchAt.toAction
          jointFiniteActionResponseSearchAtFailed action) =
      process.response JointState.failed action :=
  FiniteActionResponseSearchAt.toAction_preserves_response
    jointFiniteActionResponseSearchAtFailed action

/-- The finite-search translator stays inside the explicit joint candidate list. -/
theorem jointFiniteSearchToAction_mem_candidates
    (action : JointAction) :
    FiniteActionResponseSearchAt.toAction
        jointFiniteActionResponseSearchAtFailed action ∈
      jointActionCandidates :=
  FiniteActionResponseSearchAt.toAction_mem_candidates
    jointFiniteActionResponseSearchAtFailed action

def restorativePulseTrace : List JointAction :=
  [restorativePulse]

def adversePulseTrace : List JointAction :=
  [adversePulse]

def adverseThenRestorativePulseTrace : List JointAction :=
  [adversePulse, restorativePulse]

def restorativeThenRestorativePulseTrace : List JointAction :=
  [restorativePulse, restorativePulse]

/-- The context aggregate forgets which latent channel is active. -/
def contextAggregate : JointState -> Nat
  | JointState.latent contextAdverse contextRestorative =>
      (if contextAdverse then 1 else 0) +
        (if contextRestorative then 1 else 0)
  | JointState.ok => 1
  | JointState.failed => 1

/-- The action aggregate forgets which intervention channel is active. -/
def actionAggregate : JointAction -> Nat
  | JointAction.pulse actionAdverse actionRestorative =>
      (if actionAdverse then 1 else 0) +
        (if actionRestorative then 1 else 0)

/-- The aggregate identifies the two latent joint contexts. -/
theorem contextAggregate_identifies_jointContexts :
    contextAggregate contextAdverseOnly =
      contextAggregate contextRestorativeOnly :=
  rfl

/-- The aggregate identifies the restorative and adverse one-pulse traces. -/
theorem actionAggregateTrace_identifies_jointTraces :
    restorativePulseTrace.map actionAggregate =
      adversePulseTrace.map actionAggregate :=
  rfl

/--
The action aggregate also identifies a joint trace that collapses and repairs
with a trace that stays viable.
-/
theorem actionAggregateTrace_identifies_jointRecoveredPrefix :
    adverseThenRestorativePulseTrace.map actionAggregate =
      restorativeThenRestorativePulseTrace.map actionAggregate :=
  rfl

/-- The joint recovered-prefix pair has the same final observed response. -/
theorem jointRecoveredPrefix_traceResponse_equal :
    process.traceResponse JointState.ok adverseThenRestorativePulseTrace =
      process.traceResponse JointState.ok restorativeThenRestorativePulseTrace :=
  rfl

/--
The same joint pair has different prefix logs: the left trace crosses the
collapsed boundary before the restorative pulse repairs it.
-/
theorem jointRecoveredPrefix_traceLog_distinguished :
    process.traceLog JointState.ok adverseThenRestorativePulseTrace ≠
      process.traceLog JointState.ok restorativeThenRestorativePulseTrace := by
  decide

def jointRecoveredPrefixFinalResponsePrefixLogGap :
    CollapsedFinalResponsePrefixLogGap process Nat Nat where
  leftState := JointState.ok
  rightState := JointState.ok
  leftActions := adverseThenRestorativePulseTrace
  rightActions := restorativeThenRestorativePulseTrace
  stateCoordinate := contextAggregate
  actionCoordinate := actionAggregate
  sameState := rfl
  sameTrace := actionAggregateTrace_identifies_jointRecoveredPrefix
  traceResponse_eq := jointRecoveredPrefix_traceResponse_equal
  traceLog_ne := jointRecoveredPrefix_traceLog_distinguished

theorem jointRecoveredPrefix_finalResponse_deletion_witness :
    process.traceResponse JointState.ok adverseThenRestorativePulseTrace =
        process.traceResponse
          JointState.ok restorativeThenRestorativePulseTrace ∧
      contextAggregate JointState.ok = contextAggregate JointState.ok ∧
      adverseThenRestorativePulseTrace.map actionAggregate =
        restorativeThenRestorativePulseTrace.map actionAggregate :=
  CollapsedFinalResponsePrefixLogGap.final_response_deletion_witness
    jointRecoveredPrefixFinalResponsePrefixLogGap

theorem jointRecoveredPrefix_gap_no_prefixLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  CollapsedFinalResponsePrefixLogGap.no_preserving_prefix_log_coordinate_model
    jointRecoveredPrefixFinalResponsePrefixLogGap

def jointChannelTraceLaw :
    TwoChannelTraceLaw process where
  adverseContext := contextAdverseOnly
  restorativeContext := contextRestorativeOnly
  restorativeIntervention := restorativePulse
  adverseIntervention := adversePulse
  restorativeResponse := (JointObservation.green, BoundaryStatus.viable)
  adverseResponse := (JointObservation.red, BoundaryStatus.collapsed)
  restorative_law := rfl
  adverse_law := rfl
  response_ne := by
    decide

def jointAggregateIdentification :
    TwoChannelAggregateIdentification process Nat Nat where
  law := jointChannelTraceLaw
  stateCoordinate := contextAggregate
  actionCoordinate := actionAggregate
  sameState := contextAggregate_identifies_jointContexts
  sameTrace := actionAggregateTrace_identifies_jointTraces

theorem jointAggregateTrace_distinguished :
    process.traceResponse contextAdverseOnly restorativePulseTrace ≠
      process.traceResponse contextRestorativeOnly adversePulseTrace :=
  jointChannelTraceLaw.traceResponse_ne

def jointObservedSplit :
    ObservedJointTraceSplit process :=
  jointChannelTraceLaw.observedJointTraceSplit

theorem jointObservedSplit_forces_not_both_collapsed
    {StateCoordinate : Type u} {ActionCoordinate : Type v}
    (R : JointCoordinateTraceModel process StateCoordinate ActionCoordinate) :
    ¬
      (R.stateCoordinate contextAdverseOnly =
          R.stateCoordinate contextRestorativeOnly ∧
        restorativePulseTrace.map R.actionCoordinate =
          adversePulseTrace.map R.actionCoordinate) :=
  jointObservedSplit.preserving_model_cannot_collapse_both R

def jointAggregateSplit :
    CollapsedJointTraceSplit process Nat Nat :=
  jointAggregateIdentification.collapsedSplit

theorem jointAggregateIdentification_no_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List Nat -> JointObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointAggregateIdentification.no_traceResponse_model

theorem jointAggregateIdentification_no_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointAggregateIdentification.no_traceLog_model

/--
No trace response rule depending only on collapsed context and action
aggregates can preserve both joint traces.
-/
theorem no_jointAggregate_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List Nat -> JointObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) := by
  exact jointAggregateIdentification_no_traceResponse_model

/--
No prefix-log rule depending only on collapsed context and action aggregates
can preserve both joint traces.
-/
theorem no_jointAggregate_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) := by
  exact jointAggregateIdentification_no_traceLog_model

inductive JointResolution where
  | latent
  | ok
  | failed
  deriving DecidableEq, Repr

/-- A non-collapsed joint state coordinate keeps both context channels. -/
structure TwoChannelJointStateCoordinate where
  contextAdverse : Bool
  contextRestorative : Bool
  resolution : JointResolution
  deriving DecidableEq, Repr

/-- A non-collapsed joint action coordinate keeps both intervention channels. -/
structure TwoChannelJointActionCoordinate where
  actionAdverse : Bool
  actionRestorative : Bool
  deriving DecidableEq, Repr

def twoChannelJointStateCoordinate :
    JointState -> TwoChannelJointStateCoordinate
  | JointState.latent contextAdverse contextRestorative =>
      { contextAdverse := contextAdverse
        contextRestorative := contextRestorative
        resolution := JointResolution.latent }
  | JointState.ok =>
      { contextAdverse := false
        contextRestorative := true
        resolution := JointResolution.ok }
  | JointState.failed =>
      { contextAdverse := true
        contextRestorative := false
        resolution := JointResolution.failed }

def twoChannelJointActionCoordinate :
    JointAction -> TwoChannelJointActionCoordinate
  | JointAction.pulse actionAdverse actionRestorative =>
      { actionAdverse := actionAdverse
        actionRestorative := actionRestorative }

def stateOfTwoChannelJoint :
    TwoChannelJointStateCoordinate -> JointState
  | { contextAdverse, contextRestorative,
      resolution := JointResolution.latent } =>
      JointState.latent contextAdverse contextRestorative
  | { resolution := JointResolution.ok, .. } => JointState.ok
  | { resolution := JointResolution.failed, .. } => JointState.failed

def actionOfTwoChannelJoint :
    TwoChannelJointActionCoordinate -> JointAction
  | { actionAdverse, actionRestorative } =>
      JointAction.pulse actionAdverse actionRestorative

def traceResponseOfTwoChannelJoint
    (stateCoordinate : TwoChannelJointStateCoordinate)
    (actionCoordinates : List TwoChannelJointActionCoordinate) :
    JointObservation × BoundaryStatus :=
  process.traceResponse
    (stateOfTwoChannelJoint stateCoordinate)
    (actionCoordinates.map actionOfTwoChannelJoint)

theorem stateOf_twoChannelJointStateCoordinate (s : JointState) :
    stateOfTwoChannelJoint (twoChannelJointStateCoordinate s) = s := by
  cases s with
  | latent _ _ => rfl
  | ok => rfl
  | failed => rfl

theorem actionOf_twoChannelJointActionCoordinate (a : JointAction) :
    actionOfTwoChannelJoint (twoChannelJointActionCoordinate a) = a := by
  cases a with
  | pulse _ _ => rfl

theorem map_actionOf_twoChannelJointActionCoordinate
    (actions : List JointAction) :
    (actions.map twoChannelJointActionCoordinate).map
        actionOfTwoChannelJoint =
      actions := by
  induction actions with
  | nil => rfl
  | cons action actions ih =>
      change
        actionOfTwoChannelJoint (twoChannelJointActionCoordinate action) ::
            ((actions.map twoChannelJointActionCoordinate).map
              actionOfTwoChannelJoint) =
          action :: actions
      rw [actionOf_twoChannelJointActionCoordinate action, ih]

def twoChannelJointDecodedModel :
    DecodedJointCoordinateModel
      process TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate where
  stateCoordinate := twoChannelJointStateCoordinate
  actionCoordinate := twoChannelJointActionCoordinate
  stateOfCoordinate := stateOfTwoChannelJoint
  actionOfCoordinate := actionOfTwoChannelJoint
  state_decode := stateOf_twoChannelJointStateCoordinate
  action_decode := actionOf_twoChannelJointActionCoordinate

/-- The non-collapsed two-channel joint coordinate preserves trace response. -/
def twoChannelJointModel :
    JointCoordinateTraceModel
      process TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate :=
  twoChannelJointDecodedModel.toJointCoordinateTraceModel

def jointSplitPackage :
    TwoChannelSplitPackage
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate :=
  TwoChannelSplitPackage.ofAggregateIdentification
    jointAggregateIdentification
    twoChannelJointDecodedModel

theorem jointSplitPackage_no_collapsed_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List Nat -> JointObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointSplitPackage.no_collapsed_traceResponse_model

theorem jointSplitPackage_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointSplitPackage.no_collapsed_traceLog_model

theorem jointSplitPackage_decoded_preserves_traceResponse
    (s : JointState) (actions : List JointAction) :
    process.traceResponse s actions =
      twoChannelJointDecodedModel.traceResponseOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointSplitPackage.decoded_preserves_traceResponse s actions

def burdenRoleReadout
    (_stateCoordinate : TwoChannelJointStateCoordinate)
    (actionCoordinates : List TwoChannelJointActionCoordinate) : Bool :=
  actionCoordinates.any (fun actionCoordinate => actionCoordinate.actionAdverse)

def supportRoleReadout
    (_stateCoordinate : TwoChannelJointStateCoordinate)
    (actionCoordinates : List TwoChannelJointActionCoordinate) : Bool :=
  actionCoordinates.any
    (fun actionCoordinate => actionCoordinate.actionRestorative)

def jointChannelRoleBridgeInputs :
    ChannelRoleBridgeInputs jointSplitPackage Bool Bool where
  burdenOfRun := burdenRoleReadout
  supportOfRun := supportRoleReadout
  adverseBurden := true
  restorativeSupport := true
  adverseTrace_burden := rfl
  restorativeTrace_support := rfl

def jointChannelRoleBridgeBoundary :
    ChannelRoleBridgeBoundary
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool where
  package := jointSplitPackage
  roleInputs := jointChannelRoleBridgeInputs

theorem jointChannelRoleBridge_no_collapsed_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List Nat -> JointObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointChannelRoleBridgeBoundary.no_collapsed_traceResponse_model

theorem jointChannelRoleBridge_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointChannelRoleBridgeBoundary.no_collapsed_traceLog_model

theorem jointChannelRoleBridge_decoded_preserves_traceResponse
    (s : JointState) (actions : List JointAction) :
    process.traceResponse s actions =
      twoChannelJointDecodedModel.traceResponseOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointChannelRoleBridgeBoundary.decoded_preserves_traceResponse s actions

theorem jointChannelRoleBridge_decoded_preserves_traceLog
    (s : JointState) (actions : List JointAction) :
    process.traceLog s actions =
      twoChannelJointDecodedModel.traceLogOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointChannelRoleBridgeBoundary.decoded_preserves_traceLog s actions

theorem jointChannelRoleBridge_adverseTrace_burden :
    burdenRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointChannelRoleBridgeBoundary.adverseTrace_burden

theorem jointChannelRoleBridge_restorativeTrace_support :
    supportRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointChannelRoleBridgeBoundary.restorativeTrace_support

def jointObservedBoundaryEventBridgeInputs :
    ChannelRoleBridgeInputs jointSplitPackage Bool Bool :=
  jointSplitPackage.observedBoundaryEventRoleInputs

def jointObservedBoundaryEventBridgeBoundary :
    ChannelRoleBridgeBoundary
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool :=
  jointSplitPackage.observedBoundaryEventBridgeBoundary

def jointObservedBoundaryEventRoleSeparationCandidate :
    PrefixSensitiveRoleSeparationCandidate
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool :=
  jointSplitPackage.observedBoundaryEventRoleSeparationCandidate

theorem jointObservedBoundaryEvent_adverseTrace_collapsedPrefix :
    jointSplitPackage.observedCollapsedPrefixRole
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  rfl

theorem jointObservedBoundaryEvent_restorativeTrace_viableFinal :
    jointSplitPackage.observedViableFinalRole
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  rfl

theorem jointObservedBoundaryEvent_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  PrefixSensitiveRoleSeparationCandidate.no_collapsed_traceLog_model
    jointObservedBoundaryEventRoleSeparationCandidate

def jointPrefixSensitiveRoleSeparationCandidate :
    PrefixSensitiveRoleSeparationCandidate
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool where
  bridge := jointChannelRoleBridgeBoundary

theorem jointPrefixCandidate_no_collapsed_traceResponse_model :
    ¬ Exists
      (fun traceResponseOfAggregate :
        Nat -> List Nat -> JointObservation × BoundaryStatus =>
          forall s actions,
            process.traceResponse s actions =
              traceResponseOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointPrefixSensitiveRoleSeparationCandidate.no_collapsed_traceResponse_model

theorem jointPrefixCandidate_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointPrefixSensitiveRoleSeparationCandidate.no_collapsed_traceLog_model

theorem jointPrefixCandidate_decoded_preserves_traceLog
    (s : JointState) (actions : List JointAction) :
    process.traceLog s actions =
      twoChannelJointDecodedModel.traceLogOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointPrefixSensitiveRoleSeparationCandidate.decoded_preserves_traceLog
    s actions

theorem jointPrefixCandidate_adverseTrace_burden :
    burdenRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointPrefixSensitiveRoleSeparationCandidate.adverseTrace_burden

theorem jointPrefixCandidate_restorativeTrace_support :
    supportRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointPrefixSensitiveRoleSeparationCandidate.restorativeTrace_support

/-- A minimal maintained-target name for the toy semantic bridge. -/
inductive JointMaintainedTarget where
  | responsivePersistence
  deriving DecidableEq, Repr

def maintainsJointTarget
    (s : JointState) (_target : JointMaintainedTarget) : Prop :=
  readout s = BoundaryStatus.viable

/--
Target semantics for the toy process.

This is supplied semantic interpretation: it says what target the viable
boundary readout certifies.  The observational process itself still has no
`K`, `V_K`, burden, or support fields.
-/
def jointTargetSemantics :
    ObservationalTargetSemantics process JointMaintainedTarget where
  maintainedTarget := JointMaintainedTarget.responsivePersistence
  maintains := maintainsJointTarget
  viable_implies_maintained := by
    intro s h
    exact h

def jointIdentityObservationMap :
    ObservationalResponseMap process process where
  toState := id
  toAction := id
  preserves_observation := by
    intro s
    rfl
  preserves_readout := by
    intro s
    rfl
  preserves_response := by
    intro s action
    rfl

def jointIdentityTargetMap :
    ObservationalTargetMap
      jointTargetSemantics
      jointTargetSemantics
      jointIdentityObservationMap where
  target_eq := rfl
  preserves_maintained_target := by
    intro s h
    exact h

theorem jointTargetSemantics_nontrivial :
    jointTargetSemantics.NontrivialReadout := by
  exact ⟨JointState.ok, rfl⟩

/--
Concrete toy bridge from prefix-sensitive anti-collapse to the semantic
`F/K/V_K` recovery kernel.
-/
def jointPrefixSemanticBridge :
    PrefixSensitiveSemanticBridge
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool JointMaintainedTarget where
  candidate := jointPrefixSensitiveRoleSeparationCandidate
  sourceSemantics := jointTargetSemantics
  targetSemantics := jointTargetSemantics
  observationMap := jointIdentityObservationMap
  targetMap := jointIdentityTargetMap
  sourceNontrivial := jointTargetSemantics_nontrivial

def jointObservedBoundaryEventSemanticBridge :
    PrefixSensitiveSemanticBridge
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool JointMaintainedTarget where
  candidate := jointObservedBoundaryEventRoleSeparationCandidate
  sourceSemantics := jointTargetSemantics
  targetSemantics := jointTargetSemantics
  observationMap := jointIdentityObservationMap
  targetMap := jointIdentityTargetMap
  sourceNontrivial := jointTargetSemantics_nontrivial

def jointObservationDerivedAlternativeConstructionBoundary :
    ObservationDerivedAlternativeConstructionBoundary
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      JointMaintainedTarget where
  package := jointSplitPackage
  sourceSemantics := jointTargetSemantics
  targetSemantics := jointTargetSemantics
  observationMap := jointIdentityObservationMap
  targetMap := jointIdentityTargetMap
  sourceNontrivial := jointTargetSemantics_nontrivial

theorem jointObservationDerivedConstruction_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  ObservationDerivedAlternativeConstructionBoundary.no_collapsed_traceLog_model
    jointObservationDerivedAlternativeConstructionBoundary

theorem jointObservationDerivedConstruction_decoded_preserves_traceLog
    (s : JointState) (actions : List JointAction) :
    process.traceLog s actions =
      twoChannelJointDecodedModel.traceLogOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  ObservationDerivedAlternativeConstructionBoundary.decoded_preserves_traceLog
    jointObservationDerivedAlternativeConstructionBoundary s actions

theorem jointObservationDerivedConstruction_viableRegion_nonempty :
    (PrefixSensitiveSemanticBridge.stateRealizationViability
      (ObservationDerivedAlternativeConstructionBoundary.toSemanticBridge
        jointObservationDerivedAlternativeConstructionBoundary)).viableRegion.Nonempty :=
  ObservationDerivedAlternativeConstructionBoundary.viableRegion_nonempty
    jointObservationDerivedAlternativeConstructionBoundary

theorem jointObservationDerivedConstruction_adverseTrace_collapsedPrefix :
    jointSplitPackage.observedCollapsedPrefixRole
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointObservedBoundaryEvent_adverseTrace_collapsedPrefix

theorem jointObservationDerivedConstruction_restorativeTrace_viableFinal :
    jointSplitPackage.observedViableFinalRole
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  jointObservedBoundaryEvent_restorativeTrace_viableFinal

def jointObservationDerivedSemanticBridge :
    PrefixSensitiveSemanticBridge
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool JointMaintainedTarget :=
  ObservationDerivedAlternativeConstructionBoundary.toSemanticBridge
    jointObservationDerivedAlternativeConstructionBoundary

def jointObservationDerivedFactorizationBoundary
    (accounting :
      PrefixSensitiveLogAccountingBridge jointObservationDerivedSemanticBridge) :
    ObservationDerivedFactorizationBoundary
      jointObservationDerivedAlternativeConstructionBoundary where
  logAccounting := accounting

theorem jointObservationDerivedFactorization_no_collapsed_traceLog_model
    (accounting :
      PrefixSensitiveLogAccountingBridge jointObservationDerivedSemanticBridge) :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  (jointObservationDerivedFactorizationBoundary
    accounting).no_collapsed_traceLog_model

theorem jointObservationDerivedFactorization_viableRegion_nonempty
    (accounting :
      PrefixSensitiveLogAccountingBridge jointObservationDerivedSemanticBridge) :
    (PrefixSensitiveCanonicalFactorizationBoundary.stateRealizationViability
      (ObservationDerivedFactorizationBoundary.toCanonicalFactorization
        (jointObservationDerivedFactorizationBoundary accounting))).viableRegion.Nonempty :=
  (jointObservationDerivedFactorizationBoundary accounting).viableRegion_nonempty

theorem jointObservationDerivedFactorization_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointObservationDerivedSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        accounting.burdenLossValue
            (jointSplitPackage.observedCollapsedPrefixRole
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (accounting.ratioOfRun stateCoordinate actionCoordinates) :=
  (jointObservationDerivedFactorizationBoundary
    accounting).burden_loss_has_log_form

theorem jointObservationDerivedFactorization_adverseTrace_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointObservationDerivedSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      accounting.burdenLossValue
          (jointSplitPackage.observedCollapsedPrefixRole
            ((jointObservationDerivedFactorizationBoundary
              accounting).toCanonicalFactorization.adverseTraceStateCoordinate)
            ((jointObservationDerivedFactorizationBoundary
              accounting).toCanonicalFactorization.adverseTraceActionCoordinates)) =
        -k * Real.log
          (accounting.ratioOfRun
            ((jointObservationDerivedFactorizationBoundary
              accounting).toCanonicalFactorization.adverseTraceStateCoordinate)
            ((jointObservationDerivedFactorizationBoundary
              accounting).toCanonicalFactorization.adverseTraceActionCoordinates)) :=
  (jointObservationDerivedFactorizationBoundary
    accounting).adverseTrace_burden_loss_has_log_form

def jointObservationDerivedBurdenSupportCandidateBoundary :
    ObservationDerivedBurdenSupportCandidateBoundary
      jointObservationDerivedAlternativeConstructionBoundary where
  adverseCollapsedPrefixActive :=
    jointObservationDerivedConstruction_adverseTrace_collapsedPrefix
  adverseViableFinalInactive := rfl
  restorativeCollapsedPrefixInactive := rfl
  restorativeViableFinalActive :=
    jointObservationDerivedConstruction_restorativeTrace_viableFinal

theorem jointObservationDerivedBurdenCandidate_distinguishes_runs :
    jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.burdenCandidate_distinguishes_runs

theorem jointObservationDerivedSupportCandidate_distinguishes_runs :
    jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.supportCandidate_distinguishes_runs

theorem jointObservationDerivedBurdenCandidate_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunRoleCoordinateModel
        jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.burden_candidate_coordinate_must_distinguish model

theorem jointObservationDerivedSupportCandidate_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunRoleCoordinateModel
        jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.support_candidate_coordinate_must_distinguish model

theorem jointObservationDerivedCandidateRolePair_distinguishes_runs :
    jointObservationDerivedBurdenSupportCandidateBoundary.candidateRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointObservationDerivedBurdenSupportCandidateBoundary.candidateRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.candidateRolePair_distinguishes_runs

theorem jointObservationDerivedCandidateRolePair_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunRolePairCoordinateModel
        jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedBurdenSupportCandidateBoundary
    |>.candidate_pair_coordinate_must_distinguish model

inductive JointPromotedBurdenCandidateRole where
  | noCollapsedPrefix
  | collapsedPrefix
  deriving DecidableEq, Repr

inductive JointPromotedSupportCandidateRole where
  | nonViableFinal
  | viableFinal
  deriving DecidableEq, Repr

def jointPromoteBurdenCandidate :
    Bool -> JointPromotedBurdenCandidateRole
  | false => JointPromotedBurdenCandidateRole.noCollapsedPrefix
  | true => JointPromotedBurdenCandidateRole.collapsedPrefix

def jointPromoteSupportCandidate :
    Bool -> JointPromotedSupportCandidateRole
  | false => JointPromotedSupportCandidateRole.nonViableFinal
  | true => JointPromotedSupportCandidateRole.viableFinal

def jointObservationDerivedPromotedRoleBoundary :
    ObservationDerivedPromotedRoleBoundary
      jointObservationDerivedBurdenSupportCandidateBoundary
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole where
  promoteBurden := jointPromoteBurdenCandidate
  promoteSupport := jointPromoteSupportCandidate
  promoted_adverse_ne_restorative := by
    decide

theorem jointObservationDerivedPromotedRolePair_distinguishes_runs :
    jointObservationDerivedPromotedRoleBoundary.promotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointObservationDerivedPromotedRoleBoundary.promotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedPromotedRoleBoundary
    |>.promotedRolePair_distinguishes_runs

theorem jointObservationDerivedPromotedRolePair_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunTypedRolePairCoordinateModel
        jointObservationDerivedPromotedRoleBoundary.promotedBurden
        jointObservationDerivedPromotedRoleBoundary.promotedSupport
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedPromotedRoleBoundary
    |>.promoted_pair_coordinate_must_distinguish model

def jointObservationDerivedPromotedRoleInputs :
    ChannelRoleBridgeInputs
      jointSplitPackage
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole :=
  jointObservationDerivedPromotedRoleBoundary.promotedRoleInputs

def jointObservationDerivedPromotedBridgeBoundary :
    ChannelRoleBridgeBoundary
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridgeBoundary

def jointObservationDerivedPromotedRoleSeparationCandidate :
    PrefixSensitiveRoleSeparationCandidate
      process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole :=
  jointObservationDerivedPromotedRoleBoundary.promotedRoleSeparationCandidate

theorem jointObservationDerivedPromotedBridge_adverseTrace_burden :
    jointObservationDerivedPromotedRoleInputs.burdenOfRun
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      JointPromotedBurdenCandidateRole.collapsedPrefix :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridge_adverseTrace_burden

theorem jointObservationDerivedPromotedBridge_restorativeTrace_support :
    jointObservationDerivedPromotedRoleInputs.supportOfRun
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      JointPromotedSupportCandidateRole.viableFinal :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridge_restorativeTrace_support

theorem jointObservationDerivedPromotedBridge_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridge_no_collapsed_traceLog_model

def jointObservationDerivedPromotedSemanticBridge :
    PrefixSensitiveSemanticBridge
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole
      JointMaintainedTarget :=
  jointObservationDerivedPromotedRoleBoundary.promotedSemanticBridge

theorem jointObservationDerivedPromotedSemantic_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointObservationDerivedPromotedRoleBoundary
    |>.promotedSemantic_no_collapsed_traceLog_model

theorem jointObservationDerivedPromotedSemantic_viableRegion_nonempty :
    jointObservationDerivedPromotedSemanticBridge
      |>.stateRealizationViability.viableRegion.Nonempty :=
  jointObservationDerivedPromotedRoleBoundary
    |>.promotedSemantic_viableRegion_nonempty

theorem jointObservationDerivedPromotedSemantic_adverseTrace_burden :
    jointObservationDerivedPromotedRoleInputs.burdenOfRun
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      JointPromotedBurdenCandidateRole.collapsedPrefix :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridge_adverseTrace_burden

theorem jointObservationDerivedPromotedSemantic_restorativeTrace_support :
    jointObservationDerivedPromotedRoleInputs.supportOfRun
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      JointPromotedSupportCandidateRole.viableFinal :=
  jointObservationDerivedPromotedRoleBoundary.promotedBridge_restorativeTrace_support

def jointObservationDerivedPromotedFactorizationBoundary
    (accounting :
      PrefixSensitiveLogAccountingBridge
        jointObservationDerivedPromotedSemanticBridge) :
    ObservationDerivedPromotedFactorizationBoundary
      jointObservationDerivedPromotedRoleBoundary where
  logAccounting := accounting

theorem jointObservationDerivedPromotedFactorization_no_collapsed_traceLog_model
    (accounting :
      PrefixSensitiveLogAccountingBridge
        jointObservationDerivedPromotedSemanticBridge) :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  (jointObservationDerivedPromotedFactorizationBoundary
    accounting).no_collapsed_traceLog_model

theorem jointObservationDerivedPromotedFactorization_viableRegion_nonempty
    (accounting :
      PrefixSensitiveLogAccountingBridge
        jointObservationDerivedPromotedSemanticBridge) :
    (jointObservationDerivedPromotedFactorizationBoundary
      accounting).toCanonicalFactorization
      |>.stateRealizationViability.viableRegion.Nonempty :=
  (jointObservationDerivedPromotedFactorizationBoundary
    accounting).viableRegion_nonempty

theorem jointObservationDerivedPromotedFactorization_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge
        jointObservationDerivedPromotedSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        accounting.burdenLossValue
            (jointObservationDerivedPromotedRoleInputs.burdenOfRun
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (accounting.ratioOfRun
              stateCoordinate actionCoordinates) :=
  (jointObservationDerivedPromotedFactorizationBoundary
    accounting).burden_loss_has_log_form

theorem
    jointObservationDerivedPromotedFactorization_adverseTrace_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge
        jointObservationDerivedPromotedSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      accounting.burdenLossValue
          (jointObservationDerivedPromotedRoleInputs.burdenOfRun
            (twoChannelJointDecodedModel.stateCoordinate
              jointChannelTraceLaw.restorativeContext)
            (jointChannelTraceLaw.adverseTrace.map
              twoChannelJointDecodedModel.actionCoordinate)) =
        -k * Real.log
          (accounting.ratioOfRun
            (twoChannelJointDecodedModel.stateCoordinate
              jointChannelTraceLaw.restorativeContext)
            (jointChannelTraceLaw.adverseTrace.map
              twoChannelJointDecodedModel.actionCoordinate)) :=
  (jointObservationDerivedPromotedFactorizationBoundary
    accounting).adverseTrace_burden_loss_has_log_form

def jointObservationDerivedComponentwisePromotionBoundary :
    ObservationDerivedComponentwisePromotionBoundary
      jointObservationDerivedBurdenSupportCandidateBoundary
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole where
  promoteBurden := jointPromoteBurdenCandidate
  promoteSupport := jointPromoteSupportCandidate
  burden_true_ne_false := by
    decide
  support_false_ne_true := by
    decide

def jointObservationDerivedComponentwisePromotedRoleBoundary :
    ObservationDerivedPromotedRoleBoundary
      jointObservationDerivedBurdenSupportCandidateBoundary
      JointPromotedBurdenCandidateRole
      JointPromotedSupportCandidateRole :=
  jointObservationDerivedComponentwisePromotionBoundary.toPromotedRoleBoundary

theorem jointObservationDerivedComponentwisePromotedRolePair_distinguishes_runs :
    jointObservationDerivedComponentwisePromotedRoleBoundary.promotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointObservationDerivedComponentwisePromotedRoleBoundary.promotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedComponentwisePromotionBoundary
    |>.promotedRolePair_distinguishes_runs

theorem jointObservationDerivedComponentwisePromotedRolePair_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunTypedRolePairCoordinateModel
        jointObservationDerivedComponentwisePromotedRoleBoundary.promotedBurden
        jointObservationDerivedComponentwisePromotedRoleBoundary.promotedSupport
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointObservationDerivedComponentwisePromotionBoundary
    |>.promoted_pair_coordinate_must_distinguish model

theorem jointConstantPromotion_identifies_adverse_restorative :
    constantPromotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary
        JointPromotedBurdenCandidateRole.noCollapsedPrefix
        JointPromotedSupportCandidateRole.nonViableFinal
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates =
      constantPromotedRolePair
        jointObservationDerivedBurdenSupportCandidateBoundary
        JointPromotedBurdenCandidateRole.noCollapsedPrefix
        JointPromotedSupportCandidateRole.nonViableFinal
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  constantPromotedRolePair_identifies_adverse_restorative
    jointObservationDerivedBurdenSupportCandidateBoundary
    JointPromotedBurdenCandidateRole.noCollapsedPrefix
    JointPromotedSupportCandidateRole.nonViableFinal

def jointPromotedAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 1
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 1
  burdenScore_separates_adverse_restorative := by
    decide
  supportScore_separates_adverse_restorative := by
    decide
  adverse_total_eq_restorative := by
    decide

theorem jointPromotedTotalScore_identifies_adverse_restorative :
    jointPromotedAdditiveScoreBoundary.totalScoreOfRun
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates =
      jointPromotedAdditiveScoreBoundary.totalScoreOfRun
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedAdditiveScoreBoundary
    |>.adverseTrace_totalScore_eq_restorativeTrace

theorem jointPromotedComponentScore_distinguishes_runs :
    jointPromotedAdditiveScoreBoundary.componentScoreOfRun
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      jointPromotedAdditiveScoreBoundary.componentScoreOfRun
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedAdditiveScoreBoundary.componentScore_distinguishes_runs

theorem jointPromoted_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedAdditiveScoreBoundary.no_totalScore_componentScore_model

theorem jointPromoted_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedAdditiveScoreBoundary.no_totalScore_promotedRolePair_model

def jointPromotedIndicatorScoreLawBoundary :
    PromotedRoleIndicatorScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 1
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 1
  burdenScore_active := by
    rfl
  burdenScore_inactive := by
    rfl
  supportScore_active := by
    rfl
  supportScore_inactive := by
    rfl

def jointPromotedIndicatorAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedIndicatorScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedIndicator_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedIndicatorAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedIndicatorAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedIndicatorScoreLawBoundary.no_totalScore_componentScore_model

theorem jointPromotedIndicator_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedIndicatorAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedIndicatorScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem jointPromotedIndicator_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedIndicatorAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedIndicatorScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  scoreUnit := 2
  scoreUnit_ne_zero := by
    decide
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 2
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 2
  burdenScore_active := by
    rfl
  burdenScore_inactive := by
    rfl
  supportScore_active := by
    rfl
  supportScore_inactive := by
    rfl

def jointPromotedCommonUnitAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCommonUnitScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedCommonUnit_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedCommonUnitAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedCommonUnitAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedCommonUnitScoreLawBoundary.no_totalScore_componentScore_model

theorem jointPromotedCommonUnit_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedCommonUnitAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedCommonUnitScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem jointPromotedCommonUnit_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedCommonUnitAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedCommonUnitScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 3
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 3
  burdenScore_inactive := by
    rfl
  supportScore_inactive := by
    rfl
  active_scores_match := by
    rfl
  active_score_ne_zero := by
    decide

def jointPromotedBalancedZeroCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedBalancedZeroScoreLawBoundary.toCommonUnitScoreLawBoundary

def jointPromotedBalancedZeroAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedBalancedZeroScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedBalancedZero_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedBalancedZeroAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedBalancedZeroAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedBalancedZeroScoreLawBoundary.no_totalScore_componentScore_model

theorem jointPromotedBalancedZero_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedBalancedZeroAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedBalancedZeroScoreLawBoundary.no_totalScore_promotedRolePair_model

theorem jointPromotedBalancedZero_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedBalancedZeroAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedBalancedZeroScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedObservableBurdenProbeScore :
    TwoChannelJointStateCoordinate ->
      List TwoChannelJointActionCoordinate -> Nat :=
  fun stateCoordinate actionCoordinates =>
    if jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        stateCoordinate actionCoordinates then
      5
    else
      0

def jointPromotedObservableSupportProbeScore :
    TwoChannelJointStateCoordinate ->
      List TwoChannelJointActionCoordinate -> Nat :=
  fun stateCoordinate actionCoordinates =>
    if jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        stateCoordinate actionCoordinates then
      5
    else
      0

def jointPromotedObservableScoreProbeBoundary :
    PromotedRoleObservableScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_reads_probe := by
    intro stateCoordinate actionCoordinates
    rw [ObservationDerivedPromotedRoleBoundary.promotedBurden,
      jointPromotedObservableBurdenProbeScore]
    cases
      jointObservationDerivedBurdenSupportCandidateBoundary.burdenCandidate
        stateCoordinate actionCoordinates <;> rfl
  supportScore_reads_probe := by
    intro stateCoordinate actionCoordinates
    rw [ObservationDerivedPromotedRoleBoundary.promotedSupport,
      jointPromotedObservableSupportProbeScore]
    cases
      jointObservationDerivedBurdenSupportCandidateBoundary.supportCandidate
        stateCoordinate actionCoordinates <;> rfl
  burdenInactive_probe_zero := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_restorative_inactive]
    decide
  supportInactive_probe_zero := by
    rw [jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_adverse_inactive]
    decide
  active_probe_scores_match := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_adverse_active,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_restorative_active]
  active_probe_ne_zero := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_adverse_active]
    decide

def jointPromotedObservableBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedObservableScoreProbeBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedObservableCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedObservableScoreProbeBoundary.toCommonUnitScoreLawBoundary

def jointPromotedObservableAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedObservableScoreProbeBoundary.toAdditiveScoreBoundary

theorem jointPromotedObservable_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedObservableAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedObservableAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedObservableScoreProbeBoundary.no_totalScore_componentScore_model

theorem jointPromotedObservable_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedObservableAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedObservableScoreProbeBoundary.no_totalScore_promotedRolePair_model

theorem jointPromotedObservable_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedObservableAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedObservableScoreProbeBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedDecisiveTraceScoreProbeBoundary :
    PromotedRoleDecisiveTraceScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_probe := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_adverse_active]
    decide
  burdenScore_restorative_reads_probe := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_restorative_inactive]
    decide
  supportScore_adverse_reads_probe := by
    rw [jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_adverse_inactive]
    decide
  supportScore_restorative_reads_probe := by
    rw [jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_restorative_active]
    decide
  burdenInactive_probe_zero := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_restorative_inactive]
    decide
  supportInactive_probe_zero := by
    rw [jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_adverse_inactive]
    decide
  active_probe_scores_match := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointPromotedObservableSupportProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_adverse_active,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.supportCandidate_restorative_active]
  active_probe_ne_zero := by
    rw [jointPromotedObservableBurdenProbeScore,
      jointObservationDerivedBurdenSupportCandidateBoundary
        |>.burdenCandidate_adverse_active]
    decide

def jointPromotedDecisiveTraceBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedDecisiveTraceScoreProbeBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedDecisiveTraceCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedDecisiveTraceScoreProbeBoundary.toCommonUnitScoreLawBoundary

def jointPromotedDecisiveTraceAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedDecisiveTraceScoreProbeBoundary.toAdditiveScoreBoundary

theorem jointPromotedDecisiveTrace_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedDecisiveTraceAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedDecisiveTraceAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedDecisiveTraceScoreProbeBoundary.no_totalScore_componentScore_model

theorem jointPromotedDecisiveTrace_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedDecisiveTraceAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedDecisiveTraceScoreProbeBoundary.no_totalScore_promotedRolePair_model

theorem jointPromotedDecisiveTrace_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedDecisiveTraceAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedDecisiveTraceScoreProbeBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedTraceLogBurdenScore :
    List (JointObservation × BoundaryStatus) -> Nat :=
  fun traceLog =>
    if TwoChannelSplitPackage.hasCollapsedPrefix traceLog then
      5
    else
      0

def jointPromotedTraceLogSupportScore :
    List (JointObservation × BoundaryStatus) -> Nat :=
  fun traceLog =>
    if TwoChannelSplitPackage.finalLogReadoutViable traceLog then
      5
    else
      0

def jointPromotedTraceLocalScoreReadoutBoundary :
    PromotedRoleTraceLocalScoreReadoutBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenTraceScore := jointPromotedTraceLogBurdenScore
  supportTraceScore := jointPromotedTraceLogSupportScore
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_trace := by
    rfl
  burdenProbe_adverse_reads_trace := by
    rfl
  burdenScore_restorative_reads_trace := by
    rfl
  burdenProbe_restorative_reads_trace := by
    rfl
  supportScore_adverse_reads_trace := by
    rfl
  supportProbe_adverse_reads_trace := by
    rfl
  supportScore_restorative_reads_trace := by
    rfl
  supportProbe_restorative_reads_trace := by
    rfl
  burdenInactive_trace_zero := by
    rfl
  supportInactive_trace_zero := by
    rfl
  active_trace_scores_match := by
    rfl
  active_trace_score_ne_zero := by
    decide

def jointPromotedTraceLocalDecisiveTraceScoreProbeBoundary :
    PromotedRoleDecisiveTraceScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceLocalScoreReadoutBoundary
    |>.toDecisiveTraceScoreProbeBoundary

def jointPromotedTraceLocalBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceLocalScoreReadoutBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedTraceLocalCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceLocalScoreReadoutBoundary.toCommonUnitScoreLawBoundary

def jointPromotedTraceLocalAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceLocalScoreReadoutBoundary.toAdditiveScoreBoundary

theorem jointPromotedTraceLocal_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedTraceLocalAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedTraceLocalAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedTraceLocalScoreReadoutBoundary
    |>.no_totalScore_componentScore_model

theorem jointPromotedTraceLocal_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedTraceLocalAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedTraceLocalScoreReadoutBoundary
    |>.no_totalScore_promotedRolePair_model

theorem jointPromotedTraceLocal_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedTraceLocalAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedTraceLocalScoreReadoutBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedTraceEventScoreLawBoundary :
    PromotedRoleTraceEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  scoreUnit := 5
  scoreUnit_ne_zero := by
    decide
  burdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_eventScore := by
    rfl
  burdenProbe_adverse_reads_eventScore := by
    rfl
  burdenScore_restorative_reads_eventScore := by
    rfl
  burdenProbe_restorative_reads_eventScore := by
    rfl
  supportScore_adverse_reads_eventScore := by
    rfl
  supportProbe_adverse_reads_eventScore := by
    rfl
  supportScore_restorative_reads_eventScore := by
    rfl
  supportProbe_restorative_reads_eventScore := by
    rfl
  burdenTraceEvent_adverse_active := by
    rfl
  burdenTraceEvent_restorative_inactive := by
    rfl
  supportTraceEvent_adverse_inactive := by
    rfl
  supportTraceEvent_restorative_active := by
    rfl

def jointPromotedTraceEventLocalScoreReadoutBoundary :
    PromotedRoleTraceLocalScoreReadoutBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceEventScoreLawBoundary
    |>.toTraceLocalScoreReadoutBoundary

def jointPromotedTraceEventDecisiveTraceScoreProbeBoundary :
    PromotedRoleDecisiveTraceScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceEventScoreLawBoundary
    |>.toDecisiveTraceScoreProbeBoundary

def jointPromotedTraceEventBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceEventScoreLawBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedTraceEventCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceEventScoreLawBoundary.toCommonUnitScoreLawBoundary

def jointPromotedTraceEventAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedTraceEventScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedTraceEvent_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedTraceEventAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedTraceEventAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedTraceEventScoreLawBoundary
    |>.no_totalScore_componentScore_model

theorem jointPromotedTraceEvent_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedTraceEventAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedTraceEventScoreLawBoundary
    |>.no_totalScore_promotedRolePair_model

theorem jointPromotedTraceEvent_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedTraceEventAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedTraceEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedAdversePrefixLog :
    List (JointObservation × BoundaryStatus) :=
  [(JointObservation.red, BoundaryStatus.collapsed)]

def jointPromotedRestorativePrefixLog :
    List (JointObservation × BoundaryStatus) :=
  [(JointObservation.green, BoundaryStatus.viable)]

def jointPromotedPrefixLogEventActivityBoundary :
    PromotedRolePrefixLogEventActivityBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  adverseTraceLog := jointPromotedAdversePrefixLog
  restorativeTraceLog := jointPromotedRestorativePrefixLog
  adverseTraceLog_eq := by
    rfl
  restorativeTraceLog_eq := by
    rfl
  burdenTraceEvent_adverse_log_active := by
    rfl
  burdenTraceEvent_restorative_log_inactive := by
    rfl
  supportTraceEvent_adverse_log_inactive := by
    rfl
  supportTraceEvent_restorative_log_active := by
    rfl

def jointPromotedPrefixLogEventScoreLawBoundary :
    PromotedRolePrefixLogEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  activity := jointPromotedPrefixLogEventActivityBoundary
  scoreUnit := 5
  scoreUnit_ne_zero := by
    decide
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_eventScore := by
    rfl
  burdenProbe_adverse_reads_eventScore := by
    rfl
  burdenScore_restorative_reads_eventScore := by
    rfl
  burdenProbe_restorative_reads_eventScore := by
    rfl
  supportScore_adverse_reads_eventScore := by
    rfl
  supportProbe_adverse_reads_eventScore := by
    rfl
  supportScore_restorative_reads_eventScore := by
    rfl
  supportProbe_restorative_reads_eventScore := by
    rfl

def jointPromotedPrefixLogTraceEventScoreLawBoundary :
    PromotedRoleTraceEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary.toTraceEventScoreLawBoundary

def jointPromotedPrefixLogTraceLocalScoreReadoutBoundary :
    PromotedRoleTraceLocalScoreReadoutBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary
    |>.toTraceLocalScoreReadoutBoundary

def jointPromotedPrefixLogDecisiveTraceScoreProbeBoundary :
    PromotedRoleDecisiveTraceScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary
    |>.toDecisiveTraceScoreProbeBoundary

def jointPromotedPrefixLogBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedPrefixLogCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary.toCommonUnitScoreLawBoundary

def jointPromotedPrefixLogAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPrefixLogEventScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedPrefixLog_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedPrefixLogAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedPrefixLogAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedPrefixLogEventScoreLawBoundary
    |>.no_totalScore_componentScore_model

theorem jointPromotedPrefixLog_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedPrefixLogAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedPrefixLogEventScoreLawBoundary
    |>.no_totalScore_promotedRolePair_model

theorem jointPromotedPrefixLog_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedPrefixLogAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedPrefixLogEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedCanonicalPrefixEventPreservationBoundary :
    PromotedRoleCanonicalPrefixEventPreservationBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  adverseTraceLog := jointPromotedAdversePrefixLog
  restorativeTraceLog := jointPromotedRestorativePrefixLog
  adverseTraceLog_eq := by
    rfl
  restorativeTraceLog_eq := by
    rfl
  burdenEvent_preservation := {
    preserves_adverse := by
      rfl
    preserves_restorative := by
      rfl }
  supportEvent_preservation := {
    preserves_adverse := by
      rfl
    preserves_restorative := by
      rfl }
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointPromotedPreservedCanonicalPrefixEventAgreementBoundary :
    PromotedRoleCanonicalPrefixEventAgreementBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventPreservationBoundary
    |>.toCanonicalPrefixEventAgreementBoundary

theorem jointPromotedPreservedCanonical_burdenEvent_decisive_logs_distinguish :
    TwoChannelSplitPackage.hasCollapsedPrefix
        jointPromotedAdversePrefixLog ≠
      TwoChannelSplitPackage.hasCollapsedPrefix
        jointPromotedRestorativePrefixLog :=
  jointPromotedCanonicalPrefixEventPreservationBoundary
    |>.burdenEvent_decisive_logs_distinguish

theorem jointPromotedPreservedCanonical_supportEvent_decisive_logs_distinguish :
    TwoChannelSplitPackage.finalLogReadoutViable
        jointPromotedAdversePrefixLog ≠
      TwoChannelSplitPackage.finalLogReadoutViable
        jointPromotedRestorativePrefixLog :=
  jointPromotedCanonicalPrefixEventPreservationBoundary
    |>.supportEvent_decisive_logs_distinguish

def jointPromotedPreservedCanonicalPrefixEventScoreLawBoundary :
    PromotedRoleCanonicalPrefixEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  agreement := jointPromotedPreservedCanonicalPrefixEventAgreementBoundary
  scoreUnit := 5
  scoreUnit_ne_zero := by
    decide
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_canonicalScore := by
    rfl
  burdenProbe_adverse_reads_canonicalScore := by
    rfl
  burdenScore_restorative_reads_canonicalScore := by
    rfl
  burdenProbe_restorative_reads_canonicalScore := by
    rfl
  supportScore_adverse_reads_canonicalScore := by
    rfl
  supportProbe_adverse_reads_canonicalScore := by
    rfl
  supportScore_restorative_reads_canonicalScore := by
    rfl
  supportProbe_restorative_reads_canonicalScore := by
    rfl

def jointPromotedPreservedCanonicalAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedPreservedCanonicalPrefixEventScoreLawBoundary
    |>.toAdditiveScoreBoundary

theorem jointPromotedPreservedCanonical_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedPreservedCanonicalAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedPreservedCanonicalAdditiveScoreBoundary
                |>.totalScoreOfRun stateCoordinate actionCoordinates)) :=
  jointPromotedPreservedCanonicalPrefixEventScoreLawBoundary
    |>.no_totalScore_componentScore_model

theorem jointPromotedPreservedCanonical_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedPreservedCanonicalAdditiveScoreBoundary
                |>.totalScoreOfRun stateCoordinate actionCoordinates)) :=
  jointPromotedPreservedCanonicalPrefixEventScoreLawBoundary
    |>.no_totalScore_promotedRolePair_model

theorem jointPromotedPreservedCanonical_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedPreservedCanonicalAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedPreservedCanonicalPrefixEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

def jointPromotedCanonicalPrefixEventAgreementBoundary :
    PromotedRoleCanonicalPrefixEventAgreementBoundary
      jointObservationDerivedPromotedRoleBoundary where
  burdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurdenTraceEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportTraceEvent := TwoChannelSplitPackage.finalLogReadoutViable
  adverseTraceLog := jointPromotedAdversePrefixLog
  restorativeTraceLog := jointPromotedRestorativePrefixLog
  adverseTraceLog_eq := by
    rfl
  restorativeTraceLog_eq := by
    rfl
  burdenEvent_agrees_adverse := by
    rfl
  burdenEvent_agrees_restorative := by
    rfl
  supportEvent_agrees_adverse := by
    rfl
  supportEvent_agrees_restorative := by
    rfl
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointPromotedCanonicalPrefixEventScoreLawBoundary :
    PromotedRoleCanonicalPrefixEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary where
  agreement := jointPromotedCanonicalPrefixEventAgreementBoundary
  scoreUnit := 5
  scoreUnit_ne_zero := by
    decide
  burdenProbeScore := jointPromotedObservableBurdenProbeScore
  supportProbeScore := jointPromotedObservableSupportProbeScore
  burdenScore
    | JointPromotedBurdenCandidateRole.noCollapsedPrefix => 0
    | JointPromotedBurdenCandidateRole.collapsedPrefix => 5
  supportScore
    | JointPromotedSupportCandidateRole.nonViableFinal => 0
    | JointPromotedSupportCandidateRole.viableFinal => 5
  burdenScore_adverse_reads_canonicalScore := by
    rfl
  burdenProbe_adverse_reads_canonicalScore := by
    rfl
  burdenScore_restorative_reads_canonicalScore := by
    rfl
  burdenProbe_restorative_reads_canonicalScore := by
    rfl
  supportScore_adverse_reads_canonicalScore := by
    rfl
  supportProbe_adverse_reads_canonicalScore := by
    rfl
  supportScore_restorative_reads_canonicalScore := by
    rfl
  supportProbe_restorative_reads_canonicalScore := by
    rfl

def jointPromotedCanonicalPrefixLogEventScoreLawBoundary :
    PromotedRolePrefixLogEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.toPrefixLogEventScoreLawBoundary

def jointPromotedCanonicalTraceEventScoreLawBoundary :
    PromotedRoleTraceEventScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.toTraceEventScoreLawBoundary

def jointPromotedCanonicalTraceLocalScoreReadoutBoundary :
    PromotedRoleTraceLocalScoreReadoutBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.toTraceLocalScoreReadoutBoundary

def jointPromotedCanonicalDecisiveTraceScoreProbeBoundary :
    PromotedRoleDecisiveTraceScoreProbeBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.toDecisiveTraceScoreProbeBoundary

def jointPromotedCanonicalBalancedZeroScoreLawBoundary :
    PromotedRoleBalancedZeroScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary.toBalancedZeroScoreLawBoundary

def jointPromotedCanonicalCommonUnitScoreLawBoundary :
    PromotedRoleCommonUnitScoreLawBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary.toCommonUnitScoreLawBoundary

def jointPromotedCanonicalAdditiveScoreBoundary :
    PromotedRoleAdditiveScoreBoundary
      jointObservationDerivedPromotedRoleBoundary :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary.toAdditiveScoreBoundary

theorem jointPromotedCanonical_no_totalScore_componentScore_model :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        forall stateCoordinate actionCoordinates,
          jointPromotedCanonicalAdditiveScoreBoundary.componentScoreOfRun
              stateCoordinate actionCoordinates =
            componentOfTotal
              (jointPromotedCanonicalAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.no_totalScore_componentScore_model

theorem jointPromotedCanonical_no_totalScore_promotedRolePair_model :
    ¬ Exists
      (fun rolePairOfTotal :
        Nat -> JointPromotedBurdenCandidateRole ×
          JointPromotedSupportCandidateRole =>
        forall stateCoordinate actionCoordinates,
          jointObservationDerivedPromotedRoleBoundary.promotedRolePair
              stateCoordinate actionCoordinates =
            rolePairOfTotal
              (jointPromotedCanonicalAdditiveScoreBoundary.totalScoreOfRun
                stateCoordinate actionCoordinates)) :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.no_totalScore_promotedRolePair_model

theorem jointPromotedCanonical_componentScore_coordinate_must_distinguish
    {RunCoordinate : Type q}
    (model :
      RunComponentScoreCoordinateModel
        jointPromotedCanonicalAdditiveScoreBoundary.componentScoreOfRun
        RunCoordinate) :
    model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.adverseTraceActionCoordinates ≠
      model.coordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceStateCoordinate
        jointObservationDerivedBurdenSupportCandidateBoundary.restorativeTraceActionCoordinates :=
  jointPromotedCanonicalPrefixEventScoreLawBoundary
    |>.componentScore_coordinate_must_distinguish model

theorem jointPrefixSemanticBridge_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointPrefixSemanticBridge.no_collapsed_traceLog_model

theorem jointObservedBoundaryEventSemanticBridge_no_collapsed_traceLog_model :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  jointObservedBoundaryEventSemanticBridge.no_collapsed_traceLog_model

theorem jointPrefixSemanticBridge_decoded_preserves_traceLog
    (s : JointState) (actions : List JointAction) :
    process.traceLog s actions =
      twoChannelJointDecodedModel.traceLogOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointPrefixSemanticBridge.decoded_preserves_traceLog s actions

theorem jointObservedBoundaryEventSemanticBridge_decoded_preserves_traceLog
    (s : JointState) (actions : List JointAction) :
    process.traceLog s actions =
      twoChannelJointDecodedModel.traceLogOfCoordinates
        (twoChannelJointDecodedModel.stateCoordinate s)
        (actions.map twoChannelJointDecodedModel.actionCoordinate) :=
  jointObservedBoundaryEventSemanticBridge.decoded_preserves_traceLog s actions

theorem jointPrefixSemanticBridge_viableRegion_nonempty :
    jointPrefixSemanticBridge.stateRealizationViability.viableRegion.Nonempty :=
  jointPrefixSemanticBridge.viableRegion_nonempty

theorem jointObservedBoundaryEventSemanticBridge_viableRegion_nonempty :
    (PrefixSensitiveSemanticBridge.stateRealizationViability
      jointObservedBoundaryEventSemanticBridge).viableRegion.Nonempty :=
  jointObservedBoundaryEventSemanticBridge.viableRegion_nonempty

theorem jointPrefixSemanticBridge_viable_implies_maintained_target
    (k : jointPrefixSemanticBridge.stateRealizationViability.K)
    (hk :
      k ∈ jointPrefixSemanticBridge.stateRealizationViability.viableRegion) :
    jointTargetSemantics.maintains
      (jointPrefixSemanticBridge.stateRealizationViability.carrier k)
      jointTargetSemantics.maintainedTarget :=
  jointPrefixSemanticBridge.viable_implies_maintained_target k hk

theorem jointPrefixLogAccountingBridge_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        accounting.burdenLossValue
            (jointPrefixSemanticBridge.candidate.bridge.roleInputs.burdenOfRun
              stateCoordinate actionCoordinates) =
          -k * Real.log
            (accounting.ratioOfRun stateCoordinate actionCoordinates) :=
  accounting.burden_loss_has_log_form

theorem jointPrefixLogAccountingBridge_adverseTrace_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      accounting.burdenLossValue
          (jointPrefixSemanticBridge.candidate.bridge.roleInputs.burdenOfRun
            (jointPrefixSemanticBridge.candidate.bridge.package.decodedModel.stateCoordinate
              jointPrefixSemanticBridge.candidate.bridge.package.law.restorativeContext)
            (jointPrefixSemanticBridge.candidate.bridge.package.law.adverseTrace.map
              jointPrefixSemanticBridge.candidate.bridge.package.decodedModel.actionCoordinate)) =
        -k * Real.log
          (accounting.ratioOfRun
            (jointPrefixSemanticBridge.candidate.bridge.package.decodedModel.stateCoordinate
              jointPrefixSemanticBridge.candidate.bridge.package.law.restorativeContext)
            (jointPrefixSemanticBridge.candidate.bridge.package.law.adverseTrace.map
              jointPrefixSemanticBridge.candidate.bridge.package.decodedModel.actionCoordinate)) :=
  accounting.adverseTrace_burden_loss_has_log_form

def jointCanonicalFactorizationBoundary
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    PrefixSensitiveCanonicalFactorizationBoundary
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool JointMaintainedTarget where
  semanticBridge := jointPrefixSemanticBridge
  logAccounting := accounting

theorem jointCanonicalFactorization_no_collapsed_traceLog_model
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ¬ Exists
      (fun traceLogOfAggregate :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (contextAggregate s)
                (actions.map actionAggregate)) :=
  (jointCanonicalFactorizationBoundary accounting).no_collapsed_traceLog_model

theorem jointCanonicalFactorization_viableRegion_nonempty
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    (jointCanonicalFactorizationBoundary
        accounting).stateRealizationViability.viableRegion.Nonempty :=
  (jointCanonicalFactorizationBoundary accounting).viableRegion_nonempty

theorem jointCanonicalFactorization_adverseTrace_burden
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    burdenRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.restorativeContext)
        (jointChannelTraceLaw.adverseTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  (jointCanonicalFactorizationBoundary accounting).adverseTrace_burden

theorem jointCanonicalFactorization_restorativeTrace_support
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    supportRoleReadout
        (twoChannelJointDecodedModel.stateCoordinate
          jointChannelTraceLaw.adverseContext)
        (jointChannelTraceLaw.restorativeTrace.map
          twoChannelJointDecodedModel.actionCoordinate) =
      true :=
  (jointCanonicalFactorizationBoundary accounting).restorativeTrace_support

theorem jointCanonicalFactorization_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      ∀ stateCoordinate actionCoordinates,
        accounting.burdenLossValue
            (burdenRoleReadout stateCoordinate actionCoordinates) =
          -k * Real.log
            (accounting.ratioOfRun stateCoordinate actionCoordinates) :=
  (jointCanonicalFactorizationBoundary accounting).burden_loss_has_log_form

theorem jointCanonicalFactorization_adverseTrace_burden_loss_has_log_form
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ k : ℝ, 0 ≤ k ∧
      accounting.burdenLossValue
          (burdenRoleReadout
            (twoChannelJointDecodedModel.stateCoordinate
              jointChannelTraceLaw.restorativeContext)
            (jointChannelTraceLaw.adverseTrace.map
              twoChannelJointDecodedModel.actionCoordinate)) =
        -k * Real.log
          (accounting.ratioOfRun
            (twoChannelJointDecodedModel.stateCoordinate
              jointChannelTraceLaw.restorativeContext)
            (jointChannelTraceLaw.adverseTrace.map
              twoChannelJointDecodedModel.actionCoordinate)) :=
  (jointCanonicalFactorizationBoundary
    accounting).adverseTrace_burden_loss_has_log_form

def jointAlternativeQuantifiedFactorizationStatementBoundary
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    AlternativeQuantifiedFactorizationStatementBoundary
      process process Nat Nat
      TwoChannelJointStateCoordinate
      TwoChannelJointActionCoordinate
      Bool Bool JointMaintainedTarget where
  semanticBridge := jointPrefixSemanticBridge
  logAccounting := accounting

theorem jointAlternativeQuantifiedFactorization_produces_surface
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        process process Nat Nat
        TwoChannelJointStateCoordinate
        TwoChannelJointActionCoordinate
        Bool Bool JointMaintainedTarget,
      (¬ Exists
        (fun traceLogOfAggregate :
          Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfAggregate
                (factorization.collapsedStateCoordinate s)
                (actions.map factorization.collapsedActionCoordinate))) ∧
      factorization.stateRealizationViability.viableRegion.Nonempty ∧
      (∃ k : ℝ, 0 ≤ k ∧
        ∀ stateCoordinate actionCoordinates,
          factorization.logAccounting.burdenLossValue
              (factorization.burdenOfRun
                stateCoordinate actionCoordinates) =
            -k * Real.log
              (factorization.logAccounting.ratioOfRun
                stateCoordinate actionCoordinates)) :=
  (jointAlternativeQuantifiedFactorizationStatementBoundary
    accounting).produces_factorization_surface

theorem jointAlternativeQuantifiedFactorization_adverseTrace_log_accounting
    (accounting :
      PrefixSensitiveLogAccountingBridge jointPrefixSemanticBridge) :
    ∃ factorization :
      PrefixSensitiveCanonicalFactorizationBoundary
        process process Nat Nat
        TwoChannelJointStateCoordinate
        TwoChannelJointActionCoordinate
        Bool Bool JointMaintainedTarget,
      ∃ k : ℝ, 0 ≤ k ∧
        factorization.logAccounting.burdenLossValue
            (factorization.burdenOfRun
              factorization.adverseTraceStateCoordinate
              factorization.adverseTraceActionCoordinates) =
          -k * Real.log
            (factorization.logAccounting.ratioOfRun
              factorization.adverseTraceStateCoordinate
              factorization.adverseTraceActionCoordinates) :=
  (jointAlternativeQuantifiedFactorizationStatementBoundary
    accounting).produces_adverse_trace_log_accounting

theorem twoChannelJoint_preserves_adverseRestorativeTrace :
    process.traceResponse contextAdverseOnly restorativePulseTrace =
      traceResponseOfTwoChannelJoint
        (twoChannelJointStateCoordinate contextAdverseOnly)
        (restorativePulseTrace.map twoChannelJointActionCoordinate) :=
  rfl

theorem twoChannelJoint_preserves_restorativeAdverseTrace :
    process.traceResponse contextRestorativeOnly adversePulseTrace =
      traceResponseOfTwoChannelJoint
        (twoChannelJointStateCoordinate contextRestorativeOnly)
        (adversePulseTrace.map twoChannelJointActionCoordinate) :=
  rfl

end ToyJointProcess

end Persistence.StructuralPersistence
