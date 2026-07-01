import Persistence.StructuralPersistenceG1ObservationalCore

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-!
# G1 Composite Score Forcing Core

This file starts the vertical step after the G2 score/threshold readout lane.

The previous G2 observational forcing core showed that a single real-valued
score must distinguish two interventions when prefix-log preservation forces
them apart.  This file addresses the next, different question: when two
decisive runs have the same total score but different burden/support component
traces, a total-score-only readout cannot preserve the component trace or the
observed prefix log.

This is still not the full `L/B` and `M` theorem.  The component scores are
candidate burden/support scores supplied as functions on actions.  The point is
the anti-collapse shape: total scalar equality is compatible with component
separation, and a component-coordinate readout can separate the decisive runs
where a total-only readout cannot.
-/

namespace Persistence.StructuralPersistence

universe u v w x y

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}
variable {StateCoordinate : Type x} {ActionCoordinate : Type y}

namespace CompositeScoreTrace

/-- Candidate burden/support component coordinates for an action trace. -/
def componentTrace
    (burdenScore supportScore : Action -> Nat) :
    List Action -> List (Nat × Nat) :=
  fun actions => actions.map (fun action => (burdenScore action, supportScore action))

/-- Total scalar trace obtained by forgetting the component split. -/
def totalTrace
    (burdenScore supportScore : Action -> Nat) :
    List Action -> List Nat :=
  fun actions => actions.map (fun action => burdenScore action + supportScore action)

end CompositeScoreTrace

/--
A two-channel observational law whose two decisive runs have the same total
score trace but different candidate burden/support component traces.

The fields deliberately keep the component scores supplied.  This structure is
not yet a derivation of `L/B` and `M`; it is the anti-collapse boundary needed
before that stronger theorem can be claimed.
-/
structure TwoChannelCompositeScoreLaw
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  law : TwoChannelTraceLaw P
  burdenScore : Action -> Nat
  supportScore : Action -> Nat
  same_totalTrace :
    CompositeScoreTrace.totalTrace burdenScore supportScore law.restorativeTrace =
      CompositeScoreTrace.totalTrace burdenScore supportScore law.adverseTrace
  componentTrace_ne :
    CompositeScoreTrace.componentTrace burdenScore supportScore
        law.restorativeTrace ≠
      CompositeScoreTrace.componentTrace burdenScore supportScore law.adverseTrace

namespace TwoChannelCompositeScoreLaw

variable (C : TwoChannelCompositeScoreLaw P)

/-- The component coordinate assigned to one action. -/
def componentCoordinate (action : Action) : Nat × Nat :=
  (C.burdenScore action, C.supportScore action)

/-- The total scalar assigned to one action. -/
def totalCoordinate (action : Action) : Nat :=
  C.burdenScore action + C.supportScore action

/-- Component trace of the restorative decisive run. -/
def restorativeComponentTrace : List (Nat × Nat) :=
  CompositeScoreTrace.componentTrace C.burdenScore C.supportScore
    C.law.restorativeTrace

/-- Component trace of the adverse decisive run. -/
def adverseComponentTrace : List (Nat × Nat) :=
  CompositeScoreTrace.componentTrace C.burdenScore C.supportScore
    C.law.adverseTrace

/-- Total trace of the restorative decisive run. -/
def restorativeTotalTrace : List Nat :=
  CompositeScoreTrace.totalTrace C.burdenScore C.supportScore
    C.law.restorativeTrace

/-- Total trace of the adverse decisive run. -/
def adverseTotalTrace : List Nat :=
  CompositeScoreTrace.totalTrace C.burdenScore C.supportScore
    C.law.adverseTrace

/-- The two decisive runs have equal total scalar traces. -/
theorem restorativeTotalTrace_eq_adverseTotalTrace :
    C.restorativeTotalTrace = C.adverseTotalTrace :=
  C.same_totalTrace

/-- The two decisive runs keep different component traces. -/
theorem restorativeComponentTrace_ne_adverseComponentTrace :
    C.restorativeComponentTrace ≠ C.adverseComponentTrace :=
  C.componentTrace_ne

/--
No decoder from the total scalar trace alone can recover the component trace
on both decisive runs.

This is the core scalar-collapse red test: the total traces are equal, while
the component traces are not.
-/
theorem no_totalTrace_componentTrace_decoder :
    ¬ Exists
      (fun componentOfTotal : List Nat -> List (Nat × Nat) =>
        componentOfTotal C.restorativeTotalTrace =
            C.restorativeComponentTrace ∧
          componentOfTotal C.adverseTotalTrace =
            C.adverseComponentTrace) := by
  intro h
  rcases h with ⟨componentOfTotal, hrest, hadv⟩
  exact
    C.restorativeComponentTrace_ne_adverseComponentTrace
      (calc
        C.restorativeComponentTrace =
            componentOfTotal C.restorativeTotalTrace := hrest.symm
        _ = componentOfTotal C.adverseTotalTrace := by
          rw [C.restorativeTotalTrace_eq_adverseTotalTrace]
        _ = C.adverseComponentTrace := hadv)

/--
A total-score-only prefix-log model cannot preserve the two decisive
observational traces when the contexts are also identified.

This connects the same total-score collapse to the existing prefix-log
anti-collapse theorem from `TwoChannelTraceLaw`.
-/
theorem no_totalTrace_prefixLog_model
    (stateCoordinate : State -> StateCoordinate)
    (sameState :
      stateCoordinate C.law.adverseContext =
        stateCoordinate C.law.restorativeContext) :
    ¬ Exists
      (fun traceLogOfTotal :
        StateCoordinate -> List Nat -> List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfTotal
                (stateCoordinate s)
                (actions.map C.totalCoordinate)) :=
  CollapsedJointTraceLogSplit.no_preserving_joint_coordinate_traceLog_model
    (C.law.collapsedJointTraceLogSplit
      stateCoordinate C.totalCoordinate sameState C.same_totalTrace)

/--
A component-coordinate readout that separates the two decisive traces.

This is not a global model for every action trace.  It is the positive side of
the local red test: once the component trace is retained, the two decisive
runs can be read apart.
-/
def decisiveComponentTraceLog :
    List (Nat × Nat) -> List (Observation × BoundaryStatus) :=
  fun components =>
    if components = C.restorativeComponentTrace then
      P.traceLog C.law.adverseContext C.law.restorativeTrace
    else if components = C.adverseComponentTrace then
      P.traceLog C.law.restorativeContext C.law.adverseTrace
    else
      []

theorem decisiveComponentTraceLog_restorative :
    C.decisiveComponentTraceLog C.restorativeComponentTrace =
      P.traceLog C.law.adverseContext C.law.restorativeTrace := by
  unfold decisiveComponentTraceLog
  rw [if_pos rfl]

theorem decisiveComponentTraceLog_adverse :
    C.decisiveComponentTraceLog C.adverseComponentTrace =
      P.traceLog C.law.restorativeContext C.law.adverseTrace := by
  have hne :
      C.adverseComponentTrace ≠ C.restorativeComponentTrace := by
    intro h
    exact C.restorativeComponentTrace_ne_adverseComponentTrace h.symm
  unfold decisiveComponentTraceLog
  rw [if_neg hne, if_pos rfl]

/--
There exists a component-trace readout preserving both decisive prefix logs.
-/
theorem exists_componentTrace_decisive_readout :
    ∃ readout : List (Nat × Nat) -> List (Observation × BoundaryStatus),
      readout C.restorativeComponentTrace =
          P.traceLog C.law.adverseContext C.law.restorativeTrace ∧
        readout C.adverseComponentTrace =
          P.traceLog C.law.restorativeContext C.law.adverseTrace :=
  ⟨C.decisiveComponentTraceLog,
    C.decisiveComponentTraceLog_restorative,
    C.decisiveComponentTraceLog_adverse⟩

end TwoChannelCompositeScoreLaw

/--
Observable channel readouts that construct decisive component scores.

The readouts are Boolean classifiers on actions.  They are still supplied
source laws, but the numeric component scores are no longer arbitrary inputs:
they are obtained by reading the channel events with a shared nonzero unit.
This is a local source boundary, not a global derivation of `L/B` and `M`.
-/
structure TwoChannelComponentScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  law : TwoChannelTraceLaw P
  scoreUnit : Nat
  scoreUnit_ne_zero : scoreUnit ≠ 0
  burdenChannel : Action -> Bool
  supportChannel : Action -> Bool
  burdenChannel_restorative_inactive :
    burdenChannel law.restorativeIntervention = false
  burdenChannel_adverse_active :
    burdenChannel law.adverseIntervention = true
  supportChannel_restorative_active :
    supportChannel law.restorativeIntervention = true
  supportChannel_adverse_inactive :
    supportChannel law.adverseIntervention = false

namespace TwoChannelComponentScoreSource

variable (source : TwoChannelComponentScoreSource P)

def burdenScore (action : Action) : Nat :=
  boolEventScore source.scoreUnit (source.burdenChannel action)

def supportScore (action : Action) : Nat :=
  boolEventScore source.scoreUnit (source.supportChannel action)

theorem burdenScore_restorative :
    source.burdenScore (source.law).restorativeIntervention = 0 := by
  rw [burdenScore, source.burdenChannel_restorative_inactive, boolEventScore]

theorem burdenScore_adverse :
    source.burdenScore (source.law).adverseIntervention =
      source.scoreUnit := by
  rw [burdenScore, source.burdenChannel_adverse_active, boolEventScore]

theorem supportScore_restorative :
    source.supportScore (source.law).restorativeIntervention =
      source.scoreUnit := by
  rw [supportScore, source.supportChannel_restorative_active, boolEventScore]

theorem supportScore_adverse :
    source.supportScore (source.law).adverseIntervention = 0 := by
  rw [supportScore, source.supportChannel_adverse_inactive, boolEventScore]

theorem restorativeTotal_eq_adverseTotal :
    source.burdenScore (source.law).restorativeIntervention +
        source.supportScore (source.law).restorativeIntervention =
      source.burdenScore (source.law).adverseIntervention +
        source.supportScore (source.law).adverseIntervention := by
  rw [source.burdenScore_restorative, source.supportScore_restorative,
    source.burdenScore_adverse, source.supportScore_adverse]
  exact Nat.zero_add source.scoreUnit

theorem componentPair_restorative_ne_adverse :
    (source.burdenScore (source.law).restorativeIntervention,
        source.supportScore (source.law).restorativeIntervention) ≠
      (source.burdenScore (source.law).adverseIntervention,
        source.supportScore (source.law).adverseIntervention) := by
  intro h
  have hunit0 : source.scoreUnit = 0 := by
    have hsecond :
        source.supportScore (source.law).restorativeIntervention =
          source.supportScore (source.law).adverseIntervention :=
      (Prod.ext_iff.mp h).2
    calc
      source.scoreUnit =
          source.supportScore (source.law).restorativeIntervention :=
        source.supportScore_restorative.symm
      _ = source.supportScore (source.law).adverseIntervention := hsecond
      _ = 0 := source.supportScore_adverse
  exact source.scoreUnit_ne_zero hunit0

def toCompositeScoreLaw :
    TwoChannelCompositeScoreLaw P where
  law := source.law
  burdenScore := source.burdenScore
  supportScore := source.supportScore
  same_totalTrace := by
    unfold TwoChannelTraceLaw.restorativeTrace TwoChannelTraceLaw.adverseTrace
    change
      [source.burdenScore (source.law).restorativeIntervention +
          source.supportScore (source.law).restorativeIntervention] =
        [source.burdenScore (source.law).adverseIntervention +
          source.supportScore (source.law).adverseIntervention]
    rw [source.restorativeTotal_eq_adverseTotal]
  componentTrace_ne := by
    unfold TwoChannelTraceLaw.restorativeTrace TwoChannelTraceLaw.adverseTrace
    intro h
    exact
      source.componentPair_restorative_ne_adverse
        (List.cons.inj h).1

theorem no_totalTrace_componentTrace_decoder :
    ¬ Exists
      (fun componentOfTotal : List Nat -> List (Nat × Nat) =>
        componentOfTotal source.toCompositeScoreLaw.restorativeTotalTrace =
            source.toCompositeScoreLaw.restorativeComponentTrace ∧
          componentOfTotal source.toCompositeScoreLaw.adverseTotalTrace =
            source.toCompositeScoreLaw.adverseComponentTrace) :=
  source.toCompositeScoreLaw.no_totalTrace_componentTrace_decoder

theorem no_totalTrace_prefixLog_model
    (stateCoordinate : State -> StateCoordinate)
    (sameState :
      stateCoordinate (source.law).adverseContext =
        stateCoordinate (source.law).restorativeContext) :
    ¬ Exists
      (fun traceLogOfTotal :
        StateCoordinate -> List Nat -> List (Observation × BoundaryStatus) =>
          forall s actions,
            P.traceLog s actions =
              traceLogOfTotal
                (stateCoordinate s)
                (actions.map source.toCompositeScoreLaw.totalCoordinate)) :=
  source.toCompositeScoreLaw.no_totalTrace_prefixLog_model
    stateCoordinate sameState

theorem exists_componentTrace_decisive_readout :
    ∃ readout : List (Nat × Nat) -> List (Observation × BoundaryStatus),
      readout source.toCompositeScoreLaw.restorativeComponentTrace =
          P.traceLog (source.law).adverseContext (source.law).restorativeTrace ∧
        readout source.toCompositeScoreLaw.adverseComponentTrace =
          P.traceLog (source.law).restorativeContext (source.law).adverseTrace :=
  source.toCompositeScoreLaw.exists_componentTrace_decisive_readout

end TwoChannelComponentScoreSource

/--
Prefix-log event source for local component scores.

Unlike `TwoChannelComponentScoreSource`, this structure does not read channels
from actions.  It reads two Boolean events from the observed prefix logs of the
decisive adverse/restorative runs, then constructs the local component score
pair from those events.

This is still scoped to the two decisive logs.  It is not a global derivation
of full `L/B` and qualified support `M`, but it moves the component split from
supplied action-score functions to observation-derived event scores.
-/
structure TwoChannelTraceEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  law : TwoChannelTraceLaw P
  burdenEvent : List (Observation × BoundaryStatus) -> Bool
  supportEvent : List (Observation × BoundaryStatus) -> Bool
  burdenEvent_adverse_active :
    burdenEvent (P.traceLog law.restorativeContext law.adverseTrace) = true
  burdenEvent_restorative_inactive :
    burdenEvent (P.traceLog law.adverseContext law.restorativeTrace) = false
  supportEvent_adverse_inactive :
    supportEvent (P.traceLog law.restorativeContext law.adverseTrace) = false
  supportEvent_restorative_active :
    supportEvent (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelTraceEventScoreSource

variable (source : TwoChannelTraceEventScoreSource P)

def adverseTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).restorativeContext (source.law).adverseTrace

def restorativeTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).adverseContext (source.law).restorativeTrace

def burdenScoreOfLog (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  boolEventScore 1 (source.burdenEvent traceLog)

def supportScoreOfLog (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  boolEventScore 1 (source.supportEvent traceLog)

def componentScoreOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat × Nat :=
  (source.burdenScoreOfLog traceLog, source.supportScoreOfLog traceLog)

def totalScoreOfLog (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  (source.componentScoreOfLog traceLog).1 +
    (source.componentScoreOfLog traceLog).2

theorem adverse_componentScoreOfLog :
    source.componentScoreOfLog source.adverseTraceLog = (1, 0) := by
  unfold componentScoreOfLog burdenScoreOfLog supportScoreOfLog
    adverseTraceLog
  rw [source.burdenEvent_adverse_active,
    source.supportEvent_adverse_inactive]
  rfl

theorem restorative_componentScoreOfLog :
    source.componentScoreOfLog source.restorativeTraceLog = (0, 1) := by
  unfold componentScoreOfLog burdenScoreOfLog supportScoreOfLog
    restorativeTraceLog
  rw [source.burdenEvent_restorative_inactive,
    source.supportEvent_restorative_active]
  rfl

theorem adverse_totalScoreOfLog :
    source.totalScoreOfLog source.adverseTraceLog = 1 := by
  unfold totalScoreOfLog
  rw [source.adverse_componentScoreOfLog]
  rfl

theorem restorative_totalScoreOfLog :
    source.totalScoreOfLog source.restorativeTraceLog = 1 := by
  unfold totalScoreOfLog
  rw [source.restorative_componentScoreOfLog]
  rfl

theorem totalScoreOfLog_eq :
    source.totalScoreOfLog source.adverseTraceLog =
      source.totalScoreOfLog source.restorativeTraceLog := by
  rw [source.adverse_totalScoreOfLog, source.restorative_totalScoreOfLog]

theorem componentScoreOfLog_ne :
    source.componentScoreOfLog source.adverseTraceLog ≠
      source.componentScoreOfLog source.restorativeTraceLog := by
  rw [source.adverse_componentScoreOfLog,
    source.restorative_componentScoreOfLog]
  decide

/--
Observed total event score alone cannot recover the two observed component
scores.
-/
theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal (source.totalScoreOfLog source.adverseTraceLog) =
            source.componentScoreOfLog source.adverseTraceLog ∧
          componentOfTotal
              (source.totalScoreOfLog source.restorativeTraceLog) =
            source.componentScoreOfLog source.restorativeTraceLog) := by
  intro h
  rcases h with ⟨componentOfTotal, hadv, hrest⟩
  exact
    source.componentScoreOfLog_ne
      (calc
        source.componentScoreOfLog source.adverseTraceLog =
            componentOfTotal
              (source.totalScoreOfLog source.adverseTraceLog) := hadv.symm
        _ = componentOfTotal
              (source.totalScoreOfLog source.restorativeTraceLog) := by
          rw [source.totalScoreOfLog_eq]
        _ = source.componentScoreOfLog source.restorativeTraceLog := hrest)

/--
Observed total event score alone cannot recover both decisive prefix logs.
-/
theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal (source.totalScoreOfLog source.adverseTraceLog) =
            source.adverseTraceLog ∧
          traceLogOfTotal
              (source.totalScoreOfLog source.restorativeTraceLog) =
            source.restorativeTraceLog) := by
  intro h
  rcases h with ⟨traceLogOfTotal, hadv, hrest⟩
  have hlogs :
      source.restorativeTraceLog = source.adverseTraceLog := by
    calc
      source.restorativeTraceLog =
          traceLogOfTotal
            (source.totalScoreOfLog source.restorativeTraceLog) := hrest.symm
      _ = traceLogOfTotal
            (source.totalScoreOfLog source.adverseTraceLog) := by
        rw [source.totalScoreOfLog_eq]
      _ = source.adverseTraceLog := hadv
  exact (source.law).traceLog_ne hlogs

def componentTraceLogReadout :
    Nat × Nat -> List (Observation × BoundaryStatus) :=
  fun component =>
    if component = source.componentScoreOfLog source.adverseTraceLog then
      source.adverseTraceLog
    else if component =
        source.componentScoreOfLog source.restorativeTraceLog then
      source.restorativeTraceLog
    else
      []

theorem componentTraceLogReadout_adverse :
    source.componentTraceLogReadout
        (source.componentScoreOfLog source.adverseTraceLog) =
      source.adverseTraceLog := by
  unfold componentTraceLogReadout
  rw [if_pos rfl]

theorem componentTraceLogReadout_restorative :
    source.componentTraceLogReadout
        (source.componentScoreOfLog source.restorativeTraceLog) =
      source.restorativeTraceLog := by
  have hne :
      source.componentScoreOfLog source.restorativeTraceLog ≠
        source.componentScoreOfLog source.adverseTraceLog := by
    intro h
    exact source.componentScoreOfLog_ne h.symm
  unfold componentTraceLogReadout
  rw [if_neg hne, if_pos rfl]

theorem exists_componentTraceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      readout (source.componentScoreOfLog source.adverseTraceLog) =
          source.adverseTraceLog ∧
        readout (source.componentScoreOfLog source.restorativeTraceLog) =
          source.restorativeTraceLog :=
  ⟨source.componentTraceLogReadout,
    source.componentTraceLogReadout_adverse,
    source.componentTraceLogReadout_restorative⟩

/--
The first component alone separates the two decisive logs.

This is an explicit overclaim guard: the local two-log witness does not prove
that every possible scalar coordinate fails.  Unrestricted scalar encodings can
pick out one component.  The no-go theorems below therefore restrict the scalar
to a role-blind total-style readout.
-/
def burdenOnlyScalarOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  (source.componentScoreOfLog traceLog).1

theorem burdenOnlyScalarOfLog_adverse :
    source.burdenOnlyScalarOfLog source.adverseTraceLog = 1 := by
  unfold burdenOnlyScalarOfLog
  rw [source.adverse_componentScoreOfLog]

theorem burdenOnlyScalarOfLog_restorative :
    source.burdenOnlyScalarOfLog source.restorativeTraceLog = 0 := by
  unfold burdenOnlyScalarOfLog
  rw [source.restorative_componentScoreOfLog]

theorem burdenOnlyScalarOfLog_distinguishes :
    source.burdenOnlyScalarOfLog source.adverseTraceLog ≠
      source.burdenOnlyScalarOfLog source.restorativeTraceLog := by
  rw [source.burdenOnlyScalarOfLog_adverse,
    source.burdenOnlyScalarOfLog_restorative]
  decide

def burdenOnlyTraceLogReadout
    (score : Nat) : List (Observation × BoundaryStatus) :=
  if score = 1 then
    source.adverseTraceLog
  else if score = 0 then
    source.restorativeTraceLog
  else
    []

theorem burdenOnlyTraceLogReadout_adverse :
    source.burdenOnlyTraceLogReadout
        (source.burdenOnlyScalarOfLog source.adverseTraceLog) =
      source.adverseTraceLog := by
  rw [source.burdenOnlyScalarOfLog_adverse]
  unfold burdenOnlyTraceLogReadout
  rw [if_pos rfl]

theorem burdenOnlyTraceLogReadout_restorative :
    source.burdenOnlyTraceLogReadout
        (source.burdenOnlyScalarOfLog source.restorativeTraceLog) =
      source.restorativeTraceLog := by
  rw [source.burdenOnlyScalarOfLog_restorative]
  unfold burdenOnlyTraceLogReadout
  rw [if_neg (by decide : 0 ≠ 1), if_pos rfl]

theorem exists_burdenOnlyScalar_traceLog_readout :
    ∃ readout : Nat -> List (Observation × BoundaryStatus),
      readout (source.burdenOnlyScalarOfLog source.adverseTraceLog) =
          source.adverseTraceLog ∧
        readout (source.burdenOnlyScalarOfLog source.restorativeTraceLog) =
          source.restorativeTraceLog :=
  ⟨source.burdenOnlyTraceLogReadout,
    source.burdenOnlyTraceLogReadout_adverse,
    source.burdenOnlyTraceLogReadout_restorative⟩

end TwoChannelTraceEventScoreSource

/-- Swap the two local component-score coordinates. -/
def swapComponentScore (component : Nat × Nat) : Nat × Nat :=
  (component.2, component.1)

/--
A scalar readout that is blind to the burden/support direction.

This is the local admissibility condition for a total-style scalar: swapping
the two component slots does not change the scalar value.
-/
structure RoleBlindComponentScalar where
  scalar : Nat × Nat -> Nat
  swap_invariant :
    forall component, scalar component = scalar (swapComponentScore component)

namespace RoleBlindComponentScalar

variable (blind : RoleBlindComponentScalar)

theorem scalar_10_eq_01 :
    blind.scalar (1, 0) = blind.scalar (0, 1) := by
  simpa [swapComponentScore] using blind.swap_invariant (1, 0)

end RoleBlindComponentScalar

/--
The ordinary total component score is role-blind: it is invariant under
swapping the two local component slots.

This is the intended scalar shape for the restricted red test below.  The
restriction matters: arbitrary scalar encodings can select one component, but
total-style scalars erase the adverse/restorative direction.
-/
def totalComponentScalarValue (component : Nat × Nat) : Nat :=
  component.1 + component.2

def totalComponentScalar : RoleBlindComponentScalar where
  scalar := totalComponentScalarValue
  swap_invariant := by
    intro component
    cases component with
    | mk burden support =>
      simp [totalComponentScalarValue, swapComponentScore, Nat.add_comm]

theorem totalComponentScalar_10_eq_01 :
    totalComponentScalarValue (1, 0) =
      totalComponentScalarValue (0, 1) :=
  rfl

/-!
## Three-point scalar limitation witness

The two-log witness above rules out role-blind total-style scalars, but it does
not rule out every possible scalar: one component can still separate two logs.
The next local witness uses three logs.  Burden-only, support-only, and
role-blind total-style scalars each collapse a different pair, while the
component pair separates all three.

This still does not prove that every arbitrary scalar fails.  A finite set can
always be coded by an asymmetric scalar, so this section records that guard
explicitly.
-/

/--
Three observed logs whose local component events are neutral, burden-active,
and support-active.
-/
structure ThreeTraceEventScoreSource
    (Observation : Type w) where
  neutralLog : List (Observation × BoundaryStatus)
  burdenLog : List (Observation × BoundaryStatus)
  supportLog : List (Observation × BoundaryStatus)
  burdenEvent : List (Observation × BoundaryStatus) -> Bool
  supportEvent : List (Observation × BoundaryStatus) -> Bool
  neutral_burden_inactive : burdenEvent neutralLog = false
  neutral_support_inactive : supportEvent neutralLog = false
  burden_burden_active : burdenEvent burdenLog = true
  burden_support_inactive : supportEvent burdenLog = false
  support_burden_inactive : burdenEvent supportLog = false
  support_support_active : supportEvent supportLog = true
  neutralLog_ne_burdenLog : neutralLog ≠ burdenLog
  neutralLog_ne_supportLog : neutralLog ≠ supportLog
  burdenLog_ne_supportLog : burdenLog ≠ supportLog

namespace ThreeTraceEventScoreSource

variable {Observation : Type w}
variable (source : ThreeTraceEventScoreSource Observation)

def burdenScoreOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  boolEventScore 1 (source.burdenEvent traceLog)

def supportScoreOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  boolEventScore 1 (source.supportEvent traceLog)

def componentScoreOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat × Nat :=
  (source.burdenScoreOfLog traceLog, source.supportScoreOfLog traceLog)

def totalScoreOfLog
    (traceLog : List (Observation × BoundaryStatus)) : Nat :=
  (source.componentScoreOfLog traceLog).1 +
    (source.componentScoreOfLog traceLog).2

theorem neutral_componentScoreOfLog :
    source.componentScoreOfLog source.neutralLog = (0, 0) := by
  unfold componentScoreOfLog burdenScoreOfLog supportScoreOfLog
  rw [source.neutral_burden_inactive, source.neutral_support_inactive]
  rfl

theorem burden_componentScoreOfLog :
    source.componentScoreOfLog source.burdenLog = (1, 0) := by
  unfold componentScoreOfLog burdenScoreOfLog supportScoreOfLog
  rw [source.burden_burden_active, source.burden_support_inactive]
  rfl

theorem support_componentScoreOfLog :
    source.componentScoreOfLog source.supportLog = (0, 1) := by
  unfold componentScoreOfLog burdenScoreOfLog supportScoreOfLog
  rw [source.support_burden_inactive, source.support_support_active]
  rfl

theorem neutral_component_ne_burden_component :
    source.componentScoreOfLog source.neutralLog ≠
      source.componentScoreOfLog source.burdenLog := by
  rw [source.neutral_componentScoreOfLog, source.burden_componentScoreOfLog]
  decide

theorem neutral_component_ne_support_component :
    source.componentScoreOfLog source.neutralLog ≠
      source.componentScoreOfLog source.supportLog := by
  rw [source.neutral_componentScoreOfLog, source.support_componentScoreOfLog]
  decide

theorem burden_component_ne_support_component :
    source.componentScoreOfLog source.burdenLog ≠
      source.componentScoreOfLog source.supportLog := by
  rw [source.burden_componentScoreOfLog, source.support_componentScoreOfLog]
  decide

theorem burdenOnly_neutral_eq_support :
    source.burdenScoreOfLog source.neutralLog =
      source.burdenScoreOfLog source.supportLog := by
  unfold burdenScoreOfLog
  rw [source.neutral_burden_inactive, source.support_burden_inactive]

theorem supportOnly_neutral_eq_burden :
    source.supportScoreOfLog source.neutralLog =
      source.supportScoreOfLog source.burdenLog := by
  unfold supportScoreOfLog
  rw [source.neutral_support_inactive, source.burden_support_inactive]

theorem roleBlind_burden_eq_support
    (blind : RoleBlindComponentScalar) :
    blind.scalar (source.componentScoreOfLog source.burdenLog) =
      blind.scalar (source.componentScoreOfLog source.supportLog) := by
  rw [source.burden_componentScoreOfLog, source.support_componentScoreOfLog]
  exact blind.scalar_10_eq_01

/-- Burden-only scalars cannot decode all three component scores. -/
theorem no_burdenOnly_threePoint_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar (source.burdenScoreOfLog source.neutralLog) =
            source.componentScoreOfLog source.neutralLog ∧
          componentOfScalar (source.burdenScoreOfLog source.burdenLog) =
            source.componentScoreOfLog source.burdenLog ∧
          componentOfScalar (source.burdenScoreOfLog source.supportLog) =
            source.componentScoreOfLog source.supportLog) := by
  intro h
  rcases h with ⟨componentOfScalar, hneutral, _hburden, hsupport⟩
  exact
    source.neutral_component_ne_support_component
      (calc
        source.componentScoreOfLog source.neutralLog =
            componentOfScalar (source.burdenScoreOfLog source.neutralLog) :=
          hneutral.symm
        _ = componentOfScalar (source.burdenScoreOfLog source.supportLog) := by
          rw [source.burdenOnly_neutral_eq_support]
        _ = source.componentScoreOfLog source.supportLog := hsupport)

/-- Support-only scalars cannot decode all three component scores. -/
theorem no_supportOnly_threePoint_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar (source.supportScoreOfLog source.neutralLog) =
            source.componentScoreOfLog source.neutralLog ∧
          componentOfScalar (source.supportScoreOfLog source.burdenLog) =
            source.componentScoreOfLog source.burdenLog ∧
          componentOfScalar (source.supportScoreOfLog source.supportLog) =
            source.componentScoreOfLog source.supportLog) := by
  intro h
  rcases h with ⟨componentOfScalar, hneutral, hburden, _hsupport⟩
  exact
    source.neutral_component_ne_burden_component
      (calc
        source.componentScoreOfLog source.neutralLog =
            componentOfScalar (source.supportScoreOfLog source.neutralLog) :=
          hneutral.symm
        _ = componentOfScalar (source.supportScoreOfLog source.burdenLog) := by
          rw [source.supportOnly_neutral_eq_burden]
        _ = source.componentScoreOfLog source.burdenLog := hburden)

/-- Role-blind total-style scalars cannot decode all three component scores. -/
theorem no_roleBlind_threePoint_component_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (blind.scalar (source.componentScoreOfLog source.neutralLog)) =
          source.componentScoreOfLog source.neutralLog ∧
        componentOfScalar
            (blind.scalar (source.componentScoreOfLog source.burdenLog)) =
          source.componentScoreOfLog source.burdenLog ∧
        componentOfScalar
            (blind.scalar (source.componentScoreOfLog source.supportLog)) =
          source.componentScoreOfLog source.supportLog) := by
  intro h
  rcases h with ⟨componentOfScalar, _hneutral, hburden, hsupport⟩
  exact
    source.burden_component_ne_support_component
      (calc
        source.componentScoreOfLog source.burdenLog =
            componentOfScalar
              (blind.scalar (source.componentScoreOfLog source.burdenLog)) :=
          hburden.symm
        _ = componentOfScalar
              (blind.scalar
                (source.componentScoreOfLog source.supportLog)) := by
          rw [source.roleBlind_burden_eq_support blind]
        _ = source.componentScoreOfLog source.supportLog := hsupport)

/-- Burden-only scalars cannot recover all three logs. -/
theorem no_burdenOnly_threePoint_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar (source.burdenScoreOfLog source.neutralLog) =
            source.neutralLog ∧
          traceLogOfScalar (source.burdenScoreOfLog source.burdenLog) =
            source.burdenLog ∧
          traceLogOfScalar (source.burdenScoreOfLog source.supportLog) =
            source.supportLog) := by
  intro h
  rcases h with ⟨traceLogOfScalar, hneutral, _hburden, hsupport⟩
  have hlogs : source.neutralLog = source.supportLog := by
    calc
      source.neutralLog =
          traceLogOfScalar (source.burdenScoreOfLog source.neutralLog) :=
        hneutral.symm
      _ = traceLogOfScalar (source.burdenScoreOfLog source.supportLog) := by
        rw [source.burdenOnly_neutral_eq_support]
      _ = source.supportLog := hsupport
  exact source.neutralLog_ne_supportLog hlogs

/-- Support-only scalars cannot recover all three logs. -/
theorem no_supportOnly_threePoint_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar (source.supportScoreOfLog source.neutralLog) =
            source.neutralLog ∧
          traceLogOfScalar (source.supportScoreOfLog source.burdenLog) =
            source.burdenLog ∧
          traceLogOfScalar (source.supportScoreOfLog source.supportLog) =
            source.supportLog) := by
  intro h
  rcases h with ⟨traceLogOfScalar, hneutral, hburden, _hsupport⟩
  have hlogs : source.neutralLog = source.burdenLog := by
    calc
      source.neutralLog =
          traceLogOfScalar (source.supportScoreOfLog source.neutralLog) :=
        hneutral.symm
      _ = traceLogOfScalar (source.supportScoreOfLog source.burdenLog) := by
        rw [source.supportOnly_neutral_eq_burden]
      _ = source.burdenLog := hburden
  exact source.neutralLog_ne_burdenLog hlogs

/--
Role-blind total-style scalars cannot recover all three logs.
-/
theorem no_roleBlind_threePoint_traceLog_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (blind.scalar (source.componentScoreOfLog source.neutralLog)) =
          source.neutralLog ∧
        traceLogOfScalar
            (blind.scalar (source.componentScoreOfLog source.burdenLog)) =
          source.burdenLog ∧
        traceLogOfScalar
            (blind.scalar (source.componentScoreOfLog source.supportLog)) =
          source.supportLog) := by
  intro h
  rcases h with ⟨traceLogOfScalar, _hneutral, hburden, hsupport⟩
  have hlogs : source.burdenLog = source.supportLog := by
    calc
      source.burdenLog =
          traceLogOfScalar
            (blind.scalar (source.componentScoreOfLog source.burdenLog)) :=
        hburden.symm
      _ = traceLogOfScalar
            (blind.scalar (source.componentScoreOfLog source.supportLog)) := by
        rw [source.roleBlind_burden_eq_support blind]
      _ = source.supportLog := hsupport
  exact source.burdenLog_ne_supportLog hlogs

/--
The component pair can recover all three logs in the three-point witness.
-/
def componentTraceLogReadout
    (component : Nat × Nat) : List (Observation × BoundaryStatus) :=
  if component = source.componentScoreOfLog source.neutralLog then
    source.neutralLog
  else if component = source.componentScoreOfLog source.burdenLog then
    source.burdenLog
  else if component = source.componentScoreOfLog source.supportLog then
    source.supportLog
  else
    []

theorem componentTraceLogReadout_neutral :
    source.componentTraceLogReadout
        (source.componentScoreOfLog source.neutralLog) =
      source.neutralLog := by
  unfold componentTraceLogReadout
  rw [if_pos rfl]

theorem componentTraceLogReadout_burden :
    source.componentTraceLogReadout
        (source.componentScoreOfLog source.burdenLog) =
      source.burdenLog := by
  unfold componentTraceLogReadout
  rw [if_neg (by
    intro h
    exact source.neutral_component_ne_burden_component h.symm)]
  rw [if_pos rfl]

theorem componentTraceLogReadout_support :
    source.componentTraceLogReadout
        (source.componentScoreOfLog source.supportLog) =
      source.supportLog := by
  unfold componentTraceLogReadout
  rw [if_neg (by
    intro h
    exact source.neutral_component_ne_support_component h.symm)]
  rw [if_neg (by
    intro h
    exact source.burden_component_ne_support_component h.symm)]
  rw [if_pos rfl]

theorem exists_componentTraceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      readout (source.componentScoreOfLog source.neutralLog) =
          source.neutralLog ∧
        readout (source.componentScoreOfLog source.burdenLog) =
          source.burdenLog ∧
        readout (source.componentScoreOfLog source.supportLog) =
          source.supportLog :=
  ⟨source.componentTraceLogReadout,
    source.componentTraceLogReadout_neutral,
    source.componentTraceLogReadout_burden,
    source.componentTraceLogReadout_support⟩

/--
An unrestricted finite scalar can code this finite three-point witness.

This is an overclaim guard: the preceding no-go results are for burden-only,
support-only, and role-blind total-style scalars.  They do not assert that all
possible scalar encodings fail.
-/
def codeScalarOfComponent (component : Nat × Nat) : Nat :=
  if component = source.componentScoreOfLog source.neutralLog then
    0
  else if component = source.componentScoreOfLog source.burdenLog then
    1
  else if component = source.componentScoreOfLog source.supportLog then
    2
  else
    3

theorem codeScalarOfComponent_neutral :
    source.codeScalarOfComponent
        (source.componentScoreOfLog source.neutralLog) = 0 := by
  unfold codeScalarOfComponent
  rw [if_pos rfl]

theorem codeScalarOfComponent_burden :
    source.codeScalarOfComponent
        (source.componentScoreOfLog source.burdenLog) = 1 := by
  unfold codeScalarOfComponent
  rw [if_neg (by
    intro h
    exact source.neutral_component_ne_burden_component h.symm)]
  rw [if_pos rfl]

theorem codeScalarOfComponent_support :
    source.codeScalarOfComponent
        (source.componentScoreOfLog source.supportLog) = 2 := by
  unfold codeScalarOfComponent
  rw [if_neg (by
    intro h
    exact source.neutral_component_ne_support_component h.symm)]
  rw [if_neg (by
    intro h
    exact source.burden_component_ne_support_component h.symm)]
  rw [if_pos rfl]

def codeScalarTraceLogReadout
    (score : Nat) : List (Observation × BoundaryStatus) :=
  if score = 0 then
    source.neutralLog
  else if score = 1 then
    source.burdenLog
  else if score = 2 then
    source.supportLog
  else
    []

theorem codeScalarTraceLogReadout_neutral :
    source.codeScalarTraceLogReadout
        (source.codeScalarOfComponent
          (source.componentScoreOfLog source.neutralLog)) =
      source.neutralLog := by
  rw [source.codeScalarOfComponent_neutral]
  unfold codeScalarTraceLogReadout
  rw [if_pos rfl]

theorem codeScalarTraceLogReadout_burden :
    source.codeScalarTraceLogReadout
        (source.codeScalarOfComponent
          (source.componentScoreOfLog source.burdenLog)) =
      source.burdenLog := by
  rw [source.codeScalarOfComponent_burden]
  unfold codeScalarTraceLogReadout
  rw [if_neg (by decide : 1 ≠ 0), if_pos rfl]

theorem codeScalarTraceLogReadout_support :
    source.codeScalarTraceLogReadout
        (source.codeScalarOfComponent
          (source.componentScoreOfLog source.supportLog)) =
      source.supportLog := by
  rw [source.codeScalarOfComponent_support]
  unfold codeScalarTraceLogReadout
  rw [if_neg (by decide : 2 ≠ 0),
    if_neg (by decide : 2 ≠ 1),
    if_pos rfl]

theorem exists_codeScalar_threePoint_traceLog_readout :
    ∃ scalar : Nat × Nat -> Nat,
      ∃ readout : Nat -> List (Observation × BoundaryStatus),
        readout (scalar (source.componentScoreOfLog source.neutralLog)) =
            source.neutralLog ∧
          readout (scalar (source.componentScoreOfLog source.burdenLog)) =
            source.burdenLog ∧
          readout (scalar (source.componentScoreOfLog source.supportLog)) =
            source.supportLog :=
  ⟨source.codeScalarOfComponent,
    source.codeScalarTraceLogReadout,
    source.codeScalarTraceLogReadout_neutral,
    source.codeScalarTraceLogReadout_burden,
    source.codeScalarTraceLogReadout_support⟩

end ThreeTraceEventScoreSource

/-!
## Additive composition scalar limitation

The three-point witness above is intentionally finite: an unrestricted scalar
can code a finite set of component pairs.  The next local result moves from
static points to composition counts.  If a one-dimensional scalar is required
to compose by fixed additive burden/support units, then it cannot decode all
two-channel component counts when both units are positive.

This still does not rule out arbitrary scalar transition systems that decode
and re-encode the pair internally.  It only rules out the additive one-scalar
accounting shape.
-/

namespace AdditiveScalarComposition

/-- Two-channel component count after composing burden/support events. -/
def componentCoordinate (burdenCount supportCount : Nat) : Nat × Nat :=
  (burdenCount, supportCount)

/--
One-dimensional additive scalar accounting with fixed burden/support units.

This is the natural scalar-composition shape being tested, not a ban on all
possible encodings of pairs into `Nat`.
-/
def additiveScalarOfCounts
    (burdenUnit supportUnit burdenCount supportCount : Nat) : Nat :=
  burdenCount * burdenUnit + supportCount * supportUnit

/--
The additive scalar has an unavoidable collision on the two-channel grid:
`supportUnit` burden events have the same scalar as `burdenUnit` support
events.
-/
theorem additiveScalar_collision
    (burdenUnit supportUnit : Nat) :
    additiveScalarOfCounts burdenUnit supportUnit supportUnit 0 =
      additiveScalarOfCounts burdenUnit supportUnit 0 burdenUnit := by
  unfold additiveScalarOfCounts
  rw [Nat.zero_mul, Nat.add_zero, Nat.zero_mul, Nat.zero_add,
    Nat.mul_comm supportUnit burdenUnit]

/-- With positive units, the two colliding component counts are distinct. -/
theorem collision_componentCoordinates_ne
    {burdenUnit supportUnit : Nat}
    (_hburden : 0 < burdenUnit) (hsupport : 0 < supportUnit) :
    componentCoordinate supportUnit 0 ≠
      componentCoordinate 0 burdenUnit := by
  intro h
  have hfst : supportUnit = 0 := congrArg Prod.fst h
  exact Nat.ne_of_gt hsupport hfst

/--
No decoder from a fixed-unit additive scalar can recover all two-channel
component counts when both units are positive.

This is the composition-level red test: unlike the finite three-point witness,
the counts range over all natural compositions, so every positive fixed-unit
additive scalar has a commutativity collision.
-/
theorem no_additiveScalar_component_decoder
    {burdenUnit supportUnit : Nat}
    (hburden : 0 < burdenUnit) (hsupport : 0 < supportUnit) :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        forall burdenCount supportCount,
          componentOfScalar
              (additiveScalarOfCounts
                burdenUnit supportUnit burdenCount supportCount) =
            componentCoordinate burdenCount supportCount) := by
  intro h
  rcases h with ⟨componentOfScalar, hdecode⟩
  have hcomponents :
      componentCoordinate supportUnit 0 =
        componentCoordinate 0 burdenUnit := by
    calc
      componentCoordinate supportUnit 0 =
          componentOfScalar
            (additiveScalarOfCounts
              burdenUnit supportUnit supportUnit 0) :=
        (hdecode supportUnit 0).symm
      _ = componentOfScalar
            (additiveScalarOfCounts
              burdenUnit supportUnit 0 burdenUnit) := by
        rw [additiveScalar_collision burdenUnit supportUnit]
      _ = componentCoordinate 0 burdenUnit := hdecode 0 burdenUnit
  exact collision_componentCoordinates_ne hburden hsupport hcomponents

/-- The two-component coordinate itself trivially decodes all component counts. -/
theorem exists_componentCoordinate_decoder :
    ∃ componentOfComponent : Nat × Nat -> Nat × Nat,
      forall burdenCount supportCount,
        componentOfComponent
            (componentCoordinate burdenCount supportCount) =
          componentCoordinate burdenCount supportCount :=
  ⟨id, by
    intro burdenCount supportCount
    rfl⟩

end AdditiveScalarComposition

/-!
## Observed additive composition scalar limitation

The arithmetic collision above becomes an observational red test once the
two component counts are realized as repeated action traces.  The theorem in
this section still has a narrow scope: it rules out fixed-unit additive
one-scalar accounting for preserving all observed composition logs when a
specific colliding pair is observed to have different logs.  It does not rule
out arbitrary non-additive scalar encodings.
-/

namespace AdditiveScalarCompositionObservedTrace

/--
Compose a burden-channel action and a support-channel action by their counts.

This is an observed-trace construction, not an internal `L/B` or `M`
derivation: the two action channels and the initial state are still supplied.
-/
def compositionTrace
    (burdenAction supportAction : Action)
    (burdenCount supportCount : Nat) : List Action :=
  List.replicate burdenCount burdenAction ++
    List.replicate supportCount supportAction

/--
Observed source for the additive-composition scalar red test.

The `collision_traceLog_ne` field is the observational certificate that the
two additive-scalar-colliding composites are different at the prefix-log
level.  Without such an observed separation, the arithmetic collision would
not by itself be a persistence/collapse readout.
-/
structure ObservedAdditiveCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  initialState : State
  burdenAction : Action
  supportAction : Action
  burdenUnit : Nat
  supportUnit : Nat
  burdenUnit_pos : 0 < burdenUnit
  supportUnit_pos : 0 < supportUnit
  collision_traceLog_ne :
    P.traceLog initialState
        (compositionTrace burdenAction supportAction supportUnit 0) ≠
      P.traceLog initialState
        (compositionTrace burdenAction supportAction 0 burdenUnit)

namespace ObservedAdditiveCompositionSource

variable (source : ObservedAdditiveCompositionSource P)

/-- Observed prefix log of a two-channel composition count. -/
def traceLogOfCounts
    (burdenCount supportCount : Nat) :
    List (Observation × BoundaryStatus) :=
  P.traceLog source.initialState
    (compositionTrace source.burdenAction source.supportAction
      burdenCount supportCount)

/-- Fixed-unit additive scalar attached to the same two-channel counts. -/
def scalarOfCounts (burdenCount supportCount : Nat) : Nat :=
  AdditiveScalarComposition.additiveScalarOfCounts
    source.burdenUnit source.supportUnit burdenCount supportCount

/-- The observed colliding count pair has equal fixed-unit additive scalar. -/
theorem collision_scalar_eq :
    source.scalarOfCounts source.supportUnit 0 =
      source.scalarOfCounts 0 source.burdenUnit := by
  simpa [scalarOfCounts] using
    AdditiveScalarComposition.additiveScalar_collision
      source.burdenUnit source.supportUnit

/-- The observed colliding count pair still has distinct component counts. -/
theorem collision_componentCounts_ne :
    AdditiveScalarComposition.componentCoordinate source.supportUnit 0 ≠
      AdditiveScalarComposition.componentCoordinate 0 source.burdenUnit :=
  AdditiveScalarComposition.collision_componentCoordinates_ne
    source.burdenUnit_pos source.supportUnit_pos

/--
No fixed-unit additive scalar readout can preserve all observed composition
logs for this source.

This is the observational lift of the arithmetic collision: the same scalar
would have to decode two observed prefix logs that are certified distinct.
-/
theorem no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.scalarOfCounts burdenCount supportCount) =
            source.traceLogOfCounts burdenCount supportCount) := by
  intro h
  rcases h with ⟨traceLogOfScalar, hdecode⟩
  have hlogs :
      source.traceLogOfCounts source.supportUnit 0 =
        source.traceLogOfCounts 0 source.burdenUnit := by
    calc
      source.traceLogOfCounts source.supportUnit 0 =
          traceLogOfScalar
            (source.scalarOfCounts source.supportUnit 0) :=
        (hdecode source.supportUnit 0).symm
      _ = traceLogOfScalar
            (source.scalarOfCounts 0 source.burdenUnit) := by
        rw [source.collision_scalar_eq]
      _ = source.traceLogOfCounts 0 source.burdenUnit :=
        hdecode 0 source.burdenUnit
  exact source.collision_traceLog_ne hlogs

/--
The two-component coordinate can preserve all observed composition logs for
this source.
-/
theorem exists_componentCoordinate_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.traceLogOfCounts burdenCount supportCount :=
  ⟨fun component => source.traceLogOfCounts component.1 component.2, by
    intro burdenCount supportCount
    rfl⟩

end ObservedAdditiveCompositionSource

/--
Structured observational source for the additive-composition red test.

Instead of supplying the colliding trace-log inequality directly, this source
supplies an observed component-count readout on prefix logs.  If that readout
recovers the two composition counts for every generated composition trace,
then the additive-scalar-colliding traces are automatically separated.

This is still a certificate-consuming boundary: the component-count readout is
an observational input, not yet derived from arbitrary admissible alternatives.
-/
structure ComponentCountObservedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  initialState : State
  burdenAction : Action
  supportAction : Action
  burdenUnit : Nat
  supportUnit : Nat
  burdenUnit_pos : 0 < burdenUnit
  supportUnit_pos : 0 < supportUnit
  observedComponentOfLog :
    List (Observation × BoundaryStatus) -> Nat × Nat
  observedComponent_law :
    forall burdenCount supportCount,
      observedComponentOfLog
          (P.traceLog initialState
            (compositionTrace burdenAction supportAction
              burdenCount supportCount)) =
        AdditiveScalarComposition.componentCoordinate
          burdenCount supportCount

namespace ComponentCountObservedCompositionSource

variable (source : ComponentCountObservedCompositionSource P)

/-- Observed prefix log of a two-channel composition count. -/
def traceLogOfCounts
    (burdenCount supportCount : Nat) :
    List (Observation × BoundaryStatus) :=
  P.traceLog source.initialState
    (compositionTrace source.burdenAction source.supportAction
      burdenCount supportCount)

/--
The observed component-count readout forces the scalar-colliding composites to
have distinct prefix logs.
-/
theorem collision_traceLog_ne :
    source.traceLogOfCounts source.supportUnit 0 ≠
      source.traceLogOfCounts 0 source.burdenUnit := by
  intro hlog
  have hcomponents :
      AdditiveScalarComposition.componentCoordinate source.supportUnit 0 =
        AdditiveScalarComposition.componentCoordinate
          0 source.burdenUnit := by
    calc
      AdditiveScalarComposition.componentCoordinate source.supportUnit 0 =
          source.observedComponentOfLog
            (source.traceLogOfCounts source.supportUnit 0) :=
        (source.observedComponent_law source.supportUnit 0).symm
      _ = source.observedComponentOfLog
            (source.traceLogOfCounts 0 source.burdenUnit) := by
        rw [hlog]
      _ = AdditiveScalarComposition.componentCoordinate
            0 source.burdenUnit :=
        source.observedComponent_law 0 source.burdenUnit
  exact
    AdditiveScalarComposition.collision_componentCoordinates_ne
      source.burdenUnit_pos source.supportUnit_pos hcomponents

/--
Forget the structured component-count observation into the previous direct
observed-separation source.
-/
def toObservedAdditiveCompositionSource :
    ObservedAdditiveCompositionSource P where
  initialState := source.initialState
  burdenAction := source.burdenAction
  supportAction := source.supportAction
  burdenUnit := source.burdenUnit
  supportUnit := source.supportUnit
  burdenUnit_pos := source.burdenUnit_pos
  supportUnit_pos := source.supportUnit_pos
  collision_traceLog_ne := source.collision_traceLog_ne

/--
No fixed-unit additive scalar readout can preserve all observed composition
logs when a component-count readout is observed to recover the generated
composition counts.
-/
theorem no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toObservedAdditiveCompositionSource).scalarOfCounts
                burdenCount supportCount) =
            source.traceLogOfCounts burdenCount supportCount) :=
  (source.toObservedAdditiveCompositionSource).no_additiveScalar_traceLog_decoder

/--
The two-component coordinate can preserve all observed composition logs for
the structured component-count source.
-/
theorem exists_componentCoordinate_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.traceLogOfCounts burdenCount supportCount :=
  (source.toObservedAdditiveCompositionSource).exists_componentCoordinate_traceLog_readout

end ComponentCountObservedCompositionSource

/--
If the first burden action and first support action have different observable
responses at the same initial state, then the additive-scalar-colliding
composition traces have different observed prefix logs.

This is the first point where the collision certificate is derived from a
primitive observational response distinction rather than supplied as a raw log
inequality.
-/
theorem traceLog_ne_of_first_response_ne
    {initialState : State} {burdenAction supportAction : Action}
    {burdenUnit supportUnit : Nat}
    (hburden : 0 < burdenUnit) (hsupport : 0 < supportUnit)
    (hresponse :
      P.response initialState burdenAction ≠
        P.response initialState supportAction) :
    P.traceLog initialState
        (compositionTrace burdenAction supportAction supportUnit 0) ≠
      P.traceLog initialState
        (compositionTrace burdenAction supportAction 0 burdenUnit) := by
  obtain ⟨supportRest, hsupp⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsupport)
  obtain ⟨burdenRest, hb⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hburden)
  subst supportUnit
  subst burdenUnit
  intro hlog
  apply hresponse
  unfold compositionTrace at hlog
  simp only [List.replicate, List.nil_append] at hlog
  change P.response initialState burdenAction :: _ =
    P.response initialState supportAction :: _ at hlog
  exact (List.cons.inj hlog).1

/--
Observed additive-composition source where the collision separation is derived
from a same-state first-response distinction.

This is still scoped: the burden/support action channels, units, and
same-state response distinction are inputs.  It does not quantify over every
admissible alternative representation.
-/
structure ResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  initialState : State
  burdenAction : Action
  supportAction : Action
  burdenUnit : Nat
  supportUnit : Nat
  burdenUnit_pos : 0 < burdenUnit
  supportUnit_pos : 0 < supportUnit
  response_ne :
    P.response initialState burdenAction ≠
      P.response initialState supportAction

namespace ResponseSeparatedCompositionSource

variable (source : ResponseSeparatedCompositionSource P)

/-- Response separation induces the observed colliding-log separation. -/
theorem collision_traceLog_ne :
    P.traceLog source.initialState
        (compositionTrace source.burdenAction source.supportAction
          source.supportUnit 0) ≠
      P.traceLog source.initialState
        (compositionTrace source.burdenAction source.supportAction
          0 source.burdenUnit) :=
  traceLog_ne_of_first_response_ne
    source.burdenUnit_pos source.supportUnit_pos source.response_ne

/-- Forget the response-separated source into the direct observed source. -/
def toObservedAdditiveCompositionSource :
    ObservedAdditiveCompositionSource P where
  initialState := source.initialState
  burdenAction := source.burdenAction
  supportAction := source.supportAction
  burdenUnit := source.burdenUnit
  supportUnit := source.supportUnit
  burdenUnit_pos := source.burdenUnit_pos
  supportUnit_pos := source.supportUnit_pos
  collision_traceLog_ne := source.collision_traceLog_ne

/--
No fixed-unit additive scalar readout can preserve all observed composition
logs when the two channels are separated by their first observable response.
-/
theorem no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toObservedAdditiveCompositionSource).scalarOfCounts
                burdenCount supportCount) =
            (source.toObservedAdditiveCompositionSource).traceLogOfCounts
              burdenCount supportCount) :=
  (source.toObservedAdditiveCompositionSource).no_additiveScalar_traceLog_decoder

/--
The two-component coordinate can preserve all observed composition logs for
the response-separated source.
-/
theorem exists_componentCoordinate_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount :=
  (source.toObservedAdditiveCompositionSource).exists_componentCoordinate_traceLog_readout

/--
Current-view response-image completeness realizes each source composition log
as some target trace log.

This is deliberately weaker than the generated-prefix-state transport
boundary below: it does not choose fixed target burden/support actions and does
not construct a target-side `ResponseSeparatedCompositionSource`.  It only
records the language-image consequence of the local current-view
response-image hypothesis for the generated composition traces.
-/
theorem traceLogOfCounts_in_target_image_of_currentViewResponseImageComplete
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (complete : CurrentViewResponseImageComplete P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState)
    (burdenCount supportCount : Nat) :
    ∃ targetActions : List AlternativeAction,
      (source.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount =
        alternative.traceLog targetInitialState targetActions :=
  by
    rcases
      CurrentViewResponseImageComplete.toCurrentViewTraceImageComplete
        complete hview
        (compositionTrace source.burdenAction source.supportAction
          burdenCount supportCount) with
      ⟨targetActions, htarget⟩
    exact ⟨targetActions, htarget.symm⟩

/--
A role-free response-image simulation realizes each source composition log as
some target trace log.

This is the simulation-level version of the current-view language-image
consequence.  It still does not choose fixed target burden/support actions or
prove generated-prefix preservation; each source composition trace may be
matched by a different target trace.
-/
theorem traceLogOfCounts_in_target_image_of_responseImageSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (simulation : ObservationalResponseImageSimulation P alternative)
    (hrelated :
      simulation.related source.initialState targetInitialState)
    (burdenCount supportCount : Nat) :
    ∃ targetActions : List AlternativeAction,
      (source.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount =
        alternative.traceLog targetInitialState targetActions := by
  rcases
    simulation.traceLogImagePreservationAt hrelated
      (compositionTrace source.burdenAction source.supportAction
        burdenCount supportCount) with
    ⟨targetActions, htarget⟩
  exact ⟨targetActions, htarget.symm⟩

/--
Current-view trace-log language inclusion realizes each source composition log
as some target trace log by descending to the current-view response-image
condition.

This remains a language-image consequence.  It still does not choose fixed
target burden/support actions or prove generated-prefix preservation.
-/
theorem traceLogOfCounts_in_target_image_of_currentViewTraceLogLanguageIncluded
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (included : CurrentViewTraceLogLanguageIncluded P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState)
    (burdenCount supportCount : Nat) :
    ∃ targetActions : List AlternativeAction,
      (source.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount =
        alternative.traceLog targetInitialState targetActions :=
  source.traceLogOfCounts_in_target_image_of_currentViewResponseImageComplete
    (CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
      included)
    hview burdenCount supportCount

/--
Current-view trace-log language equivalence gives the same source-composition
language-image consequence by forgetting to forward inclusion.
-/
theorem traceLogOfCounts_in_target_image_of_currentViewTraceLogLanguageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewTraceLogLanguageEquivalent P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState)
    (burdenCount supportCount : Nat) :
    ∃ targetActions : List AlternativeAction,
      (source.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount =
        alternative.traceLog targetInitialState targetActions :=
  source.traceLogOfCounts_in_target_image_of_currentViewTraceLogLanguageIncluded
    (CurrentViewTraceLogLanguageEquivalent.toIncluded equivalent)
    hview burdenCount supportCount

/--
Current-view response-image completeness also discovers target-side witnesses
for the two initial burden/support responses.

This is still local and observational: it chooses two target actions at the
selected target initial state.  It does not provide a global action
translator, and it does not prove generated-prefix preservation for those
actions.
-/
theorem exists_targetResponseSeparatedCompositionSource_of_currentViewResponseImageComplete
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (complete : CurrentViewResponseImageComplete P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      targetSource.initialState = targetInitialState ∧
      targetSource.burdenUnit = source.burdenUnit ∧
      targetSource.supportUnit = source.supportUnit ∧
      alternative.response targetInitialState targetSource.burdenAction =
        P.response source.initialState source.burdenAction ∧
      alternative.response targetInitialState targetSource.supportAction =
        P.response source.initialState source.supportAction := by
  rcases complete hview
      (P.response source.initialState source.burdenAction)
      ⟨source.burdenAction, rfl⟩ with
    ⟨targetBurdenAction, hburden⟩
  rcases complete hview
      (P.response source.initialState source.supportAction)
      ⟨source.supportAction, rfl⟩ with
    ⟨targetSupportAction, hsupport⟩
  refine
    ⟨{ initialState := targetInitialState
       burdenAction := targetBurdenAction
       supportAction := targetSupportAction
       burdenUnit := source.burdenUnit
       supportUnit := source.supportUnit
       burdenUnit_pos := source.burdenUnit_pos
       supportUnit_pos := source.supportUnit_pos
       response_ne := ?_ },
      rfl, rfl, rfl, hburden, hsupport⟩
  intro htarget
  apply source.response_ne
  calc
    P.response source.initialState source.burdenAction =
        alternative.response targetInitialState targetBurdenAction :=
      hburden.symm
    _ = alternative.response targetInitialState targetSupportAction :=
      htarget
    _ = P.response source.initialState source.supportAction :=
      hsupport

/--
A role-free response-image simulation also discovers target-side witnesses for
the two initial burden/support responses.

This is weaker than the fixed-translator/generated-prefix route: the target
actions are chosen existentially from the simulation's one-step image law, and
no generated-prefix preservation is claimed.
-/
theorem exists_targetResponseSeparatedCompositionSource_of_responseImageSimulation
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (simulation : ObservationalResponseImageSimulation P alternative)
    (hrelated :
      simulation.related source.initialState targetInitialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      targetSource.initialState = targetInitialState ∧
      targetSource.burdenUnit = source.burdenUnit ∧
      targetSource.supportUnit = source.supportUnit ∧
      alternative.response targetInitialState targetSource.burdenAction =
        P.response source.initialState source.burdenAction ∧
      alternative.response targetInitialState targetSource.supportAction =
        P.response source.initialState source.supportAction := by
  rcases
    (simulation.actionResponseCoverageAt hrelated)
      source.burdenAction with
    ⟨targetBurdenAction, hburden⟩
  rcases
    (simulation.actionResponseCoverageAt hrelated)
      source.supportAction with
    ⟨targetSupportAction, hsupport⟩
  refine
    ⟨{ initialState := targetInitialState
       burdenAction := targetBurdenAction
       supportAction := targetSupportAction
       burdenUnit := source.burdenUnit
       supportUnit := source.supportUnit
       burdenUnit_pos := source.burdenUnit_pos
       supportUnit_pos := source.supportUnit_pos
       response_ne := ?_ },
      rfl, rfl, rfl, hburden, hsupport⟩
  intro htarget
  apply source.response_ne
  calc
    P.response source.initialState source.burdenAction =
        alternative.response targetInitialState targetBurdenAction :=
      hburden.symm
    _ = alternative.response targetInitialState targetSupportAction :=
      htarget
    _ = P.response source.initialState source.supportAction :=
      hsupport

/--
Current-view trace-log language inclusion also discovers target-side witnesses
for the two initial burden/support responses by descending through the
one-step response-image bottleneck.

The discovered witnesses are still local to the selected target initial state;
this does not provide a global action translator or generated-prefix
preservation for the chosen target actions.
-/
theorem exists_targetResponseSeparatedCompositionSource_of_currentViewTraceLogLanguageIncluded
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (included : CurrentViewTraceLogLanguageIncluded P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      targetSource.initialState = targetInitialState ∧
      targetSource.burdenUnit = source.burdenUnit ∧
      targetSource.supportUnit = source.supportUnit ∧
      alternative.response targetInitialState targetSource.burdenAction =
        P.response source.initialState source.burdenAction ∧
      alternative.response targetInitialState targetSource.supportAction =
        P.response source.initialState source.supportAction :=
  source.exists_targetResponseSeparatedCompositionSource_of_currentViewResponseImageComplete
    (CurrentViewTraceLogLanguageIncluded.toCurrentViewResponseImageComplete
      included)
    hview

/--
Current-view trace-log language equivalence gives the same target-side
response-separated witnesses by forgetting to forward inclusion.
-/
theorem exists_targetResponseSeparatedCompositionSource_of_currentViewTraceLogLanguageEquivalent
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (equivalent : CurrentViewTraceLogLanguageEquivalent P alternative)
    (hview :
      alternative.currentView targetInitialState =
        P.currentView source.initialState) :
    ∃ targetSource : ResponseSeparatedCompositionSource alternative,
      targetSource.initialState = targetInitialState ∧
      targetSource.burdenUnit = source.burdenUnit ∧
      targetSource.supportUnit = source.supportUnit ∧
      alternative.response targetInitialState targetSource.burdenAction =
        P.response source.initialState source.burdenAction ∧
      alternative.response targetInitialState targetSource.supportAction =
        P.response source.initialState source.supportAction :=
  source.exists_targetResponseSeparatedCompositionSource_of_currentViewTraceLogLanguageIncluded
    (CurrentViewTraceLogLanguageEquivalent.toIncluded equivalent)
    hview

end ResponseSeparatedCompositionSource

/--
When a two-channel law uses the same initial context for the restorative and
adverse one-step probes, its `response_ne` field yields the response-separated
composition source.
-/
def ResponseSeparatedCompositionSource.ofTwoChannelTraceLawSameContext
    (law : TwoChannelTraceLaw P)
    (sameContext : law.adverseContext = law.restorativeContext)
    (burdenUnit supportUnit : Nat)
    (hburden : 0 < burdenUnit) (hsupport : 0 < supportUnit) :
    ResponseSeparatedCompositionSource P where
  initialState := law.adverseContext
  burdenAction := law.adverseIntervention
  supportAction := law.restorativeIntervention
  burdenUnit := burdenUnit
  supportUnit := supportUnit
  burdenUnit_pos := hburden
  supportUnit_pos := hsupport
  response_ne := by
    intro h
    apply law.response_ne
    calc
      law.restorativeResponse =
          P.traceResponse law.adverseContext [law.restorativeIntervention] :=
        law.restorative_law.symm
      _ = P.response law.adverseContext law.restorativeIntervention := rfl
      _ = P.response law.adverseContext law.adverseIntervention := h.symm
      _ = P.traceResponse law.adverseContext [law.adverseIntervention] := rfl
      _ = P.traceResponse law.restorativeContext [law.adverseIntervention] := by
        rw [sameContext]
      _ = law.adverseResponse := law.adverse_law

/--
Mapping a two-channel composition trace commutes with `compositionTrace`.

This small lemma keeps the transition-map bridge role-free: it is just a list
calculation about replicated action traces.
-/
theorem map_replicate_action
    (toAction : Action -> ActionCoordinate)
    (action : Action) :
    forall count,
      (List.replicate count action).map toAction =
        List.replicate count (toAction action)
  | 0 => rfl
  | count + 1 => by
      change
        toAction action :: (List.replicate count action).map toAction =
          toAction action :: List.replicate count (toAction action)
      exact
        congrArg (fun tail => toAction action :: tail)
          (map_replicate_action toAction action count)

/-- A local foundational map/append lemma for action traces. -/
theorem map_append_action
    (toAction : Action -> ActionCoordinate) :
    forall left right : List Action,
      (left ++ right).map toAction =
        left.map toAction ++ right.map toAction
  | [], _ => rfl
  | action :: left, right => by
      change
        toAction action :: ((left ++ right).map toAction) =
          toAction action :: (left.map toAction ++ right.map toAction)
      exact
        congrArg (fun tail => toAction action :: tail)
          (map_append_action toAction left right)

theorem map_compositionTrace
    (toAction : Action -> ActionCoordinate)
    (burdenAction supportAction : Action)
    (burdenCount supportCount : Nat) :
    (compositionTrace burdenAction supportAction
      burdenCount supportCount).map toAction =
      compositionTrace (toAction burdenAction) (toAction supportAction)
        burdenCount supportCount := by
  unfold compositionTrace
  calc
    (List.replicate burdenCount burdenAction ++
        List.replicate supportCount supportAction).map toAction =
        (List.replicate burdenCount burdenAction).map toAction ++
          (List.replicate supportCount supportAction).map toAction :=
      map_append_action toAction
        (List.replicate burdenCount burdenAction)
        (List.replicate supportCount supportAction)
    _ = List.replicate burdenCount (toAction burdenAction) ++
          List.replicate supportCount (toAction supportAction) :=
      congrArg₂ (fun left right => left ++ right)
        (map_replicate_action toAction burdenAction burdenCount)
        (map_replicate_action toAction supportAction supportCount)

/--
Response-separated additive composition transported through a role-free
observational transition map.

The source-side response separation is an observational fact.  The transition
map carries it to the alternative process without mentioning burden/support
roles, viable regions, or target semantics.  This is still scoped: the
two-channel actions, positive units, and transition map are inputs.
-/
structure TransitionMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  transitionMap : ObservationalTransitionMap P alternative
  source : ResponseSeparatedCompositionSource P

namespace TransitionMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  TransitionMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The target-side response-separated source induced by the transition map.
-/
def toTargetResponseSeparatedCompositionSource :
    ResponseSeparatedCompositionSource source.alternative where
  initialState := source.transitionMap.toState source.source.initialState
  burdenAction := source.transitionMap.toAction source.source.burdenAction
  supportAction := source.transitionMap.toAction source.source.supportAction
  burdenUnit := source.source.burdenUnit
  supportUnit := source.source.supportUnit
  burdenUnit_pos := source.source.burdenUnit_pos
  supportUnit_pos := source.source.supportUnit_pos
  response_ne :=
    (source.transitionMap.toResponseMap).preserves_distinguished_response
      source.source.response_ne

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toTargetResponseSeparatedCompositionSource
    |>.toObservedAdditiveCompositionSource

/--
The source and target observed composition logs agree under the transition map.
-/
theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount := by
  calc
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
        P.traceLog source.source.initialState
          (compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount) := rfl
    _ = source.alternative.traceLog
          (source.transitionMap.toState source.source.initialState)
          ((compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount).map
              source.transitionMap.toAction) :=
        source.transitionMap.preserves_traceLog source.source.initialState
          (compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount)
    _ = source.alternative.traceLog
          (source.transitionMap.toState source.source.initialState)
          (compositionTrace
            (source.transitionMap.toAction source.source.burdenAction)
            (source.transitionMap.toAction source.source.supportAction)
            burdenCount supportCount) := by
        rw [map_compositionTrace]
    _ = source.targetObservedSource.traceLogOfCounts
          burdenCount supportCount := rfl

/--
No fixed-unit additive scalar readout can preserve all target-side observed
composition logs transported by a role-free transition map from a
response-separated source.
-/
theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toTargetResponseSeparatedCompositionSource
    |>.no_additiveScalar_traceLog_decoder

/--
The two-component coordinate can preserve all transported target-side observed
composition logs.
-/
theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toTargetResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_traceLog_readout

end TransitionMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported through a role-free
observational trace simulation.

This weakens the transition-map source above.  The target-side initial state is
not required to be the image of a source-state function; it only has to be
related to the source initial state by a simulation relation that preserves
observable views and is closed under paired actions.  The simulation relation
is still an input, so this is not yet the arbitrary-alternative G1 theorem.
-/
structure SimulationMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  simulation : ObservationalTraceSimulation P alternative
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  initial_related :
    simulation.related source.initialState targetInitialState

namespace SimulationMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  SimulationMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The target-side response-separated source induced by the trace simulation.
-/
def toTargetResponseSeparatedCompositionSource :
    ResponseSeparatedCompositionSource source.alternative where
  initialState := source.targetInitialState
  burdenAction := source.simulation.toAction source.source.burdenAction
  supportAction := source.simulation.toAction source.source.supportAction
  burdenUnit := source.source.burdenUnit
  supportUnit := source.source.supportUnit
  burdenUnit_pos := source.source.burdenUnit_pos
  supportUnit_pos := source.source.supportUnit_pos
  response_ne := by
    intro htarget
    apply source.source.response_ne
    calc
      P.response source.source.initialState source.source.burdenAction =
          source.alternative.response
            source.targetInitialState
            (source.simulation.toAction source.source.burdenAction) :=
        (source.simulation.preserves_response
          source.initial_related source.source.burdenAction).symm
      _ = source.alternative.response
            source.targetInitialState
            (source.simulation.toAction source.source.supportAction) :=
        htarget
      _ = P.response source.source.initialState source.source.supportAction :=
        source.simulation.preserves_response
          source.initial_related source.source.supportAction

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toTargetResponseSeparatedCompositionSource
    |>.toObservedAdditiveCompositionSource

/--
The source and target observed composition logs agree along the trace
simulation relation.
-/
theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount := by
  calc
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
        P.traceLog source.source.initialState
          (compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount) := rfl
    _ = source.alternative.traceLog
          source.targetInitialState
          ((compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount).map
              source.simulation.toAction) :=
        source.simulation.preserves_traceLog source.initial_related
          (compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount)
    _ = source.alternative.traceLog
          source.targetInitialState
          (compositionTrace
            (source.simulation.toAction source.source.burdenAction)
            (source.simulation.toAction source.source.supportAction)
            burdenCount supportCount) := by
        rw [map_compositionTrace]
    _ = source.targetObservedSource.traceLogOfCounts
          burdenCount supportCount := rfl

/--
No fixed-unit additive scalar readout can preserve all target-side observed
composition logs transported by a role-free trace simulation.
-/
theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toTargetResponseSeparatedCompositionSource
    |>.no_additiveScalar_traceLog_decoder

/--
The two-component coordinate can preserve all simulation-transported
target-side observed composition logs.
-/
theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toTargetResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_traceLog_readout

end SimulationMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by only the decisive
composition-trace consequences.

This is weaker than a full trace simulation: it does not require a relation
on all states, step closure, or preservation of every finite source trace.
It consumes exactly the local one-step response equalities needed to preserve
the response split, plus preservation of the generated two-channel
composition traces.
-/
structure CompositionTraceMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAction : Action -> AlternativeAction
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  preserves_burden_response :
    alternative.response targetInitialState (toAction source.burdenAction) =
      P.response source.initialState source.burdenAction
  preserves_support_response :
    alternative.response targetInitialState (toAction source.supportAction) =
      P.response source.initialState source.supportAction
  preserves_composition_traceLog :
    forall burdenCount supportCount,
      P.traceLog source.initialState
          (compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount) =
        alternative.traceLog targetInitialState
          (compositionTrace
            (toAction source.burdenAction)
            (toAction source.supportAction)
            burdenCount supportCount)

namespace CompositionTraceMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTraceMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The target-side response-separated source induced by the decisive
composition-trace data.
-/
def toTargetResponseSeparatedCompositionSource :
    ResponseSeparatedCompositionSource source.alternative where
  initialState := source.targetInitialState
  burdenAction := source.toAction source.source.burdenAction
  supportAction := source.toAction source.source.supportAction
  burdenUnit := source.source.burdenUnit
  supportUnit := source.source.supportUnit
  burdenUnit_pos := source.source.burdenUnit_pos
  supportUnit_pos := source.source.supportUnit_pos
  response_ne := by
    intro htarget
    apply source.source.response_ne
    calc
      P.response source.source.initialState source.source.burdenAction =
          source.alternative.response source.targetInitialState
            (source.toAction source.source.burdenAction) :=
        source.preserves_burden_response.symm
      _ = source.alternative.response source.targetInitialState
            (source.toAction source.source.supportAction) :=
        htarget
      _ = P.response source.source.initialState
            source.source.supportAction :=
        source.preserves_support_response

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toTargetResponseSeparatedCompositionSource
    |>.toObservedAdditiveCompositionSource

/--
The source and target observed composition logs agree by the supplied
composition-trace preservation law.
-/
theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount := by
  calc
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
        P.traceLog source.source.initialState
          (compositionTrace source.source.burdenAction
            source.source.supportAction burdenCount supportCount) := rfl
    _ = source.alternative.traceLog source.targetInitialState
          (compositionTrace
            (source.toAction source.source.burdenAction)
            (source.toAction source.source.supportAction)
            burdenCount supportCount) :=
        source.preserves_composition_traceLog burdenCount supportCount
    _ = source.targetObservedSource.traceLogOfCounts
          burdenCount supportCount := rfl

/--
No fixed-unit additive scalar readout can preserve all target-side observed
composition logs under only the decisive composition-trace preservation data.
-/
theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toTargetResponseSeparatedCompositionSource
    |>.no_additiveScalar_traceLog_decoder

/--
The two-component coordinate can preserve all composition-trace transported
target logs.
-/
theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toTargetResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_traceLog_readout

end CompositionTraceMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by generated
composition-trace behavior only.

Compared with `CompositionTraceMappedResponseSeparatedCompositionSource`, this
surface no longer supplies the one-step burden/support response equalities as
independent fields.  They are derived from preservation of the generated
composition traces at counts `(1, 0)` and `(0, 1)`.
-/
structure GeneratedTraceMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAction : Action -> AlternativeAction
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  preserves_generated_traceLog :
    forall burdenCount supportCount,
      P.traceLog source.initialState
          (compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount) =
        alternative.traceLog targetInitialState
          (compositionTrace
            (toAction source.burdenAction)
            (toAction source.supportAction)
            burdenCount supportCount)

namespace GeneratedTraceMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  GeneratedTraceMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The burden-channel one-step response equality is not an extra input: it is the
head of the generated composition trace with counts `(1, 0)`.
-/
theorem preserves_burden_response :
    source.alternative.response source.targetInitialState
        (source.toAction source.source.burdenAction) =
      P.response source.source.initialState source.source.burdenAction := by
  have h := source.preserves_generated_traceLog 1 0
  change
    P.traceLog source.source.initialState [source.source.burdenAction] =
      source.alternative.traceLog source.targetInitialState
        [source.toAction source.source.burdenAction] at h
  change
    [P.response source.source.initialState source.source.burdenAction] =
      [source.alternative.response source.targetInitialState
        (source.toAction source.source.burdenAction)] at h
  exact (List.cons.inj h).1.symm

/--
The support-channel one-step response equality is likewise the head of the
generated composition trace with counts `(0, 1)`.
-/
theorem preserves_support_response :
    source.alternative.response source.targetInitialState
        (source.toAction source.source.supportAction) =
      P.response source.source.initialState source.source.supportAction := by
  have h := source.preserves_generated_traceLog 0 1
  change
    P.traceLog source.source.initialState [source.source.supportAction] =
      source.alternative.traceLog source.targetInitialState
        [source.toAction source.source.supportAction] at h
  change
    [P.response source.source.initialState source.source.supportAction] =
      [source.alternative.response source.targetInitialState
        (source.toAction source.source.supportAction)] at h
  exact (List.cons.inj h).1.symm

/--
Generated composition-trace behavior induces the previous decisive
composition-trace transport boundary.
-/
def toCompositionTraceMappedResponseSeparatedCompositionSource :
    CompositionTraceMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  toAction := source.toAction
  source := source.source
  targetInitialState := source.targetInitialState
  preserves_burden_response := source.preserves_burden_response
  preserves_support_response := source.preserves_support_response
  preserves_composition_traceLog := source.preserves_generated_traceLog

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

/--
The generated-trace route preserves the same source/target composition-log
alignment.
-/
theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
No fixed-unit additive scalar readout can preserve all target-side observed
composition logs under generated composition-trace behavior.
-/
theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

/--
The two-component coordinate can preserve all generated-trace transported
target logs.
-/
theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end GeneratedTraceMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by a local relation that is
closed only under the two generated composition actions.

This is weaker than a full trace simulation: it does not quantify over all
source actions.  It preserves observable views along a relation and requires
step closure only for the source's burden/support actions.  From those local
facts, preservation of every generated `compositionTrace` is derived by
induction.
-/
structure CompositionTraceRelationMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAction : Action -> AlternativeAction
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  related : State -> AlternativeState -> Prop
  initial_related : related source.initialState targetInitialState
  preserves_observation :
    forall {s t}, related s t -> alternative.observe t = P.observe s
  preserves_readout :
    forall {s t}, related s t -> alternative.readout t = P.readout s
  burden_step_related :
    forall {s t}, related s t ->
      related
        (P.step s source.burdenAction)
        (alternative.step t (toAction source.burdenAction))
  support_step_related :
    forall {s t}, related s t ->
      related
        (P.step s source.supportAction)
        (alternative.step t (toAction source.supportAction))

namespace CompositionTraceRelationMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTraceRelationMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
Support-only generated traces preserve their observable prefix logs along the
local relation.
-/
theorem preserves_supportTraceLog_from_related
    (supportCount : Nat)
    {s : State} {t : AlternativeState}
    (h : source.related s t) :
    P.traceLog s
        (List.replicate supportCount source.source.supportAction) =
      source.alternative.traceLog t
        (List.replicate supportCount
          (source.toAction source.source.supportAction)) := by
  induction supportCount generalizing s t with
  | zero => rfl
  | succ supportRest ih =>
      have hnext := source.support_step_related h
      have hhead :
          (P.observe (P.step s source.source.supportAction),
              P.readout (P.step s source.source.supportAction)) =
            (source.alternative.observe
                (source.alternative.step t
                  (source.toAction source.source.supportAction)),
              source.alternative.readout
                (source.alternative.step t
                  (source.toAction source.source.supportAction))) := by
        exact
          Prod.ext
            (source.preserves_observation hnext).symm
            (source.preserves_readout hnext).symm
      have htail :
          P.traceLog
              (P.step s source.source.supportAction)
              (List.replicate supportRest source.source.supportAction) =
            source.alternative.traceLog
              (source.alternative.step t
                (source.toAction source.source.supportAction))
              (List.replicate supportRest
                (source.toAction source.source.supportAction)) :=
        ih hnext
      change
        (P.observe (P.step s source.source.supportAction),
            P.readout (P.step s source.source.supportAction)) ::
          P.traceLog
            (P.step s source.source.supportAction)
            (List.replicate supportRest source.source.supportAction) =
        (source.alternative.observe
            (source.alternative.step t
              (source.toAction source.source.supportAction)),
          source.alternative.readout
            (source.alternative.step t
              (source.toAction source.source.supportAction))) ::
          source.alternative.traceLog
            (source.alternative.step t
              (source.toAction source.source.supportAction))
            (List.replicate supportRest
              (source.toAction source.source.supportAction))
      exact congrArg₂ List.cons hhead htail

/--
Every generated burden-then-support composition trace preserves its observable
prefix log along the local two-action relation.
-/
theorem preserves_compositionTraceLog_from_related
    (burdenCount supportCount : Nat)
    {s : State} {t : AlternativeState}
    (h : source.related s t) :
    P.traceLog s
        (compositionTrace source.source.burdenAction
          source.source.supportAction burdenCount supportCount) =
      source.alternative.traceLog t
        (compositionTrace
          (source.toAction source.source.burdenAction)
          (source.toAction source.source.supportAction)
          burdenCount supportCount) := by
  induction burdenCount generalizing s t with
  | zero =>
      change
        P.traceLog s
            (List.replicate supportCount source.source.supportAction) =
          source.alternative.traceLog t
            (List.replicate supportCount
              (source.toAction source.source.supportAction))
      exact source.preserves_supportTraceLog_from_related supportCount h
  | succ burdenRest ih =>
      have hnext := source.burden_step_related h
      have hhead :
          (P.observe (P.step s source.source.burdenAction),
              P.readout (P.step s source.source.burdenAction)) =
            (source.alternative.observe
                (source.alternative.step t
                  (source.toAction source.source.burdenAction)),
              source.alternative.readout
                (source.alternative.step t
                  (source.toAction source.source.burdenAction))) := by
        exact
          Prod.ext
            (source.preserves_observation hnext).symm
            (source.preserves_readout hnext).symm
      have htail :
          P.traceLog
              (P.step s source.source.burdenAction)
              (compositionTrace source.source.burdenAction
                source.source.supportAction burdenRest supportCount) =
            source.alternative.traceLog
              (source.alternative.step t
                (source.toAction source.source.burdenAction))
              (compositionTrace
                (source.toAction source.source.burdenAction)
                (source.toAction source.source.supportAction)
                burdenRest supportCount) :=
        ih hnext
      change
        (P.observe (P.step s source.source.burdenAction),
            P.readout (P.step s source.source.burdenAction)) ::
          P.traceLog
            (P.step s source.source.burdenAction)
            (compositionTrace source.source.burdenAction
              source.source.supportAction burdenRest supportCount) =
        (source.alternative.observe
            (source.alternative.step t
              (source.toAction source.source.burdenAction)),
          source.alternative.readout
            (source.alternative.step t
              (source.toAction source.source.burdenAction))) ::
          source.alternative.traceLog
            (source.alternative.step t
              (source.toAction source.source.burdenAction))
            (compositionTrace
              (source.toAction source.source.burdenAction)
              (source.toAction source.source.supportAction)
              burdenRest supportCount)
      exact congrArg₂ List.cons hhead htail

/--
The local two-action relation induces the generated composition-trace
behavior boundary.
-/
def toGeneratedTraceMappedResponseSeparatedCompositionSource :
    GeneratedTraceMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  toAction := source.toAction
  source := source.source
  targetInitialState := source.targetInitialState
  preserves_generated_traceLog := by
    intro burdenCount supportCount
    exact
      source.preserves_compositionTraceLog_from_related
        burdenCount supportCount source.initial_related

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end CompositionTraceRelationMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by a local map that
commutes only with the two generated composition actions.

This is weaker than a full transition map: it does not quantify over all
actions.  It is also stronger than the local relation boundary above, because
the relation is no longer supplied directly; it is constructed as the graph of
`toState`.  The two local step-commutation laws are still inputs.
-/
structure CompositionTraceMapMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toState : State -> AlternativeState
  toAction : Action -> AlternativeAction
  source : ResponseSeparatedCompositionSource P
  preserves_observation :
    forall s, alternative.observe (toState s) = P.observe s
  preserves_readout :
    forall s, alternative.readout (toState s) = P.readout s
  burden_step_commutes :
    forall s,
      toState (P.step s source.burdenAction) =
        alternative.step (toState s) (toAction source.burdenAction)
  support_step_commutes :
    forall s,
      toState (P.step s source.supportAction) =
        alternative.step (toState s) (toAction source.supportAction)

namespace CompositionTraceMapMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTraceMapMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The graph relation generated by the local two-action map.
-/
def toCompositionTraceRelationMappedResponseSeparatedCompositionSource :
    CompositionTraceRelationMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  toAction := source.toAction
  source := source.source
  targetInitialState := source.toState source.source.initialState
  related := fun sourceState targetState =>
    targetState = source.toState sourceState
  initial_related := rfl
  preserves_observation := by
    intro sourceState targetState h
    rw [h]
    exact source.preserves_observation sourceState
  preserves_readout := by
    intro sourceState targetState h
    rw [h]
    exact source.preserves_readout sourceState
  burden_step_related := by
    intro sourceState targetState h
    rw [h]
    exact (source.burden_step_commutes sourceState).symm
  support_step_related := by
    intro sourceState targetState h
    rw [h]
    exact (source.support_step_commutes sourceState).symm

/--
The local two-action map induces the generated composition-trace behavior
boundary through its graph relation.
-/
def toGeneratedTraceMappedResponseSeparatedCompositionSource :
    GeneratedTraceMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction :=
  source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.toGeneratedTraceMappedResponseSeparatedCompositionSource

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem mapTrace_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem mapTrace_no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem mapTrace_exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end CompositionTraceMapMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by only a state map and
the two target generated actions.

Unlike `CompositionTraceMapMappedResponseSeparatedCompositionSource`, this
surface does not require a global action adapter `Action -> AlternativeAction`.
It supplies only the target actions corresponding to the source
burden/support generators, plus the two local step-commutation laws for those
actions.  The map and local commutation laws are still inputs.
-/
structure CompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toState : State -> AlternativeState
  source : ResponseSeparatedCompositionSource P
  targetBurdenAction : AlternativeAction
  targetSupportAction : AlternativeAction
  preserves_observation :
    forall s, alternative.observe (toState s) = P.observe s
  preserves_readout :
    forall s, alternative.readout (toState s) = P.readout s
  burden_step_commutes :
    forall s,
      toState (P.step s source.burdenAction) =
        alternative.step (toState s) targetBurdenAction
  support_step_commutes :
    forall s,
      toState (P.step s source.supportAction) =
        alternative.step (toState s) targetSupportAction

namespace CompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/-- The burden one-step response is transported by the local target action. -/
theorem preserves_burden_response :
    source.alternative.response
        (source.toState source.source.initialState)
        source.targetBurdenAction =
      P.response source.source.initialState source.source.burdenAction := by
  have hstep :
      source.alternative.step
          (source.toState source.source.initialState)
          source.targetBurdenAction =
        source.toState
          (P.step source.source.initialState source.source.burdenAction) :=
    (source.burden_step_commutes source.source.initialState).symm
  exact
    Prod.ext
      (calc
        source.alternative.observe
            (source.alternative.step
              (source.toState source.source.initialState)
              source.targetBurdenAction) =
            source.alternative.observe
              (source.toState
                (P.step source.source.initialState
                  source.source.burdenAction)) := by
          rw [hstep]
        _ = P.observe
              (P.step source.source.initialState
                source.source.burdenAction) :=
          source.preserves_observation
            (P.step source.source.initialState
              source.source.burdenAction))
      (calc
        source.alternative.readout
            (source.alternative.step
              (source.toState source.source.initialState)
              source.targetBurdenAction) =
            source.alternative.readout
              (source.toState
                (P.step source.source.initialState
                  source.source.burdenAction)) := by
          rw [hstep]
        _ = P.readout
              (P.step source.source.initialState
                source.source.burdenAction) :=
          source.preserves_readout
            (P.step source.source.initialState
              source.source.burdenAction))

/-- The support one-step response is transported by the local target action. -/
theorem preserves_support_response :
    source.alternative.response
        (source.toState source.source.initialState)
        source.targetSupportAction =
      P.response source.source.initialState source.source.supportAction := by
  have hstep :
      source.alternative.step
          (source.toState source.source.initialState)
          source.targetSupportAction =
        source.toState
          (P.step source.source.initialState source.source.supportAction) :=
    (source.support_step_commutes source.source.initialState).symm
  exact
    Prod.ext
      (calc
        source.alternative.observe
            (source.alternative.step
              (source.toState source.source.initialState)
              source.targetSupportAction) =
            source.alternative.observe
              (source.toState
                (P.step source.source.initialState
                  source.source.supportAction)) := by
          rw [hstep]
        _ = P.observe
              (P.step source.source.initialState
                source.source.supportAction) :=
          source.preserves_observation
            (P.step source.source.initialState
              source.source.supportAction))
      (calc
        source.alternative.readout
            (source.alternative.step
              (source.toState source.source.initialState)
              source.targetSupportAction) =
            source.alternative.readout
              (source.toState
                (P.step source.source.initialState
                  source.source.supportAction)) := by
          rw [hstep]
        _ = P.readout
              (P.step source.source.initialState
                source.source.supportAction) :=
          source.preserves_readout
            (P.step source.source.initialState
              source.source.supportAction))

/--
The target-side response-separated source induced by the two local target
actions.
-/
def toTargetResponseSeparatedCompositionSource :
    ResponseSeparatedCompositionSource source.alternative where
  initialState := source.toState source.source.initialState
  burdenAction := source.targetBurdenAction
  supportAction := source.targetSupportAction
  burdenUnit := source.source.burdenUnit
  supportUnit := source.source.supportUnit
  burdenUnit_pos := source.source.burdenUnit_pos
  supportUnit_pos := source.source.supportUnit_pos
  response_ne := by
    intro htarget
    apply source.source.response_ne
    calc
      P.response source.source.initialState source.source.burdenAction =
          source.alternative.response
            (source.toState source.source.initialState)
            source.targetBurdenAction :=
        (source.preserves_burden_response).symm
      _ = source.alternative.response
            (source.toState source.source.initialState)
            source.targetSupportAction := htarget
      _ = P.response source.source.initialState source.source.supportAction :=
        source.preserves_support_response

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toTargetResponseSeparatedCompositionSource
    |>.toObservedAdditiveCompositionSource

/--
Support-only generated traces preserve their observable prefix logs through
the two-action state map.
-/
theorem preserves_supportTraceLog
    (supportCount : Nat)
    (s : State) :
    P.traceLog s
        (List.replicate supportCount source.source.supportAction) =
      source.alternative.traceLog (source.toState s)
        (List.replicate supportCount source.targetSupportAction) := by
  induction supportCount generalizing s with
  | zero => rfl
  | succ supportRest ih =>
      have hstep :
          source.alternative.step (source.toState s)
              source.targetSupportAction =
            source.toState (P.step s source.source.supportAction) :=
        (source.support_step_commutes s).symm
      have hhead :
          (P.observe (P.step s source.source.supportAction),
              P.readout (P.step s source.source.supportAction)) =
            (source.alternative.observe
                (source.alternative.step (source.toState s)
                  source.targetSupportAction),
              source.alternative.readout
                (source.alternative.step (source.toState s)
                  source.targetSupportAction)) := by
        exact
          Prod.ext
            (calc
              P.observe (P.step s source.source.supportAction) =
                  source.alternative.observe
                    (source.toState
                      (P.step s source.source.supportAction)) :=
                (source.preserves_observation
                  (P.step s source.source.supportAction)).symm
              _ = source.alternative.observe
                    (source.alternative.step (source.toState s)
                      source.targetSupportAction) := by
                rw [hstep])
            (calc
              P.readout (P.step s source.source.supportAction) =
                  source.alternative.readout
                    (source.toState
                      (P.step s source.source.supportAction)) :=
                (source.preserves_readout
                  (P.step s source.source.supportAction)).symm
              _ = source.alternative.readout
                    (source.alternative.step (source.toState s)
                      source.targetSupportAction) := by
                rw [hstep])
      have htail :
          P.traceLog
              (P.step s source.source.supportAction)
              (List.replicate supportRest source.source.supportAction) =
            source.alternative.traceLog
              (source.alternative.step (source.toState s)
                source.targetSupportAction)
              (List.replicate supportRest source.targetSupportAction) := by
        simpa [hstep] using
          ih (P.step s source.source.supportAction)
      change
        (P.observe (P.step s source.source.supportAction),
            P.readout (P.step s source.source.supportAction)) ::
          P.traceLog
            (P.step s source.source.supportAction)
            (List.replicate supportRest source.source.supportAction) =
        (source.alternative.observe
            (source.alternative.step (source.toState s)
              source.targetSupportAction),
          source.alternative.readout
            (source.alternative.step (source.toState s)
              source.targetSupportAction)) ::
          source.alternative.traceLog
            (source.alternative.step (source.toState s)
              source.targetSupportAction)
            (List.replicate supportRest source.targetSupportAction)
      exact congrArg₂ List.cons hhead htail

/--
Every generated burden-then-support composition trace preserves its observable
prefix log through the two-action state map.
-/
theorem preserves_compositionTraceLog
    (burdenCount supportCount : Nat)
    (s : State) :
    P.traceLog s
        (compositionTrace source.source.burdenAction
          source.source.supportAction burdenCount supportCount) =
      source.alternative.traceLog (source.toState s)
        (compositionTrace source.targetBurdenAction
          source.targetSupportAction burdenCount supportCount) := by
  induction burdenCount generalizing s with
  | zero =>
      change
        P.traceLog s
            (List.replicate supportCount source.source.supportAction) =
          source.alternative.traceLog (source.toState s)
            (List.replicate supportCount source.targetSupportAction)
      exact source.preserves_supportTraceLog supportCount s
  | succ burdenRest ih =>
      have hstep :
          source.alternative.step (source.toState s)
              source.targetBurdenAction =
            source.toState (P.step s source.source.burdenAction) :=
        (source.burden_step_commutes s).symm
      have hhead :
          (P.observe (P.step s source.source.burdenAction),
              P.readout (P.step s source.source.burdenAction)) =
            (source.alternative.observe
                (source.alternative.step (source.toState s)
                  source.targetBurdenAction),
              source.alternative.readout
                (source.alternative.step (source.toState s)
                  source.targetBurdenAction)) := by
        exact
          Prod.ext
            (calc
              P.observe (P.step s source.source.burdenAction) =
                  source.alternative.observe
                    (source.toState
                      (P.step s source.source.burdenAction)) :=
                (source.preserves_observation
                  (P.step s source.source.burdenAction)).symm
              _ = source.alternative.observe
                    (source.alternative.step (source.toState s)
                      source.targetBurdenAction) := by
                rw [hstep])
            (calc
              P.readout (P.step s source.source.burdenAction) =
                  source.alternative.readout
                    (source.toState
                      (P.step s source.source.burdenAction)) :=
                (source.preserves_readout
                  (P.step s source.source.burdenAction)).symm
              _ = source.alternative.readout
                    (source.alternative.step (source.toState s)
                      source.targetBurdenAction) := by
                rw [hstep])
      have htail :
          P.traceLog
              (P.step s source.source.burdenAction)
              (compositionTrace source.source.burdenAction
                source.source.supportAction burdenRest supportCount) =
            source.alternative.traceLog
              (source.alternative.step (source.toState s)
                source.targetBurdenAction)
              (compositionTrace source.targetBurdenAction
                source.targetSupportAction burdenRest supportCount) := by
        simpa [hstep] using
          ih (P.step s source.source.burdenAction)
      change
        (P.observe (P.step s source.source.burdenAction),
            P.readout (P.step s source.source.burdenAction)) ::
          P.traceLog
            (P.step s source.source.burdenAction)
            (compositionTrace source.source.burdenAction
              source.source.supportAction burdenRest supportCount) =
        (source.alternative.observe
            (source.alternative.step (source.toState s)
              source.targetBurdenAction),
          source.alternative.readout
            (source.alternative.step (source.toState s)
              source.targetBurdenAction)) ::
          source.alternative.traceLog
            (source.alternative.step (source.toState s)
              source.targetBurdenAction)
            (compositionTrace source.targetBurdenAction
              source.targetSupportAction burdenRest supportCount)
      exact congrArg₂ List.cons hhead htail

theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.preserves_compositionTraceLog burdenCount supportCount
    source.source.initialState

theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toTargetResponseSeparatedCompositionSource
    |>.no_additiveScalar_traceLog_decoder

theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toTargetResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_traceLog_readout

end CompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported by a generated-prefix
state tree.

This is narrower than the two-action state-map boundary above: there is no
global source-state adapter.  It supplies source/target states only for
prefixes of the generated burden/support language, plus local step laws for
extending such prefixes by the burden or support action.  The prefix trees and
their local laws are still inputs.
-/
structure CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  source : ResponseSeparatedCompositionSource P
  targetBurdenAction : AlternativeAction
  targetSupportAction : AlternativeAction
  sourceStateOfPrefix : List Bool -> State
  targetStateOfPrefix : List Bool -> AlternativeState
  source_initial :
    sourceStateOfPrefix [] = source.initialState
  preserves_observation :
    forall pref,
      alternative.observe (targetStateOfPrefix pref) =
        P.observe (sourceStateOfPrefix pref)
  preserves_readout :
    forall pref,
      alternative.readout (targetStateOfPrefix pref) =
        P.readout (sourceStateOfPrefix pref)
  source_burden_step_commutes :
    forall pref,
      sourceStateOfPrefix (pref ++ [true]) =
        P.step (sourceStateOfPrefix pref) source.burdenAction
  source_support_step_commutes :
    forall pref,
      sourceStateOfPrefix (pref ++ [false]) =
        P.step (sourceStateOfPrefix pref) source.supportAction
  burden_step_commutes :
    forall pref,
      targetStateOfPrefix (pref ++ [true]) =
        alternative.step (targetStateOfPrefix pref) targetBurdenAction
  support_step_commutes :
    forall pref,
      targetStateOfPrefix (pref ++ [false]) =
        alternative.step (targetStateOfPrefix pref) targetSupportAction

namespace CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/-- Source action selected by a generated burden/support tag. -/
def sourceActionOfTag : Bool -> Action
  | true => source.source.burdenAction
  | false => source.source.supportAction

/-- Target action selected by a generated burden/support tag. -/
def targetActionOfTag : Bool -> AlternativeAction
  | true => source.targetBurdenAction
  | false => source.targetSupportAction

/-- Target prefix extension follows the supplied local generated-action law. -/
theorem target_step_commutes
    (pref : List Bool)
    (tag : Bool) :
    source.targetStateOfPrefix (pref ++ [tag]) =
      source.alternative.step
        (source.targetStateOfPrefix pref)
        (source.targetActionOfTag tag) := by
  cases tag
  · change
      source.targetStateOfPrefix (pref ++ [false]) =
        source.alternative.step
          (source.targetStateOfPrefix pref)
          source.targetSupportAction
    exact source.support_step_commutes pref
  · change
      source.targetStateOfPrefix (pref ++ [true]) =
        source.alternative.step
          (source.targetStateOfPrefix pref)
          source.targetBurdenAction
    exact source.burden_step_commutes pref

/-- Source prefix extension follows the supplied local generated-action law. -/
theorem source_step_commutes
    (pref : List Bool)
    (tag : Bool) :
    source.sourceStateOfPrefix (pref ++ [tag]) =
      P.step
        (source.sourceStateOfPrefix pref)
        (source.sourceActionOfTag tag) := by
  cases tag
  · change
      source.sourceStateOfPrefix (pref ++ [false]) =
        P.step
          (source.sourceStateOfPrefix pref)
          source.source.supportAction
    exact source.source_support_step_commutes pref
  · change
      source.sourceStateOfPrefix (pref ++ [true]) =
        P.step
          (source.sourceStateOfPrefix pref)
          source.source.burdenAction
    exact source.source_burden_step_commutes pref

/--
Every generated tag trace preserves its observable prefix log from any
generated prefix.
-/
theorem preserves_traceLogFromPrefix
    (pref actions : List Bool) :
    P.traceLog
        (source.sourceStateOfPrefix pref)
        (actions.map source.sourceActionOfTag) =
      source.alternative.traceLog
        (source.targetStateOfPrefix pref)
        (actions.map source.targetActionOfTag) := by
  induction actions generalizing pref with
  | nil => rfl
  | cons tag actions ih =>
      have hsource := source.source_step_commutes pref tag
      have htarget := source.target_step_commutes pref tag
      have hhead :
          (P.observe
              (P.step
                (source.sourceStateOfPrefix pref)
                (source.sourceActionOfTag tag)),
            P.readout
              (P.step
                (source.sourceStateOfPrefix pref)
                (source.sourceActionOfTag tag))) =
          (source.alternative.observe
              (source.alternative.step
                (source.targetStateOfPrefix pref)
                (source.targetActionOfTag tag)),
            source.alternative.readout
              (source.alternative.step
                (source.targetStateOfPrefix pref)
                (source.targetActionOfTag tag))) := by
        exact
          Prod.ext
            (calc
              P.observe
                  (P.step
                    (source.sourceStateOfPrefix pref)
                    (source.sourceActionOfTag tag)) =
                  P.observe
                    (source.sourceStateOfPrefix (pref ++ [tag])) := by
                rw [hsource]
              _ = source.alternative.observe
                    (source.targetStateOfPrefix (pref ++ [tag])) :=
                (source.preserves_observation (pref ++ [tag])).symm
              _ = source.alternative.observe
                    (source.alternative.step
                      (source.targetStateOfPrefix pref)
                      (source.targetActionOfTag tag)) := by
                rw [htarget])
            (calc
              P.readout
                  (P.step
                    (source.sourceStateOfPrefix pref)
                    (source.sourceActionOfTag tag)) =
                  P.readout
                    (source.sourceStateOfPrefix (pref ++ [tag])) := by
                rw [hsource]
              _ = source.alternative.readout
                    (source.targetStateOfPrefix (pref ++ [tag])) :=
                (source.preserves_readout (pref ++ [tag])).symm
              _ = source.alternative.readout
                    (source.alternative.step
                      (source.targetStateOfPrefix pref)
                      (source.targetActionOfTag tag)) := by
                rw [htarget])
      have htail :
          P.traceLog
              (P.step
                (source.sourceStateOfPrefix pref)
                (source.sourceActionOfTag tag))
              (actions.map source.sourceActionOfTag) =
            source.alternative.traceLog
              (source.alternative.step
                (source.targetStateOfPrefix pref)
                (source.targetActionOfTag tag))
              (actions.map source.targetActionOfTag) := by
        simpa [hsource, htarget] using
          ih (pref ++ [tag])
      change
        (P.observe
            (P.step
              (source.sourceStateOfPrefix pref)
              (source.sourceActionOfTag tag)),
          P.readout
            (P.step
              (source.sourceStateOfPrefix pref)
              (source.sourceActionOfTag tag))) ::
          P.traceLog
            (P.step
              (source.sourceStateOfPrefix pref)
              (source.sourceActionOfTag tag))
            (actions.map source.sourceActionOfTag) =
        (source.alternative.observe
            (source.alternative.step
              (source.targetStateOfPrefix pref)
              (source.targetActionOfTag tag)),
          source.alternative.readout
            (source.alternative.step
              (source.targetStateOfPrefix pref)
              (source.targetActionOfTag tag))) ::
          source.alternative.traceLog
            (source.alternative.step
              (source.targetStateOfPrefix pref)
              (source.targetActionOfTag tag))
            (actions.map source.targetActionOfTag)
      exact congrArg₂ List.cons hhead htail

/-- The burden one-step response is transported by the prefix tree. -/
theorem preserves_burden_response :
    source.alternative.response
        (source.targetStateOfPrefix [])
        source.targetBurdenAction =
      P.response source.source.initialState source.source.burdenAction := by
  have h := source.preserves_traceLogFromPrefix [] [true]
  rw [source.source_initial] at h
  change
    [P.response source.source.initialState source.source.burdenAction] =
      [source.alternative.response
        (source.targetStateOfPrefix []) source.targetBurdenAction] at h
  exact (List.cons.inj h).1.symm

/-- The support one-step response is transported by the prefix tree. -/
theorem preserves_support_response :
    source.alternative.response
        (source.targetStateOfPrefix [])
        source.targetSupportAction =
      P.response source.source.initialState source.source.supportAction := by
  have h := source.preserves_traceLogFromPrefix [] [false]
  rw [source.source_initial] at h
  change
    [P.response source.source.initialState source.source.supportAction] =
      [source.alternative.response
        (source.targetStateOfPrefix []) source.targetSupportAction] at h
  exact (List.cons.inj h).1.symm

/--
The target-side response-separated source induced by the prefix tree.
-/
def toTargetResponseSeparatedCompositionSource :
    ResponseSeparatedCompositionSource source.alternative where
  initialState := source.targetStateOfPrefix []
  burdenAction := source.targetBurdenAction
  supportAction := source.targetSupportAction
  burdenUnit := source.source.burdenUnit
  supportUnit := source.source.supportUnit
  burdenUnit_pos := source.source.burdenUnit_pos
  supportUnit_pos := source.source.supportUnit_pos
  response_ne := by
    intro htarget
    apply source.source.response_ne
    calc
      P.response source.source.initialState source.source.burdenAction =
          source.alternative.response
            (source.targetStateOfPrefix [])
            source.targetBurdenAction :=
        (source.preserves_burden_response).symm
      _ = source.alternative.response
            (source.targetStateOfPrefix [])
            source.targetSupportAction := htarget
      _ = P.response source.source.initialState source.source.supportAction :=
        source.preserves_support_response

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toTargetResponseSeparatedCompositionSource
    |>.toObservedAdditiveCompositionSource

/--
Every generated burden-then-support composition trace preserves its observable
prefix log through the generated-prefix tree.
-/
theorem preserves_compositionTraceLog
    (burdenCount supportCount : Nat) :
    P.traceLog source.source.initialState
        (compositionTrace source.source.burdenAction
          source.source.supportAction burdenCount supportCount) =
      source.alternative.traceLog (source.targetStateOfPrefix [])
        (compositionTrace source.targetBurdenAction
          source.targetSupportAction burdenCount supportCount) := by
  have h :=
    source.preserves_traceLogFromPrefix []
      (compositionTrace true false burdenCount supportCount)
  rw [source.source_initial] at h
  have hsourceMap :
      (compositionTrace true false burdenCount supportCount).map
          source.sourceActionOfTag =
        compositionTrace source.source.burdenAction
          source.source.supportAction burdenCount supportCount :=
    map_compositionTrace source.sourceActionOfTag true false
      burdenCount supportCount
  have htargetMap :
      (compositionTrace true false burdenCount supportCount).map
          source.targetActionOfTag =
        compositionTrace source.targetBurdenAction
          source.targetSupportAction burdenCount supportCount :=
    map_compositionTrace source.targetActionOfTag true false
      burdenCount supportCount
  calc
    P.traceLog source.source.initialState
        (compositionTrace source.source.burdenAction
          source.source.supportAction burdenCount supportCount) =
        P.traceLog source.source.initialState
          ((compositionTrace true false burdenCount supportCount).map
            source.sourceActionOfTag) := by
          rw [hsourceMap]
    _ = source.alternative.traceLog (source.targetStateOfPrefix [])
          ((compositionTrace true false burdenCount supportCount).map
            source.targetActionOfTag) := h
    _ = source.alternative.traceLog (source.targetStateOfPrefix [])
          (compositionTrace source.targetBurdenAction
            source.targetSupportAction burdenCount supportCount) := by
          rw [htargetMap]

theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.preserves_compositionTraceLog burdenCount supportCount

theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toTargetResponseSeparatedCompositionSource
    |>.no_additiveScalar_traceLog_decoder

theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toTargetResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_traceLog_readout

end CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource

/-- Generated action selected by a burden/support tag. -/
def generatedActionOfTag (burdenAction supportAction : Action) : Bool -> Action
  | true => burdenAction
  | false => supportAction

/--
State reached by folding a generated burden/support prefix.

This is a generated prefix tree, not a supplied tree: the prefix state is
computed from the initial state and the two generated actions.
-/
def generatedPrefixState
    (P : ObservationalPersistenceProcess State Action Observation)
    (initialState : State)
    (burdenAction supportAction : Action)
    (pref : List Bool) : State :=
  pref.foldl
    (fun state tag =>
      P.step state (generatedActionOfTag burdenAction supportAction tag))
    initialState

theorem generatedPrefixState_append_single
    (P : ObservationalPersistenceProcess State Action Observation)
    (initialState : State)
    (burdenAction supportAction : Action)
    (pref : List Bool)
    (tag : Bool) :
    generatedPrefixState P initialState burdenAction supportAction
        (pref ++ [tag]) =
      P.step
        (generatedPrefixState P initialState burdenAction supportAction pref)
        (generatedActionOfTag burdenAction supportAction tag) := by
  induction pref generalizing initialState with
  | nil =>
      rfl
  | cons head tail ih =>
      change
        generatedPrefixState P
            (P.step initialState
              (generatedActionOfTag burdenAction supportAction head))
            burdenAction supportAction
            (tail ++ [tag]) =
          P.step
            (generatedPrefixState P
              (P.step initialState
                (generatedActionOfTag burdenAction supportAction head))
              burdenAction supportAction tail)
            (generatedActionOfTag burdenAction supportAction tag)
      exact
        ih
          (P.step initialState
            (generatedActionOfTag burdenAction supportAction head))

/--
Canonical trace behavior is preserved along generated burden/support prefixes.

This is the fixed-translator bridge into the generated-prefix lane: once a
translator preserves all finite trace logs at the initial state, the same
trace-behavior relation holds at every generated prefix obtained by following
the translated burden/support actions.
-/
theorem traceBehaviorRelated_generatedPrefixState
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    (toAction : Action -> AlternativeAction)
    {initialState : State} {targetInitialState : AlternativeState}
    (hbehavior :
      traceBehaviorRelated P alternative toAction
        initialState targetInitialState)
    (burdenAction supportAction : Action)
    (pref : List Bool) :
    traceBehaviorRelated P alternative toAction
      (generatedPrefixState P initialState burdenAction supportAction pref)
      (generatedPrefixState alternative targetInitialState
        (toAction burdenAction) (toAction supportAction) pref) := by
  induction pref generalizing initialState targetInitialState with
  | nil =>
      exact hbehavior
  | cons tag rest ih =>
      cases tag
      · change
          traceBehaviorRelated P alternative toAction
            (generatedPrefixState P
              (P.step initialState supportAction)
              burdenAction supportAction rest)
            (generatedPrefixState alternative
              (alternative.step targetInitialState (toAction supportAction))
              (toAction burdenAction) (toAction supportAction) rest)
        exact
          ih
            (TraceBehaviorRelated.step_related
              toAction hbehavior supportAction)
      · change
          traceBehaviorRelated P alternative toAction
            (generatedPrefixState P
              (P.step initialState burdenAction)
              burdenAction supportAction rest)
            (generatedPrefixState alternative
              (alternative.step targetInitialState (toAction burdenAction))
              (toAction burdenAction) (toAction supportAction) rest)
        exact
          ih
            (TraceBehaviorRelated.step_related
              toAction hbehavior burdenAction)

/--
Response-separated additive composition transported by generated prefix states.

This removes the supplied-prefix-tree layer: source and target prefix states
are generated by folding their respective burden/support actions.  The target
initial state, target burden/support actions, and observable-view preservation
on generated prefixes remain inputs.
-/
structure CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  targetBurdenAction : AlternativeAction
  targetSupportAction : AlternativeAction
  preserves_observation :
    forall pref,
      alternative.observe
          (generatedPrefixState alternative targetInitialState
            targetBurdenAction targetSupportAction pref) =
        P.observe
          (generatedPrefixState P source.initialState
            source.burdenAction source.supportAction pref)
  preserves_readout :
    forall pref,
      alternative.readout
          (generatedPrefixState alternative targetInitialState
            targetBurdenAction targetSupportAction pref) =
        P.readout
          (generatedPrefixState P source.initialState
            source.burdenAction source.supportAction pref)

namespace ResponseSeparatedCompositionSource

variable (source : ResponseSeparatedCompositionSource P)

/--
A fixed trace-behavior translator produces the generated-prefix mapped source.

The translator and initial trace-behavior evidence are still supplied.  This
bridge only shows that those stronger observational hypotheses imply the
generated-prefix preservation fields needed by the additive M/L-separation
lane.
-/
def toGeneratedPrefixMappedResponseSeparatedCompositionSource_of_traceBehaviorRelated
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {alternative :
      ObservationalPersistenceProcess AlternativeState AlternativeAction
        Observation}
    {targetInitialState : AlternativeState}
    (toAction : Action -> AlternativeAction)
    (hbehavior :
      traceBehaviorRelated P alternative toAction
        source.initialState targetInitialState) :
    CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := alternative
  source := source
  targetInitialState := targetInitialState
  targetBurdenAction := toAction source.burdenAction
  targetSupportAction := toAction source.supportAction
  preserves_observation := by
    intro pref
    exact
      TraceBehaviorRelated.preserves_observation toAction
        (traceBehaviorRelated_generatedPrefixState
          (P := P) (alternative := alternative)
          toAction hbehavior source.burdenAction source.supportAction pref)
  preserves_readout := by
    intro pref
    exact
      TraceBehaviorRelated.preserves_readout toAction
        (traceBehaviorRelated_generatedPrefixState
          (P := P) (alternative := alternative)
          toAction hbehavior source.burdenAction source.supportAction pref)

end ResponseSeparatedCompositionSource

namespace CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/-- Source generated-prefix state. -/
def sourceStateOfPrefix (pref : List Bool) : State :=
  generatedPrefixState P source.source.initialState
    source.source.burdenAction source.source.supportAction pref

/-- Target generated-prefix state. -/
def targetStateOfPrefix (pref : List Bool) : AlternativeState :=
  generatedPrefixState source.alternative source.targetInitialState
    source.targetBurdenAction source.targetSupportAction pref

/--
The generated-prefix state route supplies the previous prefix-tree boundary.
-/
def toPrefixTreeMappedResponseSeparatedCompositionSource :
    CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  source := source.source
  targetBurdenAction := source.targetBurdenAction
  targetSupportAction := source.targetSupportAction
  sourceStateOfPrefix := source.sourceStateOfPrefix
  targetStateOfPrefix := source.targetStateOfPrefix
  source_initial := rfl
  preserves_observation := source.preserves_observation
  preserves_readout := source.preserves_readout
  source_burden_step_commutes := by
    intro pref
    simpa [sourceStateOfPrefix, generatedActionOfTag] using
      generatedPrefixState_append_single P source.source.initialState
        source.source.burdenAction source.source.supportAction pref true
  source_support_step_commutes := by
    intro pref
    simpa [sourceStateOfPrefix, generatedActionOfTag] using
      generatedPrefixState_append_single P source.source.initialState
        source.source.burdenAction source.source.supportAction pref false
  burden_step_commutes := by
    intro pref
    simpa [targetStateOfPrefix, generatedActionOfTag] using
      generatedPrefixState_append_single source.alternative
        source.targetInitialState
        source.targetBurdenAction source.targetSupportAction pref true
  support_step_commutes := by
    intro pref
    simpa [targetStateOfPrefix, generatedActionOfTag] using
      generatedPrefixState_append_single source.alternative
        source.targetInitialState
        source.targetBurdenAction source.targetSupportAction pref false

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toPrefixTreeMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.toPrefixTreeMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toPrefixTreeMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toPrefixTreeMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource

namespace SimulationMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  SimulationMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
A supplied trace simulation provides the decisive composition-trace
preservation source.

This shows the composition-trace boundary is genuinely weaker bookkeeping:
full simulation laws imply it, but the boundary itself only records the
response split and generated composition traces needed by the additive no-go.
-/
def toCompositionTraceRelationMappedResponseSeparatedCompositionSource :
    CompositionTraceRelationMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  toAction := source.simulation.toAction
  source := source.source
  targetInitialState := source.targetInitialState
  related := source.simulation.related
  initial_related := source.initial_related
  preserves_observation := by
    intro s t h
    exact source.simulation.preserves_observation h
  preserves_readout := by
    intro s t h
    exact source.simulation.preserves_readout h
  burden_step_related := by
    intro s t h
    exact source.simulation.step_related h source.source.burdenAction
  support_step_related := by
    intro s t h
    exact source.simulation.step_related h source.source.supportAction

/--
A supplied trace simulation provides the generated composition-trace behavior
source by first restricting the simulation to the two generated actions.
-/
def toGeneratedTraceMappedResponseSeparatedCompositionSource :
    GeneratedTraceMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction :=
  source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.toGeneratedTraceMappedResponseSeparatedCompositionSource

theorem relationTrace_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      (source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
        burdenCount supportCount :=
  source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem relationTrace_no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource.targetObservedSource).scalarOfCounts
                burdenCount supportCount) =
            (source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
              burdenCount supportCount) :=
  source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem relationTrace_exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
            burdenCount supportCount :=
  source.toCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
A supplied trace simulation provides the decisive composition-trace
preservation source.

This factors through the generated-trace boundary, where the one-step response
equalities are derived from the generated traces rather than supplied as
independent fields.
-/
def toCompositionTraceMappedResponseSeparatedCompositionSource :
    CompositionTraceMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.toCompositionTraceMappedResponseSeparatedCompositionSource

/--
The generated-trace route preserves the same source/target log alignment.
-/
theorem generatedTrace_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      (source.toGeneratedTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
        burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
The target-side additive scalar no-go also follows from the generated-trace
route.
-/
theorem generatedTrace_no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toGeneratedTraceMappedResponseSeparatedCompositionSource.targetObservedSource).scalarOfCounts
                burdenCount supportCount) =
            (source.toGeneratedTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
              burdenCount supportCount) :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

/--
The two-component positive readout also follows from the generated-trace
route.
-/
theorem generatedTrace_exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toGeneratedTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
            burdenCount supportCount :=
  source.toGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The composition-trace route preserves the same source/target log alignment.
-/
theorem compositionTrace_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      (source.toCompositionTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
        burdenCount supportCount :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
The target-side additive scalar no-go also follows from the weaker
composition-trace route.
-/
theorem compositionTrace_no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toCompositionTraceMappedResponseSeparatedCompositionSource.targetObservedSource).scalarOfCounts
                burdenCount supportCount) =
            (source.toCompositionTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
              burdenCount supportCount) :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

/--
The two-component positive readout also follows from the weaker
composition-trace route.
-/
theorem compositionTrace_exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toCompositionTraceMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
            burdenCount supportCount :=
  source.toCompositionTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end SimulationMappedResponseSeparatedCompositionSource

/--
Response-separated additive composition transported through the canonical
trace-behavior relation.

This removes one supplied-simulation layer.  The relation is not an arbitrary
field: it is defined by equality of current observable views and all finite
translated prefix logs.  The action translation and the target initial state
are still inputs, so this is not yet an automatic action-adapter discovery
theorem.
-/
structure BehaviorMappedResponseSeparatedCompositionSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAction : Action -> AlternativeAction
  source : ResponseSeparatedCompositionSource P
  targetInitialState : AlternativeState
  initial_behavior :
    traceBehaviorRelated P alternative toAction
      source.initialState targetInitialState

namespace BehaviorMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  BehaviorMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
The trace simulation constructed from observable trace behavior.
-/
def toSimulationMappedResponseSeparatedCompositionSource :
    SimulationMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  simulation :=
    TraceBehaviorRelated.toTraceSimulation source.toAction
  source := source.source
  targetInitialState := source.targetInitialState
  initial_related := source.initial_behavior

/-- The target-side observed additive-composition source. -/
def targetObservedSource :
    ObservedAdditiveCompositionSource source.alternative :=
  source.toSimulationMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

/--
The source and target observed composition logs agree by the canonical
trace-behavior relation.
-/
theorem source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      source.targetObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  source.toSimulationMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
No fixed-unit additive scalar readout can preserve all target-side observed
composition logs transported by canonical trace behavior.
-/
theorem no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (source.targetObservedSource.scalarOfCounts
                burdenCount supportCount) =
            source.targetObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  source.toSimulationMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

/--
The two-component coordinate can preserve all behavior-transported target
composition logs.
-/
theorem exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          source.targetObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  source.toSimulationMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end BehaviorMappedResponseSeparatedCompositionSource

namespace SimulationMappedResponseSeparatedCompositionSource

variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable (source :
  SimulationMappedResponseSeparatedCompositionSource
    P AlternativeState AlternativeAction)

/--
A supplied trace simulation can be re-expressed as the canonical
trace-behavior relation for the additive-composition lane.

This does not derive the simulation from arbitrary alternatives.  It only says
that once local simulation laws are supplied, the all-prefix behavior relation
used by `BehaviorMappedResponseSeparatedCompositionSource` is no longer an
extra independent input.
-/
def toBehaviorMappedResponseSeparatedCompositionSource :
    BehaviorMappedResponseSeparatedCompositionSource
      P AlternativeState AlternativeAction where
  alternative := source.alternative
  toAction := source.simulation.toAction
  source := source.source
  targetInitialState := source.targetInitialState
  initial_behavior :=
    TraceBehaviorRelated.ofTraceSimulation
      source.simulation source.initial_related

/--
The behavior-derived route preserves the same source/target composition-log
alignment.
-/
theorem behavior_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    (source.source.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      (source.toBehaviorMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
        burdenCount supportCount :=
  source.toBehaviorMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

/--
The fixed-unit additive scalar no-go is unchanged after routing the supplied
simulation through canonical trace behavior.
-/
theorem behavior_no_additiveScalar_target_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((source.toBehaviorMappedResponseSeparatedCompositionSource.targetObservedSource).scalarOfCounts
                burdenCount supportCount) =
            (source.toBehaviorMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
              burdenCount supportCount) :=
  source.toBehaviorMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

/--
The two-component coordinate readout is also unchanged after the behavior
route.
-/
theorem behavior_exists_componentCoordinate_target_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          (source.toBehaviorMappedResponseSeparatedCompositionSource.targetObservedSource).traceLogOfCounts
            burdenCount supportCount :=
  source.toBehaviorMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

end SimulationMappedResponseSeparatedCompositionSource

end AdditiveScalarCompositionObservedTrace

namespace TwoChannelTraceEventScoreSource

variable (source : TwoChannelTraceEventScoreSource P)

theorem roleBlindScalar_same_decisiveLogs
    (blind : RoleBlindComponentScalar) :
    blind.scalar (source.componentScoreOfLog source.adverseTraceLog) =
      blind.scalar
        (source.componentScoreOfLog source.restorativeTraceLog) := by
  rw [source.adverse_componentScoreOfLog,
    source.restorative_componentScoreOfLog]
  exact blind.scalar_10_eq_01

/--
No role-blind scalar can recover the two component scores.

This is the restricted one-scalar red test.  It does not ban arbitrary scalar
encodings; it bans total-style scalars that erase the component direction.
-/
theorem no_roleBlindScalar_component_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (blind.scalar
              (source.componentScoreOfLog source.adverseTraceLog)) =
          source.componentScoreOfLog source.adverseTraceLog ∧
        componentOfScalar
            (blind.scalar
              (source.componentScoreOfLog source.restorativeTraceLog)) =
          source.componentScoreOfLog source.restorativeTraceLog) := by
  intro h
  rcases h with ⟨componentOfScalar, hadv, hrest⟩
  exact
    source.componentScoreOfLog_ne
      (calc
        source.componentScoreOfLog source.adverseTraceLog =
            componentOfScalar
              (blind.scalar
                (source.componentScoreOfLog source.adverseTraceLog)) :=
          hadv.symm
        _ = componentOfScalar
              (blind.scalar
                (source.componentScoreOfLog
                  source.restorativeTraceLog)) := by
          rw [source.roleBlindScalar_same_decisiveLogs blind]
        _ = source.componentScoreOfLog source.restorativeTraceLog := hrest)

/--
No role-blind scalar can recover both decisive prefix logs.
-/
theorem no_roleBlindScalar_traceLog_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (blind.scalar
              (source.componentScoreOfLog source.adverseTraceLog)) =
          source.adverseTraceLog ∧
        traceLogOfScalar
            (blind.scalar
              (source.componentScoreOfLog source.restorativeTraceLog)) =
          source.restorativeTraceLog) := by
  intro h
  rcases h with ⟨traceLogOfScalar, hadv, hrest⟩
  have hlogs :
      source.restorativeTraceLog = source.adverseTraceLog := by
    calc
      source.restorativeTraceLog =
          traceLogOfScalar
            (blind.scalar
              (source.componentScoreOfLog
                source.restorativeTraceLog)) := hrest.symm
      _ = traceLogOfScalar
            (blind.scalar
              (source.componentScoreOfLog source.adverseTraceLog)) := by
        rw [source.roleBlindScalar_same_decisiveLogs blind]
      _ = source.adverseTraceLog := hadv
  exact (source.law).traceLog_ne hlogs

/--
The concrete total component scalar identifies the two decisive logs.
-/
theorem totalComponentScalar_same_decisiveLogs :
    totalComponentScalarValue
        (source.componentScoreOfLog source.adverseTraceLog) =
      totalComponentScalarValue
        (source.componentScoreOfLog source.restorativeTraceLog) :=
  by
    rw [source.adverse_componentScoreOfLog,
      source.restorative_componentScoreOfLog]
    rfl

/--
The concrete total component scalar cannot recover both component-score pairs.
-/
theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.componentScoreOfLog source.adverseTraceLog)) =
          source.componentScoreOfLog source.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.componentScoreOfLog source.restorativeTraceLog)) =
          source.componentScoreOfLog source.restorativeTraceLog) :=
  by
    intro h
    rcases h with ⟨componentOfScalar, hadv, hrest⟩
    exact
      source.componentScoreOfLog_ne
        (calc
          source.componentScoreOfLog source.adverseTraceLog =
              componentOfScalar
                (totalComponentScalarValue
                  (source.componentScoreOfLog source.adverseTraceLog)) :=
            hadv.symm
          _ = componentOfScalar
                (totalComponentScalarValue
                  (source.componentScoreOfLog
                    source.restorativeTraceLog)) := by
            rw [source.totalComponentScalar_same_decisiveLogs]
          _ = source.componentScoreOfLog source.restorativeTraceLog := hrest)

/--
The concrete total component scalar cannot recover both decisive prefix logs.
-/
theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.componentScoreOfLog source.adverseTraceLog)) =
          source.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.componentScoreOfLog source.restorativeTraceLog)) =
          source.restorativeTraceLog) :=
  by
    intro h
    rcases h with ⟨traceLogOfScalar, hadv, hrest⟩
    have hlogs :
        source.restorativeTraceLog = source.adverseTraceLog := by
      calc
        source.restorativeTraceLog =
            traceLogOfScalar
              (totalComponentScalarValue
                (source.componentScoreOfLog
                  source.restorativeTraceLog)) := hrest.symm
        _ = traceLogOfScalar
              (totalComponentScalarValue
                (source.componentScoreOfLog source.adverseTraceLog)) := by
          rw [source.totalComponentScalar_same_decisiveLogs]
        _ = source.adverseTraceLog := hadv
    exact (source.law).traceLog_ne hlogs

end TwoChannelTraceEventScoreSource

/-
Equality-event readouts derived directly from the two decisive observed logs
of a two-channel law.

These events are intentionally local: they only say that distinct observed
prefix logs can be separated by equality tests.  They are not global
burden/support roles and do not identify full `L/B` or `M`.
-/
namespace TwoChannelTraceLaw

variable [DecidableEq Observation]
variable (law : TwoChannelTraceLaw P)

def adverseTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog law.restorativeContext law.adverseTrace

def restorativeTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog law.adverseContext law.restorativeTrace

def adverseEqualityEvent :
    List (Observation × BoundaryStatus) -> Bool :=
  fun traceLog =>
    match decEq traceLog law.adverseTraceLog with
    | isTrue _ => true
    | isFalse _ => false

def restorativeEqualityEvent :
    List (Observation × BoundaryStatus) -> Bool :=
  fun traceLog =>
    match decEq traceLog law.restorativeTraceLog with
    | isTrue _ => true
    | isFalse _ => false

theorem adverseEqualityEvent_adverse_active :
    law.adverseEqualityEvent law.adverseTraceLog = true := by
  unfold adverseEqualityEvent
  cases h :
      decEq law.adverseTraceLog law.adverseTraceLog with
  | isTrue _ => rfl
  | isFalse hfalse => exact False.elim (hfalse rfl)

theorem adverseEqualityEvent_restorative_inactive :
    law.adverseEqualityEvent law.restorativeTraceLog = false := by
  unfold adverseEqualityEvent adverseTraceLog restorativeTraceLog
  cases h :
      decEq
        (P.traceLog law.adverseContext law.restorativeTrace)
        (P.traceLog law.restorativeContext law.adverseTrace) with
  | isTrue heq => exact False.elim (law.traceLog_ne heq)
  | isFalse _ => rfl

theorem restorativeEqualityEvent_adverse_inactive :
    law.restorativeEqualityEvent law.adverseTraceLog = false := by
  unfold restorativeEqualityEvent adverseTraceLog restorativeTraceLog
  cases h :
      decEq
        (P.traceLog law.restorativeContext law.adverseTrace)
        (P.traceLog law.adverseContext law.restorativeTrace) with
  | isTrue heq => exact False.elim (law.traceLog_ne heq.symm)
  | isFalse _ => rfl

theorem restorativeEqualityEvent_restorative_active :
    law.restorativeEqualityEvent law.restorativeTraceLog = true := by
  unfold restorativeEqualityEvent
  cases h :
      decEq law.restorativeTraceLog law.restorativeTraceLog with
  | isTrue _ => rfl
  | isFalse hfalse => exact False.elim (hfalse rfl)

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource P where
  law := law
  burdenEvent := law.adverseEqualityEvent
  supportEvent := law.restorativeEqualityEvent
  burdenEvent_adverse_active := law.adverseEqualityEvent_adverse_active
  burdenEvent_restorative_inactive :=
    law.adverseEqualityEvent_restorative_inactive
  supportEvent_adverse_inactive :=
    law.restorativeEqualityEvent_adverse_inactive
  supportEvent_restorative_active :=
    law.restorativeEqualityEvent_restorative_active

theorem decisiveEquality_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (law.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              law.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            law.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (law.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  law.toDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem decisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (law.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              law.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          law.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (law.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  law.toDecisiveEqualityEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem decisiveEquality_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                law.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            law.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                law.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  law.toDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem decisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                law.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          law.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (law.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                law.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          law.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  law.toDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelTraceLaw

/--
Observable prefix-log map that induces local event preservation.

The primitive data here is a map on observed prefix logs.  If a candidate
event is the canonical event read after that log map, and the map fixes the
two decisive observed logs, then the existing local
`PrefixLogEventPreservation` certificate is constructed rather than supplied
directly.

This is still local to the two decisive logs.  It is not a global event
uniqueness theorem and does not quantify over all admissible alternatives.
-/
structure PrefixLogEventObservedMap
    {Observation : Type w}
    (candidateEvent canonicalEvent :
      List (Observation × BoundaryStatus) -> Bool)
    (adverseTraceLog restorativeTraceLog :
      List (Observation × BoundaryStatus)) where
  canonicalLogOf :
    List (Observation × BoundaryStatus) ->
      List (Observation × BoundaryStatus)
  reads_canonical :
    forall traceLog,
      candidateEvent traceLog = canonicalEvent (canonicalLogOf traceLog)
  preserves_adverse_log :
    canonicalLogOf adverseTraceLog = adverseTraceLog
  preserves_restorative_log :
    canonicalLogOf restorativeTraceLog = restorativeTraceLog

namespace PrefixLogEventObservedMap

variable {Observation : Type w}
variable {candidateEvent canonicalEvent :
  List (Observation × BoundaryStatus) -> Bool}
variable {adverseTraceLog restorativeTraceLog :
  List (Observation × BoundaryStatus)}
variable (source :
  PrefixLogEventObservedMap
    candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog)

def toPrefixLogEventPreservation :
    PrefixLogEventPreservation
      candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog where
  preserves_adverse := by
    calc
      candidateEvent adverseTraceLog =
          canonicalEvent (source.canonicalLogOf adverseTraceLog) :=
        source.reads_canonical adverseTraceLog
      _ = canonicalEvent adverseTraceLog := by
        rw [source.preserves_adverse_log]
  preserves_restorative := by
    calc
      candidateEvent restorativeTraceLog =
          canonicalEvent (source.canonicalLogOf restorativeTraceLog) :=
        source.reads_canonical restorativeTraceLog
      _ = canonicalEvent restorativeTraceLog := by
        rw [source.preserves_restorative_log]

theorem candidate_distinguishes_of_canonical_true_false
    (source :
      PrefixLogEventObservedMap
        candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog)
    (canonical_adverse_active : canonicalEvent adverseTraceLog = true)
    (canonical_restorative_inactive :
      canonicalEvent restorativeTraceLog = false) :
    candidateEvent adverseTraceLog ≠
      candidateEvent restorativeTraceLog :=
  toPrefixLogEventPreservation source
    |>.candidate_distinguishes_of_canonical_true_false
      canonical_adverse_active canonical_restorative_inactive

theorem candidate_distinguishes_of_canonical_false_true
    (source :
      PrefixLogEventObservedMap
        candidateEvent canonicalEvent adverseTraceLog restorativeTraceLog)
    (canonical_adverse_inactive : canonicalEvent adverseTraceLog = false)
    (canonical_restorative_active :
      canonicalEvent restorativeTraceLog = true) :
    candidateEvent adverseTraceLog ≠
      candidateEvent restorativeTraceLog :=
  toPrefixLogEventPreservation source
    |>.candidate_distinguishes_of_canonical_false_true
      canonical_adverse_inactive canonical_restorative_active

end PrefixLogEventObservedMap

/--
An observable prefix-log map induced by a prefix-log-preserving coordinate
model on the two decisive traces.

The source data is now a `JointCoordinateTraceLogModel`: an observational
prefix-log preservation hypothesis.  From it we build a local map on observed
logs that fixes the adverse and restorative decisive logs.  This still does
not say that every admissible alternative supplies such a model; it only moves
the previous fixed-log laws under an explicit prefix-log preservation model.
-/
structure TwoChannelTraceLogModelObservedMapSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  law : TwoChannelTraceLaw P
  model : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate

namespace TwoChannelTraceLogModelObservedMapSource

variable [DecidableEq Observation]
variable {ActionCoordinate : Type y}
variable (source :
  TwoChannelTraceLogModelObservedMapSource
    P StateCoordinate ActionCoordinate)

def adverseTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).restorativeContext (source.law).adverseTrace

def restorativeTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).adverseContext (source.law).restorativeTrace

def canonicalLogOf
    (traceLog : List (Observation × BoundaryStatus)) :
    List (Observation × BoundaryStatus) :=
  if traceLog = adverseTraceLog source then
    source.model.traceLogOfCoordinates
      (source.model.stateCoordinate (source.law).restorativeContext)
      ((source.law).adverseTrace.map source.model.actionCoordinate)
  else if traceLog = restorativeTraceLog source then
    source.model.traceLogOfCoordinates
      (source.model.stateCoordinate (source.law).adverseContext)
      ((source.law).restorativeTrace.map source.model.actionCoordinate)
  else
    traceLog

theorem canonicalLogOf_adverse :
    canonicalLogOf source (adverseTraceLog source) =
      adverseTraceLog source := by
  unfold canonicalLogOf adverseTraceLog
  rw [if_pos rfl]
  exact
    (source.model.preserves_traceLog
      (source.law).restorativeContext (source.law).adverseTrace).symm

theorem canonicalLogOf_restorative :
    canonicalLogOf source (restorativeTraceLog source) =
      restorativeTraceLog source := by
  have hne : restorativeTraceLog source ≠ adverseTraceLog source :=
    (source.law).traceLog_ne
  unfold canonicalLogOf
  rw [if_neg hne, if_pos rfl]
  exact
    (source.model.preserves_traceLog
      (source.law).adverseContext (source.law).restorativeTrace).symm

def toPrefixLogEventObservedMap
    (canonicalEvent : List (Observation × BoundaryStatus) -> Bool) :
    PrefixLogEventObservedMap
      (fun traceLog => canonicalEvent (canonicalLogOf source traceLog))
      canonicalEvent (adverseTraceLog source) (restorativeTraceLog source) where
  canonicalLogOf := canonicalLogOf source
  reads_canonical := by
    intro traceLog
    rfl
  preserves_adverse_log := canonicalLogOf_adverse source
  preserves_restorative_log := canonicalLogOf_restorative source

end TwoChannelTraceLogModelObservedMapSource

/--
Prefix-log event preservation source for local component scores.

This is one step less supplied than `TwoChannelTraceEventScoreSource`: the
candidate adverse/restorative events are not given their active/inactive laws
directly.  Instead, they locally preserve canonical events on the two decisive
observed prefix logs, and the canonical events carry the active/inactive laws.

The preservation certificates are still inputs.  This is not a proof that every
admissible alternative must preserve these events.
-/
structure TwoChannelPreservedTraceEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  law : TwoChannelTraceLaw P
  burdenEvent : List (Observation × BoundaryStatus) -> Bool
  supportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  burdenEvent_preservation :
    PrefixLogEventPreservation
      burdenEvent canonicalBurdenEvent
      (P.traceLog law.restorativeContext law.adverseTrace)
      (P.traceLog law.adverseContext law.restorativeTrace)
  supportEvent_preservation :
    PrefixLogEventPreservation
      supportEvent canonicalSupportEvent
      (P.traceLog law.restorativeContext law.adverseTrace)
      (P.traceLog law.adverseContext law.restorativeTrace)
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelPreservedTraceEventScoreSource

variable (source : TwoChannelPreservedTraceEventScoreSource P)

def adverseTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).restorativeContext (source.law).adverseTrace

def restorativeTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).adverseContext (source.law).restorativeTrace

theorem burdenEvent_adverse_active :
    source.burdenEvent source.adverseTraceLog = true :=
  source.burdenEvent_preservation.preserves_adverse.trans
    source.canonicalBurden_adverse_active

theorem burdenEvent_restorative_inactive :
    source.burdenEvent source.restorativeTraceLog = false :=
  source.burdenEvent_preservation.preserves_restorative.trans
    source.canonicalBurden_restorative_inactive

theorem supportEvent_adverse_inactive :
    source.supportEvent source.adverseTraceLog = false :=
  source.supportEvent_preservation.preserves_adverse.trans
    source.canonicalSupport_adverse_inactive

theorem supportEvent_restorative_active :
    source.supportEvent source.restorativeTraceLog = true :=
  source.supportEvent_preservation.preserves_restorative.trans
    source.canonicalSupport_restorative_active

def toTraceEventScoreSource :
    TwoChannelTraceEventScoreSource P where
  law := source.law
  burdenEvent := source.burdenEvent
  supportEvent := source.supportEvent
  burdenEvent_adverse_active := source.burdenEvent_adverse_active
  burdenEvent_restorative_inactive :=
    source.burdenEvent_restorative_inactive
  supportEvent_adverse_inactive := source.supportEvent_adverse_inactive
  supportEvent_restorative_active := source.supportEvent_restorative_active

theorem componentScoreOfLog_ne :
    source.toTraceEventScoreSource.componentScoreOfLog
        source.toTraceEventScoreSource.adverseTraceLog ≠
      source.toTraceEventScoreSource.componentScoreOfLog
        source.toTraceEventScoreSource.restorativeTraceLog :=
  source.toTraceEventScoreSource.componentScoreOfLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelPreservedTraceEventScoreSource

/--
Prefix-log event score source whose preservation certificates are induced by
observable log maps.

Compared with `TwoChannelPreservedTraceEventScoreSource`, this no longer takes
`PrefixLogEventPreservation` certificates as primitive fields.  It takes
observable prefix-log maps that read candidate events through canonical events
and fix the two decisive logs; the local preservation certificates then follow.

The log maps are still supplied local inputs.  This is not yet a theorem that
every admissible alternative determines such maps.
-/
structure TwoChannelObservedLogPreservedTraceEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation) where
  law : TwoChannelTraceLaw P
  burdenEvent : List (Observation × BoundaryStatus) -> Bool
  supportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  burdenEvent_logMap :
    PrefixLogEventObservedMap
      burdenEvent canonicalBurdenEvent
      (P.traceLog law.restorativeContext law.adverseTrace)
      (P.traceLog law.adverseContext law.restorativeTrace)
  supportEvent_logMap :
    PrefixLogEventObservedMap
      supportEvent canonicalSupportEvent
      (P.traceLog law.restorativeContext law.adverseTrace)
      (P.traceLog law.adverseContext law.restorativeTrace)
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelObservedLogPreservedTraceEventScoreSource

variable (source : TwoChannelObservedLogPreservedTraceEventScoreSource P)

def adverseTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).restorativeContext (source.law).adverseTrace

def restorativeTraceLog : List (Observation × BoundaryStatus) :=
  P.traceLog (source.law).adverseContext (source.law).restorativeTrace

def burdenEvent_preservation :
    PrefixLogEventPreservation
      source.burdenEvent source.canonicalBurdenEvent
      source.adverseTraceLog source.restorativeTraceLog :=
  source.burdenEvent_logMap.toPrefixLogEventPreservation

def supportEvent_preservation :
    PrefixLogEventPreservation
      source.supportEvent source.canonicalSupportEvent
      source.adverseTraceLog source.restorativeTraceLog :=
  source.supportEvent_logMap.toPrefixLogEventPreservation

theorem burdenEvent_adverse_active :
    source.burdenEvent source.adverseTraceLog = true :=
  source.burdenEvent_preservation.preserves_adverse.trans
    source.canonicalBurden_adverse_active

theorem burdenEvent_restorative_inactive :
    source.burdenEvent source.restorativeTraceLog = false :=
  source.burdenEvent_preservation.preserves_restorative.trans
    source.canonicalBurden_restorative_inactive

theorem supportEvent_adverse_inactive :
    source.supportEvent source.adverseTraceLog = false :=
  source.supportEvent_preservation.preserves_adverse.trans
    source.canonicalSupport_adverse_inactive

theorem supportEvent_restorative_active :
    source.supportEvent source.restorativeTraceLog = true :=
  source.supportEvent_preservation.preserves_restorative.trans
    source.canonicalSupport_restorative_active

def toPreservedTraceEventScoreSource :
    TwoChannelPreservedTraceEventScoreSource P where
  law := source.law
  burdenEvent := source.burdenEvent
  supportEvent := source.supportEvent
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  burdenEvent_preservation := source.burdenEvent_preservation
  supportEvent_preservation := source.supportEvent_preservation
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toTraceEventScoreSource :
    TwoChannelTraceEventScoreSource P :=
  source.toPreservedTraceEventScoreSource.toTraceEventScoreSource

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelObservedLogPreservedTraceEventScoreSource

/--
Event-score source induced by a prefix-log-preserving coordinate model.

This is one layer lower than `TwoChannelObservedLogPreservedTraceEventScoreSource`:
the candidate event readouts are not supplied.  They are the canonical event
readouts after the observed-log map induced by a `JointCoordinateTraceLogModel`.

The coordinate model is still an input.  This is a scoped preservation-surface
step, not the full arbitrary-alternative G1 theorem.
-/
structure TwoChannelTraceLogModelEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (StateCoordinate : Type x) (ActionCoordinate : Type y) where
  law : TwoChannelTraceLaw P
  model : JointCoordinateTraceLogModel P StateCoordinate ActionCoordinate
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelTraceLogModelEventScoreSource

variable [DecidableEq Observation]
variable {ActionCoordinate : Type y}
variable (source :
  TwoChannelTraceLogModelEventScoreSource P StateCoordinate ActionCoordinate)

def observedMapSource :
    TwoChannelTraceLogModelObservedMapSource
      P StateCoordinate ActionCoordinate where
  law := source.law
  model := source.model

def burdenEvent
    (traceLog : List (Observation × BoundaryStatus)) : Bool :=
  source.canonicalBurdenEvent
    (TwoChannelTraceLogModelObservedMapSource.canonicalLogOf
      source.observedMapSource traceLog)

def supportEvent
    (traceLog : List (Observation × BoundaryStatus)) : Bool :=
  source.canonicalSupportEvent
    (TwoChannelTraceLogModelObservedMapSource.canonicalLogOf
      source.observedMapSource traceLog)

def toObservedLogPreservedTraceEventScoreSource :
    TwoChannelObservedLogPreservedTraceEventScoreSource P where
  law := source.law
  burdenEvent := source.burdenEvent
  supportEvent := source.supportEvent
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  burdenEvent_logMap :=
    TwoChannelTraceLogModelObservedMapSource.toPrefixLogEventObservedMap
      source.observedMapSource
      source.canonicalBurdenEvent
  supportEvent_logMap :=
    TwoChannelTraceLogModelObservedMapSource.toPrefixLogEventObservedMap
      source.observedMapSource
      source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toTraceEventScoreSource :
    TwoChannelTraceEventScoreSource P :=
  source.toObservedLogPreservedTraceEventScoreSource.toTraceEventScoreSource

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelTraceLogModelEventScoreSource

/--
Alternative-observation source for a prefix-log model.

This is one layer lower than `TwoChannelTraceLogModelEventScoreSource`: instead
of supplying a `JointCoordinateTraceLogModel` directly, it supplies an
alternative observational process together with state/action translations and
an explicit prefix-log preservation law.  The preservation law is still an
input, and no burden/support roles occur in it.
-/
structure TwoChannelAlternativeTraceLogEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  preserves_traceLog :
    forall s actions,
      P.traceLog s actions =
        alternative.traceLog
          (toAlternativeState s)
          (actions.map toAlternativeAction)
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelAlternativeTraceLogEventScoreSource

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable (source :
  TwoChannelAlternativeTraceLogEventScoreSource
    P StateCoordinate AlternativeAction)

/--
The prefix-log-preserving coordinate model induced by the alternative
observational process and the supplied observational preservation law.
-/
def toJointCoordinateTraceLogModel :
    JointCoordinateTraceLogModel P StateCoordinate AlternativeAction where
  stateCoordinate := source.toAlternativeState
  actionCoordinate := source.toAlternativeAction
  traceLogOfCoordinates := source.alternative.traceLog
  preserves_traceLog := source.preserves_traceLog

/--
Route the alternative-observation source through the existing trace-log model
event-score source.
-/
def toTraceLogModelEventScoreSource :
    TwoChannelTraceLogModelEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  model := source.toJointCoordinateTraceLogModel
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toObservedLogPreservedTraceEventScoreSource :
    TwoChannelObservedLogPreservedTraceEventScoreSource P :=
  source.toTraceLogModelEventScoreSource
    |>.toObservedLogPreservedTraceEventScoreSource

def toTraceEventScoreSource :
    TwoChannelTraceEventScoreSource P :=
  source.toTraceLogModelEventScoreSource.toTraceEventScoreSource

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceLogModelEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceLogModelEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceLogModelEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toTraceLogModelEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelAlternativeTraceLogEventScoreSource

/--
Event-score source induced by a step-commuting observational transition map.

This is one layer lower than `TwoChannelAlternativeTraceLogEventScoreSource`:
the full prefix-log preservation law is no longer a primitive field.  It is
derived from a role-free transition map between observational processes.  The
transition map is still an input; this is not yet the arbitrary-alternative
semantic G1 theorem.
-/
structure TwoChannelTransitionMapEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  transitionMap : ObservationalTransitionMap P alternative
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelTransitionMapEventScoreSource

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable (source :
  TwoChannelTransitionMapEventScoreSource
    P StateCoordinate AlternativeAction)

def toAlternativeTraceLogEventScoreSource :
    TwoChannelAlternativeTraceLogEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.transitionMap.toState
  toAlternativeAction := source.transitionMap.toAction
  preserves_traceLog := source.transitionMap.preserves_traceLog
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toTraceLogModelEventScoreSource :
    TwoChannelTraceLogModelEventScoreSource
      P StateCoordinate AlternativeAction :=
  source.toAlternativeTraceLogEventScoreSource
    |>.toTraceLogModelEventScoreSource

def toTraceEventScoreSource :
    TwoChannelTraceEventScoreSource P :=
  source.toAlternativeTraceLogEventScoreSource.toTraceEventScoreSource

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toAlternativeTraceLogEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.adverseTraceLog) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTraceEventScoreSource.totalScoreOfLog
              source.toTraceEventScoreSource.restorativeTraceLog) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toAlternativeTraceLogEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.componentScoreOfLog
            source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toAlternativeTraceLogEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.adverseTraceLog)) =
          source.toTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTraceEventScoreSource.componentScoreOfLog
                source.toTraceEventScoreSource.restorativeTraceLog)) =
          source.toTraceEventScoreSource.restorativeTraceLog) :=
  source.toAlternativeTraceLogEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelTransitionMapEventScoreSource

/--
Event-score source transported through a role-free observational trace
simulation.

This is the relation-based counterpart of
`TwoChannelTransitionMapEventScoreSource`.  The target contexts are not images
of a state function; they are supplied states related to the two source
contexts by the simulation.  The Boolean event laws are transported through
the induced decisive prefix-log equalities.  The simulation relation is still
an input, so this is not yet the arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelTraceSimulationEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  simulation : ObservationalTraceSimulation P alternative
  targetAdverseContext : AlternativeState
  targetRestorativeContext : AlternativeState
  adverse_related :
    simulation.related law.adverseContext targetAdverseContext
  restorative_related :
    simulation.related law.restorativeContext targetRestorativeContext
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelTraceSimulationEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelTraceSimulationEventScoreSource
    P StateCoordinate AlternativeAction)

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.simulation.toTwoChannelTraceLaw
    source.law source.targetAdverseContext source.targetRestorativeContext
    source.adverse_related source.restorative_related

theorem target_adverseTraceLog_eq_source :
    source.alternative.traceLog
        source.targetLaw.restorativeContext
        source.targetLaw.adverseTrace =
      P.traceLog source.law.restorativeContext source.law.adverseTrace := by
  calc
    source.alternative.traceLog
        source.targetLaw.restorativeContext
        source.targetLaw.adverseTrace =
        source.alternative.traceLog
          source.targetRestorativeContext
          (source.law.adverseTrace.map source.simulation.toAction) := by
      rfl
    _ = P.traceLog source.law.restorativeContext source.law.adverseTrace :=
      (source.simulation.preserves_traceLog
        source.restorative_related source.law.adverseTrace).symm

theorem target_restorativeTraceLog_eq_source :
    source.alternative.traceLog
        source.targetLaw.adverseContext
        source.targetLaw.restorativeTrace =
      P.traceLog source.law.adverseContext source.law.restorativeTrace := by
  calc
    source.alternative.traceLog
        source.targetLaw.adverseContext
        source.targetLaw.restorativeTrace =
        source.alternative.traceLog
          source.targetAdverseContext
          (source.law.restorativeTrace.map source.simulation.toAction) := by
      rfl
    _ = P.traceLog source.law.adverseContext source.law.restorativeTrace :=
      (source.simulation.preserves_traceLog
        source.adverse_related source.law.restorativeTrace).symm

/--
The target-side event-score source induced by the trace simulation.
-/
def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative where
  law := source.targetLaw
  burdenEvent := source.canonicalBurdenEvent
  supportEvent := source.canonicalSupportEvent
  burdenEvent_adverse_active := by
    rw [source.target_adverseTraceLog_eq_source]
    exact source.canonicalBurden_adverse_active
  burdenEvent_restorative_inactive := by
    rw [source.target_restorativeTraceLog_eq_source]
    exact source.canonicalBurden_restorative_inactive
  supportEvent_adverse_inactive := by
    rw [source.target_adverseTraceLog_eq_source]
    exact source.canonicalSupport_adverse_inactive
  supportEvent_restorative_active := by
    rw [source.target_restorativeTraceLog_eq_source]
    exact source.canonicalSupport_restorative_active

theorem target_traceLog_ne :
    source.alternative.traceLog
        source.targetLaw.adverseContext
        source.targetLaw.restorativeTrace ≠
      source.alternative.traceLog
        source.targetLaw.restorativeContext
        source.targetLaw.adverseTrace :=
  source.targetLaw.traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelTraceSimulationEventScoreSource

/--
Event-score source transported by only two fixed decisive prefix-log
equalities.

This is weaker than `TwoChannelTraceSimulationEventScoreSource`: no simulation
relation, state map, or step-closure field is present.  The source consumes
only the two observable decisive-log equalities needed to reconstruct the
target two-channel law and move the canonical event laws to the target side.
Those equalities are still inputs, so this is not yet the arbitrary-alternative
semantic G1 theorem.
-/
structure TwoChannelFixedTraceLogEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  transport : TwoChannelFixedTraceLogTransport P alternative
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog transport.law.restorativeContext
          transport.law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog transport.law.adverseContext
          transport.law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog transport.law.restorativeContext
          transport.law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog transport.law.adverseContext
          transport.law.restorativeTrace) = true

namespace TwoChannelFixedTraceLogEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelFixedTraceLogEventScoreSource
    P StateCoordinate AlternativeAction)

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.transport.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative where
  law := source.targetLaw
  burdenEvent := source.canonicalBurdenEvent
  supportEvent := source.canonicalSupportEvent
  burdenEvent_adverse_active := by
    change source.canonicalBurdenEvent
        (source.alternative.traceLog
          source.transport.targetRestorativeContext
          [source.transport.targetAdverseIntervention]) = true
    rw [source.transport.target_adverseTraceLog_eq_source]
    exact source.canonicalBurden_adverse_active
  burdenEvent_restorative_inactive := by
    change source.canonicalBurdenEvent
        (source.alternative.traceLog
          source.transport.targetAdverseContext
          [source.transport.targetRestorativeIntervention]) = false
    rw [source.transport.target_restorativeTraceLog_eq_source]
    exact source.canonicalBurden_restorative_inactive
  supportEvent_adverse_inactive := by
    change source.canonicalSupportEvent
        (source.alternative.traceLog
          source.transport.targetRestorativeContext
          [source.transport.targetAdverseIntervention]) = false
    rw [source.transport.target_adverseTraceLog_eq_source]
    exact source.canonicalSupport_adverse_inactive
  supportEvent_restorative_active := by
    change source.canonicalSupportEvent
        (source.alternative.traceLog
          source.transport.targetAdverseContext
          [source.transport.targetRestorativeIntervention]) = true
    rw [source.transport.target_restorativeTraceLog_eq_source]
    exact source.canonicalSupport_restorative_active

theorem target_traceLog_ne :
    source.alternative.traceLog
        source.transport.targetAdverseContext
        [source.transport.targetRestorativeIntervention] ≠
      source.alternative.traceLog
        source.transport.targetRestorativeContext
        [source.transport.targetAdverseIntervention] :=
  source.transport.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toTargetTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

end TwoChannelFixedTraceLogEventScoreSource

/--
Event-score source transported by two fixed one-step response equalities.

This is weaker than `TwoChannelFixedTraceLogEventScoreSource`: it does not
take prefix-log equalities as primitive fields.  It derives those fixed-log
equalities from the two one-step intervention-response equalities of
`TwoChannelFixedResponseTransport`, then reuses the fixed-log event-score
surface.  The response equalities are still inputs, so this is not yet the
arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelFixedResponseEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  transport : TwoChannelFixedResponseTransport P alternative
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog transport.law.restorativeContext
          transport.law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog transport.law.adverseContext
          transport.law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog transport.law.restorativeContext
          transport.law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog transport.law.adverseContext
          transport.law.restorativeTrace) = true

namespace TwoChannelFixedResponseEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelFixedResponseEventScoreSource
    P StateCoordinate AlternativeAction)

def toFixedTraceLogEventScoreSource :
    TwoChannelFixedTraceLogEventScoreSource
      P StateCoordinate AlternativeAction where
  alternative := source.alternative
  transport := source.transport.toFixedTraceLogTransport
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.transport.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toFixedTraceLogEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        source.transport.targetAdverseContext
        [source.transport.targetRestorativeIntervention] ≠
      source.alternative.traceLog
        source.transport.targetRestorativeContext
        [source.transport.targetAdverseIntervention] :=
  source.transport.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedTraceLogEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedTraceLogEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedTraceLogEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedTraceLogEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelFixedResponseEventScoreSource

/-
Decisive equality-event score sources induced by transport surfaces.

These bridges remove the supplied canonical event laws from the minimal
transport no-go: once a target two-channel law has been reconstructed, the two
target decisive logs themselves generate local equality events.  This is still
only a local observed-log separation, not a derivation of global `L/B` or `M`
roles.
-/
namespace TwoChannelFixedTraceLogTransport

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable {alternative :
  ObservationalPersistenceProcess StateCoordinate AlternativeAction
    Observation}
variable (transport : TwoChannelFixedTraceLogTransport P alternative)

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource alternative :=
  transport.targetLaw.toDecisiveEqualityEventScoreSource

theorem decisiveEquality_target_traceLog_ne :
    alternative.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      alternative.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.target_traceLog_ne

theorem decisiveEquality_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem decisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem decisiveEquality_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem decisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelFixedTraceLogTransport

namespace TwoChannelFixedResponseTransport

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable {alternative :
  ObservationalPersistenceProcess StateCoordinate AlternativeAction
    Observation}
variable (transport : TwoChannelFixedResponseTransport P alternative)

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource alternative :=
  transport.toFixedTraceLogTransport.toDecisiveEqualityEventScoreSource

theorem decisiveEquality_target_traceLog_ne :
    alternative.traceLog
        transport.targetAdverseContext
        [transport.targetRestorativeIntervention] ≠
      alternative.traceLog
        transport.targetRestorativeContext
        [transport.targetAdverseIntervention] :=
  transport.toFixedTraceLogTransport.decisiveEquality_target_traceLog_ne

theorem decisiveEquality_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toFixedTraceLogTransport
    |>.decisiveEquality_no_totalScoreOfLog_componentScore_decoder

theorem decisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (transport.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toFixedTraceLogTransport
    |>.decisiveEquality_no_totalScoreOfLog_traceLog_decoder

theorem decisiveEquality_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toFixedTraceLogTransport
    |>.decisiveEquality_no_totalComponentScalar_component_decoder

theorem decisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (transport.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          transport.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  transport.toFixedTraceLogTransport
    |>.decisiveEquality_no_totalComponentScalar_traceLog_decoder

end TwoChannelFixedResponseTransport

/--
Event-score source transported through a local two-probe response map, using
only the decisive equality events induced by the transported target logs.

This is the equality-event counterpart of
`TwoChannelLocalResponseMapEventScoreSource`: it has no canonical
collapsed-prefix / viable-final event fields.  The only preservation inputs
are the two observable one-step response equalities for the decisive probes.
Those local response equalities are still inputs, so this is not yet the
arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  preserves_restorative_probe :
    alternative.response
        (toAlternativeState law.adverseContext)
        (toAlternativeAction law.restorativeIntervention) =
      P.response law.adverseContext law.restorativeIntervention
  preserves_adverse_probe :
    alternative.response
        (toAlternativeState law.restorativeContext)
        (toAlternativeAction law.adverseIntervention) =
      P.response law.restorativeContext law.adverseIntervention

namespace TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource
    P StateCoordinate AlternativeAction)

def toFixedResponseTransport :
    TwoChannelFixedResponseTransport P source.alternative where
  law := source.law
  targetAdverseContext :=
    source.toAlternativeState source.law.adverseContext
  targetRestorativeContext :=
    source.toAlternativeState source.law.restorativeContext
  targetRestorativeIntervention :=
    source.toAlternativeAction source.law.restorativeIntervention
  targetAdverseIntervention :=
    source.toAlternativeAction source.law.adverseIntervention
  target_restorativeResponse_eq_source :=
    source.preserves_restorative_probe
  target_adverseResponse_eq_source :=
    source.preserves_adverse_probe

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toFixedResponseTransport.targetLaw

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toFixedResponseTransport.toDecisiveEqualityEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.toAlternativeState source.law.adverseContext)
        [source.toAlternativeAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.toAlternativeState source.law.restorativeContext)
        [source.toAlternativeAction source.law.adverseIntervention] :=
  source.toFixedResponseTransport.decisiveEquality_target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseTransport
    |>.decisiveEquality_no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseTransport
    |>.decisiveEquality_no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseTransport
    |>.decisiveEquality_no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseTransport
    |>.decisiveEquality_no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource

/--
Event-score source transported through a role-free observational response map,
using only the decisive equality events induced by the transported target logs.

This removes the canonical event-law fields from the response-map route.  It
still consumes a supplied `ObservationalResponseMap`; it does not prove that
every admissible alternative determines such a map.
-/
structure TwoChannelResponseMapDecisiveEqualityEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  responseMap : ObservationalResponseMap P alternative

namespace TwoChannelResponseMapDecisiveEqualityEventScoreSource

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable (source :
  TwoChannelResponseMapDecisiveEqualityEventScoreSource
    P StateCoordinate AlternativeAction)

def toLocalResponseMapDecisiveEqualityEventScoreSource :
    TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.responseMap.toState
  toAlternativeAction := source.responseMap.toAction
  preserves_restorative_probe :=
    source.responseMap.preserves_response
      source.law.adverseContext source.law.restorativeIntervention
  preserves_adverse_probe :=
    source.responseMap.preserves_response
      source.law.restorativeContext source.law.adverseIntervention

def toFixedResponseTransport :
    TwoChannelFixedResponseTransport P source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.toFixedResponseTransport

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource.targetLaw

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.toDecisiveEqualityEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.responseMap.toState source.law.adverseContext)
        [source.responseMap.toAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.responseMap.toState source.law.restorativeContext)
        [source.responseMap.toAction source.law.adverseIntervention] :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelResponseMapDecisiveEqualityEventScoreSource

/--
Event-score source transported through local post-step view preservation, using
only the decisive equality events induced by the transported target logs.

This is one layer below
`TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource`: it does not take
one-step response equalities as primitive fields.  It derives them from
post-step observation/readout equalities for the two decisive probes.  These
local post-step equalities are still inputs, so this is not yet the
arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalPostStepViewDecisiveEqualityEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  preserves_restorative_observation :
    alternative.observe
        (alternative.step
          (toAlternativeState law.adverseContext)
          (toAlternativeAction law.restorativeIntervention)) =
      P.observe (P.step law.adverseContext law.restorativeIntervention)
  preserves_restorative_readout :
    alternative.readout
        (alternative.step
          (toAlternativeState law.adverseContext)
          (toAlternativeAction law.restorativeIntervention)) =
      P.readout (P.step law.adverseContext law.restorativeIntervention)
  preserves_adverse_observation :
    alternative.observe
        (alternative.step
          (toAlternativeState law.restorativeContext)
          (toAlternativeAction law.adverseIntervention)) =
      P.observe (P.step law.restorativeContext law.adverseIntervention)
  preserves_adverse_readout :
    alternative.readout
        (alternative.step
          (toAlternativeState law.restorativeContext)
          (toAlternativeAction law.adverseIntervention)) =
      P.readout (P.step law.restorativeContext law.adverseIntervention)

namespace TwoChannelLocalPostStepViewDecisiveEqualityEventScoreSource

variable [DecidableEq Observation]
variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalPostStepViewDecisiveEqualityEventScoreSource
    P StateCoordinate AlternativeAction)

theorem preserves_restorative_probe :
    source.alternative.response
        (source.toAlternativeState source.law.adverseContext)
        (source.toAlternativeAction source.law.restorativeIntervention) =
      P.response source.law.adverseContext
        source.law.restorativeIntervention := by
  exact
    Prod.ext
      source.preserves_restorative_observation
      source.preserves_restorative_readout

theorem preserves_adverse_probe :
    source.alternative.response
        (source.toAlternativeState source.law.restorativeContext)
        (source.toAlternativeAction source.law.adverseIntervention) =
      P.response source.law.restorativeContext
        source.law.adverseIntervention := by
  exact
    Prod.ext
      source.preserves_adverse_observation
      source.preserves_adverse_readout

def toLocalResponseMapDecisiveEqualityEventScoreSource :
    TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.toAlternativeState
  toAlternativeAction := source.toAlternativeAction
  preserves_restorative_probe := source.preserves_restorative_probe
  preserves_adverse_probe := source.preserves_adverse_probe

def toFixedResponseTransport :
    TwoChannelFixedResponseTransport P source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.toFixedResponseTransport

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource.targetLaw

def toDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.toDecisiveEqualityEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.toAlternativeState source.law.adverseContext)
        [source.toAlternativeAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.toAlternativeState source.law.restorativeContext)
        [source.toAlternativeAction source.law.adverseIntervention] :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.adverseTraceLog) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toDecisiveEqualityEventScoreSource.totalScoreOfLog
              source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
            source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toDecisiveEqualityEventScoreSource.componentScoreOfLog
                source.toDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          source.toDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalPostStepViewDecisiveEqualityEventScoreSource

/--
Event-score source transported through a local two-probe response map.

This is weaker than a full `ObservationalResponseMap`: it only carries state
and action translations for the two decisive probes of a `TwoChannelTraceLaw`,
plus the two response equalities needed by
`TwoChannelFixedResponseEventScoreSource`.  The local probe equalities are
still inputs, so this is not yet the arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalResponseMapEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  preserves_restorative_probe :
    alternative.response
        (toAlternativeState law.adverseContext)
        (toAlternativeAction law.restorativeIntervention) =
      P.response law.adverseContext law.restorativeIntervention
  preserves_adverse_probe :
    alternative.response
        (toAlternativeState law.restorativeContext)
        (toAlternativeAction law.adverseIntervention) =
      P.response law.restorativeContext law.adverseIntervention
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelLocalResponseMapEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalResponseMapEventScoreSource
    P StateCoordinate AlternativeAction)

def toFixedResponseEventScoreSource :
    TwoChannelFixedResponseEventScoreSource
      P StateCoordinate AlternativeAction where
  alternative := source.alternative
  transport := {
    law := source.law
    targetAdverseContext :=
      source.toAlternativeState source.law.adverseContext
    targetRestorativeContext :=
      source.toAlternativeState source.law.restorativeContext
    targetRestorativeIntervention :=
      source.toAlternativeAction source.law.restorativeIntervention
    targetAdverseIntervention :=
      source.toAlternativeAction source.law.adverseIntervention
    target_restorativeResponse_eq_source :=
      source.preserves_restorative_probe
    target_adverseResponse_eq_source :=
      source.preserves_adverse_probe }
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toFixedResponseEventScoreSource.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toFixedResponseEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.toAlternativeState source.law.adverseContext)
        [source.toAlternativeAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.toAlternativeState source.law.restorativeContext)
        [source.toAlternativeAction source.law.adverseIntervention] :=
  source.toFixedResponseEventScoreSource.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalResponseMapEventScoreSource

/--
Event-score source transported through local post-step view preservation.

This is one layer below `TwoChannelLocalResponseMapEventScoreSource`: the
primitive fields preserve the observation and boundary readout after the two
decisive target steps.  The one-step response equalities are derived from
those four observable equalities.  These local post-step equalities are still
inputs, so this is not yet the arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalPostStepViewEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  preserves_restorative_observation :
    alternative.observe
        (alternative.step
          (toAlternativeState law.adverseContext)
          (toAlternativeAction law.restorativeIntervention)) =
      P.observe (P.step law.adverseContext law.restorativeIntervention)
  preserves_restorative_readout :
    alternative.readout
        (alternative.step
          (toAlternativeState law.adverseContext)
          (toAlternativeAction law.restorativeIntervention)) =
      P.readout (P.step law.adverseContext law.restorativeIntervention)
  preserves_adverse_observation :
    alternative.observe
        (alternative.step
          (toAlternativeState law.restorativeContext)
          (toAlternativeAction law.adverseIntervention)) =
      P.observe (P.step law.restorativeContext law.adverseIntervention)
  preserves_adverse_readout :
    alternative.readout
        (alternative.step
          (toAlternativeState law.restorativeContext)
          (toAlternativeAction law.adverseIntervention)) =
      P.readout (P.step law.restorativeContext law.adverseIntervention)
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelLocalPostStepViewEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalPostStepViewEventScoreSource
    P StateCoordinate AlternativeAction)

theorem preserves_restorative_probe :
    source.alternative.response
        (source.toAlternativeState source.law.adverseContext)
        (source.toAlternativeAction source.law.restorativeIntervention) =
      P.response source.law.adverseContext
        source.law.restorativeIntervention := by
  exact
    Prod.ext
      source.preserves_restorative_observation
      source.preserves_restorative_readout

theorem preserves_adverse_probe :
    source.alternative.response
        (source.toAlternativeState source.law.restorativeContext)
        (source.toAlternativeAction source.law.adverseIntervention) =
      P.response source.law.restorativeContext
        source.law.adverseIntervention := by
  exact
    Prod.ext
      source.preserves_adverse_observation
      source.preserves_adverse_readout

def toLocalResponseMapEventScoreSource :
    TwoChannelLocalResponseMapEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.toAlternativeState
  toAlternativeAction := source.toAlternativeAction
  preserves_restorative_probe := source.preserves_restorative_probe
  preserves_adverse_probe := source.preserves_adverse_probe
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toLocalResponseMapEventScoreSource.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toLocalResponseMapEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.toAlternativeState source.law.adverseContext)
        [source.toAlternativeAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.toAlternativeState source.law.restorativeContext)
        [source.toAlternativeAction source.law.adverseIntervention] :=
  source.toLocalResponseMapEventScoreSource.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalResponseMapEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalPostStepViewEventScoreSource

/--
Event-score source transported through local decisive-step view preservation.

This is one layer below `TwoChannelLocalPostStepViewEventScoreSource`: the
primitive fields preserve only the two decisive step squares and the
observation/readout views at the two reached source states.  The post-step
view equalities are derived by rewriting through the local step squares.  The
local step/view facts are still inputs, so this is not yet the
arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalStepViewEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  toAlternativeState : State -> AlternativeState
  toAlternativeAction : Action -> AlternativeAction
  restorative_step_commutes :
    toAlternativeState
        (P.step law.adverseContext law.restorativeIntervention) =
      alternative.step
        (toAlternativeState law.adverseContext)
        (toAlternativeAction law.restorativeIntervention)
  adverse_step_commutes :
    toAlternativeState
        (P.step law.restorativeContext law.adverseIntervention) =
      alternative.step
        (toAlternativeState law.restorativeContext)
        (toAlternativeAction law.adverseIntervention)
  preserves_restorative_post_observation :
    alternative.observe
        (toAlternativeState
          (P.step law.adverseContext law.restorativeIntervention)) =
      P.observe (P.step law.adverseContext law.restorativeIntervention)
  preserves_restorative_post_readout :
    alternative.readout
        (toAlternativeState
          (P.step law.adverseContext law.restorativeIntervention)) =
      P.readout (P.step law.adverseContext law.restorativeIntervention)
  preserves_adverse_post_observation :
    alternative.observe
        (toAlternativeState
          (P.step law.restorativeContext law.adverseIntervention)) =
      P.observe (P.step law.restorativeContext law.adverseIntervention)
  preserves_adverse_post_readout :
    alternative.readout
        (toAlternativeState
          (P.step law.restorativeContext law.adverseIntervention)) =
      P.readout (P.step law.restorativeContext law.adverseIntervention)
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelLocalStepViewEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalStepViewEventScoreSource
    P StateCoordinate AlternativeAction)

theorem preserves_restorative_observation :
    source.alternative.observe
        (source.alternative.step
          (source.toAlternativeState source.law.adverseContext)
          (source.toAlternativeAction source.law.restorativeIntervention)) =
      P.observe (P.step source.law.adverseContext
        source.law.restorativeIntervention) := by
  calc
    source.alternative.observe
        (source.alternative.step
          (source.toAlternativeState source.law.adverseContext)
          (source.toAlternativeAction source.law.restorativeIntervention)) =
        source.alternative.observe
          (source.toAlternativeState
            (P.step source.law.adverseContext
              source.law.restorativeIntervention)) := by
          rw [← source.restorative_step_commutes]
    _ = P.observe
        (P.step source.law.adverseContext
          source.law.restorativeIntervention) :=
      source.preserves_restorative_post_observation

theorem preserves_restorative_readout :
    source.alternative.readout
        (source.alternative.step
          (source.toAlternativeState source.law.adverseContext)
          (source.toAlternativeAction source.law.restorativeIntervention)) =
      P.readout (P.step source.law.adverseContext
        source.law.restorativeIntervention) := by
  calc
    source.alternative.readout
        (source.alternative.step
          (source.toAlternativeState source.law.adverseContext)
          (source.toAlternativeAction source.law.restorativeIntervention)) =
        source.alternative.readout
          (source.toAlternativeState
            (P.step source.law.adverseContext
              source.law.restorativeIntervention)) := by
          rw [← source.restorative_step_commutes]
    _ = P.readout
        (P.step source.law.adverseContext
          source.law.restorativeIntervention) :=
      source.preserves_restorative_post_readout

theorem preserves_adverse_observation :
    source.alternative.observe
        (source.alternative.step
          (source.toAlternativeState source.law.restorativeContext)
          (source.toAlternativeAction source.law.adverseIntervention)) =
      P.observe (P.step source.law.restorativeContext
        source.law.adverseIntervention) := by
  calc
    source.alternative.observe
        (source.alternative.step
          (source.toAlternativeState source.law.restorativeContext)
          (source.toAlternativeAction source.law.adverseIntervention)) =
        source.alternative.observe
          (source.toAlternativeState
            (P.step source.law.restorativeContext
              source.law.adverseIntervention)) := by
          rw [← source.adverse_step_commutes]
    _ = P.observe
        (P.step source.law.restorativeContext
          source.law.adverseIntervention) :=
      source.preserves_adverse_post_observation

theorem preserves_adverse_readout :
    source.alternative.readout
        (source.alternative.step
          (source.toAlternativeState source.law.restorativeContext)
          (source.toAlternativeAction source.law.adverseIntervention)) =
      P.readout (P.step source.law.restorativeContext
        source.law.adverseIntervention) := by
  calc
    source.alternative.readout
        (source.alternative.step
          (source.toAlternativeState source.law.restorativeContext)
          (source.toAlternativeAction source.law.adverseIntervention)) =
        source.alternative.readout
          (source.toAlternativeState
            (P.step source.law.restorativeContext
              source.law.adverseIntervention)) := by
          rw [← source.adverse_step_commutes]
    _ = P.readout
        (P.step source.law.restorativeContext
          source.law.adverseIntervention) :=
      source.preserves_adverse_post_readout

def toLocalPostStepViewEventScoreSource :
    TwoChannelLocalPostStepViewEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.toAlternativeState
  toAlternativeAction := source.toAlternativeAction
  preserves_restorative_observation :=
    source.preserves_restorative_observation
  preserves_restorative_readout := source.preserves_restorative_readout
  preserves_adverse_observation := source.preserves_adverse_observation
  preserves_adverse_readout := source.preserves_adverse_readout
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toLocalPostStepViewEventScoreSource.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toLocalPostStepViewEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.toAlternativeState source.law.adverseContext)
        [source.toAlternativeAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.toAlternativeState source.law.restorativeContext)
        [source.toAlternativeAction source.law.adverseIntervention] :=
  source.toLocalPostStepViewEventScoreSource.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalPostStepViewEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalPostStepViewEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalPostStepViewEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalPostStepViewEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalStepViewEventScoreSource

/--
Event-score source transported through a local decisive-step relation.

This is the relation-based local counterpart to the local step/view source
above.  It does not require a state function, action function, full transition
map, or full trace simulation.  It consumes only a role-free relation, view
preservation along that relation, and two local step-closure facts for the
decisive probes.  The relation and its local step closure are still inputs, so
this is not yet the arbitrary-alternative semantic G1 theorem.
-/
structure TwoChannelLocalStepRelationEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  targetAdverseContext : AlternativeState
  targetRestorativeContext : AlternativeState
  targetRestorativeIntervention : AlternativeAction
  targetAdverseIntervention : AlternativeAction
  related : State -> AlternativeState -> Prop
  preserves_observation :
    forall {s t}, related s t -> alternative.observe t = P.observe s
  preserves_readout :
    forall {s t}, related s t -> alternative.readout t = P.readout s
  adverse_context_related :
    related law.adverseContext targetAdverseContext
  restorative_context_related :
    related law.restorativeContext targetRestorativeContext
  restorative_step_related :
    related law.adverseContext targetAdverseContext ->
      related
        (P.step law.adverseContext law.restorativeIntervention)
        (alternative.step targetAdverseContext targetRestorativeIntervention)
  adverse_step_related :
    related law.restorativeContext targetRestorativeContext ->
      related
        (P.step law.restorativeContext law.adverseIntervention)
        (alternative.step targetRestorativeContext targetAdverseIntervention)
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelLocalStepRelationEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelLocalStepRelationEventScoreSource
    P StateCoordinate AlternativeAction)

theorem restorative_post_related :
    source.related
        (P.step source.law.adverseContext
          source.law.restorativeIntervention)
        (source.alternative.step source.targetAdverseContext
          source.targetRestorativeIntervention) :=
  source.restorative_step_related source.adverse_context_related

theorem adverse_post_related :
    source.related
        (P.step source.law.restorativeContext
          source.law.adverseIntervention)
        (source.alternative.step source.targetRestorativeContext
          source.targetAdverseIntervention) :=
  source.adverse_step_related source.restorative_context_related

theorem preserves_restorative_probe :
    source.alternative.response
        source.targetAdverseContext source.targetRestorativeIntervention =
      P.response source.law.adverseContext
        source.law.restorativeIntervention := by
  exact
    Prod.ext
      (source.preserves_observation source.restorative_post_related)
      (source.preserves_readout source.restorative_post_related)

theorem preserves_adverse_probe :
    source.alternative.response
        source.targetRestorativeContext source.targetAdverseIntervention =
      P.response source.law.restorativeContext
        source.law.adverseIntervention := by
  exact
    Prod.ext
      (source.preserves_observation source.adverse_post_related)
      (source.preserves_readout source.adverse_post_related)

def toFixedResponseEventScoreSource :
    TwoChannelFixedResponseEventScoreSource
      P StateCoordinate AlternativeAction where
  alternative := source.alternative
  transport := {
    law := source.law
    targetAdverseContext := source.targetAdverseContext
    targetRestorativeContext := source.targetRestorativeContext
    targetRestorativeIntervention := source.targetRestorativeIntervention
    targetAdverseIntervention := source.targetAdverseIntervention
    target_restorativeResponse_eq_source :=
      source.preserves_restorative_probe
    target_adverseResponse_eq_source :=
      source.preserves_adverse_probe }
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toFixedResponseEventScoreSource.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toFixedResponseEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        source.targetAdverseContext
        [source.targetRestorativeIntervention] ≠
      source.alternative.traceLog
        source.targetRestorativeContext
        [source.targetAdverseIntervention] :=
  source.toFixedResponseEventScoreSource.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelLocalStepRelationEventScoreSource

/-
Route a supplied role-free trace simulation through the smaller local
decisive-step relation interface.

This bridge does not derive the simulation relation for arbitrary
alternatives.  It only records that once such a simulation is supplied, its
observation/readout preservation and one-step closure fields supply exactly
the local relation data consumed by theorem 57.
-/
namespace TwoChannelTraceSimulationEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelTraceSimulationEventScoreSource
    P StateCoordinate AlternativeAction)

def toLocalStepRelationEventScoreSource :
    TwoChannelLocalStepRelationEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  targetAdverseContext := source.targetAdverseContext
  targetRestorativeContext := source.targetRestorativeContext
  targetRestorativeIntervention :=
    source.simulation.toAction source.law.restorativeIntervention
  targetAdverseIntervention :=
    source.simulation.toAction source.law.adverseIntervention
  related := source.simulation.related
  preserves_observation := by
    intro sourceState targetState h
    exact source.simulation.preserves_observation h
  preserves_readout := by
    intro sourceState targetState h
    exact source.simulation.preserves_readout h
  adverse_context_related := source.adverse_related
  restorative_context_related := source.restorative_related
  restorative_step_related := by
    intro h
    exact source.simulation.step_related h source.law.restorativeIntervention
  adverse_step_related := by
    intro h
    exact source.simulation.step_related h source.law.adverseIntervention
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toLocalStepRelationTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toLocalStepRelationEventScoreSource.toTargetTraceEventScoreSource

theorem localStepRelation_target_traceLog_ne :
    source.alternative.traceLog
        source.targetAdverseContext
        [source.simulation.toAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        source.targetRestorativeContext
        [source.simulation.toAction source.law.adverseIntervention] :=
  source.toLocalStepRelationEventScoreSource.target_traceLog_ne

theorem localStepRelation_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toLocalStepRelationTargetTraceEventScoreSource.totalScoreOfLog
              source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog) =
          source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
            source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toLocalStepRelationTargetTraceEventScoreSource.totalScoreOfLog
              source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
            source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalStepRelationEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem localStepRelation_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toLocalStepRelationTargetTraceEventScoreSource.totalScoreOfLog
              source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog) =
          source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toLocalStepRelationTargetTraceEventScoreSource.totalScoreOfLog
              source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalStepRelationEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem localStepRelation_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
                source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
            source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
                source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
            source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalStepRelationEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem localStepRelation_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
                source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toLocalStepRelationTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toLocalStepRelationTargetTraceEventScoreSource.componentScoreOfLog
                source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toLocalStepRelationTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toLocalStepRelationEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelTraceSimulationEventScoreSource

/--
Event-score source transported through a role-free observational response map.

This weakens `TwoChannelFixedResponseEventScoreSource`: the two decisive
one-step response equalities are no longer supplied separately.  They are
derived from `ObservationalResponseMap.preserves_response`.  The response map
itself is still an input, so this is not yet the arbitrary-alternative
semantic G1 theorem.
-/
structure TwoChannelResponseMapEventScoreSource
    {State : Type u} {Action : Type v} {Observation : Type w}
    (P : ObservationalPersistenceProcess State Action Observation)
    (AlternativeState : Type x) (AlternativeAction : Type y) where
  law : TwoChannelTraceLaw P
  alternative :
    ObservationalPersistenceProcess AlternativeState AlternativeAction
      Observation
  responseMap : ObservationalResponseMap P alternative
  canonicalBurdenEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalSupportEvent : List (Observation × BoundaryStatus) -> Bool
  canonicalBurden_adverse_active :
    canonicalBurdenEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = true
  canonicalBurden_restorative_inactive :
    canonicalBurdenEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = false
  canonicalSupport_adverse_inactive :
    canonicalSupportEvent
        (P.traceLog law.restorativeContext law.adverseTrace) = false
  canonicalSupport_restorative_active :
    canonicalSupportEvent
        (P.traceLog law.adverseContext law.restorativeTrace) = true

namespace TwoChannelResponseMapEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelResponseMapEventScoreSource
    P StateCoordinate AlternativeAction)

def toLocalResponseMapEventScoreSource :
    TwoChannelLocalResponseMapEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  toAlternativeState := source.responseMap.toState
  toAlternativeAction := source.responseMap.toAction
  preserves_restorative_probe :=
    source.responseMap.preserves_response
      source.law.adverseContext source.law.restorativeIntervention
  preserves_adverse_probe :=
    source.responseMap.preserves_response
      source.law.restorativeContext source.law.adverseIntervention
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toFixedResponseEventScoreSource :
    TwoChannelFixedResponseEventScoreSource
      P StateCoordinate AlternativeAction where
  alternative := source.alternative
  transport := {
    law := source.law
    targetAdverseContext := source.responseMap.toState source.law.adverseContext
    targetRestorativeContext :=
      source.responseMap.toState source.law.restorativeContext
    targetRestorativeIntervention :=
      source.responseMap.toAction source.law.restorativeIntervention
    targetAdverseIntervention :=
      source.responseMap.toAction source.law.adverseIntervention
    target_restorativeResponse_eq_source :=
      source.responseMap.preserves_response
        source.law.adverseContext source.law.restorativeIntervention
    target_adverseResponse_eq_source :=
      source.responseMap.preserves_response
        source.law.restorativeContext source.law.adverseIntervention }
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def targetLaw : TwoChannelTraceLaw source.alternative :=
  source.toFixedResponseEventScoreSource.targetLaw

def toTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toFixedResponseEventScoreSource.toTargetTraceEventScoreSource

theorem target_traceLog_ne :
    source.alternative.traceLog
        (source.responseMap.toState source.law.adverseContext)
        [source.responseMap.toAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.responseMap.toState source.law.restorativeContext)
        [source.responseMap.toAction source.law.adverseIntervention] :=
  source.toFixedResponseEventScoreSource.target_traceLog_ne

theorem no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.adverseTraceLog) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toTargetTraceEventScoreSource.totalScoreOfLog
              source.toTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.componentScoreOfLog
            source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toTargetTraceEventScoreSource.componentScoreOfLog
                source.toTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toFixedResponseEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelResponseMapEventScoreSource

/-
Route a step-commuting observational transition map through the response-map
event-score surface.

The transition map is still an input.  This bridge only records that the
role-free `toResponseMap` projection is enough to reuse the fixed-response
event-score no-go in the target observational process.
-/
namespace TwoChannelTransitionMapEventScoreSource

variable {AlternativeAction : Type y}
variable (source :
  TwoChannelTransitionMapEventScoreSource
    P StateCoordinate AlternativeAction)

def toResponseMapEventScoreSource :
    TwoChannelResponseMapEventScoreSource
      P StateCoordinate AlternativeAction where
  law := source.law
  alternative := source.alternative
  responseMap := source.transitionMap.toResponseMap
  canonicalBurdenEvent := source.canonicalBurdenEvent
  canonicalSupportEvent := source.canonicalSupportEvent
  canonicalBurden_adverse_active := source.canonicalBurden_adverse_active
  canonicalBurden_restorative_inactive :=
    source.canonicalBurden_restorative_inactive
  canonicalSupport_adverse_inactive :=
    source.canonicalSupport_adverse_inactive
  canonicalSupport_restorative_active :=
    source.canonicalSupport_restorative_active

def toResponseMapTargetTraceEventScoreSource :
    TwoChannelTraceEventScoreSource source.alternative :=
  source.toResponseMapEventScoreSource.toTargetTraceEventScoreSource

theorem responseMap_target_traceLog_ne :
    source.alternative.traceLog
        (source.transitionMap.toState source.law.adverseContext)
        [source.transitionMap.toAction source.law.restorativeIntervention] ≠
      source.alternative.traceLog
        (source.transitionMap.toState source.law.restorativeContext)
        [source.transitionMap.toAction source.law.adverseIntervention] :=
  source.toResponseMapEventScoreSource.target_traceLog_ne

theorem responseMap_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (source.toResponseMapTargetTraceEventScoreSource.totalScoreOfLog
              source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog) =
          source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
            source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (source.toResponseMapTargetTraceEventScoreSource.totalScoreOfLog
              source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
            source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toResponseMapEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem responseMap_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfTotal
            (source.toResponseMapTargetTraceEventScoreSource.totalScoreOfLog
              source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog) =
          source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (source.toResponseMapTargetTraceEventScoreSource.totalScoreOfLog
              source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) =
          source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toResponseMapEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem responseMap_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
                source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
            source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
                source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
            source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toResponseMapEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem responseMap_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (Observation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
                source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog)) =
          source.toResponseMapTargetTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (source.toResponseMapTargetTraceEventScoreSource.componentScoreOfLog
                source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog)) =
          source.toResponseMapTargetTraceEventScoreSource.restorativeTraceLog) :=
  source.toResponseMapEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

end TwoChannelTransitionMapEventScoreSource

namespace ToyJointProcess

/--
Candidate burden score for the joint toy process.

The adverse pulse contributes one burden unit; the restorative channel does
not.  This is a toy score, not a derived global `L/B` coordinate.
-/
def jointCompositeBurdenScore : JointAction -> Nat
  | JointAction.pulse actionAdverse _ =>
      if actionAdverse then 1 else 0

/--
Candidate support score for the joint toy process.

The restorative pulse contributes one support unit; the adverse channel does
not.  This is a toy score, not a derived global `M` coordinate.
-/
def jointCompositeSupportScore : JointAction -> Nat
  | JointAction.pulse _ actionRestorative =>
      if actionRestorative then 1 else 0

/--
Observable channel source for the joint toy component scores.

The numeric component scores are constructed from the adverse/restorative
Boolean action channels with unit score `1`.
-/
def jointComponentScoreSource :
    TwoChannelComponentScoreSource process where
  law := jointChannelTraceLaw
  scoreUnit := 1
  scoreUnit_ne_zero := by
    decide
  burdenChannel
    | JointAction.pulse actionAdverse _ => actionAdverse
  supportChannel
    | JointAction.pulse _ actionRestorative => actionRestorative
  burdenChannel_restorative_inactive := by
    rfl
  burdenChannel_adverse_active := by
    rfl
  supportChannel_restorative_active := by
    rfl
  supportChannel_adverse_inactive := by
    rfl

def jointSourceDerivedCompositeScoreLaw :
    TwoChannelCompositeScoreLaw process :=
  jointComponentScoreSource.toCompositeScoreLaw

theorem jointSourceDerivedCompositeScore_same_totalTrace :
    jointSourceDerivedCompositeScoreLaw.restorativeTotalTrace =
      jointSourceDerivedCompositeScoreLaw.adverseTotalTrace :=
  jointSourceDerivedCompositeScoreLaw.restorativeTotalTrace_eq_adverseTotalTrace

theorem jointSourceDerivedCompositeScore_componentTrace_ne :
    jointSourceDerivedCompositeScoreLaw.restorativeComponentTrace ≠
      jointSourceDerivedCompositeScoreLaw.adverseComponentTrace :=
  jointSourceDerivedCompositeScoreLaw.restorativeComponentTrace_ne_adverseComponentTrace

theorem jointSourceDerivedCompositeScore_no_totalTrace_componentTrace_decoder :
    ¬ Exists
      (fun componentOfTotal : List Nat -> List (Nat × Nat) =>
        componentOfTotal
              jointSourceDerivedCompositeScoreLaw.restorativeTotalTrace =
            jointSourceDerivedCompositeScoreLaw.restorativeComponentTrace ∧
          componentOfTotal
              jointSourceDerivedCompositeScoreLaw.adverseTotalTrace =
            jointSourceDerivedCompositeScoreLaw.adverseComponentTrace) :=
  jointComponentScoreSource.no_totalTrace_componentTrace_decoder

theorem jointSourceDerivedCompositeScore_no_totalTrace_prefixLog_model :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfTotal
                (contextAggregate s)
                (actions.map
                  jointSourceDerivedCompositeScoreLaw.totalCoordinate)) :=
  jointComponentScoreSource.no_totalTrace_prefixLog_model
    contextAggregate contextAggregate_identifies_jointContexts

theorem jointSourceDerivedCompositeScore_exists_componentTrace_decisive_readout :
    ∃ readout : List (Nat × Nat) ->
        List (JointObservation × BoundaryStatus),
      readout jointSourceDerivedCompositeScoreLaw.restorativeComponentTrace =
          process.traceLog
            jointChannelTraceLaw.adverseContext
            jointChannelTraceLaw.restorativeTrace ∧
        readout jointSourceDerivedCompositeScoreLaw.adverseComponentTrace =
          process.traceLog
            jointChannelTraceLaw.restorativeContext
            jointChannelTraceLaw.adverseTrace :=
  jointComponentScoreSource.exists_componentTrace_decisive_readout

/--
Prefix-log event source for the joint toy component scores.

The component score pair is read from observed prefix-log events:
collapsed-prefix activity on the adverse decisive log, and viable-final
activity on the restorative decisive log.
-/
def jointTraceEventScoreSource :
    TwoChannelTraceEventScoreSource process where
  law := jointChannelTraceLaw
  burdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  burdenEvent_adverse_active := by
    rfl
  burdenEvent_restorative_inactive := by
    rfl
  supportEvent_adverse_inactive := by
    rfl
  supportEvent_restorative_active := by
    rfl

/--
The joint toy event source with Boolean events derived only from equality to
the two decisive observed prefix logs.

This does not use the canonical collapsed-prefix / viable-final readouts.  It
only records the minimal observation-derived fact that the two distinct
decisive logs can be separated by local equality tests.
-/
def jointDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource process :=
  jointChannelTraceLaw.toDecisiveEqualityEventScoreSource

theorem jointDecisiveEqualityEventScore_burdenEvent_adverse_active :
    jointChannelTraceLaw.adverseEqualityEvent
        jointDecisiveEqualityEventScoreSource.adverseTraceLog = true :=
  jointChannelTraceLaw.adverseEqualityEvent_adverse_active

theorem jointDecisiveEqualityEventScore_supportEvent_restorative_active :
    jointChannelTraceLaw.restorativeEqualityEvent
        jointDecisiveEqualityEventScoreSource.restorativeTraceLog = true :=
  jointChannelTraceLaw.restorativeEqualityEvent_restorative_active

theorem jointDecisiveEqualityEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointDecisiveEqualityEventScoreSource.adverseTraceLog) =
          jointDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          jointDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointChannelTraceLaw.decisiveEquality_no_totalScoreOfLog_traceLog_decoder

theorem jointDecisiveEqualityEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          jointDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          jointDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointChannelTraceLaw
    |>.decisiveEquality_no_totalComponentScalar_traceLog_decoder

/--
The same joint toy event source, but routed through local preservation of
canonical prefix-log events.

This exposes the next boundary: the active/inactive event laws can be read
from preservation certificates for canonical observed events, rather than
being supplied directly as candidate-event laws.
-/
def jointPreservedTraceEventScoreSource :
    TwoChannelPreservedTraceEventScoreSource process where
  law := jointChannelTraceLaw
  burdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
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

def jointPreservedTraceEventScoreTraceEventSource :
    TwoChannelTraceEventScoreSource process :=
  jointPreservedTraceEventScoreSource.toTraceEventScoreSource

/--
The joint toy event source routed one layer lower: the preservation
certificates are induced by observable prefix-log maps.  In the toy witness the
map is the identity on logs, but the construction now exposes the exact place
where a nontrivial admissible alternative would have to preserve the decisive
prefix logs.
-/
def jointObservedLogPreservedTraceEventScoreSource :
    TwoChannelObservedLogPreservedTraceEventScoreSource process where
  law := jointChannelTraceLaw
  burdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  burdenEvent_logMap := {
    canonicalLogOf := fun traceLog => traceLog
    reads_canonical := by
      intro traceLog
      rfl
    preserves_adverse_log := by
      rfl
    preserves_restorative_log := by
      rfl }
  supportEvent_logMap := {
    canonicalLogOf := fun traceLog => traceLog
    reads_canonical := by
      intro traceLog
      rfl
    preserves_adverse_log := by
      rfl
    preserves_restorative_log := by
      rfl }
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointObservedLogPreservedTraceEventScoreTraceEventSource :
    TwoChannelTraceEventScoreSource process :=
  jointObservedLogPreservedTraceEventScoreSource.toTraceEventScoreSource

def jointCompositeIdentityTraceLogModel :
    JointCoordinateTraceLogModel process JointState JointAction where
  stateCoordinate := id
  actionCoordinate := id
  traceLogOfCoordinates := fun state actions => process.traceLog state actions
  preserves_traceLog := by
    intro state actions
    change process.traceLog state actions =
      process.traceLog state (actions.map id)
    have hmap : actions.map id = actions := by
      induction actions with
      | nil => rfl
      | cons action actions ih =>
          change action :: actions.map id = action :: actions
          rw [ih]
    rw [hmap]

/--
The same joint toy score source, now routed through a prefix-log-preserving
coordinate model.  The model is the identity model in this toy instance; the
point is that the event score source now consumes an observational trace-log
preservation surface rather than direct fixed-log event preservation fields.
-/
def jointTraceLogModelEventScoreSource :
    TwoChannelTraceLogModelEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  model := jointCompositeIdentityTraceLogModel
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointTraceLogModelEventScoreTraceEventSource :
    TwoChannelTraceEventScoreSource process :=
  jointTraceLogModelEventScoreSource.toTraceEventScoreSource

/--
The same joint toy score source, routed through an explicit alternative
observational process plus a prefix-log preservation law.

Here the alternative is the identity process.  The point is not the identity
example itself, but the interface boundary: once an alternative process and an
observational prefix-log preservation law are supplied, the older trace-log
model source is constructed rather than given directly.
-/
def jointAlternativeTraceLogEventScoreSource :
    TwoChannelAlternativeTraceLogEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  preserves_traceLog := jointCompositeIdentityTraceLogModel.preserves_traceLog
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointAlternativeTraceLogEventScoreTraceEventSource :
    TwoChannelTraceEventScoreSource process :=
  jointAlternativeTraceLogEventScoreSource.toTraceEventScoreSource

/--
Identity transition map for the joint toy process.

The proof is intentionally role-free: observations/readouts are preserved and
the step function commutes with identity translations.
-/
def jointIdentityTransitionMap :
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
The joint toy score source routed through a step-commuting observational map.

This derives the prefix-log preservation law from `jointIdentityTransitionMap`
rather than supplying it directly.
-/
def jointTransitionMapEventScoreSource :
    TwoChannelTransitionMapEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  transitionMap := jointIdentityTransitionMap
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointTransitionMapEventScoreTraceEventSource :
    TwoChannelTraceEventScoreSource process :=
  jointTransitionMapEventScoreSource.toTraceEventScoreSource

/--
The joint toy event source routed through a relation-based observational trace
simulation.  The witness relation is induced by the identity transition map,
but the consumed interface is the weaker simulation relation.
-/
def jointTraceSimulationEventScoreSource :
    TwoChannelTraceSimulationEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  simulation :=
    ObservationalTraceSimulation.ofTransitionMap jointIdentityTransitionMap
  targetAdverseContext := jointChannelTraceLaw.adverseContext
  targetRestorativeContext := jointChannelTraceLaw.restorativeContext
  adverse_related := rfl
  restorative_related := rfl
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointTraceSimulationEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointTraceSimulationEventScoreSource.toTargetTraceEventScoreSource

theorem jointTraceSimulationEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        jointTraceSimulationEventScoreSource.targetLaw.restorativeTrace ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        jointTraceSimulationEventScoreSource.targetLaw.adverseTrace :=
  jointTraceSimulationEventScoreSource.target_traceLog_ne

theorem jointTraceSimulationEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTraceSimulationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationEventScoreTargetSource.adverseTraceLog) =
          jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointTraceSimulationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) =
          jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointTraceSimulationEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTraceSimulationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationEventScoreTargetSource.adverseTraceLog) =
          jointTraceSimulationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTraceSimulationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) =
          jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointTraceSimulationEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationEventScoreTargetSource.adverseTraceLog)) =
          jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationEventScoreTargetSource.restorativeTraceLog)) =
          jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointTraceSimulationEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationEventScoreTargetSource.adverseTraceLog)) =
          jointTraceSimulationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationEventScoreTargetSource.restorativeTraceLog)) =
          jointTraceSimulationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource.no_totalComponentScalar_traceLog_decoder

def jointTraceSimulationLocalStepRelationEventScoreSource :
    TwoChannelLocalStepRelationEventScoreSource
      process JointState JointAction :=
  jointTraceSimulationEventScoreSource.toLocalStepRelationEventScoreSource

def jointTraceSimulationLocalStepRelationEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointTraceSimulationEventScoreSource
    |>.toLocalStepRelationTargetTraceEventScoreSource

theorem jointTraceSimulationLocalStepRelation_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointTraceSimulationEventScoreSource.localStepRelation_target_traceLog_ne

theorem jointTraceSimulationLocalStepRelation_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTraceSimulationLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointTraceSimulationLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource
    |>.localStepRelation_no_totalScoreOfLog_componentScore_decoder

theorem jointTraceSimulationLocalStepRelation_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTraceSimulationLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTraceSimulationLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource
    |>.localStepRelation_no_totalScoreOfLog_traceLog_decoder

theorem jointTraceSimulationLocalStepRelation_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog)) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog)) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource
    |>.localStepRelation_no_totalComponentScalar_component_decoder

theorem jointTraceSimulationLocalStepRelation_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog)) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceSimulationLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog)) =
          jointTraceSimulationLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointTraceSimulationEventScoreSource
    |>.localStepRelation_no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through only the two decisive fixed-log
equalities.  This removes even the simulation relation from the consumed
interface for this toy witness.
-/
def jointFixedTraceLogEventScoreSource :
    TwoChannelFixedTraceLogEventScoreSource
      process JointState JointAction where
  alternative := process
  transport := {
    law := jointChannelTraceLaw
    targetAdverseContext := jointChannelTraceLaw.adverseContext
    targetRestorativeContext := jointChannelTraceLaw.restorativeContext
    targetRestorativeIntervention := jointChannelTraceLaw.restorativeIntervention
    targetAdverseIntervention := jointChannelTraceLaw.adverseIntervention
    target_restorativeTraceLog_eq_source := by
      rfl
    target_adverseTraceLog_eq_source := by
      rfl }
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointFixedTraceLogEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointFixedTraceLogEventScoreSource.toTargetTraceEventScoreSource

theorem jointFixedTraceLogEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointFixedTraceLogEventScoreSource.target_traceLog_ne

theorem jointFixedTraceLogEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointFixedTraceLogEventScoreTargetSource.totalScoreOfLog
              jointFixedTraceLogEventScoreTargetSource.adverseTraceLog) =
          jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
            jointFixedTraceLogEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointFixedTraceLogEventScoreTargetSource.totalScoreOfLog
              jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) =
          jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
            jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointFixedTraceLogEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointFixedTraceLogEventScoreTargetSource.totalScoreOfLog
              jointFixedTraceLogEventScoreTargetSource.adverseTraceLog) =
          jointFixedTraceLogEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointFixedTraceLogEventScoreTargetSource.totalScoreOfLog
              jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) =
          jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointFixedTraceLogEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
                jointFixedTraceLogEventScoreTargetSource.adverseTraceLog)) =
          jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
            jointFixedTraceLogEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
                jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog)) =
          jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
            jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointFixedTraceLogEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
                jointFixedTraceLogEventScoreTargetSource.adverseTraceLog)) =
          jointFixedTraceLogEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogEventScoreTargetSource.componentScoreOfLog
                jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog)) =
          jointFixedTraceLogEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.no_totalComponentScalar_traceLog_decoder

/--
The same fixed-log toy transport can construct its local event scores from the
two decisive target logs themselves, without supplying canonical event laws for
this minimal no-go.
-/
def jointFixedTraceLogDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource process :=
  jointFixedTraceLogEventScoreSource.transport
    |>.toDecisiveEqualityEventScoreSource

theorem jointFixedTraceLogDecisiveEquality_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointFixedTraceLogEventScoreSource.transport
    |>.decisiveEquality_target_traceLog_ne

theorem jointFixedTraceLogDecisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointFixedTraceLogDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointFixedTraceLogDecisiveEqualityEventScoreSource.adverseTraceLog) =
          jointFixedTraceLogDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointFixedTraceLogDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointFixedTraceLogDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          jointFixedTraceLogDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.transport
    |>.decisiveEquality_no_totalScoreOfLog_traceLog_decoder

theorem jointFixedTraceLogDecisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointFixedTraceLogDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          jointFixedTraceLogDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedTraceLogDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointFixedTraceLogDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          jointFixedTraceLogDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointFixedTraceLogEventScoreSource.transport
    |>.decisiveEquality_no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through only the two decisive one-step
response equalities.  The fixed-log transport is derived from these response
equalities.
-/
def jointFixedResponseEventScoreSource :
    TwoChannelFixedResponseEventScoreSource
      process JointState JointAction where
  alternative := process
  transport := {
    law := jointChannelTraceLaw
    targetAdverseContext := jointChannelTraceLaw.adverseContext
    targetRestorativeContext := jointChannelTraceLaw.restorativeContext
    targetRestorativeIntervention := jointChannelTraceLaw.restorativeIntervention
    targetAdverseIntervention := jointChannelTraceLaw.adverseIntervention
    target_restorativeResponse_eq_source := by
      rfl
    target_adverseResponse_eq_source := by
      rfl }
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointFixedResponseEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointFixedResponseEventScoreSource.toTargetTraceEventScoreSource

theorem jointFixedResponseEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointFixedResponseEventScoreSource.target_traceLog_ne

theorem jointFixedResponseEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointFixedResponseEventScoreTargetSource.totalScoreOfLog
              jointFixedResponseEventScoreTargetSource.adverseTraceLog) =
          jointFixedResponseEventScoreTargetSource.componentScoreOfLog
            jointFixedResponseEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointFixedResponseEventScoreTargetSource.totalScoreOfLog
              jointFixedResponseEventScoreTargetSource.restorativeTraceLog) =
          jointFixedResponseEventScoreTargetSource.componentScoreOfLog
            jointFixedResponseEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointFixedResponseEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointFixedResponseEventScoreTargetSource.totalScoreOfLog
              jointFixedResponseEventScoreTargetSource.adverseTraceLog) =
          jointFixedResponseEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointFixedResponseEventScoreTargetSource.totalScoreOfLog
              jointFixedResponseEventScoreTargetSource.restorativeTraceLog) =
          jointFixedResponseEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointFixedResponseEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointFixedResponseEventScoreTargetSource.componentScoreOfLog
                jointFixedResponseEventScoreTargetSource.adverseTraceLog)) =
          jointFixedResponseEventScoreTargetSource.componentScoreOfLog
            jointFixedResponseEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointFixedResponseEventScoreTargetSource.componentScoreOfLog
                jointFixedResponseEventScoreTargetSource.restorativeTraceLog)) =
          jointFixedResponseEventScoreTargetSource.componentScoreOfLog
            jointFixedResponseEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointFixedResponseEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedResponseEventScoreTargetSource.componentScoreOfLog
                jointFixedResponseEventScoreTargetSource.adverseTraceLog)) =
          jointFixedResponseEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedResponseEventScoreTargetSource.componentScoreOfLog
                jointFixedResponseEventScoreTargetSource.restorativeTraceLog)) =
          jointFixedResponseEventScoreTargetSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.no_totalComponentScalar_traceLog_decoder

/--
The same fixed-response toy transport derives fixed-log transport first, then
constructs local decisive equality events from the transported target logs.
-/
def jointFixedResponseDecisiveEqualityEventScoreSource :
    TwoChannelTraceEventScoreSource process :=
  jointFixedResponseEventScoreSource.transport
    |>.toDecisiveEqualityEventScoreSource

theorem jointFixedResponseDecisiveEquality_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointFixedResponseEventScoreSource.transport
    |>.decisiveEquality_target_traceLog_ne

theorem jointFixedResponseDecisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointFixedResponseDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointFixedResponseDecisiveEqualityEventScoreSource.adverseTraceLog) =
          jointFixedResponseDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointFixedResponseDecisiveEqualityEventScoreSource.totalScoreOfLog
              jointFixedResponseDecisiveEqualityEventScoreSource.restorativeTraceLog) =
          jointFixedResponseDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.transport
    |>.decisiveEquality_no_totalScoreOfLog_traceLog_decoder

theorem jointFixedResponseDecisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedResponseDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointFixedResponseDecisiveEqualityEventScoreSource.adverseTraceLog)) =
          jointFixedResponseDecisiveEqualityEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointFixedResponseDecisiveEqualityEventScoreSource.componentScoreOfLog
                jointFixedResponseDecisiveEqualityEventScoreSource.restorativeTraceLog)) =
          jointFixedResponseDecisiveEqualityEventScoreSource.restorativeTraceLog) :=
  jointFixedResponseEventScoreSource.transport
    |>.decisiveEquality_no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through a local two-probe response map.

Only the two decisive intervention responses are preserved.  This is weaker
than supplying the full `jointIdentityObservationMap`.
-/
def jointLocalResponseMapEventScoreSource :
    TwoChannelLocalResponseMapEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  preserves_restorative_probe := by
    rfl
  preserves_adverse_probe := by
    rfl
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointLocalResponseMapEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalResponseMapEventScoreSource.toTargetTraceEventScoreSource

theorem jointLocalResponseMapEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalResponseMapEventScoreSource.target_traceLog_ne

theorem jointLocalResponseMapEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointLocalResponseMapEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
            jointLocalResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointLocalResponseMapEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
            jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointLocalResponseMapEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalResponseMapEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointLocalResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalResponseMapEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalResponseMapEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
            jointLocalResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
            jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointLocalResponseMapEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointLocalResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapEventScoreSource.no_totalComponentScalar_traceLog_decoder

/--
The same local two-probe response route, but with local equality-to-decisive-log
events instead of canonical collapsed-prefix / viable-final event laws.
-/
def jointLocalResponseMapDecisiveEqualityEventScoreSource :
    TwoChannelLocalResponseMapDecisiveEqualityEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  preserves_restorative_probe := by
    rfl
  preserves_adverse_probe := by
    rfl

def jointLocalResponseMapDecisiveEqualityEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalResponseMapDecisiveEqualityEventScoreSource
    |>.toDecisiveEqualityEventScoreSource

theorem jointLocalResponseMapDecisiveEquality_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalResponseMapDecisiveEqualityEventScoreSource.target_traceLog_ne

theorem jointLocalResponseMapDecisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog) =
          jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) =
          jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalResponseMapDecisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog)) =
          jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through post-step observation/readout
preservation on only the two decisive probes.
-/
def jointLocalPostStepViewEventScoreSource :
    TwoChannelLocalPostStepViewEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  preserves_restorative_observation := by
    rfl
  preserves_restorative_readout := by
    rfl
  preserves_adverse_observation := by
    rfl
  preserves_adverse_readout := by
    rfl
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointLocalPostStepViewEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalPostStepViewEventScoreSource.toTargetTraceEventScoreSource

theorem jointLocalPostStepViewEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalPostStepViewEventScoreSource.target_traceLog_ne

theorem jointLocalPostStepViewEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointLocalPostStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog) =
          jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointLocalPostStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) =
          jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointLocalPostStepViewEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalPostStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog) =
          jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalPostStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) =
          jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalPostStepViewEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog)) =
          jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointLocalPostStepViewEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog)) =
          jointLocalPostStepViewEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalPostStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
The same post-step view route, but with local equality-to-decisive-log events
instead of canonical collapsed-prefix / viable-final event laws.
-/
def jointLocalPostStepViewDecisiveEqualityEventScoreSource :
    TwoChannelLocalPostStepViewDecisiveEqualityEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  preserves_restorative_observation := by
    rfl
  preserves_restorative_readout := by
    rfl
  preserves_adverse_observation := by
    rfl
  preserves_adverse_readout := by
    rfl

def jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalPostStepViewDecisiveEqualityEventScoreSource
    |>.toDecisiveEqualityEventScoreSource

theorem jointLocalPostStepViewDecisiveEquality_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalPostStepViewDecisiveEqualityEventScoreSource.target_traceLog_ne

theorem jointLocalPostStepViewDecisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.adverseTraceLog) =
          jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) =
          jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalPostStepViewDecisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.adverseTraceLog)) =
          jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalPostStepViewDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalPostStepViewDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through local decisive-step view data.

This refines `jointLocalPostStepViewEventScoreSource`: the post-step views are
obtained after the two local step squares are checked for the identity toy map.
-/
def jointLocalStepViewEventScoreSource :
    TwoChannelLocalStepViewEventScoreSource process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  toAlternativeState := id
  toAlternativeAction := id
  restorative_step_commutes := by
    rfl
  adverse_step_commutes := by
    rfl
  preserves_restorative_post_observation := by
    rfl
  preserves_restorative_post_readout := by
    rfl
  preserves_adverse_post_observation := by
    rfl
  preserves_adverse_post_readout := by
    rfl
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointLocalStepViewEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalStepViewEventScoreSource.toTargetTraceEventScoreSource

theorem jointLocalStepViewEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalStepViewEventScoreSource.target_traceLog_ne

theorem jointLocalStepViewEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointLocalStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalStepViewEventScoreTargetSource.adverseTraceLog) =
          jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalStepViewEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointLocalStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) =
          jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepViewEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointLocalStepViewEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalStepViewEventScoreTargetSource.adverseTraceLog) =
          jointLocalStepViewEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalStepViewEventScoreTargetSource.totalScoreOfLog
              jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) =
          jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepViewEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalStepViewEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalStepViewEventScoreTargetSource.adverseTraceLog)) =
          jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalStepViewEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalStepViewEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
            jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepViewEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointLocalStepViewEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalStepViewEventScoreTargetSource.adverseTraceLog)) =
          jointLocalStepViewEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalStepViewEventScoreTargetSource.componentScoreOfLog
                jointLocalStepViewEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalStepViewEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepViewEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed through a local decisive-step relation.

The relation is equality in the toy process, but the consumed interface is the
local relation plus two local step-closure facts rather than a full map or a
full simulation.
-/
def jointLocalStepRelationEventScoreSource :
    TwoChannelLocalStepRelationEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  targetAdverseContext := jointChannelTraceLaw.adverseContext
  targetRestorativeContext := jointChannelTraceLaw.restorativeContext
  targetRestorativeIntervention :=
    jointChannelTraceLaw.restorativeIntervention
  targetAdverseIntervention := jointChannelTraceLaw.adverseIntervention
  related := fun sourceState targetState => targetState = sourceState
  preserves_observation := by
    intro sourceState targetState h
    rw [h]
  preserves_readout := by
    intro sourceState targetState h
    rw [h]
  adverse_context_related := by
    rfl
  restorative_context_related := by
    rfl
  restorative_step_related := by
    intro h
    rw [h]
  adverse_step_related := by
    intro h
    rw [h]
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointLocalStepRelationEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointLocalStepRelationEventScoreSource.toTargetTraceEventScoreSource

theorem jointLocalStepRelationEventScore_target_traceLog_ne :
    process.traceLog
        jointChannelTraceLaw.adverseContext
        [jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        jointChannelTraceLaw.restorativeContext
        [jointChannelTraceLaw.adverseIntervention] :=
  jointLocalStepRelationEventScoreSource.target_traceLog_ne

theorem jointLocalStepRelationEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointLocalStepRelationEventScoreTargetSource.adverseTraceLog) =
          jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) =
          jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepRelationEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointLocalStepRelationEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointLocalStepRelationEventScoreTargetSource.adverseTraceLog) =
          jointLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointLocalStepRelationEventScoreTargetSource.totalScoreOfLog
              jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) =
          jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepRelationEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem jointLocalStepRelationEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointLocalStepRelationEventScoreTargetSource.adverseTraceLog)) =
          jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
            jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepRelationEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointLocalStepRelationEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointLocalStepRelationEventScoreTargetSource.adverseTraceLog)) =
          jointLocalStepRelationEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointLocalStepRelationEventScoreTargetSource.componentScoreOfLog
                jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog)) =
          jointLocalStepRelationEventScoreTargetSource.restorativeTraceLog) :=
  jointLocalStepRelationEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
Deletion guard for the local step-relation source.

This alternative keeps the current observation/readout layer identical but
breaks the restorative decisive step.  It shows that preserving current views
along a relation is not enough to obtain theorem 57's fixed response transport;
the local step-closure field carries real proof load.
-/
def jointNoStepClosureStep : JointState -> JointAction -> JointState
  | JointState.latent true false, JointAction.pulse false true =>
      JointState.failed
  | state, action => step state action

def jointNoStepClosureProcess :
    ObservationalPersistenceProcess
      JointState JointAction JointObservation where
  observe := observe
  step := jointNoStepClosureStep
  readout := readout

theorem jointNoStepClosure_preserves_adverse_current_view :
    jointNoStepClosureProcess.currentView contextAdverseOnly =
      process.currentView contextAdverseOnly :=
  rfl

theorem jointNoStepClosure_preserves_restorative_current_view :
    jointNoStepClosureProcess.currentView contextRestorativeOnly =
      process.currentView contextRestorativeOnly :=
  rfl

theorem jointNoStepClosure_restorative_step_not_related :
    ¬
      ((fun sourceState targetState : JointState =>
          targetState = sourceState)
        (process.step contextAdverseOnly restorativePulse)
        (jointNoStepClosureProcess.step
          contextAdverseOnly restorativePulse)) := by
  decide

theorem jointNoStepClosure_restorative_response_ne :
    jointNoStepClosureProcess.response
        contextAdverseOnly restorativePulse ≠
      process.response contextAdverseOnly restorativePulse := by
  decide

theorem jointNoStepClosure_traceLog_ne :
    jointNoStepClosureProcess.traceLog
        contextAdverseOnly [restorativePulse] ≠
      process.traceLog contextAdverseOnly [restorativePulse] := by
  decide

/--
Deletion guard for the local view-preservation fields.

This alternative keeps the transition law unchanged, so the equality relation
is closed under the two decisive steps.  It only changes the observable view of
the reached `ok` state.  Thus local step closure alone is not enough to obtain
theorem 57's fixed response transport; reached-state view preservation also
carries real proof load.
-/
def jointNoPostViewObserve : JointState -> JointObservation
  | JointState.ok => JointObservation.red
  | state => observe state

def jointNoPostViewReadout : JointState -> BoundaryStatus
  | JointState.ok => BoundaryStatus.collapsed
  | state => readout state

def jointNoPostViewProcess :
    ObservationalPersistenceProcess
      JointState JointAction JointObservation where
  observe := jointNoPostViewObserve
  step := step
  readout := jointNoPostViewReadout

theorem jointNoPostView_preserves_adverse_current_view :
    jointNoPostViewProcess.currentView contextAdverseOnly =
      process.currentView contextAdverseOnly :=
  rfl

theorem jointNoPostView_preserves_restorative_current_view :
    jointNoPostViewProcess.currentView contextRestorativeOnly =
      process.currentView contextRestorativeOnly :=
  rfl

theorem jointNoPostView_restorative_step_related :
    (fun sourceState targetState : JointState => targetState = sourceState)
        (process.step contextAdverseOnly restorativePulse)
        (jointNoPostViewProcess.step
          contextAdverseOnly restorativePulse) :=
  rfl

theorem jointNoPostView_adverse_step_related :
    (fun sourceState targetState : JointState => targetState = sourceState)
        (process.step contextRestorativeOnly adversePulse)
        (jointNoPostViewProcess.step
          contextRestorativeOnly adversePulse) :=
  rfl

theorem jointNoPostView_restorative_post_view_ne :
    jointNoPostViewProcess.currentView
        (jointNoPostViewProcess.step contextAdverseOnly restorativePulse) ≠
      process.currentView
        (process.step contextAdverseOnly restorativePulse) := by
  decide

theorem jointNoPostView_restorative_response_ne :
    jointNoPostViewProcess.response
        contextAdverseOnly restorativePulse ≠
      process.response contextAdverseOnly restorativePulse := by
  decide

theorem jointNoPostView_traceLog_ne :
    jointNoPostViewProcess.traceLog
        contextAdverseOnly [restorativePulse] ≠
      process.traceLog contextAdverseOnly [restorativePulse] := by
  decide

/--
The joint toy event source routed through a role-free observational response
map.  The decisive response equalities are induced by
`jointIdentityObservationMap`.
-/
def jointResponseMapEventScoreSource :
    TwoChannelResponseMapEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  responseMap := jointIdentityObservationMap
  canonicalBurdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  canonicalSupportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  canonicalBurden_adverse_active := by
    rfl
  canonicalBurden_restorative_inactive := by
    rfl
  canonicalSupport_adverse_inactive := by
    rfl
  canonicalSupport_restorative_active := by
    rfl

def jointResponseMapEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointResponseMapEventScoreSource.toTargetTraceEventScoreSource

theorem jointResponseMapEventScore_target_traceLog_ne :
    process.traceLog
        (jointIdentityObservationMap.toState jointChannelTraceLaw.adverseContext)
        [jointIdentityObservationMap.toAction
          jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        (jointIdentityObservationMap.toState
          jointChannelTraceLaw.restorativeContext)
        [jointIdentityObservationMap.toAction
          jointChannelTraceLaw.adverseIntervention] :=
  jointResponseMapEventScoreSource.target_traceLog_ne

theorem jointResponseMapEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointResponseMapEventScoreTargetSource.totalScoreOfLog
              jointResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointResponseMapEventScoreTargetSource.componentScoreOfLog
            jointResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointResponseMapEventScoreTargetSource.totalScoreOfLog
              jointResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointResponseMapEventScoreTargetSource.componentScoreOfLog
            jointResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointResponseMapEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointResponseMapEventScoreTargetSource.totalScoreOfLog
              jointResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointResponseMapEventScoreTargetSource.totalScoreOfLog
              jointResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointResponseMapEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointResponseMapEventScoreTargetSource.componentScoreOfLog
                jointResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointResponseMapEventScoreTargetSource.componentScoreOfLog
            jointResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointResponseMapEventScoreTargetSource.componentScoreOfLog
                jointResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointResponseMapEventScoreTargetSource.componentScoreOfLog
            jointResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointResponseMapEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointResponseMapEventScoreTargetSource.componentScoreOfLog
                jointResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointResponseMapEventScoreTargetSource.componentScoreOfLog
                jointResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapEventScoreSource.no_totalComponentScalar_traceLog_decoder

/--
The same response-map route, but with local equality-to-decisive-log events
instead of canonical collapsed-prefix / viable-final event laws.
-/
def jointResponseMapDecisiveEqualityEventScoreSource :
    TwoChannelResponseMapDecisiveEqualityEventScoreSource
      process JointState JointAction where
  law := jointChannelTraceLaw
  alternative := process
  responseMap := jointIdentityObservationMap

def jointResponseMapDecisiveEqualityEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointResponseMapDecisiveEqualityEventScoreSource
    |>.toDecisiveEqualityEventScoreSource

theorem jointResponseMapDecisiveEquality_target_traceLog_ne :
    process.traceLog
        (jointIdentityObservationMap.toState jointChannelTraceLaw.adverseContext)
        [jointIdentityObservationMap.toAction
          jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        (jointIdentityObservationMap.toState
          jointChannelTraceLaw.restorativeContext)
        [jointIdentityObservationMap.toAction
          jointChannelTraceLaw.adverseIntervention] :=
  jointResponseMapDecisiveEqualityEventScoreSource.target_traceLog_ne

theorem jointResponseMapDecisiveEquality_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointResponseMapDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog) =
          jointResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointResponseMapDecisiveEqualityEventScoreTargetSource.totalScoreOfLog
              jointResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) =
          jointResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem jointResponseMapDecisiveEquality_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointResponseMapDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog)) =
          jointResponseMapDecisiveEqualityEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointResponseMapDecisiveEqualityEventScoreTargetSource.componentScoreOfLog
                jointResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog)) =
          jointResponseMapDecisiveEqualityEventScoreTargetSource.restorativeTraceLog) :=
  jointResponseMapDecisiveEqualityEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

/--
The joint toy event source routed from the identity transition map through the
response-map event-score surface.
-/
def jointTransitionResponseMapEventScoreSource :
    TwoChannelResponseMapEventScoreSource
      process JointState JointAction :=
  jointTransitionMapEventScoreSource.toResponseMapEventScoreSource

def jointTransitionResponseMapEventScoreTargetSource :
    TwoChannelTraceEventScoreSource process :=
  jointTransitionResponseMapEventScoreSource.toTargetTraceEventScoreSource

theorem jointTransitionResponseMapEventScore_target_traceLog_ne :
    process.traceLog
        (jointIdentityTransitionMap.toState jointChannelTraceLaw.adverseContext)
        [jointIdentityTransitionMap.toAction
          jointChannelTraceLaw.restorativeIntervention] ≠
      process.traceLog
        (jointIdentityTransitionMap.toState
          jointChannelTraceLaw.restorativeContext)
        [jointIdentityTransitionMap.toAction
          jointChannelTraceLaw.adverseIntervention] :=
  jointTransitionMapEventScoreSource.responseMap_target_traceLog_ne

theorem jointTransitionResponseMapEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTransitionResponseMapEventScoreTargetSource.totalScoreOfLog
              jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
            jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfTotal
            (jointTransitionResponseMapEventScoreTargetSource.totalScoreOfLog
              jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
            jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.responseMap_no_totalScoreOfLog_componentScore_decoder

theorem jointTransitionResponseMapEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTransitionResponseMapEventScoreTargetSource.totalScoreOfLog
              jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog) =
          jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTransitionResponseMapEventScoreTargetSource.totalScoreOfLog
              jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) =
          jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.responseMap_no_totalScoreOfLog_traceLog_decoder

theorem jointTransitionResponseMapEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
                jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
            jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
                jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
            jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.responseMap_no_totalComponentScalar_component_decoder

theorem jointTransitionResponseMapEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
                jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog)) =
          jointTransitionResponseMapEventScoreTargetSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTransitionResponseMapEventScoreTargetSource.componentScoreOfLog
                jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog)) =
          jointTransitionResponseMapEventScoreTargetSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.responseMap_no_totalComponentScalar_traceLog_decoder

/--
Same-state response-separated additive-composition source for the joint toy
process.

The initial state is `failed`: an adverse pulse keeps the process failed/red,
while a restorative pulse repairs it to ok/green.  This is deliberately a
same-state witness for the response-separated additive path, separate from the
two-context `jointChannelTraceLaw` used by the earlier event-score lane.
-/
def jointResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
      process where
  initialState := JointState.failed
  burdenAction := adversePulse
  supportAction := restorativePulse
  burdenUnit := 1
  supportUnit := 1
  burdenUnit_pos := by
    decide
  supportUnit_pos := by
    decide
  response_ne := by
    decide

/--
The same joint toy response-separated additive source, routed through a
role-free observational transition map.  The transition map is the identity in
this witness; the point is the interface: target-side no-go is obtained from a
transition-preserving alternative process rather than by supplying target logs
directly.
-/
def jointTransitionMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.TransitionMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  transitionMap := jointIdentityTransitionMap
  source := jointResponseSeparatedCompositionSource

def jointTransitionMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointTransitionMappedResponseSeparatedCompositionSource.targetObservedSource

theorem jointTransitionMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointTransitionMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointTransitionMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointTransitionMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointTransitionMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointTransitionMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointTransitionMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointTransitionMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointTransitionMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointTransitionMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same response-separated additive source routed through a relation-based
trace simulation.  The witness relation is induced by the identity transition
map, but the consumed interface is the weaker `ObservationalTraceSimulation`.
-/
def jointSimulationMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.SimulationMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  simulation :=
    ObservationalTraceSimulation.ofTransitionMap jointIdentityTransitionMap
  source := jointResponseSeparatedCompositionSource
  targetInitialState := JointState.failed
  initial_related := rfl

def jointSimulationMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointSimulationMappedResponseSeparatedCompositionSource.targetObservedSource

theorem jointSimulationMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointSimulationMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointSimulationMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointSimulationMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointSimulationMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointSimulationMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointSimulationMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointSimulationMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointSimulationMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointSimulationMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through the smaller decisive composition-trace
boundary.  This consumes only the response split and generated
composition-trace preservation exposed by the supplied simulation above.
-/
def jointCompositionTraceMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTraceMappedResponseSeparatedCompositionSource
      process JointState JointAction :=
  jointSimulationMappedResponseSeparatedCompositionSource
    |>.toCompositionTraceMappedResponseSeparatedCompositionSource

def jointCompositionTraceMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTraceMappedResponseSeparatedCompositionSource.targetObservedSource

theorem jointCompositionTraceMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointCompositionTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointCompositionTraceMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointCompositionTraceMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointCompositionTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointCompositionTraceMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointCompositionTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through generated composition-trace behavior.  The
one-step response equalities used by the previous boundary are recovered from
the generated traces rather than supplied separately.
-/
def jointGeneratedTraceMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.GeneratedTraceMappedResponseSeparatedCompositionSource
      process JointState JointAction :=
  jointSimulationMappedResponseSeparatedCompositionSource
    |>.toGeneratedTraceMappedResponseSeparatedCompositionSource

def jointGeneratedTraceMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource.targetObservedSource

theorem jointGeneratedTraceMappedResponseSeparated_preserves_burden_response :
    process.response JointState.failed adversePulse =
      process.response JointState.failed adversePulse :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.preserves_burden_response

theorem jointGeneratedTraceMappedResponseSeparated_preserves_support_response :
    process.response JointState.failed restorativePulse =
      process.response JointState.failed restorativePulse :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.preserves_support_response

theorem jointGeneratedTraceMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointGeneratedTraceMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointGeneratedTraceMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointGeneratedTraceMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointGeneratedTraceMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through the local two-action relation boundary.
The relation is equality in the toy process, but the consumed interface only
knows the burden/support composition actions, not every action of the process.
-/
def jointCompositionTraceRelationMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTraceRelationMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  toAction := id
  source := jointResponseSeparatedCompositionSource
  targetInitialState := JointState.failed
  related := fun sourceState targetState => targetState = sourceState
  initial_related := rfl
  preserves_observation := by
    intro sourceState targetState h
    rw [h]
  preserves_readout := by
    intro sourceState targetState h
    rw [h]
  burden_step_related := by
    intro sourceState targetState h
    rw [h]
    rfl
  support_step_related := by
    intro sourceState targetState h
    rw [h]
    rfl

def jointRelationGeneratedTraceMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem jointRelationGeneratedTraceMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointRelationGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointRelationGeneratedTraceMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointRelationGeneratedTraceMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointRelationGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointRelationGeneratedTraceMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointRelationGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTraceRelationMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through the local two-action map boundary.  The
map is identity in the toy process, but the consumed interface only requires
observable preservation and step commutation for the burden/support generated
actions.
-/
def jointCompositionTraceMapMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTraceMapMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  toState := id
  toAction := id
  source := jointResponseSeparatedCompositionSource
  preserves_observation := by
    intro sourceState
    rfl
  preserves_readout := by
    intro sourceState
    rfl
  burden_step_commutes := by
    intro sourceState
    rfl
  support_step_commutes := by
    intro sourceState
    rfl

def jointMapGeneratedTraceMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTraceMapMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem jointMapGeneratedTraceMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointMapGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTraceMapMappedResponseSeparatedCompositionSource
    |>.mapTrace_source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointMapGeneratedTraceMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointMapGeneratedTraceMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointMapGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTraceMapMappedResponseSeparatedCompositionSource
    |>.mapTrace_no_additiveScalar_target_traceLog_decoder

theorem jointMapGeneratedTraceMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointMapGeneratedTraceMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTraceMapMappedResponseSeparatedCompositionSource
    |>.mapTrace_exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through the two-action map boundary.  This witness
does not supply a global action adapter; it only names the target burden and
support actions and proves the two local step-commutation facts.
-/
def jointCompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  toState := id
  source := jointResponseSeparatedCompositionSource
  targetBurdenAction := adversePulse
  targetSupportAction := restorativePulse
  preserves_observation := by
    intro sourceState
    rfl
  preserves_readout := by
    intro sourceState
    rfl
  burden_step_commutes := by
    intro sourceState
    rfl
  support_step_commutes := by
    intro sourceState
    rfl

def jointTwoActionMapResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem jointTwoActionMapResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointTwoActionMapResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointTwoActionMapResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointTwoActionMapResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointTwoActionMapResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointTwoActionMapResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointTwoActionMapResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTraceTwoActionMapMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
Concrete generated-prefix state for the joint toy response-separated lane.
Only the last generated tag matters: burden leaves the state failed, support
leaves it ok, and the empty prefix starts failed.
-/
def jointGeneratedPrefixState (pref : List Bool) : JointState :=
  match pref with
  | [] => JointState.failed
  | true :: [] => JointState.failed
  | false :: [] => JointState.ok
  | _ :: second :: rest => jointGeneratedPrefixState (second :: rest)

theorem jointGeneratedPrefixState_burden_step
    (pref : List Bool) :
    jointGeneratedPrefixState (pref ++ [true]) =
      process.step (jointGeneratedPrefixState pref) adversePulse := by
  induction pref with
  | nil =>
      rfl
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases head <;> rfl
      | cons second rest =>
          cases head <;> exact ih

theorem jointGeneratedPrefixState_support_step
    (pref : List Bool) :
    jointGeneratedPrefixState (pref ++ [false]) =
      process.step (jointGeneratedPrefixState pref) restorativePulse := by
  induction pref with
  | nil =>
      rfl
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases head <;> rfl
      | cons second rest =>
          cases head <;> exact ih

/--
The same toy source routed through the generated-prefix tree boundary.  This
witness does not supply a global source-state map: source/target states are
supplied only for finite burden/support prefixes.
-/
def jointCompositionTracePrefixTreeMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  source := jointResponseSeparatedCompositionSource
  targetBurdenAction := adversePulse
  targetSupportAction := restorativePulse
  sourceStateOfPrefix := jointGeneratedPrefixState
  targetStateOfPrefix := jointGeneratedPrefixState
  source_initial := rfl
  preserves_observation := by
    intro pref
    rfl
  preserves_readout := by
    intro pref
    rfl
  source_burden_step_commutes := by
    intro pref
    exact jointGeneratedPrefixState_burden_step pref
  source_support_step_commutes := by
    intro pref
    exact jointGeneratedPrefixState_support_step pref
  burden_step_commutes := by
    intro pref
    exact jointGeneratedPrefixState_burden_step pref
  support_step_commutes := by
    intro pref
    exact jointGeneratedPrefixState_support_step pref

def jointPrefixTreeResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem jointPrefixTreeResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointPrefixTreeResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointPrefixTreeResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointPrefixTreeResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointPrefixTreeResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointPrefixTreeResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointPrefixTreeResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTracePrefixTreeMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same toy source routed through generated prefix states.  This witness no
longer supplies a custom prefix tree or local extension laws: source and target
prefix states are both generated by folding the two named actions from the
initial failed state.
-/
def jointCompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.CompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  source := jointResponseSeparatedCompositionSource
  targetInitialState := JointState.failed
  targetBurdenAction := adversePulse
  targetSupportAction := restorativePulse
  preserves_observation := by
    intro pref
    rfl
  preserves_readout := by
    intro pref
    rfl

def jointGeneratedPrefixResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointCompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    |>.targetObservedSource

theorem jointGeneratedPrefixResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointGeneratedPrefixResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointCompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointGeneratedPrefixResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointGeneratedPrefixResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointGeneratedPrefixResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointCompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointGeneratedPrefixResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointGeneratedPrefixResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointCompositionTraceGeneratedPrefixMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

/--
The same response-separated additive source routed through canonical
trace-behavior relatedness.  This removes the supplied simulation relation
from the consumed witness: relatedness is the observable current-view plus
all-finite-prefix-log relation generated by the identity action translation.
-/
def jointBehaviorMappedResponseSeparatedCompositionSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.BehaviorMappedResponseSeparatedCompositionSource
      process JointState JointAction where
  alternative := process
  toAction := id
  source := jointResponseSeparatedCompositionSource
  targetInitialState := JointState.failed
  initial_behavior := by
    constructor
    · rfl
    · intro actions
      exact jointIdentityTransitionMap.preserves_traceLog
        JointState.failed actions

def jointBehaviorMappedResponseSeparatedObservedSource :
    Persistence.StructuralPersistence.AdditiveScalarCompositionObservedTrace.ObservedAdditiveCompositionSource
      process :=
  jointBehaviorMappedResponseSeparatedCompositionSource.targetObservedSource

theorem jointBehaviorMappedResponseSeparated_source_traceLogOfCounts_eq_target
    (burdenCount supportCount : Nat) :
    jointResponseSeparatedCompositionSource.toObservedAdditiveCompositionSource.traceLogOfCounts
        burdenCount supportCount =
      jointBehaviorMappedResponseSeparatedObservedSource.traceLogOfCounts
        burdenCount supportCount :=
  jointBehaviorMappedResponseSeparatedCompositionSource
    |>.source_traceLogOfCounts_eq_target burdenCount supportCount

theorem jointBehaviorMappedResponseSeparated_no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              (jointBehaviorMappedResponseSeparatedObservedSource.scalarOfCounts
                burdenCount supportCount) =
            jointBehaviorMappedResponseSeparatedObservedSource.traceLogOfCounts
              burdenCount supportCount) :=
  jointBehaviorMappedResponseSeparatedCompositionSource
    |>.no_additiveScalar_target_traceLog_decoder

theorem jointBehaviorMappedResponseSeparated_exists_componentCoordinate_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
              burdenCount supportCount) =
          jointBehaviorMappedResponseSeparatedObservedSource.traceLogOfCounts
            burdenCount supportCount :=
  jointBehaviorMappedResponseSeparatedCompositionSource
    |>.exists_componentCoordinate_target_traceLog_readout

theorem jointPreservedTraceEventScore_burdenEvent_adverse_active :
    TwoChannelSplitPackage.hasCollapsedPrefix
        jointTraceEventScoreSource.adverseTraceLog = true := by
  rfl

theorem jointPreservedTraceEventScore_supportEvent_restorative_active :
    TwoChannelSplitPackage.finalLogReadoutViable
        jointTraceEventScoreSource.restorativeTraceLog = true := by
  rfl

theorem jointObservedLogPreservedTraceEventScore_burdenEvent_adverse_active :
    TwoChannelSplitPackage.hasCollapsedPrefix
        jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog =
      true :=
  jointObservedLogPreservedTraceEventScoreSource.burdenEvent_adverse_active

theorem jointObservedLogPreservedTraceEventScore_supportEvent_restorative_active :
    TwoChannelSplitPackage.finalLogReadoutViable
        jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog =
      true :=
  jointObservedLogPreservedTraceEventScoreSource.supportEvent_restorative_active

theorem jointTraceEventScore_adverse_componentScoreOfLog :
    jointTraceEventScoreSource.componentScoreOfLog
        jointTraceEventScoreSource.adverseTraceLog = (1, 0) :=
  jointTraceEventScoreSource.adverse_componentScoreOfLog

theorem jointTraceEventScore_restorative_componentScoreOfLog :
    jointTraceEventScoreSource.componentScoreOfLog
        jointTraceEventScoreSource.restorativeTraceLog = (0, 1) :=
  jointTraceEventScoreSource.restorative_componentScoreOfLog

theorem jointTraceEventScore_totalScoreOfLog_eq :
    jointTraceEventScoreSource.totalScoreOfLog
        jointTraceEventScoreSource.adverseTraceLog =
      jointTraceEventScoreSource.totalScoreOfLog
        jointTraceEventScoreSource.restorativeTraceLog :=
  jointTraceEventScoreSource.totalScoreOfLog_eq

theorem jointTraceEventScore_componentScoreOfLog_ne :
    jointTraceEventScoreSource.componentScoreOfLog
        jointTraceEventScoreSource.adverseTraceLog ≠
      jointTraceEventScoreSource.componentScoreOfLog
        jointTraceEventScoreSource.restorativeTraceLog :=
  jointTraceEventScoreSource.componentScoreOfLog_ne

theorem jointTraceEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTraceEventScoreSource.totalScoreOfLog
              jointTraceEventScoreSource.adverseTraceLog) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.adverseTraceLog ∧
        componentOfTotal
            (jointTraceEventScoreSource.totalScoreOfLog
              jointTraceEventScoreSource.restorativeTraceLog) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.restorativeTraceLog) :=
  jointTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointTraceEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTraceEventScoreSource.totalScoreOfLog
              jointTraceEventScoreSource.adverseTraceLog) =
          jointTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTraceEventScoreSource.totalScoreOfLog
              jointTraceEventScoreSource.restorativeTraceLog) =
          jointTraceEventScoreSource.restorativeTraceLog) :=
  jointTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointTraceEventScore_exists_componentTraceLog_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      readout
          (jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.adverseTraceLog) =
        jointTraceEventScoreSource.adverseTraceLog ∧
      readout
          (jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.restorativeTraceLog) =
        jointTraceEventScoreSource.restorativeTraceLog :=
  jointTraceEventScoreSource.exists_componentTraceLog_readout

theorem jointTraceEventScore_burdenOnlyScalar_distinguishes :
    jointTraceEventScoreSource.burdenOnlyScalarOfLog
        jointTraceEventScoreSource.adverseTraceLog ≠
      jointTraceEventScoreSource.burdenOnlyScalarOfLog
        jointTraceEventScoreSource.restorativeTraceLog :=
  jointTraceEventScoreSource.burdenOnlyScalarOfLog_distinguishes

theorem jointTraceEventScore_exists_burdenOnlyScalar_traceLog_readout :
    ∃ readout : Nat -> List (JointObservation × BoundaryStatus),
      readout
          (jointTraceEventScoreSource.burdenOnlyScalarOfLog
            jointTraceEventScoreSource.adverseTraceLog) =
        jointTraceEventScoreSource.adverseTraceLog ∧
      readout
          (jointTraceEventScoreSource.burdenOnlyScalarOfLog
            jointTraceEventScoreSource.restorativeTraceLog) =
        jointTraceEventScoreSource.restorativeTraceLog :=
  jointTraceEventScoreSource.exists_burdenOnlyScalar_traceLog_readout

theorem jointTraceEventScore_no_roleBlindScalar_component_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (blind.scalar
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog)) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (blind.scalar
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog)) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.restorativeTraceLog) :=
  jointTraceEventScoreSource.no_roleBlindScalar_component_decoder blind

theorem jointTraceEventScore_no_roleBlindScalar_traceLog_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (blind.scalar
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog)) =
          jointTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (blind.scalar
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog)) =
          jointTraceEventScoreSource.restorativeTraceLog) :=
  jointTraceEventScoreSource.no_roleBlindScalar_traceLog_decoder blind

/--
Three-point joint toy source.

The neutral point is an empty prefix log, while the other two points are the
decisive adverse/restorative logs from `jointTraceEventScoreSource`.
-/
def jointThreeTraceEventScoreSource :
    ThreeTraceEventScoreSource JointObservation where
  neutralLog := []
  burdenLog := jointTraceEventScoreSource.adverseTraceLog
  supportLog := jointTraceEventScoreSource.restorativeTraceLog
  burdenEvent := TwoChannelSplitPackage.hasCollapsedPrefix
  supportEvent := TwoChannelSplitPackage.finalLogReadoutViable
  neutral_burden_inactive := by
    rfl
  neutral_support_inactive := by
    rfl
  burden_burden_active := by
    rfl
  burden_support_inactive := by
    rfl
  support_burden_inactive := by
    rfl
  support_support_active := by
    rfl
  neutralLog_ne_burdenLog := by
    decide
  neutralLog_ne_supportLog := by
    decide
  burdenLog_ne_supportLog := by
    decide

theorem jointThreeTrace_no_burdenOnly_threePoint_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.neutralLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.neutralLog ∧
        componentOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.burdenLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.burdenLog ∧
        componentOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.supportLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_burdenOnly_threePoint_component_decoder

theorem jointThreeTrace_no_supportOnly_threePoint_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.neutralLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.neutralLog ∧
        componentOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.burdenLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.burdenLog ∧
        componentOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.supportLog) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_supportOnly_threePoint_component_decoder

theorem jointThreeTrace_no_roleBlind_threePoint_component_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.neutralLog)) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.neutralLog ∧
        componentOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.burdenLog)) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.burdenLog ∧
        componentOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.supportLog)) =
          jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_roleBlind_threePoint_component_decoder blind

theorem jointThreeTrace_no_burdenOnly_threePoint_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.neutralLog) =
          jointThreeTraceEventScoreSource.neutralLog ∧
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.burdenLog) =
          jointThreeTraceEventScoreSource.burdenLog ∧
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.burdenScoreOfLog
              jointThreeTraceEventScoreSource.supportLog) =
          jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_burdenOnly_threePoint_traceLog_decoder

theorem jointThreeTrace_no_supportOnly_threePoint_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.neutralLog) =
          jointThreeTraceEventScoreSource.neutralLog ∧
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.burdenLog) =
          jointThreeTraceEventScoreSource.burdenLog ∧
        traceLogOfScalar
            (jointThreeTraceEventScoreSource.supportScoreOfLog
              jointThreeTraceEventScoreSource.supportLog) =
          jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_supportOnly_threePoint_traceLog_decoder

theorem jointThreeTrace_no_roleBlind_threePoint_traceLog_decoder
    (blind : RoleBlindComponentScalar) :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.neutralLog)) =
          jointThreeTraceEventScoreSource.neutralLog ∧
        traceLogOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.burdenLog)) =
          jointThreeTraceEventScoreSource.burdenLog ∧
        traceLogOfScalar
            (blind.scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.supportLog)) =
          jointThreeTraceEventScoreSource.supportLog) :=
  jointThreeTraceEventScoreSource.no_roleBlind_threePoint_traceLog_decoder blind

theorem jointThreeTrace_exists_componentTraceLog_readout :
    ∃ readout : Nat × Nat -> List (JointObservation × BoundaryStatus),
      readout
          (jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.neutralLog) =
        jointThreeTraceEventScoreSource.neutralLog ∧
      readout
          (jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.burdenLog) =
        jointThreeTraceEventScoreSource.burdenLog ∧
      readout
          (jointThreeTraceEventScoreSource.componentScoreOfLog
            jointThreeTraceEventScoreSource.supportLog) =
        jointThreeTraceEventScoreSource.supportLog :=
  jointThreeTraceEventScoreSource.exists_componentTraceLog_readout

theorem jointThreeTrace_exists_codeScalar_traceLog_readout :
    ∃ scalar : Nat × Nat -> Nat,
      ∃ readout : Nat -> List (JointObservation × BoundaryStatus),
        readout
            (scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.neutralLog)) =
          jointThreeTraceEventScoreSource.neutralLog ∧
        readout
            (scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.burdenLog)) =
          jointThreeTraceEventScoreSource.burdenLog ∧
        readout
            (scalar
              (jointThreeTraceEventScoreSource.componentScoreOfLog
                jointThreeTraceEventScoreSource.supportLog)) =
          jointThreeTraceEventScoreSource.supportLog :=
  jointThreeTraceEventScoreSource.exists_codeScalar_threePoint_traceLog_readout

theorem jointTraceEventScore_totalComponentScalar_same_decisiveLogs :
    totalComponentScalarValue
        (jointTraceEventScoreSource.componentScoreOfLog
          jointTraceEventScoreSource.adverseTraceLog) =
      totalComponentScalarValue
        (jointTraceEventScoreSource.componentScoreOfLog
          jointTraceEventScoreSource.restorativeTraceLog) :=
  by
    change
      jointTraceEventScoreSource.totalScoreOfLog
          jointTraceEventScoreSource.adverseTraceLog =
        jointTraceEventScoreSource.totalScoreOfLog
          jointTraceEventScoreSource.restorativeTraceLog
    exact jointTraceEventScore_totalScoreOfLog_eq

theorem jointTraceEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog)) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog)) =
          jointTraceEventScoreSource.componentScoreOfLog
            jointTraceEventScoreSource.restorativeTraceLog) :=
  by
    change
      ¬ Exists
        (fun componentOfScalar : Nat -> Nat × Nat =>
          componentOfScalar
              (jointTraceEventScoreSource.totalScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog) =
            jointTraceEventScoreSource.componentScoreOfLog
              jointTraceEventScoreSource.adverseTraceLog ∧
          componentOfScalar
              (jointTraceEventScoreSource.totalScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog) =
            jointTraceEventScoreSource.componentScoreOfLog
              jointTraceEventScoreSource.restorativeTraceLog)
    exact jointTraceEventScore_no_totalScoreOfLog_componentScore_decoder

theorem jointTraceEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog)) =
          jointTraceEventScoreSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceEventScoreSource.componentScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog)) =
          jointTraceEventScoreSource.restorativeTraceLog) :=
  by
    change
      ¬ Exists
        (fun traceLogOfScalar :
          Nat -> List (JointObservation × BoundaryStatus) =>
          traceLogOfScalar
              (jointTraceEventScoreSource.totalScoreOfLog
                jointTraceEventScoreSource.adverseTraceLog) =
            jointTraceEventScoreSource.adverseTraceLog ∧
          traceLogOfScalar
              (jointTraceEventScoreSource.totalScoreOfLog
                jointTraceEventScoreSource.restorativeTraceLog) =
            jointTraceEventScoreSource.restorativeTraceLog)
    exact jointTraceEventScore_no_totalScoreOfLog_traceLog_decoder

theorem jointPreservedTraceEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog) =
          jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfTotal
            (jointPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) =
          jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointPreservedTraceEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointPreservedTraceEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog) =
          jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) =
          jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointPreservedTraceEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointPreservedTraceEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog)) =
          jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog)) =
          jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointPreservedTraceEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointPreservedTraceEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog)) =
          jointPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog)) =
            jointPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointPreservedTraceEventScoreSource.no_totalComponentScalar_traceLog_decoder

theorem jointObservedLogPreservedTraceEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointObservedLogPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfTotal
            (jointObservedLogPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointObservedLogPreservedTraceEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointObservedLogPreservedTraceEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointObservedLogPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointObservedLogPreservedTraceEventScoreTraceEventSource.totalScoreOfLog
              jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointObservedLogPreservedTraceEventScoreSource
    |>.no_totalScoreOfLog_traceLog_decoder

theorem jointObservedLogPreservedTraceEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog)) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog)) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
            jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointObservedLogPreservedTraceEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointObservedLogPreservedTraceEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog)) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointObservedLogPreservedTraceEventScoreTraceEventSource.componentScoreOfLog
                jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog)) =
          jointObservedLogPreservedTraceEventScoreTraceEventSource.restorativeTraceLog) :=
  jointObservedLogPreservedTraceEventScoreSource
    |>.no_totalComponentScalar_traceLog_decoder

theorem jointTraceLogModelEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTraceLogModelEventScoreTraceEventSource.totalScoreOfLog
              jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog) =
          jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
            jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfTotal
            (jointTraceLogModelEventScoreTraceEventSource.totalScoreOfLog
              jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) =
          jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
            jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTraceLogModelEventScoreSource.no_totalScoreOfLog_componentScore_decoder

theorem jointTraceLogModelEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTraceLogModelEventScoreTraceEventSource.totalScoreOfLog
              jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog) =
          jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTraceLogModelEventScoreTraceEventSource.totalScoreOfLog
              jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) =
          jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTraceLogModelEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointTraceLogModelEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
                jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog)) =
          jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
            jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
                jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog)) =
          jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
            jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTraceLogModelEventScoreSource.no_totalComponentScalar_component_decoder

theorem jointTraceLogModelEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
                jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog)) =
          jointTraceLogModelEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTraceLogModelEventScoreTraceEventSource.componentScoreOfLog
                jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog)) =
          jointTraceLogModelEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTraceLogModelEventScoreSource.no_totalComponentScalar_traceLog_decoder

theorem jointAlternativeTraceLogEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointAlternativeTraceLogEventScoreTraceEventSource.totalScoreOfLog
              jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog) =
          jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
            jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfTotal
            (jointAlternativeTraceLogEventScoreTraceEventSource.totalScoreOfLog
              jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) =
          jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
            jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) :=
  jointAlternativeTraceLogEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointAlternativeTraceLogEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointAlternativeTraceLogEventScoreTraceEventSource.totalScoreOfLog
              jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog) =
          jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointAlternativeTraceLogEventScoreTraceEventSource.totalScoreOfLog
              jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) =
          jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) :=
  jointAlternativeTraceLogEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointAlternativeTraceLogEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
                jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog)) =
          jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
            jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
                jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog)) =
          jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
            jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) :=
  jointAlternativeTraceLogEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointAlternativeTraceLogEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
                jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog)) =
          jointAlternativeTraceLogEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointAlternativeTraceLogEventScoreTraceEventSource.componentScoreOfLog
                jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog)) =
          jointAlternativeTraceLogEventScoreTraceEventSource.restorativeTraceLog) :=
  jointAlternativeTraceLogEventScoreSource.no_totalComponentScalar_traceLog_decoder

theorem jointTransitionMapEventScore_no_totalScoreOfLog_componentScore_decoder :
    ¬ Exists
      (fun componentOfTotal : Nat -> Nat × Nat =>
        componentOfTotal
            (jointTransitionMapEventScoreTraceEventSource.totalScoreOfLog
              jointTransitionMapEventScoreTraceEventSource.adverseTraceLog) =
          jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
            jointTransitionMapEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfTotal
            (jointTransitionMapEventScoreTraceEventSource.totalScoreOfLog
              jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) =
          jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
            jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.no_totalScoreOfLog_componentScore_decoder

theorem jointTransitionMapEventScore_no_totalScoreOfLog_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfTotal
            (jointTransitionMapEventScoreTraceEventSource.totalScoreOfLog
              jointTransitionMapEventScoreTraceEventSource.adverseTraceLog) =
          jointTransitionMapEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfTotal
            (jointTransitionMapEventScoreTraceEventSource.totalScoreOfLog
              jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) =
          jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource.no_totalScoreOfLog_traceLog_decoder

theorem jointTransitionMapEventScore_no_totalComponentScalar_component_decoder :
    ¬ Exists
      (fun componentOfScalar : Nat -> Nat × Nat =>
        componentOfScalar
            (totalComponentScalarValue
              (jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
                jointTransitionMapEventScoreTraceEventSource.adverseTraceLog)) =
          jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
            jointTransitionMapEventScoreTraceEventSource.adverseTraceLog ∧
        componentOfScalar
            (totalComponentScalarValue
              (jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
                jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog)) =
          jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
            jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource
    |>.no_totalComponentScalar_component_decoder

theorem jointTransitionMapEventScore_no_totalComponentScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar :
        Nat -> List (JointObservation × BoundaryStatus) =>
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
                jointTransitionMapEventScoreTraceEventSource.adverseTraceLog)) =
          jointTransitionMapEventScoreTraceEventSource.adverseTraceLog ∧
        traceLogOfScalar
            (totalComponentScalarValue
              (jointTransitionMapEventScoreTraceEventSource.componentScoreOfLog
                jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog)) =
          jointTransitionMapEventScoreTraceEventSource.restorativeTraceLog) :=
  jointTransitionMapEventScoreSource.no_totalComponentScalar_traceLog_decoder

/--
The joint toy law has equal total score trace but distinct component traces.

This is the concrete witness for the composite-score red test: total scalar
readout alone forgets the direction of the channel.
-/
def jointCompositeScoreLaw :
    TwoChannelCompositeScoreLaw process where
  law := jointChannelTraceLaw
  burdenScore := jointCompositeBurdenScore
  supportScore := jointCompositeSupportScore
  same_totalTrace := by
    rfl
  componentTrace_ne := by
    decide

theorem jointCompositeScore_same_totalTrace :
    jointCompositeScoreLaw.restorativeTotalTrace =
      jointCompositeScoreLaw.adverseTotalTrace :=
  jointCompositeScoreLaw.restorativeTotalTrace_eq_adverseTotalTrace

theorem jointCompositeScore_componentTrace_ne :
    jointCompositeScoreLaw.restorativeComponentTrace ≠
      jointCompositeScoreLaw.adverseComponentTrace :=
  jointCompositeScoreLaw.restorativeComponentTrace_ne_adverseComponentTrace

theorem jointCompositeScore_no_totalTrace_componentTrace_decoder :
    ¬ Exists
      (fun componentOfTotal : List Nat -> List (Nat × Nat) =>
        componentOfTotal jointCompositeScoreLaw.restorativeTotalTrace =
            jointCompositeScoreLaw.restorativeComponentTrace ∧
          componentOfTotal jointCompositeScoreLaw.adverseTotalTrace =
            jointCompositeScoreLaw.adverseComponentTrace) :=
  jointCompositeScoreLaw.no_totalTrace_componentTrace_decoder

theorem jointCompositeScore_no_totalTrace_prefixLog_model :
    ¬ Exists
      (fun traceLogOfTotal :
        Nat -> List Nat -> List (JointObservation × BoundaryStatus) =>
          forall s actions,
            process.traceLog s actions =
              traceLogOfTotal
                (contextAggregate s)
                (actions.map jointCompositeScoreLaw.totalCoordinate)) :=
  jointCompositeScoreLaw.no_totalTrace_prefixLog_model
    contextAggregate contextAggregate_identifies_jointContexts

theorem jointCompositeScore_exists_componentTrace_decisive_readout :
    ∃ readout : List (Nat × Nat) ->
        List (JointObservation × BoundaryStatus),
      readout jointCompositeScoreLaw.restorativeComponentTrace =
          process.traceLog
            jointChannelTraceLaw.adverseContext
            jointChannelTraceLaw.restorativeTrace ∧
        readout jointCompositeScoreLaw.adverseComponentTrace =
          process.traceLog
            jointChannelTraceLaw.restorativeContext
            jointChannelTraceLaw.adverseTrace :=
  jointCompositeScoreLaw.exists_componentTrace_decisive_readout

end ToyJointProcess

end Persistence.StructuralPersistence
