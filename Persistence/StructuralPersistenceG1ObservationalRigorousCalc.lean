import Persistence.StructuralPersistenceG1InducedBoundaryCore
import Persistence.StructuralPersistenceG1ObservationalCore

/-!
# G1 Observationally Rigorous Calculations

This module starts the strong G1 inevitability skeleton with an observation-only
antecedent.  The input calculation records target identity and observable
dynamics/readouts.  It does not store `K`, `V_K`, `L/B`, `M`, adapters,
certificates, or supplied representation maps as fields.

The first predicates are intentionally small red-test gates: constant or
empty-action calculations can instantiate the observation-only structure, but
they do not satisfy response separation or non-collapse.
-/

namespace Persistence.StructuralPersistence

universe u v w q

/--
Observation-only persistence/collapse calculation for the strong G1 target.

The process supplies observable dynamics and readouts; the target fields say
which target is being maintained and how a viable readout licenses maintenance.
No realization carrier, viable-region object, burden/support coordinate, or
certificate is a field of this antecedent.
-/
structure ObservationallyRigorousCalc
    (State : Type u) (Action : Type v) (Observation : Type w)
    (Target : Type q) where
  process : ObservationalPersistenceProcess State Action Observation
  maintainedTarget : Target
  maintains : State -> Target -> Prop
  viable_implies_maintained :
    forall s, process.readout s = BoundaryStatus.viable ->
      maintains s maintainedTarget

namespace ObservationallyRigorousCalc

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {Target : Type q}
variable (A : ObservationallyRigorousCalc State Action Observation Target)

/-- One-step observable response, inherited from the underlying process. -/
def response (s : State) (a : Action) : Observation × BoundaryStatus :=
  A.process.response s a

/-- Finite prefix trace log, inherited from the underlying process. -/
def traceLog (s : State) (actions : List Action) :
    List (Observation × BoundaryStatus) :=
  A.process.traceLog s actions

/--
Observation-only response separation.

This predicate names the minimal fact that two actions can have different
observable one-step effects at the same state.  The names `adverseAction` and
`recoveryAction` are only witnesses of observational difference; they are not
stored burden/support roles.
-/
def ResponseSeparated : Prop :=
  exists (s : State) (adverseAction recoveryAction : Action),
    A.response s adverseAction ≠ A.response s recoveryAction

/--
Observation-only non-collapse against a constant response summary.

This says the calculation cannot be represented by one global constant
observable response.
-/
def NonCollapse : Prop :=
  ¬ exists r : Observation × BoundaryStatus,
      forall (s : State) (a : Action), A.response s a = r

/-- Current-view extensionality is the existing observation-only wall. -/
def CurrentViewExtensional : Prop :=
  CurrentViewOneStepExtensional A.process

/-- Forget to the existing observational target-semantics scaffold. -/
def toTargetSemantics : ObservationalTargetSemantics A.process Target where
  maintainedTarget := A.maintainedTarget
  maintains := A.maintains
  viable_implies_maintained := A.viable_implies_maintained

/-- The center `F/K/V_K` scaffold recovered from the observation-only input. -/
def coreInterface : CorePersistenceInterface State Target where
  maintainedTarget := A.maintainedTarget
  K := State
  carrier := id
  realizes := A.maintains
  viableRegion := {s | A.process.readout s = BoundaryStatus.viable}
  viable_realizes := A.viable_implies_maintained

/--
The viable-state predicate induced by the recovered core interface agrees with
the observable viable readout.
-/
theorem core_inducedViableState_iff
    (s : State) :
    s ∈ A.coreInterface.inducedViableState ↔
      A.process.readout s = BoundaryStatus.viable := by
  constructor
  · intro h
    rcases h with ⟨k, hk, hviable⟩
    simpa [coreInterface] using hk.symm ▸ hviable
  · intro h
    exact ⟨s, rfl, h⟩

/--
The induced boundary readout of the recovered core interface is viable exactly
on the original observable viable readout.
-/
theorem core_inducedBoundaryReadout_viable_iff
    [DecidablePred (fun s : State =>
      s ∈ A.coreInterface.inducedViableState)]
    (s : State) :
    A.coreInterface.inducedBoundaryReadout s = BoundaryStatus.viable ↔
      A.process.readout s = BoundaryStatus.viable := by
  rw [CorePersistenceInterface.inducedBoundaryReadout_viable_iff]
  exact A.core_inducedViableState_iff s

/-- Response separation rules out constant response collapse. -/
theorem nonCollapse_of_responseSeparated
    (h : A.ResponseSeparated) :
    A.NonCollapse := by
  intro hconstant
  rcases h with ⟨s, adverseAction, recoveryAction, hne⟩
  rcases hconstant with ⟨r, hr⟩
  exact hne ((hr s adverseAction).trans (hr s recoveryAction).symm)

end ObservationallyRigorousCalc

/-! ## Red-test witnesses -/

/-- Constant observation/readout process. -/
def constantObservationProcess
    (State : Type u) (Action : Type v) (Observation : Type w)
    (obs : Observation) (status : BoundaryStatus) :
    ObservationalPersistenceProcess State Action Observation where
  observe := fun _ => obs
  step := fun s _ => s
  readout := fun _ => status

/-- Constant observation-only calculation. -/
def constantObservationallyRigorousCalc
    (State : Type u) (Action : Type v) (Observation : Type w)
    (Target : Type q)
    (obs : Observation) (status : BoundaryStatus) (target : Target) :
    ObservationallyRigorousCalc State Action Observation Target where
  process := constantObservationProcess State Action Observation obs status
  maintainedTarget := target
  maintains := fun _ _ => True
  viable_implies_maintained := by
    intro _s _h
    trivial

/--
A constant calculation can instantiate the antecedent structure but is not
response-separated.
-/
theorem constantCalc_not_responseSeparated
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type q}
    (obs : Observation) (status : BoundaryStatus) (target : Target) :
    ¬ (constantObservationallyRigorousCalc
        State Action Observation Target obs status target).ResponseSeparated := by
  intro h
  rcases h with ⟨s, adverseAction, recoveryAction, hne⟩
  exact hne rfl

/-- A constant calculation also fails the non-collapse predicate. -/
theorem constantCalc_not_nonCollapse
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type q}
    (obs : Observation) (status : BoundaryStatus) (target : Target) :
    ¬ (constantObservationallyRigorousCalc
        State Action Observation Target obs status target).NonCollapse := by
  intro h
  apply h
  exact ⟨(obs, status), by
    intro _s _a
    rfl⟩

/-- Empty-action calculations cannot be response-separated. -/
theorem emptyAction_not_responseSeparated
    {State : Type u} {Observation : Type w} {Target : Type q}
    (A : ObservationallyRigorousCalc State Empty Observation Target) :
    ¬ A.ResponseSeparated := by
  intro h
  rcases h with ⟨_s, adverseAction, _recoveryAction, _hne⟩
  cases adverseAction

end Persistence.StructuralPersistence
