import Persistence.StructuralPersistenceG1ObservationalRigorousCalc
import Persistence.StructuralPersistenceG1ScopedMLSeparation

/-!
# G1 Rigorous Calculation to Scoped M/L Separation

This module connects the observation-only `ObservationallyRigorousCalc`
antecedent to the existing scoped additive M/L-separation entrance.

It does not add a new bridge/source structure.  From the observation-only
`ResponseSeparated` predicate it directly constructs the already existing
response-separated source as an existential conclusion, then reuses the
existing scoped M/L separation theorem.
-/

namespace Persistence.StructuralPersistence

universe u v w q

namespace ObservationallyRigorousCalc

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {Target : Type q}
variable (A : ObservationallyRigorousCalc State Action Observation Target)

/--
Observation-only response separation enters the existing scoped additive
M/L-separation theorem.

This is still a scoped entrance theorem, not full `L/B` and `M` recovery.  It
shows that the observation-only antecedent can feed the already proved
fixed-unit additive scalar no-go without supplying role fields as input.
-/
theorem responseSeparated_forces_scopedAdditiveMLSeparation
    (h : A.ResponseSeparated) :
    ∃ source :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        A.process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion source :=
by
  rcases h with ⟨s, adverseAction, recoveryAction, hne⟩
  let source :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        A.process :=
    { initialState := s
      burdenAction := adverseAction
      supportAction := recoveryAction
      burdenUnit := 1
      supportUnit := 1
      burdenUnit_pos := by decide
      supportUnit_pos := by decide
      response_ne := hne }
  exact
    ⟨source,
      ScopedMLSeparation.responseSeparated_forces_scopedAdditiveMLSeparation
        source⟩

/--
The current G1 inevitability skeleton from an observation-only response
separation.

This theorem bundles three already-checked consequences without adding any new
input role fields:

* the state-carrier `F/K/V_K` scaffold is given by `A.coreInterface`;
* the boundary predicate induced by that core agrees with the observed viable
  readout;
* the same response separation enters the scoped additive M/L-separation
  entrance and rules out constant response collapse.

This is still not the full no-alternative theorem: it does not quantify over
arbitrary alternatives and does not prove full native `L/B` or `M` recovery.
-/
theorem responseSeparated_forces_current_inevitability_skeleton
    (h : A.ResponseSeparated) :
    (forall s,
      s ∈ A.coreInterface.inducedViableState ↔
        A.process.readout s = BoundaryStatus.viable) ∧
    A.NonCollapse ∧
    ∃ source :
      AdditiveScalarCompositionObservedTrace.ResponseSeparatedCompositionSource
        A.process,
      ScopedMLSeparation.ScopedAdditiveMLSeparationConclusion source := by
  exact
    ⟨fun s => A.core_inducedViableState_iff s,
      A.nonCollapse_of_responseSeparated h,
      A.responseSeparated_forces_scopedAdditiveMLSeparation h⟩

end ObservationallyRigorousCalc

end Persistence.StructuralPersistence
