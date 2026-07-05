import Persistence.Examples.SmallWitness
import Persistence.StructuralPersistenceG1CompositeScoreForcingCore

/-!
# Projection Incompleteness Examples

This file factors two existing anti-collapse phenomena through one elementary
projection lemma.

The point is not to claim a new data-processing theorem.  It is to make the
load-bearing interface obligation explicit: when a persistence/collapse claim
uses only a projected readout, any distinction collapsed by that projection is
unavailable to readout-only decoders.

In particular, the hidden semantic witness from `SmallWitness` has two states
with the same boundary readout and current view but different maintained-target
realization.  Therefore maintained-target realization cannot be recovered from
boundary-readout-only or current-view-only predicates on that witness.
-/

namespace Persistence.StructuralPersistence
namespace Examples.ProjectionIncompleteness

universe u v w

/--
Projection-only predicate incompleteness.

Here `decode : Obs -> Prop` is not an accidental restriction: it is the formal
meaning of a predicate that factors through the projected observation `pi`.
If `pi` identifies two states while `P` separates them, no such projection-only
predicate can recover `P`.
-/
theorem no_projection_only_predicate_decoder
    {State : Type u} {Obs : Type v}
    (pi : State -> Obs) (P : State -> Prop)
    (collision : ∃ left right,
      pi left = pi right ∧ P left ∧ ¬ P right) :
    ¬ ∃ decode : Obs -> Prop, ∀ state, decode (pi state) ↔ P state := by
  rintro ⟨decode, hdecode⟩
  rcases collision with ⟨left, right, sameProjected, leftP, rightNotP⟩
  have leftDecoded : decode (pi left) := (hdecode left).2 leftP
  have rightNotDecoded : ¬ decode (pi right) := by
    intro decoded
    exact rightNotP ((hdecode right).1 decoded)
  exact rightNotDecoded (by simpa [sameProjected] using leftDecoded)

/--
Projection-only value incompleteness.

This value-valued companion is the same anti-collapse pattern for decoders
whose target is data rather than a proposition.
-/
theorem no_projection_only_value_decoder
    {State : Type u} {Obs : Type v} {Value : Type w}
    (pi : State -> Obs) (value : State -> Value)
    (collision : ∃ left right,
      pi left = pi right ∧ value left ≠ value right) :
    ¬ ∃ decode : Obs -> Value, ∀ state, decode (pi state) = value state := by
  rintro ⟨decode, hdecode⟩
  rcases collision with ⟨left, right, sameProjected, valueDifferent⟩
  exact valueDifferent (by
    calc
      value left = decode (pi left) := (hdecode left).symm
      _ = decode (pi right) := by rw [sameProjected]
      _ = value right := hdecode right)

/--
The enriched projection keeps both the reduced observation and the value that
the reduced observation may have collapsed.
-/
def enrichedProjection
    {State : Type u} {Obs : Type v} {Value : Type w}
    (pi : State -> Obs) (value : State -> Value) :
    State -> Obs × Value :=
  fun state => (pi state, value state)

/--
Reduced-versus-enriched projection separation.

This is the safe interface claim: it does not say another theory cannot encode
the value.  It says that once a claim surface has reduced states through `pi`,
any value distinction collapsed by `pi` is unavailable from the reduced
interface alone, while the enriched interface `(pi, value)` still separates it.
-/
theorem reduced_loses_while_enriched_separates
    {State : Type u} {Obs : Type v} {Value : Type w}
    (pi : State -> Obs) (value : State -> Value)
    (collision : ∃ left right,
      pi left = pi right ∧ value left ≠ value right) :
    (∃ left right,
      pi left = pi right ∧
        enrichedProjection pi value left ≠
          enrichedProjection pi value right) ∧
      ¬ ∃ decode : Obs -> Value,
        ∀ state, decode (pi state) = value state := by
  constructor
  · rcases collision with ⟨left, right, sameProjected, valueDifferent⟩
    exact
      ⟨left, right, sameProjected, by
        intro enrichedSame
        exact valueDifferent (Prod.mk.inj enrichedSame).2⟩
  · exact no_projection_only_value_decoder pi value collision

namespace HiddenSemanticWitness

open Persistence.StructuralPersistence.Examples.SmallWitness.HiddenSemanticWitness

/--
Boolean maintained-target realization flag for the finite hidden witness.

This is only the finite-witness value form of the `maintains` predicate; the
next theorem records the equivalence explicitly.
-/
def maintainedFlag : HiddenState -> Bool
  | .ready => true
  | .hiddenMaintained => true
  | .hiddenLost => false
  | .failed => false

/-- The Boolean flag agrees with the semantic `maintains` predicate. -/
theorem maintainedFlag_eq_true_iff_maintains (state : HiddenState) :
    maintainedFlag state = true ↔
      calculation.maintains state calculation.maintainedTarget := by
  cases state <;> simp [maintainedFlag, calculation, maintains]

/--
Boundary-readout-only predicates cannot recover maintained-target realization
on the hidden semantic witness.

The decoder type `BoundaryStatus -> Prop` is exactly the formal definition of
"using only the boundary readout".
-/
theorem no_boundaryReadout_only_maintains_decoder :
    ¬ ∃ decode : BoundaryStatus -> Prop,
      ∀ state : HiddenState,
        decode (calculation.boundaryReadout state) ↔
          calculation.maintains state calculation.maintainedTarget := by
  exact
    no_projection_only_predicate_decoder
      (pi := fun state : HiddenState => calculation.boundaryReadout state)
      (P := fun state : HiddenState =>
        calculation.maintains state calculation.maintainedTarget)
      (by
        rcases same_readout_different_maintains with
          ⟨left, right, _differentStates, sameReadout,
            leftMaintains, rightNotMaintains⟩
        exact ⟨left, right, sameReadout, leftMaintains, rightNotMaintains⟩)

/--
Current-view-only predicates also cannot recover maintained-target realization
on the hidden semantic witness.

The current view includes both observation and boundary readout, but it still
forgets the semantic distinction between the two hidden states.
-/
theorem no_currentView_only_maintains_decoder :
    ¬ ∃ decode : HiddenObservation × BoundaryStatus -> Prop,
      ∀ state : HiddenState,
        decode (process.currentView state) ↔
          calculation.maintains state calculation.maintainedTarget := by
  exact
    no_projection_only_predicate_decoder
      (pi := fun state : HiddenState => process.currentView state)
      (P := fun state : HiddenState =>
        calculation.maintains state calculation.maintainedTarget)
      (by
        rcases same_currentView_different_maintains with
          ⟨left, right, _differentStates, sameCurrentView,
            leftMaintains, rightNotMaintains⟩
        exact
          ⟨left, right, sameCurrentView, leftMaintains, rightNotMaintains⟩)

/--
Combined readout-only incompleteness summary for the hidden semantic witness.
-/
theorem hidden_readout_only_incompleteness_summary :
    (¬ ∃ decode : BoundaryStatus -> Prop,
      ∀ state : HiddenState,
        decode (calculation.boundaryReadout state) ↔
          calculation.maintains state calculation.maintainedTarget) ∧
    (¬ ∃ decode : HiddenObservation × BoundaryStatus -> Prop,
      ∀ state : HiddenState,
        decode (process.currentView state) ↔
          calculation.maintains state calculation.maintainedTarget) :=
  ⟨no_boundaryReadout_only_maintains_decoder,
    no_currentView_only_maintains_decoder⟩

/--
Dropping the maintained-target realization flag from the boundary readout loses
information that the enriched interface preserves.

The reduced interface is `boundaryReadout`; the enriched interface is
`(boundaryReadout, maintainedFlag)`.
-/
theorem boundaryReadout_reduced_loses_enriched_maintainedFlag :
    (∃ left right : HiddenState,
      calculation.boundaryReadout left =
        calculation.boundaryReadout right ∧
      enrichedProjection
          (fun state : HiddenState => calculation.boundaryReadout state)
          maintainedFlag left ≠
        enrichedProjection
          (fun state : HiddenState => calculation.boundaryReadout state)
          maintainedFlag right) ∧
    ¬ ∃ decode : BoundaryStatus -> Bool,
      ∀ state : HiddenState,
        decode (calculation.boundaryReadout state) =
          maintainedFlag state := by
  exact
    reduced_loses_while_enriched_separates
      (pi := fun state : HiddenState => calculation.boundaryReadout state)
      (value := maintainedFlag)
      (by
        exact
          ⟨HiddenState.hiddenMaintained, HiddenState.hiddenLost,
            by simp [calculation, process, readout],
            by simp [maintainedFlag]⟩)

/--
Dropping the maintained-target realization flag from the full current view also
loses information that the enriched interface preserves.

The reduced interface is `currentView`; the enriched interface is
`(currentView, maintainedFlag)`.
-/
theorem currentView_reduced_loses_enriched_maintainedFlag :
    (∃ left right : HiddenState,
      process.currentView left = process.currentView right ∧
      enrichedProjection
          (fun state : HiddenState => process.currentView state)
          maintainedFlag left ≠
        enrichedProjection
          (fun state : HiddenState => process.currentView state)
          maintainedFlag right) ∧
    ¬ ∃ decode : HiddenObservation × BoundaryStatus -> Bool,
      ∀ state : HiddenState,
        decode (process.currentView state) = maintainedFlag state := by
  exact
    reduced_loses_while_enriched_separates
      (pi := fun state : HiddenState => process.currentView state)
      (value := maintainedFlag)
      (by
        exact
          ⟨HiddenState.hiddenMaintained, HiddenState.hiddenLost,
            by
              simp [process, observe, readout,
                ObservationalPersistenceProcess.currentView],
            by simp [maintainedFlag]⟩)

/--
Combined reduced/enriched interface summary for the hidden witness.

The hidden witness does not show that other frameworks cannot encode the
distinction.  It shows that a claim surface which drops maintained-target
realization from its interface cannot recover that distinction from the
reduced readout alone, while the enriched interface keeps it.
-/
theorem reduced_enriched_interface_summary :
    (∀ state : HiddenState,
      maintainedFlag state = true ↔
        calculation.maintains state calculation.maintainedTarget) ∧
    ((∃ left right : HiddenState,
      calculation.boundaryReadout left =
        calculation.boundaryReadout right ∧
      enrichedProjection
          (fun state : HiddenState => calculation.boundaryReadout state)
          maintainedFlag left ≠
        enrichedProjection
          (fun state : HiddenState => calculation.boundaryReadout state)
          maintainedFlag right) ∧
      ¬ ∃ decode : BoundaryStatus -> Bool,
        ∀ state : HiddenState,
          decode (calculation.boundaryReadout state) =
            maintainedFlag state) ∧
    ((∃ left right : HiddenState,
      process.currentView left = process.currentView right ∧
      enrichedProjection
          (fun state : HiddenState => process.currentView state)
          maintainedFlag left ≠
        enrichedProjection
          (fun state : HiddenState => process.currentView state)
          maintainedFlag right) ∧
      ¬ ∃ decode : HiddenObservation × BoundaryStatus -> Bool,
        ∀ state : HiddenState,
          decode (process.currentView state) = maintainedFlag state) := by
  exact
    ⟨maintainedFlag_eq_true_iff_maintains,
      boundaryReadout_reduced_loses_enriched_maintainedFlag,
      currentView_reduced_loses_enriched_maintainedFlag⟩

end HiddenSemanticWitness

namespace CompositeScoreProjection

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {P : ObservationalPersistenceProcess State Action Observation}

/--
The existing total-trace/component-trace no-go is another instance of the same
projection incompleteness pattern.

The projected value is the total scalar trace of a decisive run; the lost value
is its burden/support component trace.  Equal total traces with unequal
component traces block any total-trace-only decoder.
-/
theorem no_totalTrace_componentTrace_decoder_via_projection
    (C : TwoChannelCompositeScoreLaw P) :
    ¬ ∃ componentOfTotal : List Nat -> List (Nat × Nat),
      ∀ decisiveRun : Bool,
        componentOfTotal
            (if decisiveRun then
              C.restorativeTotalTrace
            else
              C.adverseTotalTrace) =
          (if decisiveRun then
            C.restorativeComponentTrace
          else
            C.adverseComponentTrace) := by
  exact
    no_projection_only_value_decoder
      (pi := fun decisiveRun : Bool =>
        if decisiveRun then C.restorativeTotalTrace else C.adverseTotalTrace)
      (value := fun decisiveRun : Bool =>
        if decisiveRun then
          C.restorativeComponentTrace
        else
          C.adverseComponentTrace)
      (by
        refine ⟨true, false, ?_, ?_⟩
        · simpa using C.restorativeTotalTrace_eq_adverseTotalTrace
        · simpa using C.restorativeComponentTrace_ne_adverseComponentTrace)

/--
The usual two-conjunct decoder shape follows from the projection lemma.

This restates the earlier scalar-collapse red test through the same abstract
projection theorem used for readout-only maintained-target incompleteness.
-/
theorem no_totalTrace_componentTrace_decoder_pair_shape_via_projection
    (C : TwoChannelCompositeScoreLaw P) :
    ¬ Exists
      (fun componentOfTotal : List Nat -> List (Nat × Nat) =>
        componentOfTotal C.restorativeTotalTrace =
            C.restorativeComponentTrace ∧
          componentOfTotal C.adverseTotalTrace =
            C.adverseComponentTrace) := by
  intro candidate
  rcases candidate with ⟨componentOfTotal, restEq, advEq⟩
  exact
    (no_totalTrace_componentTrace_decoder_via_projection C)
      ⟨componentOfTotal, by
        intro decisiveRun
        cases decisiveRun <;> simp [restEq, advEq]⟩

end CompositeScoreProjection

end Examples.ProjectionIncompleteness
end Persistence.StructuralPersistence
