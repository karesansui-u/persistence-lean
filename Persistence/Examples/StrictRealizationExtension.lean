import Persistence.Examples.SmallWitness

/-!
# Strict Realization Extension

This module records the first theorem in this development whose deductive weight
comes from the persistence interface condition itself, rather than from a
general projection lemma.

The interface condition `viable_implies_maintained` of
`AlternativePersistenceCalculation` states that the viable region is contained
in the realization region:

```text
viable region  ⊆  { states realizing the maintained target }.
```

The theorem below says: if that containment is *strict* -- there is a state
that realizes the maintained target yet is not viable -- then the viable
region is a proper subregion of the realization region.  Concretely, the
realization region minus the viable region is inhabited.

This is not a general projection no-go.  It does not hold for an arbitrary
`pi`/`value` pair: the argument uses the ordered relationship between the
`boundaryReadout` and `maintains` fields that the calculation structure fixes
(`viable ⊆ maintains`).  Stripping the persistence framing leaves nothing to
state — an arbitrary predicate pair has no viable/realization containment to be
strict about.

This is a kernel-level interface theorem, not a new mathematical result and
not a real-domain measurement claim.  Its point is only that the
viable-inside-maintains ordering does deductive work: the interface
distinction between "viable" and "realizing the maintained target" is
load-bearing, not decorative.

The final local hypothesis in this file, `CollapsedExcludesMaintainsHypothesis`,
is deliberately not added to the core calculation structure.  It is tested here
as an example-side condition: if collapsed readouts exclude maintained-target
realization, then a maintained-outside-viable state is forced into the stopped
readout rather than the collapsed readout.
-/

namespace Persistence.StructuralPersistence
namespace Examples.StrictRealizationExtension

open AlternativePersistenceCalculation

universe u v

variable {State : Type u} {Target : Type v}

/--
A state that realizes the maintained target but is not viable: it sits in the
realization region and outside the viable region.

This is the "stopped but still realizing" witness shape at the level of the
abstract calculation, phrased without naming any particular non-viable readout
value.
-/
def MaintainedOutsideViable
    (A : AlternativePersistenceCalculation State Target) (s : State) : Prop :=
  A.maintains s A.maintainedTarget ∧
    A.boundaryReadout s ≠ BoundaryStatus.viable

/-- The realization region on the raw state space. -/
def realizationRegion
    (A : AlternativePersistenceCalculation State Target) : Set State :=
  {s | A.maintains s A.maintainedTarget}

/--
The viable region is contained in the realization region.

This is the structural half supplied by `AlternativePersistenceCalculation`,
via `viable_implies_maintained`.
-/
theorem stateViableRegion_subset_realizationRegion
    (A : AlternativePersistenceCalculation State Target) :
    A.stateViableRegion ⊆ realizationRegion A := by
  intro s hViable
  exact A.stateViableRegion_sound s hViable

/--
Strict extension hypothesis: the realization region strictly extends the viable
region.

The `subset` direction is free from the structure (`viable_implies_maintained`),
so the only content this predicate adds is the strict witness: some realizing
state is not viable.  It is stated as a structure to keep the two halves of
"strict containment" explicit at the call site.
-/
structure StrictExtensionHypothesis
    (A : AlternativePersistenceCalculation State Target) : Prop where
  strict_witness :
    ∃ s, A.maintains s A.maintainedTarget ∧
      A.boundaryReadout s ≠ BoundaryStatus.viable

/--
The viable region is strictly contained in the realization region when the
strict-extension witness is available.

This is the interface theorem where the persistence-specific ordering is used:
`stateViableRegion_subset_realizationRegion` supplies the structural
containment `viable ⊆ maintains`, and the strict witness supplies a realizing
state outside the viable region.  No projection, decoder, or auxiliary value
type appears.
-/
theorem stateViableRegion_strictly_inside_realizationRegion
    (A : AlternativePersistenceCalculation State Target)
    (h : StrictExtensionHypothesis A) :
    A.stateViableRegion ⊂ realizationRegion A := by
  constructor
  · exact stateViableRegion_subset_realizationRegion A
  · intro reverseSubset
    rcases h.strict_witness with ⟨s, hMaintains, hNotViable⟩
    exact hNotViable (reverseSubset hMaintains)

/--
If the realization region strictly extends the viable region, then a
maintained-outside-viable state exists.

This is the witness form of
`stateViableRegion_strictly_inside_realizationRegion`.
-/
theorem exists_maintained_not_viable_of_strictExtension
    (A : AlternativePersistenceCalculation State Target)
    (h : StrictExtensionHypothesis A) :
    ∃ s, MaintainedOutsideViable A s := by
  rcases h.strict_witness with ⟨s, hMaintains, hNotViable⟩
  exact ⟨s, hMaintains, hNotViable⟩

/--
The maintained-outside-viable state is genuinely outside the viable region but
inside the realization region.  This records that the produced state separates
the two interface regions, i.e. the containment `viable ⊆ maintains` is strict.
-/
theorem maintainedOutsideViable_separates_regions
    (A : AlternativePersistenceCalculation State Target)
    (s : State) (h : MaintainedOutsideViable A s) :
    s ∉ A.stateViableRegion ∧
      A.maintains s A.maintainedTarget := by
  refine ⟨?_, h.1⟩
  intro hmem
  exact h.2 hmem

/--
Contrapositive reading used below: a maintained-outside-viable state is not in
the viable region, so the viable region does not exhaust the realization
region.
-/
theorem stateViableRegion_not_all_realizers_of_strictExtension
    (A : AlternativePersistenceCalculation State Target)
    (h : StrictExtensionHypothesis A) :
    ∃ s, A.maintains s A.maintainedTarget ∧ s ∉ A.stateViableRegion := by
  rcases exists_maintained_not_viable_of_strictExtension A h with
    ⟨s, hMaintains, hNotViable⟩
  exact ⟨s, hMaintains, fun hmem => hNotViable hmem⟩

/--
Local hypothesis: a collapsed boundary readout excludes realization of the
maintained target.

This is intentionally a hypothesis in the example layer, not a field added to
`AlternativePersistenceCalculation`.  It lets this file test the next semantic
asymmetry without changing the core interface.
-/
structure CollapsedExcludesMaintainsHypothesis
    (A : AlternativePersistenceCalculation State Target) : Prop where
  collapsed_excludes :
    ∀ s, A.boundaryReadout s = BoundaryStatus.collapsed ->
      ¬ A.maintains s A.maintainedTarget

/--
Under collapsed-excludes-maintains, a maintained-outside-viable state cannot be
collapsed.
-/
theorem maintainedOutsideViable_not_collapsed
    (A : AlternativePersistenceCalculation State Target)
    (hCollapsed : CollapsedExcludesMaintainsHypothesis A)
    {s : State} (h : MaintainedOutsideViable A s) :
    A.boundaryReadout s ≠ BoundaryStatus.collapsed := by
  intro hReadout
  exact (hCollapsed.collapsed_excludes s hReadout) h.1

/--
Under collapsed-excludes-maintains, a maintained-outside-viable state has the
stopped readout.

This is the local three-way boundary consequence:

```text
maintains s  and  not viable s  and  collapsed excludes maintains
  ==> boundaryReadout s = stopped.
```

It turns the strict-extension witness into a middle-status witness, while still
keeping the collapsed/maintains asymmetry outside the core structure.
-/
theorem maintainedOutsideViable_readout_stopped
    (A : AlternativePersistenceCalculation State Target)
    (hCollapsed : CollapsedExcludesMaintainsHypothesis A)
    {s : State} (h : MaintainedOutsideViable A s) :
    A.boundaryReadout s = BoundaryStatus.stopped := by
  cases hReadout : A.boundaryReadout s with
  | viable =>
      exact False.elim (h.2 hReadout)
  | stopped =>
      rfl
  | collapsed =>
      exact False.elim
        ((maintainedOutsideViable_not_collapsed A hCollapsed h) hReadout)

/--
Strict realization extension plus collapsed-excludes-maintains yields a stopped
but still maintaining state.
-/
theorem exists_stopped_maintained_of_strictExtension
    (A : AlternativePersistenceCalculation State Target)
    (hStrict : StrictExtensionHypothesis A)
    (hCollapsed : CollapsedExcludesMaintainsHypothesis A) :
    ∃ s,
      A.boundaryReadout s = BoundaryStatus.stopped ∧
        A.maintains s A.maintainedTarget := by
  rcases exists_maintained_not_viable_of_strictExtension A hStrict with
    ⟨s, hOutside⟩
  exact
    ⟨s,
      maintainedOutsideViable_readout_stopped A hCollapsed hOutside,
      hOutside.1⟩

namespace HiddenWitness

open Persistence.StructuralPersistence.Examples.SmallWitness.HiddenSemanticWitness

/--
The hidden semantic witness strictly extends its viable region: `hiddenMaintained`
realizes the service target but is not viable (its readout is `stopped`).
-/
theorem strictRealizationExtension :
    StrictExtensionHypothesis calculation where
  strict_witness :=
    ⟨HiddenState.hiddenMaintained,
      by
        show calculation.maintains HiddenState.hiddenMaintained
          calculation.maintainedTarget
        simp only [calculation]
        trivial,
      by simp [calculation, process, readout]⟩

/--
In the hidden witness, collapsed readout excludes maintained-target
realization.
-/
theorem collapsedExcludesMaintains :
    CollapsedExcludesMaintainsHypothesis calculation where
  collapsed_excludes := by
    intro state hCollapsed
    cases state <;>
      simp [calculation, process, readout,
        Persistence.StructuralPersistence.Examples.SmallWitness.HiddenSemanticWitness.maintains]
        at hCollapsed ⊢

/--
Applying the core interface theorem to the hidden witness: a maintained-outside-
viable state exists there.

This is `hiddenMaintained` — a state the boundary readout marks non-viable
(`stopped`) while the maintained target is still realized.  It is produced from
the strict-extension hypothesis through the interface ordering, not from a
projection collision.
-/
theorem exists_maintainedOutsideViable :
    ∃ s, MaintainedOutsideViable calculation s :=
  exists_maintained_not_viable_of_strictExtension calculation
    strictRealizationExtension

/--
The hidden witness has a stopped but still maintaining state.

This is `hiddenMaintained`, obtained through the strict-extension theorem plus
the local collapsed-excludes-maintains hypothesis.
-/
theorem exists_stoppedMaintained :
    ∃ s,
      calculation.boundaryReadout s = BoundaryStatus.stopped ∧
        calculation.maintains s calculation.maintainedTarget :=
  exists_stopped_maintained_of_strictExtension calculation
    strictRealizationExtension collapsedExcludesMaintains

/--
Combined summary: the hidden witness strictly extends its viable region, and a
maintained-outside-viable state therefore exists, separating the viable and
realization regions.  With the local collapsed-excludes-maintains hypothesis,
that state is forced into the stopped readout rather than collapsed.
-/
theorem strict_realization_extension_summary :
    StrictExtensionHypothesis calculation ∧
      CollapsedExcludesMaintainsHypothesis calculation ∧
      calculation.stateViableRegion ⊂ realizationRegion calculation ∧
      (∃ s, MaintainedOutsideViable calculation s) ∧
      (∃ s, calculation.maintains s calculation.maintainedTarget ∧
        s ∉ calculation.stateViableRegion) ∧
      (∃ s,
        calculation.boundaryReadout s = BoundaryStatus.stopped ∧
          calculation.maintains s calculation.maintainedTarget) :=
  ⟨strictRealizationExtension,
    collapsedExcludesMaintains,
    stateViableRegion_strictly_inside_realizationRegion calculation
      strictRealizationExtension,
    exists_maintainedOutsideViable,
    stateViableRegion_not_all_realizers_of_strictExtension calculation
      strictRealizationExtension,
    exists_stoppedMaintained⟩

end HiddenWitness

end Examples.StrictRealizationExtension
end Persistence.StructuralPersistence
