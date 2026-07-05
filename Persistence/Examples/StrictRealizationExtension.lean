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
Combined summary: the hidden witness strictly extends its viable region, and a
maintained-outside-viable state therefore exists, separating the viable and
realization regions.
-/
theorem strict_realization_extension_summary :
    StrictExtensionHypothesis calculation ∧
      calculation.stateViableRegion ⊂ realizationRegion calculation ∧
      (∃ s, MaintainedOutsideViable calculation s) ∧
      (∃ s, calculation.maintains s calculation.maintainedTarget ∧
        s ∉ calculation.stateViableRegion) :=
  ⟨strictRealizationExtension,
    stateViableRegion_strictly_inside_realizationRegion calculation
      strictRealizationExtension,
    exists_maintainedOutsideViable,
    stateViableRegion_not_all_realizers_of_strictExtension calculation
      strictRealizationExtension⟩

end HiddenWitness

end Examples.StrictRealizationExtension
end Persistence.StructuralPersistence
