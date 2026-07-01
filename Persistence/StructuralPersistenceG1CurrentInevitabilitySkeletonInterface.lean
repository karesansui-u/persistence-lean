import Persistence.StructuralPersistenceG1RigorousToScopedMLSeparation

/-!
# G1 Current Inevitability Skeleton Interface

This module packages the current observation-only G1 skeleton as an output
interface.

The input remains `ObservationallyRigorousCalc`: target identity, observable
dynamics, readout, response, and trace vocabulary only.  The output package
contains the current state-carrier `F/K/V_K` scaffold, the derived boundary
agreement, and the current scoped additive M/L-separation entrance.

This is still not the full G1 no-alternative theorem.  It does not prove full
native `L/B` recovery, qualified-support `M`, arbitrary adapter discovery, or
same-interface uniqueness for every competing representation.
-/

namespace Persistence.StructuralPersistence

open AdditiveScalarCompositionObservedTrace
open ScopedMLSeparation

universe u v w q x y

/--
Output-only package for the current strong-G1 skeleton.

The package is deliberately an output of the theorem below.  It must not be
used as an antecedent structure for the final inevitability theorem; otherwise
the roles would be smuggled into the hypotheses.
-/
structure CurrentInevitabilitySkeletonInterface
    {State : Type u} {Action : Type v} {Observation : Type w}
    {Target : Type q}
    (A : ObservationallyRigorousCalc State Action Observation Target) where
  core : CorePersistenceInterface.{u, q, u} State Target
  viable_agrees :
    forall s, s ∈ core.inducedViableState ↔
      A.process.readout s = BoundaryStatus.viable
  nonCollapse : A.NonCollapse
  mlSource : ResponseSeparatedCompositionSource A.process
  mlSeparation : ScopedAdditiveMLSeparationConclusion mlSource

namespace CurrentInevitabilitySkeletonInterface

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {Target : Type q}
variable {A : ObservationallyRigorousCalc State Action Observation Target}
variable (I : CurrentInevitabilitySkeletonInterface A)

/--
The boundary readout induced by the output core scaffold.

It is a definition from the output `core`, not an input field of the
observation-only calculation.
-/
def inducedBoundaryReadout
    [DecidablePred (fun s : State => s ∈ I.core.inducedViableState)]
    (s : State) : BoundaryStatus :=
  I.core.inducedBoundaryReadout s

/--
The induced boundary readout agrees with the observable viable readout.
-/
theorem inducedBoundaryReadout_viable_iff
    [DecidablePred (fun s : State => s ∈ I.core.inducedViableState)]
    (s : State) :
    I.inducedBoundaryReadout s = BoundaryStatus.viable ↔
      A.process.readout s = BoundaryStatus.viable := by
  unfold inducedBoundaryReadout
  rw [CorePersistenceInterface.inducedBoundaryReadout_viable_iff]
  exact I.viable_agrees s

/--
The scalar-collapse no-go carried by the current scoped M/L entrance.
-/
theorem no_additiveScalar_traceLog_decoder :
    ¬ Exists
      (fun traceLogOfScalar : Nat -> List (Observation × BoundaryStatus) =>
        forall burdenCount supportCount,
          traceLogOfScalar
              ((I.mlSource.toObservedAdditiveCompositionSource).scalarOfCounts
                burdenCount supportCount) =
            (I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
              burdenCount supportCount) :=
  I.mlSeparation.1

/--
The positive two-component readout carried by the current scoped M/L entrance.
-/
theorem exists_componentCoordinate_traceLog_readout :
    ∃ readout : Nat × Nat -> List (Observation × BoundaryStatus),
      forall burdenCount supportCount,
        readout
            (AdditiveScalarComposition.componentCoordinate
            burdenCount supportCount) =
          (I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount :=
  I.mlSeparation.2

/--
Trace-level alignment between two current skeleton packages.

This is the current "same observed two-channel language" relation: both
packages agree on the maintained target and on every generated burden/support
composition trace used by the scoped M/L entrance.  It is weaker than full
same-interface uniqueness.
-/
structure TraceAligned
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target}
    (J : CurrentInevitabilitySkeletonInterface B) : Prop where
  target_eq : B.maintainedTarget = A.maintainedTarget
  traceLogOfCounts_eq :
    forall burdenCount supportCount,
      (I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount =
        (J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount

/--
Current skeleton factorization, in the deliberately narrow sense currently
proved.

It says that the observation-only calculation is read through the output
package for:

* viable-state membership / induced boundary predicate;
* constant-response non-collapse;
* the generated two-channel composition traces used by the scoped M/L entrance;
* the scoped additive M/L-separation conclusion itself.

It is not a full behavioral factorization theorem and not a same-interface
uniqueness theorem.
-/
def FactorsThroughCurrentSkeleton : Prop :=
  (forall s,
    s ∈ I.core.inducedViableState ↔
      A.process.readout s = BoundaryStatus.viable) ∧
  A.NonCollapse ∧
  (forall burdenCount supportCount,
    (I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount =
      A.process.traceLog I.mlSource.initialState
        (compositionTrace I.mlSource.burdenAction I.mlSource.supportAction
          burdenCount supportCount)) ∧
  ScopedAdditiveMLSeparationConclusion I.mlSource

/--
Same-skeleton surface currently proved for two output packages.

This is the scoped semantic surface, not full native interface equality.  It
bundles the facts that both calculations factor through their output skeletons
and that the generated two-channel composition trace languages agree.
-/
def SameCurrentSkeletonSurface
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target}
    (J : CurrentInevitabilitySkeletonInterface B) : Prop :=
  I.FactorsThroughCurrentSkeleton ∧
  J.FactorsThroughCurrentSkeleton ∧
  I.TraceAligned J

/-- The current package factors the observation-only calculation through the
proved skeleton surface. -/
theorem factorsThroughCurrentSkeleton :
    I.FactorsThroughCurrentSkeleton := by
  refine ⟨I.viable_agrees, I.nonCollapse, ?_, I.mlSeparation⟩
  intro burdenCount supportCount
  rfl

end CurrentInevitabilitySkeletonInterface

namespace ObservationallyRigorousCalc

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {Target : Type q}
variable (A : ObservationallyRigorousCalc State Action Observation Target)

/--
Observation-only response separation produces the current G1 inevitability
skeleton interface.

The roles are not input fields: the output core is the current state-carrier
scaffold `A.coreInterface`, the boundary readout is induced from that core, and
the scoped M/L entrance is constructed from the response-separation witness.
-/
theorem nonempty_currentInevitabilitySkeletonInterface
    (h : A.ResponseSeparated) :
    Nonempty (CurrentInevitabilitySkeletonInterface A) := by
  rcases A.responseSeparated_forces_scopedAdditiveMLSeparation h with
    ⟨source, hsource⟩
  refine
    ⟨{ core := A.coreInterface
       viable_agrees := ?_
       nonCollapse := A.nonCollapse_of_responseSeparated h
       mlSource := source
       mlSeparation := hsource }⟩
  intro s
  exact A.core_inducedViableState_iff s

/--
Observation-only response separation produces an output skeleton interface
that factors the calculation through the current proved skeleton surface.
-/
theorem exists_currentInevitabilitySkeletonInterface_factorsThrough
    (h : A.ResponseSeparated) :
    ∃ I : CurrentInevitabilitySkeletonInterface A,
      I.FactorsThroughCurrentSkeleton := by
  rcases A.nonempty_currentInevitabilitySkeletonInterface h with ⟨I⟩
  exact ⟨I, I.factorsThroughCurrentSkeleton⟩

end ObservationallyRigorousCalc

end Persistence.StructuralPersistence
