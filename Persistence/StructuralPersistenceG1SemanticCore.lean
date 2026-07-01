import Mathlib.Data.Set.Basic

/-!
# G1 Semantic Core

This module starts a proof-substance track for G1 that is separate from the
existing status/readout ledger.

The goal here is deliberately small: from a maintained target, a boundary
readout, and an explicit same-calculation map, recover a target carrier and a
viable region that are actually used by the theorem statement.  This is not the
full no-alternative theorem.  It is the first semantic kernel that future G1
work can extend toward burden/support separation and factorization.
-/

namespace Persistence.StructuralPersistence

universe u v w

/-- Boundary status for the minimal G1 semantic core. -/
inductive BoundaryStatus where
  | viable
  | stopped
  | collapsed
  deriving DecidableEq, Repr

/--
Minimal semantic object for a persistence/collapse calculation.

The structure contains a maintained target, a target-realization predicate,
and a boundary readout.  The key non-ledger condition is that a viable boundary
readout really entails realization of the maintained target.
-/
structure AlternativePersistenceCalculation
    (State : Type u) (Target : Type v) where
  maintainedTarget : Target
  maintains : State -> Target -> Prop
  boundaryReadout : State -> BoundaryStatus
  viable_implies_maintained :
    forall s, boundaryReadout s = BoundaryStatus.viable ->
      maintains s maintainedTarget

namespace AlternativePersistenceCalculation

variable {State : Type u} {Target : Type v}
variable (A : AlternativePersistenceCalculation State Target)

/-- The recovered realization carrier: states that realize the maintained target. -/
def RecoveredCarrier : Type u :=
  {s : State // A.maintains s A.maintainedTarget}

/-- The viable region is recovered as the preimage of the viable boundary readout. -/
def recoveredViableRegion : Set A.RecoveredCarrier :=
  {k | A.boundaryReadout k.1 = BoundaryStatus.viable}

/-- The viable region on the raw state space, before passing to a carrier subtype. -/
def stateViableRegion : Set State :=
  {s | A.boundaryReadout s = BoundaryStatus.viable}

/-- Realization on the recovered carrier is inherited from the calculation. -/
def realizes (k : A.RecoveredCarrier) (target : Target) : Prop :=
  A.maintains k.1 target

/-- A viable state canonically enters the recovered carrier. -/
def recoverCarrierOfViable (s : State)
    (h : A.boundaryReadout s = BoundaryStatus.viable) : A.RecoveredCarrier :=
  ⟨s, A.viable_implies_maintained s h⟩

/-- The carrier recovered from a viable readout lies in the recovered viable region. -/
theorem recoverCarrierOfViable_mem_recoveredViableRegion (s : State)
    (h : A.boundaryReadout s = BoundaryStatus.viable) :
    A.recoverCarrierOfViable s h ∈ A.recoveredViableRegion := by
  simp [recoveredViableRegion, recoverCarrierOfViable, h]

/-- Membership in the recovered viable region realizes the maintained target. -/
theorem recoveredViableRegion_sound
    (k : A.RecoveredCarrier) :
    k ∈ A.recoveredViableRegion -> A.realizes k A.maintainedTarget := by
  intro _h
  exact k.2

/--
Membership in the raw viable region entails realization of the maintained
target.  This is the boundary-to-realization step, using the semantic condition of
the calculation rather than a subtype projection.
-/
theorem stateViableRegion_sound
    (s : State) :
    s ∈ A.stateViableRegion -> A.maintains s A.maintainedTarget := by
  intro h
  exact A.viable_implies_maintained s h

/-- A nontrivial readout has at least one viable state. -/
structure NontrivialReadout : Prop where
  viable_state : exists s, A.boundaryReadout s = BoundaryStatus.viable

/--
A nontrivial readout gives a nonempty recovered viable region.  This is the
small negative-test guard against an unconstrained phantom viable region.
-/
theorem nontrivial_recoveredViableRegion_nonempty
    (h : A.NontrivialReadout) :
    A.recoveredViableRegion.Nonempty := by
  rcases h.viable_state with ⟨s, hs⟩
  exact
    ⟨A.recoverCarrierOfViable s hs,
      A.recoverCarrierOfViable_mem_recoveredViableRegion s hs⟩

/-- A nontrivial readout gives a nonempty raw viable region. -/
theorem nontrivial_stateViableRegion_nonempty
    (h : A.NontrivialReadout) :
    A.stateViableRegion.Nonempty := by
  rcases h.viable_state with ⟨s, hs⟩
  exact ⟨s, hs⟩

end AlternativePersistenceCalculation

/--
An explicit same-calculation map between two semantic calculations.

This is intentionally not a status token.  It contains an actual state map and
the preservation facts needed to transport the target carrier and boundary
readout.
-/
structure SameCalculationMap
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    (A : AlternativePersistenceCalculation StateA Target)
    (B : AlternativePersistenceCalculation StateB Target) where
  toFun : StateA -> StateB
  target_eq : A.maintainedTarget = B.maintainedTarget
  preserves_boundary :
    forall s, B.boundaryReadout (toFun s) = A.boundaryReadout s
  preserves_maintained_target :
    forall s, A.maintains s A.maintainedTarget ->
      B.maintains (toFun s) B.maintainedTarget

namespace SameCalculationMap

variable {StateA : Type u} {StateB : Type v} {Target : Type w}
variable {A : AlternativePersistenceCalculation StateA Target}
variable {B : AlternativePersistenceCalculation StateB Target}
variable (phi : SameCalculationMap A B)

/-- The same-calculation map sends recovered carriers to recovered carriers. -/
def mapRecoveredCarrier
    (k : A.RecoveredCarrier) : B.RecoveredCarrier :=
  ⟨phi.toFun k.1, phi.preserves_maintained_target k.1 k.2⟩

/-- Viable-region membership is preserved and reflected by the boundary-preserving map. -/
theorem mapRecoveredCarrier_mem_recoveredViableRegion_iff
    (k : A.RecoveredCarrier) :
    phi.mapRecoveredCarrier k ∈ B.recoveredViableRegion ↔
      k ∈ A.recoveredViableRegion := by
  constructor
  · intro h
    dsimp [AlternativePersistenceCalculation.recoveredViableRegion,
      mapRecoveredCarrier] at h ⊢
    exact (phi.preserves_boundary k.1).symm.trans h
  · intro h
    dsimp [AlternativePersistenceCalculation.recoveredViableRegion,
      mapRecoveredCarrier] at h ⊢
    exact (phi.preserves_boundary k.1).trans h

end SameCalculationMap

/--
Recovered realization and viability data for the first semantic G1 kernel.

`K` and `viableRegion` are not phantom fields supplied from outside: the
constructor below recovers them from the alternative calculation and its
boundary readout, then shows that the explicit same-calculation map preserves
the viable region.
-/
structure RealizationViabilityRecovery
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    (A : AlternativePersistenceCalculation StateA Target)
    (B : AlternativePersistenceCalculation StateB Target)
    (phi : SameCalculationMap A B) where
  K : Type u
  carrier : K -> StateA
  realizes : K -> Target -> Prop
  viableRegion : Set K
  mapToCanonicalCarrier : K -> B.RecoveredCarrier
  carrier_realizes_target : forall k, realizes k A.maintainedTarget
  viable_iff_mapped_viable :
    forall k, k ∈ viableRegion ↔
      mapToCanonicalCarrier k ∈ B.recoveredViableRegion
  viable_implies_realizes_target :
    forall k, k ∈ viableRegion -> realizes k A.maintainedTarget

/-- Construct the recovered realization/viability interface from semantic data. -/
def recoverRealizationAndViability
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    {A : AlternativePersistenceCalculation StateA Target}
    {B : AlternativePersistenceCalculation StateB Target}
    (phi : SameCalculationMap A B) :
    RealizationViabilityRecovery A B phi where
  K := A.RecoveredCarrier
  carrier := fun k => k.1
  realizes := fun k target => A.realizes k target
  viableRegion := A.recoveredViableRegion
  mapToCanonicalCarrier := fun k => phi.mapRecoveredCarrier k
  carrier_realizes_target := fun k => k.2
  viable_iff_mapped_viable := fun k =>
    (phi.mapRecoveredCarrier_mem_recoveredViableRegion_iff k).symm
  viable_implies_realizes_target := fun k hk =>
    A.recoveredViableRegion_sound k hk

/--
G1a/G1b semantic kernel: an explicit same-calculation map recovers a target
carrier and viable region, and the viable region is preserved by the map.

This theorem is intentionally narrower than the full no-alternative theorem.
It proves the first non-ledger step needed by the target specification.
-/
theorem maintained_target_forces_realization_and_viability
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    {A : AlternativePersistenceCalculation StateA Target}
    {B : AlternativePersistenceCalculation StateB Target}
    (phi : SameCalculationMap A B) :
    exists (K : Type u)
      (carrier : K -> StateA)
      (realizes : K -> Target -> Prop)
      (viableRegion : Set K)
      (mapToCanonicalCarrier : K -> B.RecoveredCarrier),
        A.maintainedTarget = B.maintainedTarget ∧
        (forall k, A.maintains (carrier k) A.maintainedTarget) ∧
        (forall k, realizes k A.maintainedTarget) ∧
        (forall k, k ∈ viableRegion ↔
          mapToCanonicalCarrier k ∈ B.recoveredViableRegion) ∧
        (forall k, k ∈ viableRegion -> realizes k A.maintainedTarget) :=
  ⟨A.RecoveredCarrier,
    fun k => k.1,
    fun k target => A.realizes k target,
    A.recoveredViableRegion,
    fun k => phi.mapRecoveredCarrier k,
    phi.target_eq,
    fun k => k.2,
    fun k => k.2,
    fun k => (phi.mapRecoveredCarrier_mem_recoveredViableRegion_iff k).symm,
    fun k hk => A.recoveredViableRegion_sound k hk⟩

/--
State-based recovery data for the stronger G1a/G1b semantic kernel.

Unlike the recovered-carrier subtype, this keeps `K := StateA` available and
uses the boundary readout itself to prove that viable states realize the
maintained target.
-/
structure StateRealizationViabilityRecovery
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    (A : AlternativePersistenceCalculation StateA Target)
    (B : AlternativePersistenceCalculation StateB Target)
    (phi : SameCalculationMap A B) where
  K : Type u
  carrier : K -> StateA
  realizes : K -> Target -> Prop
  viableRegion : Set K
  mapToCanonicalState : K -> StateB
  target_eq : A.maintainedTarget = B.maintainedTarget
  viableRegion_nonempty : viableRegion.Nonempty
  viable_implies_carrier_realizes :
    forall k, k ∈ viableRegion -> A.maintains (carrier k) A.maintainedTarget
  viable_implies_realizes_target :
    forall k, k ∈ viableRegion -> realizes k A.maintainedTarget
  viable_iff_mapped_viable :
    forall k, k ∈ viableRegion ↔
      B.boundaryReadout (mapToCanonicalState k) = BoundaryStatus.viable

/--
Construct the state-based recovery interface from a nontrivial semantic
calculation and an explicit same-calculation map.
-/
def recoverStateRealizationAndViability
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    {A : AlternativePersistenceCalculation StateA Target}
    {B : AlternativePersistenceCalculation StateB Target}
    (phi : SameCalculationMap A B)
    (h : A.NontrivialReadout) :
    StateRealizationViabilityRecovery A B phi where
  K := StateA
  carrier := id
  realizes := fun s target => A.maintains s target
  viableRegion := A.stateViableRegion
  mapToCanonicalState := phi.toFun
  target_eq := phi.target_eq
  viableRegion_nonempty := A.nontrivial_stateViableRegion_nonempty h
  viable_implies_carrier_realizes := fun s hs =>
    A.stateViableRegion_sound s hs
  viable_implies_realizes_target := fun s hs =>
    A.stateViableRegion_sound s hs
  viable_iff_mapped_viable := fun s => by
    constructor
    · intro hs
      exact (phi.preserves_boundary s).trans hs
    · intro hs
      exact (phi.preserves_boundary s).symm.trans hs

/--
Stronger G1a/G1b semantic kernel: a nontrivial calculation with an explicit
same-calculation map recovers a nonempty viable region on the raw state space,
and viable membership itself forces realization of the maintained target.
-/
theorem nontrivial_same_calculation_forces_state_realization_and_viability
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    {A : AlternativePersistenceCalculation StateA Target}
    {B : AlternativePersistenceCalculation StateB Target}
    (phi : SameCalculationMap A B)
    (h : A.NontrivialReadout) :
    exists R : StateRealizationViabilityRecovery A B phi, R.K = StateA :=
  ⟨recoverStateRealizationAndViability phi h, rfl⟩

/--
If the alternative calculation has a nontrivial viable readout, the recovered
viable region in the semantic kernel is nonempty.
-/
theorem semantic_recovered_viableRegion_nonempty_of_nontrivial
    {StateA : Type u} {StateB : Type v} {Target : Type w}
    {A : AlternativePersistenceCalculation StateA Target}
    {B : AlternativePersistenceCalculation StateB Target}
    (phi : SameCalculationMap A B)
    (h : A.NontrivialReadout) :
    (recoverRealizationAndViability phi).viableRegion.Nonempty :=
  A.nontrivial_recoveredViableRegion_nonempty h

end Persistence.StructuralPersistence
