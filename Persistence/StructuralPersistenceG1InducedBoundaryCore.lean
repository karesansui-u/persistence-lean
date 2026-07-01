import Persistence.StructuralPersistenceG1SemanticCore

/-!
# G1 Induced Boundary Core

This module records one small semantic step for the strong G1 inevitability
target: the central interface is `F/K/V_K/L-B/M`; a boundary readout is induced
after a carrier, realization predicate, and viable region have been fixed.

This is not the full no-alternative theorem.  It only prevents one recurring
wording drift: treating `boundary` as a peer coordinate beside the core
`F/K/V_K` scaffold.
-/

namespace Persistence.StructuralPersistence

universe u v w

/--
The minimal target/structure/viability side of the G1 core interface.

The fields are deliberately limited to the maintained target `F`, a carrying
structure `K`, the carrier map into states, the realization predicate, and the
viable region `V_K`.  No boundary readout is stored as a field here.
-/
structure CorePersistenceInterface
    (State : Type u) (Target : Type v) where
  maintainedTarget : Target
  K : Type w
  carrier : K -> State
  realizes : K -> Target -> Prop
  viableRegion : Set K
  viable_realizes :
    forall k, k ∈ viableRegion -> realizes k maintainedTarget

namespace CorePersistenceInterface

variable {State : Type u} {Target : Type v}
variable (C : CorePersistenceInterface State Target)

/--
The state-level viable predicate induced by the core interface.

A raw state is viable exactly when it is carried by some viable `K`-state.
-/
def inducedViableState : Set State :=
  {s | exists k, C.carrier k = s ∧ k ∈ C.viableRegion}

/--
The proposition-level boundary predicate induced by the core interface.

This is the boundary before choosing a report format such as
`BoundaryStatus.viable` / `collapsed`.
-/
def inducedBoundaryPredicate (s : State) : Prop :=
  s ∈ C.inducedViableState

/--
The induced boundary predicate is sound for the maintained target: if a state is
inside the induced viable region, then some carrier realizing that state
realizes the maintained target.
-/
theorem inducedBoundaryPredicate_sound
    (s : State) :
    C.inducedBoundaryPredicate s ->
      exists k, C.carrier k = s ∧ C.realizes k C.maintainedTarget := by
  intro h
  rcases h with ⟨k, hcarrier, hviable⟩
  exact ⟨k, hcarrier, C.viable_realizes k hviable⟩

/--
When the induced viable predicate is decidable, it can be reported as the
minimal `BoundaryStatus` readout.  The readout is derived from the core
interface; it is not a peer coordinate stored in the interface.
-/
def inducedBoundaryReadout
    [DecidablePred (fun s : State => s ∈ C.inducedViableState)]
    (s : State) : BoundaryStatus :=
  if s ∈ C.inducedViableState then
    BoundaryStatus.viable
  else
    BoundaryStatus.collapsed

/--
The derived status readout says `viable` exactly on the induced viable region.
-/
theorem inducedBoundaryReadout_viable_iff
    [DecidablePred (fun s : State => s ∈ C.inducedViableState)]
    (s : State) :
    C.inducedBoundaryReadout s = BoundaryStatus.viable ↔
      s ∈ C.inducedViableState := by
  unfold inducedBoundaryReadout
  by_cases h : s ∈ C.inducedViableState
  · simp [h]
  · simp [h]

/--
The derived status readout is sound for the maintained target.
-/
theorem inducedBoundaryReadout_sound
    [DecidablePred (fun s : State => s ∈ C.inducedViableState)]
    (s : State) :
    C.inducedBoundaryReadout s = BoundaryStatus.viable ->
      exists k, C.carrier k = s ∧ C.realizes k C.maintainedTarget := by
  intro h
  exact
    C.inducedBoundaryPredicate_sound s
      ((C.inducedBoundaryReadout_viable_iff s).mp h)

end CorePersistenceInterface

end Persistence.StructuralPersistence
