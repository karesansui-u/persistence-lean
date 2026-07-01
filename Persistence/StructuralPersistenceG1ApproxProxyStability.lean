import Persistence.StructuralPersistenceG1CurrentInevitabilitySkeletonInterface

/-!
# G1 Approximate / Proxy Stability Surface

This module is the first Lean-checked step toward the approximate/proxy G1
target described in `docs/lean/G1_APPROX_PROXY_STABILITY_DESIGN_SPEC.md`.

It does not prove proxy validity or empirical support.
It introduces a relation-valued approximate current-skeleton surface and proves
the anti-ledger guard:

```text
epsilon = 0  <->  the approximate surface is exactly the current exact surface
```

The point is to make the approximate route a conservative extension of the
current exact G1 skeleton surface before adding dynamics or margin claims.

The second small theorem-side step is a concrete natural-number trace
closeness instance.  It rejects unequal trace lengths, embeds exact equality,
and collapses zero-error closeness back to equality.

The third small theorem-side step is a memoryless finite-prefix stability
lemma: when each emitted one-step value is close, the generated trace is close.

The fourth small theorem-side step is a state-dependent finite-prefix stability
lemma under emission-coordinate non-expansiveness.

The fifth small theorem-side step generalizes that fixed-budget result to an
additive error envelope: if each step can increase the emission error by at
most `d`, every finite generated trace is close under the induced envelope.

The sixth small theorem-side step lifts natural-number pointwise trace
closeness through an injective frozen score map from actual G1 trace symbols.
This is the first bridge from the Nat trace toolkit back to
`SameApproxCurrentSkeletonSurface`; it does not derive the score-level trace
bound or proxy validity.

The seventh small theorem-side step shows that an observational `traceLog`, and
therefore `traceLogOfCounts`, is a stateful generator after extending the state
with the remaining action list.  Under the additive-envelope hypothesis it
derives a count-dependent score-level trace bound.

The eighth small theorem-side step introduces a bounded-horizon approximate
surface and consumes those count-dependent bounds inside a finite horizon.  It
does not claim one global finite error budget for unbounded additive drift.

The ninth small theorem-side step is a concrete natural-number boundary margin
lemma: a proxy score with a stated error bound preserves a binary threshold
readout outside the boundary band, and is explicitly unlicensed inside the
band.  This is not a theorem that any real proxy is valid; the error
certificate is still a domain-side obligation.

The tenth small theorem-side step splits concrete usability witnesses.  A
minimal Boolean process shows the bounded-horizon surface is inhabited.  A
nondegenerate finite drift process then uses two different action channels:
fixed budget `1` fails, while the additive envelope succeeds.  These witnesses
show that the abstract stability theorem can be used, without claiming that a
real domain proxy satisfies its hypotheses.
-/

namespace Persistence.StructuralPersistence

open AdditiveScalarCompositionObservedTrace
open ScopedMLSeparation

universe u v w q x y e

/--
A relation-valued trace closeness package.

The first approximate route deliberately avoids choosing a numeric metric.  It
only requires the facts needed for a safe exact-limit theorem:

* close traces have the same length, so finite-prefix comparison is not silently
  truncated;
* equality implies closeness, so exact traces embed into the approximate
  surface;
* zero-error closeness implies equality, so the approximate surface collapses
  back to the exact surface at `zero`.
-/
structure TraceCloseness (Eps : Type e) (α : Type u) where
  zero : Eps
  close : Eps -> List α -> List α -> Prop
  length_eq_of_close :
    forall {eps : Eps} {xs ys : List α}, close eps xs ys -> xs.length = ys.length
  close_of_eq :
    forall {eps : Eps} {xs ys : List α}, xs = ys -> close eps xs ys
  exact_of_zero :
    forall {xs ys : List α}, close zero xs ys -> xs = ys

namespace TraceCloseness

variable {Eps : Type e} {α : Type u}
variable (T : TraceCloseness Eps α)

/-- Exact equality as a degenerate trace-closeness relation. -/
def equality : TraceCloseness PUnit α where
  zero := PUnit.unit
  close := fun _ xs ys => xs = ys
  length_eq_of_close := by
    intro _ xs ys h
    rw [h]
  close_of_eq := by
    intro _ _ _ h
    exact h
  exact_of_zero := by
    intro xs ys h
    exact h

/-- Symmetric natural-number point closeness with additive error `eps`. -/
def natPointClose (eps a b : Nat) : Prop :=
  a <= b + eps ∧ b <= a + eps

/--
Pointwise natural-number trace closeness.

The relation is intentionally defined by recursion on the lists, not by
zipping.  Unequal lengths are rejected rather than silently truncating a
finite-prefix comparison.
-/
def natPointwiseClose (eps : Nat) : List Nat -> List Nat -> Prop
  | [], [] => True
  | x :: xs, y :: ys =>
      natPointClose eps x y ∧ natPointwiseClose eps xs ys
  | _, _ => False

/-- Pointwise-close natural-number traces have equal length. -/
theorem natPointwiseClose_length_eq
    {eps : Nat} {xs ys : List Nat}
    (h : natPointwiseClose eps xs ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => cases h
  | cons _ xs ih =>
      cases ys with
      | nil => cases h
      | cons _ ys =>
          exact congrArg Nat.succ (ih h.2)

/-- Exact equality embeds into pointwise closeness for every error budget. -/
theorem natPointwiseClose_of_eq
    {eps : Nat} {xs ys : List Nat}
    (h : xs = ys) :
    natPointwiseClose eps xs ys := by
  subst ys
  induction xs with
  | nil =>
      trivial
  | cons x xs ih =>
      exact
        ⟨⟨Nat.le_add_right x eps, Nat.le_add_right x eps⟩, ih⟩

/-- Zero-error pointwise closeness collapses to exact equality. -/
theorem natPointwiseClose_exact_of_zero
    {xs ys : List Nat}
    (h : natPointwiseClose 0 xs ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => cases h
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          have hxy : x = y := by
            exact
              Nat.le_antisymm
                (by simpa only [Nat.add_zero] using h.1.1)
                (by simpa only [Nat.add_zero] using h.1.2)
          have htail : xs = ys := ih h.2
          cases hxy
          cases htail
          rfl

/--
Concrete `TraceCloseness` instance for natural-number traces under pointwise
additive error.
-/
def natPointwise : TraceCloseness Nat Nat where
  zero := 0
  close := natPointwiseClose
  length_eq_of_close := by
    intro eps xs ys h
    exact natPointwiseClose_length_eq h
  close_of_eq := by
    intro eps xs ys h
    exact natPointwiseClose_of_eq h
  exact_of_zero := by
    intro xs ys h
    exact natPointwiseClose_exact_of_zero h

/--
Lists are equal when their mapped natural-number traces are equal through an
injective frozen score map.

This is the small bridge needed to reuse the natural-number trace stability
toolkit on real trace symbols without breaking the zero-error exact-limit
guard.
-/
theorem list_eq_of_map_eq_of_injective
    {α : Type u} {score : α -> Nat}
    (hinj : Function.Injective score)
    {xs ys : List α}
    (h : xs.map score = ys.map score) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          rfl
      | cons _ _ =>
          cases h
  | cons x xs ih =>
      cases ys with
      | nil =>
          cases h
      | cons y ys =>
          injection h with hhead htail
          have hxy : x = y := hinj hhead
          have hxs : xs = ys := ih htail
          cases hxy
          cases hxs
          rfl

/--
Lift pointwise natural-number trace closeness through a lossless frozen score
map from arbitrary trace symbols.

The injectivity hypothesis is not cosmetic: `TraceCloseness.exact_of_zero`
requires zero-error closeness to recover exact trace equality.  A lossy score
map belongs to a weaker approximate surface, not this conservative extension of
exact G1.
-/
def natPointwiseMapped
    {α : Type u} (score : α -> Nat) (hinj : Function.Injective score) :
    TraceCloseness Nat α where
  zero := 0
  close := fun eps xs ys => natPointwiseClose eps (xs.map score) (ys.map score)
  length_eq_of_close := by
    intro eps xs ys h
    simpa only [List.length_map] using natPointwiseClose_length_eq h
  close_of_eq := by
    intro eps xs ys h
    subst ys
    exact natPointwiseClose_of_eq rfl
  exact_of_zero := by
    intro xs ys h
    exact list_eq_of_map_eq_of_injective hinj (natPointwiseClose_exact_of_zero h)

/--
Red test: a constant score map cannot support the zero-error exact-limit guard.

The singleton traces `[0]` and `[1]` both map to `[0]`, so zero-error
score-closeness alone cannot recover trace equality.
-/
theorem not_constantScore_exact_of_zero :
    ¬ (forall xs ys : List Nat,
        natPointwiseClose 0
          (xs.map (fun _ : Nat => 0))
          (ys.map (fun _ : Nat => 0)) ->
        xs = ys) := by
  intro h
  have hclose :
      natPointwiseClose 0
        ([0].map (fun _ : Nat => 0))
        ([1].map (fun _ : Nat => 0)) := by
    exact natPointwiseClose_of_eq rfl
  have heq : [0] = [1] := h [0] [1] hclose
  injection heq with hhead
  exact Nat.zero_ne_one hhead

/-- Example: nonzero pointwise closeness permits nearby but unequal traces. -/
theorem natPointwiseClose_nonzero_example :
    natPointwiseClose 2 [1, 5] [3, 4] ∧ [1, 5] ≠ [3, 4] := by
  exact
    ⟨⟨⟨by decide, by decide⟩,
        ⟨⟨by decide, by decide⟩, trivial⟩⟩,
      by decide⟩

/-- Red test: zero-error pointwise closeness rejects unequal traces. -/
theorem not_natPointwiseClose_zero_unequal_example :
    ¬ natPointwiseClose 0 [1] [2] := by
  intro h
  exact Nat.not_succ_le_self 1 (by simpa only [Nat.add_zero] using h.1.2)

/-- Red test: a one-point trace outside the error budget is not close. -/
theorem not_natPointwiseClose_one_far_example :
    ¬ natPointwiseClose 1 [0] [3] := by
  intro h
  have hbad : 3 <= 1 := h.1.2
  exact Nat.not_succ_le_self 2 (Nat.le_trans hbad (Nat.le_succ 1))

/--
Reverse-indexed memoryless natural-number trace generator.

`natMemorylessTrace f n` emits one observation for each step index below `n`,
starting from `n - 1` and ending at `0`.  Both compared traces use the same
order, so pointwise stability is unaffected by this convention.  It is
deliberately state-free: this is the easy trace-stability branch before adding
state drift or non-expansiveness hypotheses.
-/
def natMemorylessTrace (f : Nat -> Nat) : Nat -> List Nat
  | 0 => []
  | n + 1 => f n :: natMemorylessTrace f n

/--
Memoryless finite-prefix stability.

If every emitted one-step value is `eps`-close, then the generated finite
traces are pointwise `eps`-close.  This is the first `(S)` theorem-side brick;
it does not yet cover state-dependent error propagation.
-/
theorem natPointwiseClose_natMemorylessTrace_of_step_close
    {eps n : Nat} {f g : Nat -> Nat}
    (hstep : forall i, i < n -> natPointClose eps (f i) (g i)) :
    natPointwiseClose eps (natMemorylessTrace f n) (natMemorylessTrace g n) := by
  induction n with
  | zero =>
      trivial
  | succ n ih =>
      exact
        ⟨hstep n (Nat.lt_succ_self n),
          ih (by
            intro i hi
            exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)))⟩

/-- Example: a uniformly shifted memoryless trace is close with matching error. -/
theorem natMemorylessTrace_close_shift_example :
    natPointwiseClose 1
      (natMemorylessTrace (fun i => i) 3)
      (natMemorylessTrace (fun i => i + 1) 3) := by
  exact natPointwiseClose_natMemorylessTrace_of_step_close
    (eps := 1) (n := 3)
    (f := fun i => i) (g := fun i => i + 1)
    (by
      intro i _hi
      exact
        ⟨Nat.le_trans (Nat.le_succ i) (Nat.le_succ (i + 1)),
          Nat.le_refl (i + 1)⟩)

/--
Red test: if a one-step memoryless emission is outside the error budget, the
generated one-step trace is not close.
-/
theorem not_natMemorylessTrace_close_when_step_far :
    ¬ natPointwiseClose 1
      (natMemorylessTrace (fun _ => 0) 1)
      (natMemorylessTrace (fun _ => 3) 1) := by
  exact not_natPointwiseClose_one_far_example

/--
State-dependent natural-number trace generator.

`natStatefulTrace step emit s n` emits from the current state, advances by
`step`, and repeats for `n` observations.  Unlike `natMemorylessTrace`, later
outputs can depend on earlier state evolution.
-/
def natStatefulTrace {State : Type v}
    (step : State -> State) (emit : State -> Nat) : State -> Nat -> List Nat
  | _, 0 => []
  | s, n + 1 => emit s :: natStatefulTrace step emit (step s) n

/--
State for replaying an action list as a uniform stateful trace generator.

The original process may use a different action at every step.  To reuse
`natStatefulTrace`, the remaining action list is made part of the state; the
uniform step consumes its head action when one is available.
-/
def actionListTraceStep
    {State : Type v} {Action : Type w} {Observation : Type x}
    (P : ObservationalPersistenceProcess State Action Observation) :
    State × List Action -> State × List Action
  | (s, []) => (s, [])
  | (s, action :: actions) => (P.step s action, actions)

/--
Emit the scored one-step response of the head action in an action-list trace
state.  The empty-list case is arbitrary because the replay theorem uses
exactly `actions.length` emissions.  Later stability hypotheses that quantify
over all action-list states therefore also cover this sentinel case; this is a
conservative proof surface, not a claim that empty traces have a meaningful
next response.
-/
def actionListTraceEmit
    {State : Type v} {Action : Type w} {Observation : Type x}
    (P : ObservationalPersistenceProcess State Action Observation)
    (score : Observation × BoundaryStatus -> Nat) :
    State × List Action -> Nat
  | (_s, []) => 0
  | (s, action :: _actions) => score (P.response s action)

/--
The mapped observational `traceLog` is exactly the stateful trace obtained by
threading the current state together with the remaining action list.

This is the generator-correspondence bridge: `traceLog` is not a separate
oracle once the process `step`, current state, action list, and score map are
fixed.
-/
theorem map_traceLog_eq_natStatefulTrace_actionList
    {State : Type v} {Action : Type w} {Observation : Type x}
    (P : ObservationalPersistenceProcess State Action Observation)
    (score : Observation × BoundaryStatus -> Nat)
    (s : State) :
    forall actions : List Action,
      (P.traceLog s actions).map score =
        natStatefulTrace
          (actionListTraceStep P)
          (actionListTraceEmit P score)
          (s, actions)
          actions.length
  | [] => rfl
  | action :: actions => by
      change
        score (P.response s action) :: (P.traceLog (P.step s action) actions).map score =
          score (P.response s action) ::
            natStatefulTrace
              (actionListTraceStep P)
              (actionListTraceEmit P score)
              (P.step s action, actions)
              actions.length
      exact
        congrArg (fun tail => score (P.response s action) :: tail)
          (map_traceLog_eq_natStatefulTrace_actionList P score (P.step s action) actions)

theorem compositionTrace_length
    {Action : Type v}
    (burdenAction supportAction : Action)
    (burdenCount supportCount : Nat) :
    (compositionTrace burdenAction supportAction
      burdenCount supportCount).length =
      burdenCount + supportCount := by
  unfold compositionTrace
  rw [List.length_append, List.length_replicate, List.length_replicate]

theorem map_traceLogOfCounts_eq_natStatefulTrace_actionList
    {State : Type v} {Action : Type w} {Observation : Type x}
    {P : ObservationalPersistenceProcess State Action Observation}
    (source : ObservedAdditiveCompositionSource P)
    (score : Observation × BoundaryStatus -> Nat)
    (burdenCount supportCount : Nat) :
    (source.traceLogOfCounts burdenCount supportCount).map score =
      natStatefulTrace
        (actionListTraceStep P)
        (actionListTraceEmit P score)
        (source.initialState,
          compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount)
        (burdenCount + supportCount) := by
  calc
    (source.traceLogOfCounts burdenCount supportCount).map score =
        (P.traceLog source.initialState
          (compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount)).map score := rfl
    _ =
        natStatefulTrace
          (actionListTraceStep P)
          (actionListTraceEmit P score)
          (source.initialState,
            compositionTrace source.burdenAction source.supportAction
              burdenCount supportCount)
          (compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount).length :=
        map_traceLog_eq_natStatefulTrace_actionList P score source.initialState
          (compositionTrace source.burdenAction source.supportAction
            burdenCount supportCount)
    _ =
        natStatefulTrace
          (actionListTraceStep P)
          (actionListTraceEmit P score)
          (source.initialState,
            compositionTrace source.burdenAction source.supportAction
              burdenCount supportCount)
          (burdenCount + supportCount) := by
        rw [compositionTrace_length]

/--
State-dependent finite-prefix stability under emission-coordinate
non-expansiveness.

If the two current emissions are `eps`-close, and stepping preserves that
emission closeness, then every finite generated trace is pointwise
`eps`-close.  This is a theorem-side stability result; it does not claim that a
real proxy map satisfies the non-expansiveness hypothesis.
-/
theorem natPointwiseClose_natStatefulTrace_of_emit_nonexpansive
    {StateA : Type v} {StateB : Type w}
    {eps n : Nat}
    {stepA : StateA -> StateA} {emitA : StateA -> Nat}
    {stepB : StateB -> StateB} {emitB : StateB -> Nat}
    {sA : StateA} {sB : StateB}
    (hinit : natPointClose eps (emitA sA) (emitB sB))
    (hstep :
      forall sA sB,
        natPointClose eps (emitA sA) (emitB sB) ->
          natPointClose eps (emitA (stepA sA)) (emitB (stepB sB))) :
    natPointwiseClose eps
      (natStatefulTrace stepA emitA sA n)
      (natStatefulTrace stepB emitB sB n) := by
  induction n generalizing sA sB with
  | zero =>
      trivial
  | succ n ih =>
      exact
        ⟨hinit,
          ih (hstep sA sB hinit)⟩

/-- Example: synchronized successor dynamics preserve a one-unit shift. -/
theorem natStatefulTrace_close_successor_shift_example :
    natPointwiseClose 1
      (natStatefulTrace (fun i => i + 1) (fun i => i) 0 4)
      (natStatefulTrace (fun i => i + 1) (fun i => i) 1 4) := by
  exact natPointwiseClose_natStatefulTrace_of_emit_nonexpansive
    (eps := 1) (n := 4)
    (stepA := fun i => i + 1) (emitA := fun i => i)
    (stepB := fun i => i + 1) (emitB := fun i => i)
    (sA := 0) (sB := 1)
    ⟨by decide, by decide⟩
    (by
      intro sA sB h
      exact
        ⟨Nat.succ_le_succ h.1,
          Nat.succ_le_succ h.2⟩)

/--
Red test: close initial emissions do not imply trace closeness if stepping can
move the emissions outside the error budget.
-/
theorem not_natStatefulTrace_close_without_nonexpansive_step :
    natPointClose 1 ((fun i => i) 0) ((fun i => i) 0) ∧
      ¬ natPointwiseClose 1
        (natStatefulTrace (fun _ : Nat => 0) (fun i => i) 0 2)
        (natStatefulTrace (fun _ : Nat => 3) (fun i => i) 0 2) := by
  exact
    ⟨⟨by decide, by decide⟩,
      by
        intro h
        exact not_natPointwiseClose_one_far_example h.2⟩

/--
Additive error envelope: starting at `eps`, add at most `d` per step.

For a nonempty trace this is a conservative prefix envelope: the final emitted
point of an `n`-observation trace only needs the first `n - 1` propagated
increments, but using `n` keeps the induction shape simple and monotone.
-/
def natAdditiveEnvelope (eps d : Nat) : Nat -> Nat
  | 0 => eps
  | n + 1 => natAdditiveEnvelope (eps + d) d n

/-- The additive envelope always contains the starting error budget. -/
theorem natAdditiveEnvelope_start_le
    (eps d n : Nat) :
    eps <= natAdditiveEnvelope eps d n := by
  induction n generalizing eps with
  | zero =>
      exact Nat.le_refl eps
  | succ n ih =>
      exact Nat.le_trans (Nat.le_add_right eps d) (ih (eps + d))

/-- Point closeness is monotone in the error budget. -/
theorem natPointClose_mono
    {eps eps' a b : Nat}
    (hbudget : eps <= eps')
    (h : natPointClose eps a b) :
    natPointClose eps' a b :=
  ⟨Nat.le_trans h.1 (Nat.add_le_add_left hbudget b),
    Nat.le_trans h.2 (Nat.add_le_add_left hbudget a)⟩

/-- Pointwise trace closeness is monotone in the error budget. -/
theorem natPointwiseClose_mono
    {eps eps' : Nat} {xs ys : List Nat}
    (hbudget : eps <= eps')
    (h : natPointwiseClose eps xs ys) :
    natPointwiseClose eps' xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => trivial
      | cons _ _ => cases h
  | cons _ xs ih =>
      cases ys with
      | nil => cases h
      | cons _ ys =>
          exact ⟨natPointClose_mono hbudget h.1, ih h.2⟩

/--
State-dependent finite-prefix stability under an additive error envelope.

If each step can increase the current emission error by at most `d`, then every
finite generated trace is close under the additive envelope.  This generalizes
the fixed non-expansive theorem above: the case `d = 0` keeps the budget fixed.
-/
theorem natPointwiseClose_natStatefulTrace_of_emit_additiveEnvelope
    {StateA : Type v} {StateB : Type w}
    {eps d n : Nat}
    {stepA : StateA -> StateA} {emitA : StateA -> Nat}
    {stepB : StateB -> StateB} {emitB : StateB -> Nat}
    {sA : StateA} {sB : StateB}
    (hinit : natPointClose eps (emitA sA) (emitB sB))
    (hstep :
      forall budget sA sB,
        natPointClose budget (emitA sA) (emitB sB) ->
          natPointClose (budget + d) (emitA (stepA sA)) (emitB (stepB sB))) :
    natPointwiseClose (natAdditiveEnvelope eps d n)
      (natStatefulTrace stepA emitA sA n)
      (natStatefulTrace stepB emitB sB n) := by
  induction n generalizing eps sA sB with
  | zero =>
      trivial
  | succ n ih =>
      exact
        ⟨natPointClose_mono (natAdditiveEnvelope_start_le eps d (n + 1)) hinit,
          by
            change natPointwiseClose (natAdditiveEnvelope (eps + d) d n)
              (natStatefulTrace stepA emitA (stepA sA) n)
              (natStatefulTrace stepB emitB (stepB sB) n)
            exact ih (hstep eps sA sB hinit)⟩

/--
State-dependent finite-prefix stability under an additive error envelope, with
a preserved side relation on the paired states.

The relation is useful for action-list replays: the meaningful theorem only
needs the two remaining action lists to stay length-aligned, not a step bound
over arbitrary mismatched sentinel states.
-/
theorem natPointwiseClose_natStatefulTrace_of_emit_additiveEnvelope_rel
    {StateA : Type v} {StateB : Type w}
    {eps d n : Nat}
    {stepA : StateA -> StateA} {emitA : StateA -> Nat}
    {stepB : StateB -> StateB} {emitB : StateB -> Nat}
    {Rel : StateA -> StateB -> Prop}
    {sA : StateA} {sB : StateB}
    (hrel : Rel sA sB)
    (hinit : natPointClose eps (emitA sA) (emitB sB))
    (hstepRel :
      forall sA sB,
        Rel sA sB -> Rel (stepA sA) (stepB sB))
    (hstep :
      forall budget sA sB,
        Rel sA sB ->
          natPointClose budget (emitA sA) (emitB sB) ->
          natPointClose (budget + d) (emitA (stepA sA)) (emitB (stepB sB))) :
    natPointwiseClose (natAdditiveEnvelope eps d n)
      (natStatefulTrace stepA emitA sA n)
      (natStatefulTrace stepB emitB sB n) := by
  induction n generalizing eps sA sB with
  | zero =>
      trivial
  | succ n ih =>
      exact
        ⟨natPointClose_mono (natAdditiveEnvelope_start_le eps d (n + 1)) hinit,
          by
            change natPointwiseClose (natAdditiveEnvelope (eps + d) d n)
              (natStatefulTrace stepA emitA (stepA sA) n)
              (natStatefulTrace stepB emitB (stepB sB) n)
            exact ih (hstepRel sA sB hrel) (hstep eps sA sB hrel hinit)⟩

theorem actionListTraceStep_preserves_length_eq
    {StateA : Type v} {ActionA : Type w}
    {StateB : Type x} {ActionB : Type y}
    {Observation : Type q}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (stateA : StateA × List ActionA) (stateB : StateB × List ActionB)
    (h : stateA.2.length = stateB.2.length) :
    (actionListTraceStep P stateA).2.length =
      (actionListTraceStep Q stateB).2.length := by
  cases stateA with
  | mk sA actionsA =>
      cases stateB with
      | mk sB actionsB =>
          cases actionsA with
          | nil =>
              cases actionsB with
              | nil =>
                  rfl
              | cons _ _ =>
                  cases h
          | cons _ tailA =>
              cases actionsB with
              | nil =>
                  cases h
              | cons _ tailB =>
                  exact Nat.succ.inj h

theorem natPointwiseClose_map_traceLog_of_actionList_additiveEnvelope_aligned
    {StateA : Type v} {ActionA : Type w}
    {StateB : Type x} {ActionB : Type y}
    {Observation : Type q}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (score : Observation × BoundaryStatus -> Nat)
    {eps d : Nat}
    {sA : StateA} {sB : StateB}
    {actionsA : List ActionA} {actionsB : List ActionB}
    (hlen : actionsA.length = actionsB.length)
    (hinit :
      natPointClose eps
        (actionListTraceEmit P score (sA, actionsA))
        (actionListTraceEmit Q score (sB, actionsB)))
    (hstep :
      forall budget stateA stateB,
        stateA.2.length = stateB.2.length ->
          natPointClose budget
            (actionListTraceEmit P score stateA)
            (actionListTraceEmit Q score stateB) ->
          natPointClose (budget + d)
            (actionListTraceEmit P score (actionListTraceStep P stateA))
            (actionListTraceEmit Q score (actionListTraceStep Q stateB))) :
    natPointwiseClose (natAdditiveEnvelope eps d actionsA.length)
      ((P.traceLog sA actionsA).map score)
      ((Q.traceLog sB actionsB).map score) := by
  rw [map_traceLog_eq_natStatefulTrace_actionList P score sA actionsA]
  rw [map_traceLog_eq_natStatefulTrace_actionList Q score sB actionsB]
  rw [← hlen]
  exact
    natPointwiseClose_natStatefulTrace_of_emit_additiveEnvelope_rel
      (eps := eps) (d := d) (n := actionsA.length)
      (stepA := actionListTraceStep P)
      (emitA := actionListTraceEmit P score)
      (stepB := actionListTraceStep Q)
      (emitB := actionListTraceEmit Q score)
      (Rel := fun stateA stateB => stateA.2.length = stateB.2.length)
      (sA := (sA, actionsA)) (sB := (sB, actionsB))
      hlen hinit
      (actionListTraceStep_preserves_length_eq P Q)
      hstep

theorem natPointwiseClose_map_traceLogOfCounts_of_actionList_additiveEnvelope_aligned
    {StateA : Type v} {ActionA : Type w}
    {StateB : Type x} {ActionB : Type y}
    {Observation : Type q}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    (sourceA : ObservedAdditiveCompositionSource P)
    (sourceB : ObservedAdditiveCompositionSource Q)
    (score : Observation × BoundaryStatus -> Nat)
    {eps d : Nat}
    (burdenCount supportCount : Nat)
    (hinit :
      natPointClose eps
        (actionListTraceEmit P score
          (sourceA.initialState,
            compositionTrace sourceA.burdenAction sourceA.supportAction
              burdenCount supportCount))
        (actionListTraceEmit Q score
          (sourceB.initialState,
            compositionTrace sourceB.burdenAction sourceB.supportAction
              burdenCount supportCount)))
    (hstep :
      forall budget stateA stateB,
        stateA.2.length = stateB.2.length ->
          natPointClose budget
            (actionListTraceEmit P score stateA)
            (actionListTraceEmit Q score stateB) ->
          natPointClose (budget + d)
            (actionListTraceEmit P score (actionListTraceStep P stateA))
            (actionListTraceEmit Q score (actionListTraceStep Q stateB))) :
    natPointwiseClose
      (natAdditiveEnvelope eps d (burdenCount + supportCount))
      ((sourceA.traceLogOfCounts burdenCount supportCount).map score)
      ((sourceB.traceLogOfCounts burdenCount supportCount).map score) := by
  have hlen :
      (compositionTrace sourceA.burdenAction sourceA.supportAction
        burdenCount supportCount).length =
        (compositionTrace sourceB.burdenAction sourceB.supportAction
          burdenCount supportCount).length := by
    rw [compositionTrace_length, compositionTrace_length]
  simpa [ObservedAdditiveCompositionSource.traceLogOfCounts,
    compositionTrace_length] using
    natPointwiseClose_map_traceLog_of_actionList_additiveEnvelope_aligned
      P Q score hlen hinit hstep

theorem natPointwiseClose_map_traceLog_of_actionList_additiveEnvelope
    {StateA : Type v} {ActionA : Type w}
    {StateB : Type x} {ActionB : Type y}
    {Observation : Type q}
    (P : ObservationalPersistenceProcess StateA ActionA Observation)
    (Q : ObservationalPersistenceProcess StateB ActionB Observation)
    (score : Observation × BoundaryStatus -> Nat)
    {eps d : Nat}
    {sA : StateA} {sB : StateB}
    {actionsA : List ActionA} {actionsB : List ActionB}
    (hlen : actionsA.length = actionsB.length)
    (hinit :
      natPointClose eps
        (actionListTraceEmit P score (sA, actionsA))
        (actionListTraceEmit Q score (sB, actionsB)))
    (hstep :
      forall budget stateA stateB,
        natPointClose budget
          (actionListTraceEmit P score stateA)
          (actionListTraceEmit Q score stateB) ->
          natPointClose (budget + d)
            (actionListTraceEmit P score (actionListTraceStep P stateA))
            (actionListTraceEmit Q score (actionListTraceStep Q stateB))) :
    natPointwiseClose (natAdditiveEnvelope eps d actionsA.length)
      ((P.traceLog sA actionsA).map score)
      ((Q.traceLog sB actionsB).map score) := by
  rw [map_traceLog_eq_natStatefulTrace_actionList P score sA actionsA]
  rw [map_traceLog_eq_natStatefulTrace_actionList Q score sB actionsB]
  rw [← hlen]
  exact
    natPointwiseClose_natStatefulTrace_of_emit_additiveEnvelope
      (eps := eps) (d := d) (n := actionsA.length)
      (stepA := actionListTraceStep P)
      (emitA := actionListTraceEmit P score)
      (stepB := actionListTraceStep Q)
      (emitB := actionListTraceEmit Q score)
      (sA := (sA, actionsA)) (sB := (sB, actionsB))
      hinit hstep

theorem natPointwiseClose_map_traceLogOfCounts_of_actionList_additiveEnvelope
    {StateA : Type v} {ActionA : Type w}
    {StateB : Type x} {ActionB : Type y}
    {Observation : Type q}
    {P : ObservationalPersistenceProcess StateA ActionA Observation}
    {Q : ObservationalPersistenceProcess StateB ActionB Observation}
    (sourceA : ObservedAdditiveCompositionSource P)
    (sourceB : ObservedAdditiveCompositionSource Q)
    (score : Observation × BoundaryStatus -> Nat)
    {eps d : Nat}
    (burdenCount supportCount : Nat)
    (hinit :
      natPointClose eps
        (actionListTraceEmit P score
          (sourceA.initialState,
            compositionTrace sourceA.burdenAction sourceA.supportAction
              burdenCount supportCount))
        (actionListTraceEmit Q score
          (sourceB.initialState,
            compositionTrace sourceB.burdenAction sourceB.supportAction
              burdenCount supportCount)))
    (hstep :
      forall budget stateA stateB,
        natPointClose budget
          (actionListTraceEmit P score stateA)
          (actionListTraceEmit Q score stateB) ->
          natPointClose (budget + d)
            (actionListTraceEmit P score (actionListTraceStep P stateA))
            (actionListTraceEmit Q score (actionListTraceStep Q stateB))) :
    natPointwiseClose
      (natAdditiveEnvelope eps d (burdenCount + supportCount))
      ((sourceA.traceLogOfCounts burdenCount supportCount).map score)
      ((sourceB.traceLogOfCounts burdenCount supportCount).map score) := by
  have hlen :
      (compositionTrace sourceA.burdenAction sourceA.supportAction
        burdenCount supportCount).length =
        (compositionTrace sourceB.burdenAction sourceB.supportAction
          burdenCount supportCount).length := by
    rw [compositionTrace_length, compositionTrace_length]
  simpa [ObservedAdditiveCompositionSource.traceLogOfCounts,
    compositionTrace_length] using
    natPointwiseClose_map_traceLog_of_actionList_additiveEnvelope
      P Q score hlen hinit hstep

/-- Example: additive envelope permits one side to drift by one per step. -/
theorem natStatefulTrace_additiveEnvelope_growth_example :
    natPointwiseClose (natAdditiveEnvelope 0 1 4)
      (natStatefulTrace (fun _ : Nat => 0) (fun _ => 0) 0 4)
      (natStatefulTrace (fun i : Nat => i + 1) (fun i => i) 0 4) := by
  exact natPointwiseClose_natStatefulTrace_of_emit_additiveEnvelope
    (eps := 0) (d := 1) (n := 4)
    (stepA := fun _ : Nat => 0) (emitA := fun _ => 0)
    (stepB := fun i : Nat => i + 1) (emitB := fun i => i)
    (sA := 0) (sB := 0)
    ⟨Nat.le_refl 0, Nat.le_refl 0⟩
    (by
      intro budget sA sB h
      exact
        ⟨Nat.zero_le (sB + 1 + (budget + 1)),
          by
            change sB + 1 <= ((fun _ : Nat => 0) sA + budget) + 1
            exact Nat.succ_le_succ h.2⟩)

/-- Red test: a fixed too-small budget cannot absorb accumulating drift. -/
theorem not_natStatefulTrace_fixedBudget_absorbs_growth_example :
    ¬ natPointwiseClose 1
      (natStatefulTrace (fun _ : Nat => 0) (fun i => i) 0 3)
      (natStatefulTrace (fun i : Nat => i + 1) (fun i => i) 0 3) := by
  intro h
  have htail : natPointwiseClose 1 [0] [2] := h.2.2
  have hbad : 2 <= 1 := htail.1.2
  exact Nat.not_succ_le_self 1 hbad

end TraceCloseness

/-! ## Boundary margin / error preservation

The next theorem-side step is deliberately small and concrete.  It does not
say that a real proxy is valid.  It says that once a proxy score has a stated
integer error bound, a binary threshold readout is preserved outside the
boundary error band, and is unlicensed inside that band.
-/

/-- A minimal proxy-licensed boundary status. -/
inductive ApproxBoundaryReadoutStatus where
  | preserved
  | indeterminate
deriving DecidableEq, Repr

namespace ApproxBoundaryReadoutStatus

/-- Binary threshold readout for a natural-number boundary score. -/
def natBoundaryReadout (threshold score : Nat) : BoundaryStatus :=
  if score < threshold then BoundaryStatus.viable else BoundaryStatus.collapsed

/-- Symmetric natural-number error band. -/
def WithinNatError (err exact proxy : Nat) : Prop :=
  proxy <= exact + err ∧ exact <= proxy + err

/--
The exact score is outside the proxy error band around the threshold.

Either it is safely below the threshold (`exact + err < threshold`) or safely
on/above it (`threshold + err <= exact`).
-/
def HasNatBoundaryMargin (threshold err exact : Nat) : Prop :=
  exact + err < threshold ∨ threshold + err <= exact

/-- Local cancellation for natural-number error bands. -/
theorem nat_le_of_add_le_add_right_local
    {a b : Nat} (err : Nat) (h : a + err <= b + err) : a <= b := by
  induction err with
  | zero =>
      simpa using h
  | succ err ih =>
      apply ih
      exact Nat.le_of_succ_le_succ (by simpa only [Nat.add_succ] using h)

/--
Proxy-licensed readout status: preserved only when the exact score has enough
margin for the stated error budget; otherwise indeterminate.

This is a licensing readout for the proxy calculation, not a claim that the
underlying exact system has no real boundary status.
-/
def natBoundaryLicense
    (threshold err exact : Nat) : ApproxBoundaryReadoutStatus :=
  if exact + err < threshold then
    ApproxBoundaryReadoutStatus.preserved
  else if threshold + err <= exact then
    ApproxBoundaryReadoutStatus.preserved
  else
    ApproxBoundaryReadoutStatus.indeterminate

/--
Safe-below side: if the proxy error band stays below the threshold, the proxy
readout is viable whenever the exact readout is viable.
-/
theorem natBoundaryReadout_preserved_below
    {threshold err exact proxy : Nat}
    (hclose : WithinNatError err exact proxy)
    (hmargin : exact + err < threshold) :
    natBoundaryReadout threshold proxy = natBoundaryReadout threshold exact := by
  unfold natBoundaryReadout
  have hproxy : proxy < threshold := lt_of_le_of_lt hclose.1 hmargin
  have hexact : exact < threshold := lt_of_le_of_lt (Nat.le_add_right exact err) hmargin
  simp [hproxy, hexact]

/--
Safe-above side: if the proxy error band stays on/above the threshold, the
proxy readout is collapsed whenever the exact readout is collapsed.
-/
theorem natBoundaryReadout_preserved_above
    {threshold err exact proxy : Nat}
    (hclose : WithinNatError err exact proxy)
    (hmargin : threshold + err <= exact) :
    natBoundaryReadout threshold proxy = natBoundaryReadout threshold exact := by
  unfold natBoundaryReadout
  have hthreshold_proxy_add : threshold + err <= proxy + err :=
    le_trans hmargin hclose.2
  have hthreshold_proxy : threshold <= proxy :=
    nat_le_of_add_le_add_right_local err hthreshold_proxy_add
  have hnot_proxy : ¬ proxy < threshold := by
    intro hlt
    exact Nat.lt_irrefl proxy (Nat.lt_of_lt_of_le hlt hthreshold_proxy)
  have hthreshold_exact : threshold <= exact :=
    le_trans (Nat.le_add_right threshold err) hmargin
  have hnot_exact : ¬ exact < threshold := by
    intro hlt
    exact Nat.lt_irrefl exact (Nat.lt_of_lt_of_le hlt hthreshold_exact)
  rw [if_neg hnot_proxy, if_neg hnot_exact]

/--
Boundary decision preservation outside the proxy error band.

This is the minimal margin/error theorem for the proxy-stability track.  It is
purely theorem-side: the caller must still justify that the proxy score really
lies within `err` of the exact score.
-/
theorem natBoundaryReadout_preserved_of_margin
    {threshold err exact proxy : Nat}
    (hclose : WithinNatError err exact proxy)
    (hmargin : HasNatBoundaryMargin threshold err exact) :
    natBoundaryReadout threshold proxy = natBoundaryReadout threshold exact := by
  rcases hmargin with hbelow | habove
  · exact natBoundaryReadout_preserved_below hclose hbelow
  · exact natBoundaryReadout_preserved_above hclose habove

/-- Inside the boundary error band, the proxy readout is not licensed. -/
theorem natBoundaryLicense_indeterminate_of_no_margin
    {threshold err exact : Nat}
    (hbelow : ¬ exact + err < threshold)
    (habove : ¬ threshold + err <= exact) :
    natBoundaryLicense threshold err exact =
      ApproxBoundaryReadoutStatus.indeterminate := by
  unfold natBoundaryLicense
  simp [hbelow, habove]

/-- Red test: a point exactly at the threshold with positive error is unlicensed. -/
theorem natBoundaryLicense_threshold_error_one_indeterminate :
    natBoundaryLicense 10 1 10 = ApproxBoundaryReadoutStatus.indeterminate := by
  exact natBoundaryLicense_indeterminate_of_no_margin
    (by decide)
    (by decide)

/--
Red test: without margin, the same exact score and error budget permit close
proxy scores with both boundary labels.

This is why the no-margin-band result must be `indeterminate`: the proxy evidence
alone cannot license either boundary label.
-/
theorem natBoundaryNoMargin_allows_viable_and_collapsed_proxies :
    ∃ proxyViable proxyCollapsed,
      WithinNatError 1 10 proxyViable ∧
        WithinNatError 1 10 proxyCollapsed ∧
        natBoundaryReadout 10 proxyViable = BoundaryStatus.viable ∧
        natBoundaryReadout 10 proxyCollapsed = BoundaryStatus.collapsed := by
  exact
    ⟨9, 10,
      ⟨by decide, by decide⟩,
      ⟨by decide, by decide⟩,
      by decide,
      by decide⟩

/-- Sanity check: outside the error band, a close proxy preserves the readout. -/
theorem natBoundaryReadout_preserved_example :
    natBoundaryReadout 10 4 = natBoundaryReadout 10 3 := by
  exact natBoundaryReadout_preserved_of_margin
    (threshold := 10) (err := 1) (exact := 3) (proxy := 4)
    ⟨by decide, by decide⟩
    (Or.inl (by decide))

end ApproxBoundaryReadoutStatus

namespace CurrentInevitabilitySkeletonInterface

variable {State : Type u} {Action : Type v} {Observation : Type w}
variable {Target : Type q}
variable {AlternativeState : Type x} {AlternativeAction : Type y}
variable {Eps : Type e}
variable {A : ObservationallyRigorousCalc State Action Observation Target}
variable {B :
  ObservationallyRigorousCalc AlternativeState AlternativeAction
    Observation Target}
variable (T : TraceCloseness Eps (Observation × BoundaryStatus))
variable (eps : Eps)
variable (I : CurrentInevitabilitySkeletonInterface A)
variable (J : CurrentInevitabilitySkeletonInterface B)

/--
Approximate version of `SameCurrentSkeletonSurface`.

The exact surface uses equality of generated two-channel traces.  The
approximate surface replaces that equality by the relation `T.close eps`.  The
factor-through facts remain exact because this surface relates already
constructed output skeleton interfaces; future modules can add proxy/margin
theorems that construct such interfaces from noisy observations.
-/
structure SameApproxCurrentSkeletonSurface : Prop where
  source_factors : I.FactorsThroughCurrentSkeleton
  target_factors : J.FactorsThroughCurrentSkeleton
  target_eq : B.maintainedTarget = A.maintainedTarget
  trace_close :
    forall burdenCount supportCount,
      T.close eps
        ((I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount)
        ((J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
          burdenCount supportCount)

/--
The approximate surface is length-safe by construction: each close generated
trace pair has equal length.
-/
theorem trace_length_eq_of_sameApproxCurrentSkeletonSurface
    (h : I.SameApproxCurrentSkeletonSurface T eps J)
    (burdenCount supportCount : Nat) :
    ((I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount).length =
      ((J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount).length :=
  T.length_eq_of_close (h.trace_close burdenCount supportCount)

/--
Exact G1 embeds into the approximate surface for any error parameter.

This is the forward conservative-extension direction: an exact
`SameCurrentSkeletonSurface` is also approximate, because equality of generated
traces implies trace closeness.
-/
theorem sameApproxCurrentSkeletonSurface_of_sameCurrentSkeletonSurface
    (h : I.SameCurrentSkeletonSurface J) :
    I.SameApproxCurrentSkeletonSurface T eps J := by
  rcases h with ⟨hI, hJ, haligned⟩
  refine
    { source_factors := hI
      target_factors := hJ
      target_eq := haligned.target_eq
      trace_close := ?_ }
  intro burdenCount supportCount
  exact T.close_of_eq (haligned.traceLogOfCounts_eq burdenCount supportCount)

/--
Zero-error approximate G1 reduces to the exact current G1 skeleton surface.

This is the anti-ledger guard for approximate/proxy G1: if the error parameter
is the trace-closeness zero, then the approximate surface has no extra
freedom.  Trace closeness collapses to trace equality and the exact
`SameCurrentSkeletonSurface` is recovered.
-/
theorem sameCurrentSkeletonSurface_of_sameApproxCurrentSkeletonSurface_zero
    (h : I.SameApproxCurrentSkeletonSurface T T.zero J) :
    I.SameCurrentSkeletonSurface J := by
  refine ⟨h.source_factors, h.target_factors, ?_⟩
  refine
    { target_eq := h.target_eq
      traceLogOfCounts_eq := ?_ }
  intro burdenCount supportCount
  exact T.exact_of_zero (h.trace_close burdenCount supportCount)

/--
At zero error, the approximate and exact current skeleton surfaces are
equivalent.
-/
theorem sameApproxCurrentSkeletonSurface_zero_iff_sameCurrentSkeletonSurface :
    I.SameApproxCurrentSkeletonSurface T T.zero J ↔
      I.SameCurrentSkeletonSurface J := by
  constructor
  · intro h
    exact I.sameCurrentSkeletonSurface_of_sameApproxCurrentSkeletonSurface_zero
      T J h
  · intro h
    exact I.sameApproxCurrentSkeletonSurface_of_sameCurrentSkeletonSurface
      T T.zero J h

/--
Score-level trace closeness gives an approximate current skeleton surface when
the score map is lossless.

This is the first bridge from the natural-number trace-stability toolkit back
to the actual G1 trace symbols `(Observation × BoundaryStatus)`.  It does not
prove that a real proxy score is valid; it says that a frozen, injective score
with a supplied pointwise trace bound can feed the existing approximate surface
without weakening the zero-error exact-limit guard.
-/
theorem sameApproxCurrentSkeletonSurface_of_natPointwiseScoreTraceClose
    (score : Observation × BoundaryStatus -> Nat)
    (hinj : Function.Injective score)
    (eps : Nat)
    (target_eq : B.maintainedTarget = A.maintainedTarget)
    (htrace :
      forall burdenCount supportCount,
        TraceCloseness.natPointwiseClose eps
          (((I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount).map score)
          (((J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount).map score)) :
    I.SameApproxCurrentSkeletonSurface
      (TraceCloseness.natPointwiseMapped score hinj) eps J := by
  refine
    { source_factors := I.factorsThroughCurrentSkeleton
      target_factors := J.factorsThroughCurrentSkeleton
      target_eq := target_eq
      trace_close := ?_ }
  intro burdenCount supportCount
  exact htrace burdenCount supportCount

/--
Trace alignment only up to a finite burden/support horizon.

This is the exact counterpart of the bounded approximate surface below.  It is
the right zero-error target for a bounded-horizon approximate theorem: at zero
error we recover exact trace equality for the count pairs inside the horizon,
not for unbounded traces outside the theorem's scope.
-/
structure TraceAlignedUpTo
    (horizon : Nat)
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target}
    (J : CurrentInevitabilitySkeletonInterface B) : Prop where
  target_eq : B.maintainedTarget = A.maintainedTarget
  traceLogOfCounts_eq :
    forall burdenCount supportCount,
      burdenCount + supportCount <= horizon ->
        (I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount =
          (J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount

/-- Exact same-skeleton surface restricted to a finite count horizon. -/
def SameCurrentSkeletonSurfaceUpTo
    (horizon : Nat)
    {AlternativeState : Type x} {AlternativeAction : Type y}
    {B :
      ObservationallyRigorousCalc AlternativeState AlternativeAction
        Observation Target}
    (J : CurrentInevitabilitySkeletonInterface B) : Prop :=
  I.FactorsThroughCurrentSkeleton ∧
  J.FactorsThroughCurrentSkeleton ∧
  I.TraceAlignedUpTo horizon J

/--
Bounded-horizon approximate current skeleton surface.

The global surface above asks for one fixed error budget over all count pairs.
For additive drift `d > 0`, the derived budget grows with
`burdenCount + supportCount`, so the honest first public surface is bounded by
a finite horizon `H`.
-/
structure SameApproxCurrentSkeletonSurfaceUpTo
    (T : TraceCloseness Eps (Observation × BoundaryStatus))
    (eps : Eps) (horizon : Nat)
    (J : CurrentInevitabilitySkeletonInterface B) : Prop where
  source_factors : I.FactorsThroughCurrentSkeleton
  target_factors : J.FactorsThroughCurrentSkeleton
  target_eq : B.maintainedTarget = A.maintainedTarget
  trace_close :
    forall burdenCount supportCount,
      burdenCount + supportCount <= horizon ->
        T.close eps
          ((I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount)
          ((J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
            burdenCount supportCount)

/-- A global approximate surface restricts to every bounded horizon. -/
theorem sameApproxCurrentSkeletonSurfaceUpTo_of_sameApproxCurrentSkeletonSurface
    (horizon : Nat)
    (h : I.SameApproxCurrentSkeletonSurface T eps J) :
    I.SameApproxCurrentSkeletonSurfaceUpTo T eps horizon J := by
  refine
    { source_factors := h.source_factors
      target_factors := h.target_factors
      target_eq := h.target_eq
      trace_close := ?_ }
  intro burdenCount supportCount _hbound
  exact h.trace_close burdenCount supportCount

/-- Exact G1 embeds into every bounded approximate surface. -/
theorem sameApproxCurrentSkeletonSurfaceUpTo_of_sameCurrentSkeletonSurface
    (horizon : Nat)
    (h : I.SameCurrentSkeletonSurface J) :
    I.SameApproxCurrentSkeletonSurfaceUpTo T eps horizon J := by
  exact I.sameApproxCurrentSkeletonSurfaceUpTo_of_sameApproxCurrentSkeletonSurface
    T eps J horizon
    (I.sameApproxCurrentSkeletonSurface_of_sameCurrentSkeletonSurface T eps J h)

/--
At zero error, the bounded approximate surface recovers the bounded exact
current skeleton surface.
-/
theorem sameCurrentSkeletonSurfaceUpTo_of_sameApproxCurrentSkeletonSurfaceUpTo_zero
    (horizon : Nat)
    (h : I.SameApproxCurrentSkeletonSurfaceUpTo T T.zero horizon J) :
    I.SameCurrentSkeletonSurfaceUpTo horizon J := by
  refine ⟨h.source_factors, h.target_factors, ?_⟩
  refine
    { target_eq := h.target_eq
      traceLogOfCounts_eq := ?_ }
  intro burdenCount supportCount hbound
  exact T.exact_of_zero (h.trace_close burdenCount supportCount hbound)

/-- Zero-error bounded approximate and bounded exact surfaces are equivalent. -/
theorem sameApproxCurrentSkeletonSurfaceUpTo_zero_iff_sameCurrentSkeletonSurfaceUpTo
    (horizon : Nat) :
    I.SameApproxCurrentSkeletonSurfaceUpTo T T.zero horizon J ↔
      I.SameCurrentSkeletonSurfaceUpTo horizon J := by
  constructor
  · intro h
    exact I.sameCurrentSkeletonSurfaceUpTo_of_sameApproxCurrentSkeletonSurfaceUpTo_zero
      T J horizon h
  · intro h
    rcases h with ⟨hI, hJ, haligned⟩
    refine
      { source_factors := hI
        target_factors := hJ
        target_eq := haligned.target_eq
        trace_close := ?_ }
    intro burdenCount supportCount hbound
    exact T.close_of_eq (haligned.traceLogOfCounts_eq
      burdenCount supportCount hbound)

/--
Monotonicity of the additive envelope in the trace length/horizon parameter.
-/
theorem natAdditiveEnvelope_mono_steps
    (eps d : Nat) {n m : Nat}
    (h : n <= m) :
    TraceCloseness.natAdditiveEnvelope eps d n <=
      TraceCloseness.natAdditiveEnvelope eps d m := by
  induction m generalizing n eps with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero h
      cases hn
      exact Nat.le_refl (TraceCloseness.natAdditiveEnvelope eps d 0)
  | succ m ih =>
      cases n with
      | zero =>
          exact TraceCloseness.natAdditiveEnvelope_start_le eps d (m + 1)
      | succ n =>
          have hnm : n <= m := Nat.succ_le_succ_iff.mp h
          exact ih (eps + d) hnm

/--
Count-dependent score-level trace bounds can be consumed by a bounded-horizon
surface.

Inside the horizon, the local budget
`natAdditiveEnvelope eps d (burdenCount + supportCount)` is monotone-bounded by
the global horizon budget `natAdditiveEnvelope eps d horizon`.
-/
theorem sameApproxCurrentSkeletonSurfaceUpTo_of_natPointwiseScoreTraceClose_boundedHorizon
    (score : Observation × BoundaryStatus -> Nat)
    (hinj : Function.Injective score)
    (eps d horizon : Nat)
    (target_eq : B.maintainedTarget = A.maintainedTarget)
    (htrace :
      forall burdenCount supportCount,
        burdenCount + supportCount <= horizon ->
          TraceCloseness.natPointwiseClose
            (TraceCloseness.natAdditiveEnvelope eps d
              (burdenCount + supportCount))
            (((I.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
              burdenCount supportCount).map score)
            (((J.mlSource.toObservedAdditiveCompositionSource).traceLogOfCounts
              burdenCount supportCount).map score)) :
    I.SameApproxCurrentSkeletonSurfaceUpTo
      (TraceCloseness.natPointwiseMapped score hinj)
      (TraceCloseness.natAdditiveEnvelope eps d horizon)
      horizon J := by
  refine
    { source_factors := I.factorsThroughCurrentSkeleton
      target_factors := J.factorsThroughCurrentSkeleton
      target_eq := target_eq
      trace_close := ?_ }
  intro burdenCount supportCount hbound
  exact
    TraceCloseness.natPointwiseClose_mono
      (natAdditiveEnvelope_mono_steps eps d hbound)
      (htrace burdenCount supportCount hbound)

/--
Generator-derived bounded-horizon approximate surface.

This is the bounded-horizon consumption theorem for additive trace drift: the
score-level trace bound is no longer supplied directly.  It is derived from the
actual generated `traceLogOfCounts`, replayed as an action-list stateful trace,
and then widened to the horizon budget.
-/
theorem sameApproxCurrentSkeletonSurfaceUpTo_of_actionList_additiveEnvelope
    (score : Observation × BoundaryStatus -> Nat)
    (hinj : Function.Injective score)
    (eps d horizon : Nat)
    (target_eq : B.maintainedTarget = A.maintainedTarget)
    (hinit :
      forall burdenCount supportCount,
        burdenCount + supportCount <= horizon ->
          TraceCloseness.natPointClose eps
            (TraceCloseness.actionListTraceEmit A.process score
              ((I.mlSource.toObservedAdditiveCompositionSource).initialState,
                compositionTrace
                  (I.mlSource.toObservedAdditiveCompositionSource).burdenAction
                  (I.mlSource.toObservedAdditiveCompositionSource).supportAction
                  burdenCount supportCount))
            (TraceCloseness.actionListTraceEmit B.process score
              ((J.mlSource.toObservedAdditiveCompositionSource).initialState,
                compositionTrace
                  (J.mlSource.toObservedAdditiveCompositionSource).burdenAction
                  (J.mlSource.toObservedAdditiveCompositionSource).supportAction
                  burdenCount supportCount)))
    (hstep :
      forall budget stateA stateB,
        TraceCloseness.natPointClose budget
          (TraceCloseness.actionListTraceEmit A.process score stateA)
          (TraceCloseness.actionListTraceEmit B.process score stateB) ->
          TraceCloseness.natPointClose (budget + d)
            (TraceCloseness.actionListTraceEmit A.process score
              (TraceCloseness.actionListTraceStep A.process stateA))
            (TraceCloseness.actionListTraceEmit B.process score
              (TraceCloseness.actionListTraceStep B.process stateB))) :
    I.SameApproxCurrentSkeletonSurfaceUpTo
      (TraceCloseness.natPointwiseMapped score hinj)
      (TraceCloseness.natAdditiveEnvelope eps d horizon)
      horizon J := by
  exact
    I.sameApproxCurrentSkeletonSurfaceUpTo_of_natPointwiseScoreTraceClose_boundedHorizon
      J score hinj eps d horizon target_eq
      (by
        intro burdenCount supportCount hbound
        exact
          TraceCloseness.natPointwiseClose_map_traceLogOfCounts_of_actionList_additiveEnvelope
            (I.mlSource.toObservedAdditiveCompositionSource)
            (J.mlSource.toObservedAdditiveCompositionSource)
            score burdenCount supportCount
            (hinit burdenCount supportCount hbound)
            hstep)

end CurrentInevitabilitySkeletonInterface

/-! ## Concrete finite witnesses for the bounded-horizon surface

This section is intentionally finite.  Its purpose is not empirical support.
The Boolean process is a minimal inhabitedness witness: it shows that the
bounded-horizon surface is not vacuous.  The finite drift process below is the
nondegenerate witness where a fixed budget can fail and the additive envelope is
actually consumed.
-/

namespace ApproxProxyConcreteWitness

/-- Lossless score for Boolean observations and all boundary statuses. -/
def boolStatusScore : Bool × BoundaryStatus -> Nat
  | (false, BoundaryStatus.viable) => 0
  | (true, BoundaryStatus.viable) => 1
  | (false, BoundaryStatus.stopped) => 2
  | (true, BoundaryStatus.stopped) => 3
  | (false, BoundaryStatus.collapsed) => 4
  | (true, BoundaryStatus.collapsed) => 5

/-- The Boolean/status score is injective, so zero score-error recovers traces. -/
theorem boolStatusScore_injective :
    Function.Injective boolStatusScore := by
  intro x y h
  cases x with
  | mk xb xs =>
      cases y with
      | mk yb ys =>
          cases xb <;> cases xs <;> cases yb <;> cases ys <;>
            first
            | rfl
            | cases h

/--
A minimal response-separated Boolean process.

The next state is the chosen action.  The boundary readout is constantly
viable; response separation is carried by the observable post-action Boolean.
-/
def boolSwitchProcess :
    ObservationalPersistenceProcess Bool Bool Bool where
  observe := fun s => s
  step := fun _s action => action
  readout := fun _s => BoundaryStatus.viable

/-- Observation-only Boolean calculation used by the concrete proxy witness. -/
def boolSwitchCalc :
    ObservationallyRigorousCalc Bool Bool Bool Unit where
  process := boolSwitchProcess
  maintainedTarget := ()
  maintains := fun _s _target => True
  viable_implies_maintained := by
    intro _s _h
    trivial

/-- The Boolean process is response-separated at one state by its two actions. -/
theorem boolSwitchCalc_responseSeparated :
    boolSwitchCalc.ResponseSeparated := by
  refine ⟨false, false, true, ?_⟩
  intro h
  cases h

/-- Every Boolean action-list emission used by the witness has score at most 1. -/
theorem boolSwitch_actionListEmit_le_one
    (state : Bool × List Bool) :
    TraceCloseness.actionListTraceEmit boolSwitchProcess boolStatusScore
      state <= 1 := by
  cases state with
  | mk s actions =>
      cases actions with
      | nil =>
          change 0 <= 1
          exact Nat.zero_le 1
      | cons action actions =>
          cases action
          · change 0 <= 1
            exact Nat.zero_le 1
          · change 1 <= 1
            exact Nat.le_refl 1

/-- Any two natural numbers below one are one-close. -/
theorem natPointClose_one_of_le_one
    {a b : Nat} (ha : a <= 1) (hb : b <= 1) :
    TraceCloseness.natPointClose 1 a b :=
  ⟨Nat.le_trans ha (Nat.succ_le_succ (Nat.zero_le b)),
    Nat.le_trans hb (Nat.succ_le_succ (Nat.zero_le a))⟩

/--
Every emitted score of the Boolean process is either `0` or `1`; hence any two
action-list emissions are one unit apart at most.
-/
theorem boolSwitch_actionListEmit_pointClose_one
    (stateA stateB : Bool × List Bool) :
    TraceCloseness.natPointClose 1
      (TraceCloseness.actionListTraceEmit boolSwitchProcess boolStatusScore
        stateA)
      (TraceCloseness.actionListTraceEmit boolSwitchProcess boolStatusScore
        stateB) := by
  exact
    natPointClose_one_of_le_one
      (boolSwitch_actionListEmit_le_one stateA)
      (boolSwitch_actionListEmit_le_one stateB)

/--
Boolean emissions are always within one unit, so they are within any successor
budget.  This keeps the minimal bounded-surface witness inhabited; the
nondegenerate drift witness below is where the additive envelope carries load.
-/
theorem boolSwitch_actionListEmit_pointClose_succ
    (budget : Nat) (stateA stateB : Bool × List Bool) :
    TraceCloseness.natPointClose (budget + 1)
      (TraceCloseness.actionListTraceEmit boolSwitchProcess boolStatusScore
        stateA)
      (TraceCloseness.actionListTraceEmit boolSwitchProcess boolStatusScore
        stateB) := by
  exact
    TraceCloseness.natPointClose_mono
      (Nat.le_add_left 1 budget)
      (boolSwitch_actionListEmit_pointClose_one stateA stateB)

/--
Concrete bounded-horizon approximate G1 surface for the Boolean process.

This is the minimal process-level use of the abstract bounded theorem: the
interfaces are obtained from response separation, the score map is injective,
and the `hinit`/`hstep` obligations are consistent.  It is an inhabitedness
witness, not the nondegenerate drift example and not a claim that any empirical
proxy is valid.
-/
theorem exists_boolSwitch_boundedHorizonApproxSurface
    (horizon : Nat) :
    ∃ I J : CurrentInevitabilitySkeletonInterface boolSwitchCalc,
      I.SameApproxCurrentSkeletonSurfaceUpTo
        (TraceCloseness.natPointwiseMapped
          boolStatusScore boolStatusScore_injective)
        (TraceCloseness.natAdditiveEnvelope 1 1 horizon)
        horizon J := by
  rcases boolSwitchCalc.nonempty_currentInevitabilitySkeletonInterface
      boolSwitchCalc_responseSeparated with ⟨I⟩
  rcases boolSwitchCalc.nonempty_currentInevitabilitySkeletonInterface
      boolSwitchCalc_responseSeparated with ⟨J⟩
  refine ⟨I, J, ?_⟩
  exact
    I.sameApproxCurrentSkeletonSurfaceUpTo_of_actionList_additiveEnvelope
      J boolStatusScore boolStatusScore_injective 1 1 horizon rfl
      (by
        intro burdenCount supportCount _hbound
        exact boolSwitch_actionListEmit_pointClose_one _ _)
      (by
        intro budget stateA stateB _hclose
        exact boolSwitch_actionListEmit_pointClose_succ budget _ _)

/-- A nonzero finite-horizon instance, to keep the witness from being `H = 0`. -/
theorem exists_boolSwitch_horizon_three_approxSurface :
    ∃ I J : CurrentInevitabilitySkeletonInterface boolSwitchCalc,
      I.SameApproxCurrentSkeletonSurfaceUpTo
        (TraceCloseness.natPointwiseMapped
          boolStatusScore boolStatusScore_injective)
        (TraceCloseness.natAdditiveEnvelope 1 1 3)
        3 J :=
  exists_boolSwitch_boundedHorizonApproxSurface 3

/-! ### Nondegenerate finite drift witness

The Boolean witness above only proves inhabitedness of the bounded surface.  In
the next witness the score range has three viable levels and the two interfaces
use different action channels, so a fixed one-step budget can fail while the
additive envelope succeeds.
-/

inductive DriftObs where
  | zero
  | one
  | two
deriving DecidableEq, Repr

inductive DriftAction where
  | stay
  | up
deriving DecidableEq, Repr

def driftObsScore : DriftObs -> Nat
  | DriftObs.zero => 0
  | DriftObs.one => 1
  | DriftObs.two => 2

def driftStepObs : DriftObs -> DriftAction -> DriftObs
  | DriftObs.zero, DriftAction.stay => DriftObs.zero
  | DriftObs.zero, DriftAction.up => DriftObs.one
  | DriftObs.one, DriftAction.stay => DriftObs.one
  | DriftObs.one, DriftAction.up => DriftObs.two
  | DriftObs.two, _ => DriftObs.two

/-- Lossless score for the finite drift observation and all boundary statuses. -/
def driftStatusScore : DriftObs × BoundaryStatus -> Nat
  | (DriftObs.zero, BoundaryStatus.viable) => 0
  | (DriftObs.one, BoundaryStatus.viable) => 1
  | (DriftObs.two, BoundaryStatus.viable) => 2
  | (DriftObs.zero, BoundaryStatus.stopped) => 3
  | (DriftObs.one, BoundaryStatus.stopped) => 4
  | (DriftObs.two, BoundaryStatus.stopped) => 5
  | (DriftObs.zero, BoundaryStatus.collapsed) => 6
  | (DriftObs.one, BoundaryStatus.collapsed) => 7
  | (DriftObs.two, BoundaryStatus.collapsed) => 8

theorem driftStatusScore_injective :
    Function.Injective driftStatusScore := by
  intro x y h
  cases x with
  | mk xo xs =>
      cases y with
      | mk yo ys =>
          cases xo <;> cases xs <;> cases yo <;> cases ys <;>
            first
            | rfl
            | cases h

/--
Finite clamped drift process.

`up` can increase the observed state by one until saturation at `two`; `stay`
preserves the state.  The boundary readout is kept viable so this witness tests
trace drift, not boundary-margin licensing.
-/
def driftSwitchProcess :
    ObservationalPersistenceProcess DriftObs DriftAction DriftObs where
  observe := fun s => s
  step := driftStepObs
  readout := fun _s => BoundaryStatus.viable

def driftSwitchCalc :
    ObservationallyRigorousCalc DriftObs DriftAction DriftObs Unit where
  process := driftSwitchProcess
  maintainedTarget := ()
  maintains := fun _s _target => True
  viable_implies_maintained := by
    intro _s _h
    trivial

theorem driftSwitch_response_ne :
    driftSwitchProcess.response DriftObs.zero DriftAction.stay ≠
      driftSwitchProcess.response DriftObs.zero DriftAction.up := by
  intro h
  cases h

theorem driftSwitchCalc_responseSeparated :
    driftSwitchCalc.ResponseSeparated :=
  ⟨DriftObs.zero, DriftAction.stay, DriftAction.up, driftSwitch_response_ne⟩

def driftSourceSlowFast :
    ResponseSeparatedCompositionSource driftSwitchProcess where
  initialState := DriftObs.zero
  burdenAction := DriftAction.stay
  supportAction := DriftAction.up
  burdenUnit := 1
  supportUnit := 1
  burdenUnit_pos := by decide
  supportUnit_pos := by decide
  response_ne := driftSwitch_response_ne

def driftSourceFastSlow :
    ResponseSeparatedCompositionSource driftSwitchProcess where
  initialState := DriftObs.zero
  burdenAction := DriftAction.up
  supportAction := DriftAction.stay
  burdenUnit := 1
  supportUnit := 1
  burdenUnit_pos := by decide
  supportUnit_pos := by decide
  response_ne := by
    intro h
    exact driftSwitch_response_ne h.symm

def driftInterfaceSlowFast :
    CurrentInevitabilitySkeletonInterface driftSwitchCalc where
  core := driftSwitchCalc.coreInterface
  viable_agrees := by
    intro s
    exact driftSwitchCalc.core_inducedViableState_iff s
  nonCollapse :=
    driftSwitchCalc.nonCollapse_of_responseSeparated
      driftSwitchCalc_responseSeparated
  mlSource := driftSourceSlowFast
  mlSeparation :=
    ScopedMLSeparation.responseSeparated_forces_scopedAdditiveMLSeparation
      driftSourceSlowFast

def driftInterfaceFastSlow :
    CurrentInevitabilitySkeletonInterface driftSwitchCalc where
  core := driftSwitchCalc.coreInterface
  viable_agrees := by
    intro s
    exact driftSwitchCalc.core_inducedViableState_iff s
  nonCollapse :=
    driftSwitchCalc.nonCollapse_of_responseSeparated
      driftSwitchCalc_responseSeparated
  mlSource := driftSourceFastSlow
  mlSeparation :=
    ScopedMLSeparation.responseSeparated_forces_scopedAdditiveMLSeparation
      driftSourceFastSlow

theorem driftSwitch_initial_emit_close_one
    (burdenCount supportCount : Nat) :
    TraceCloseness.natPointClose 1
      (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
        (DriftObs.zero,
          compositionTrace DriftAction.stay DriftAction.up
            burdenCount supportCount))
      (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
        (DriftObs.zero,
          compositionTrace DriftAction.up DriftAction.stay
            burdenCount supportCount)) := by
  cases burdenCount with
  | zero =>
      cases supportCount with
      | zero =>
          change TraceCloseness.natPointClose 1 0 0
          exact ⟨by decide, by decide⟩
      | succ supportCount =>
          change TraceCloseness.natPointClose 1 1 0
          exact ⟨by decide, by decide⟩
  | succ burdenCount =>
      change TraceCloseness.natPointClose 1 0 1
      exact ⟨by decide, by decide⟩

theorem natPointClose_succ_of_monotone_step
    {budget x y x' y' : Nat}
    (h : TraceCloseness.natPointClose budget x y)
    (hxlo : x <= x') (hxhi : x' <= x + 1)
    (hylo : y <= y') (hyhi : y' <= y + 1) :
    TraceCloseness.natPointClose (budget + 1) x' y' := by
  constructor
  · have hx_to_y : x + 1 <= y + (budget + 1) := by
      simpa [Nat.add_assoc] using Nat.succ_le_succ h.1
    have hy_mono : y + (budget + 1) <= y' + (budget + 1) :=
      Nat.add_le_add_right hylo (budget + 1)
    exact Nat.le_trans (Nat.le_trans hxhi hx_to_y) hy_mono
  · have hy_to_x : y + 1 <= x + (budget + 1) := by
      simpa [Nat.add_assoc] using Nat.succ_le_succ h.2
    have hx_mono : x + (budget + 1) <= x' + (budget + 1) :=
      Nat.add_le_add_right hxlo (budget + 1)
    exact Nat.le_trans (Nat.le_trans hyhi hy_to_x) hx_mono

theorem driftStatusScore_next_between
    (s : DriftObs) (action next : DriftAction) :
    let current :=
      driftStatusScore (driftStepObs s action, BoundaryStatus.viable)
    let nextScore :=
      driftStatusScore
        (driftStepObs (driftStepObs s action) next,
          BoundaryStatus.viable)
    current <= nextScore ∧ nextScore <= current + 1 := by
  cases s <;> cases action <;> cases next <;>
    exact ⟨by decide, by decide⟩

theorem driftSwitch_oneStep_score_close_succ
    (budget : Nat)
    (sA sB : DriftObs)
    (actionA actionB nextA nextB : DriftAction)
    (hclose :
      TraceCloseness.natPointClose budget
        (driftStatusScore (driftStepObs sA actionA, BoundaryStatus.viable))
        (driftStatusScore (driftStepObs sB actionB, BoundaryStatus.viable))) :
    TraceCloseness.natPointClose (budget + 1)
      (driftStatusScore
        (driftStepObs (driftStepObs sA actionA) nextA,
          BoundaryStatus.viable))
      (driftStatusScore
        (driftStepObs (driftStepObs sB actionB) nextB,
          BoundaryStatus.viable)) := by
  have hA := driftStatusScore_next_between sA actionA nextA
  have hB := driftStatusScore_next_between sB actionB nextB
  exact natPointClose_succ_of_monotone_step hclose hA.1 hA.2 hB.1 hB.2

theorem driftSwitch_lengthAligned_step_close
    (budget : Nat)
    (stateA stateB : DriftObs × List DriftAction)
    (hlen : stateA.2.length = stateB.2.length)
    (hclose :
      TraceCloseness.natPointClose budget
        (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
          stateA)
        (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
          stateB)) :
    TraceCloseness.natPointClose (budget + 1)
      (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
        (TraceCloseness.actionListTraceStep driftSwitchProcess stateA))
      (TraceCloseness.actionListTraceEmit driftSwitchProcess driftStatusScore
        (TraceCloseness.actionListTraceStep driftSwitchProcess stateB)) := by
  cases stateA with
  | mk sA actionsA =>
      cases stateB with
      | mk sB actionsB =>
          cases actionsA with
          | nil =>
              cases actionsB with
              | nil =>
                  change TraceCloseness.natPointClose (budget + 1) 0 0
                  exact ⟨Nat.zero_le _, Nat.zero_le _⟩
              | cons actionB tailB =>
                  cases hlen
          | cons actionA tailA =>
              cases actionsB with
              | nil =>
                  cases hlen
              | cons actionB tailB =>
                  have htailLen : tailA.length = tailB.length :=
                    Nat.succ.inj hlen
                  cases tailA with
                  | nil =>
                      cases tailB with
                      | nil =>
                          change TraceCloseness.natPointClose
                            (budget + 1) 0 0
                          exact ⟨Nat.zero_le _, Nat.zero_le _⟩
                      | cons headB tailB =>
                          cases htailLen
                  | cons headA tailA =>
                      cases tailB with
                      | nil =>
                          cases htailLen
                      | cons headB tailB =>
                          apply driftSwitch_oneStep_score_close_succ
                          simpa [TraceCloseness.actionListTraceEmit,
                            driftSwitchProcess,
                            ObservationalPersistenceProcess.response]
                            using hclose

theorem driftSwitch_traceLogOfCounts_close_additiveEnvelope
    (burdenCount supportCount : Nat) :
    TraceCloseness.natPointwiseClose
      (TraceCloseness.natAdditiveEnvelope 1 1 (burdenCount + supportCount))
      (((driftSourceSlowFast.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount).map driftStatusScore)
      (((driftSourceFastSlow.toObservedAdditiveCompositionSource).traceLogOfCounts
        burdenCount supportCount).map driftStatusScore) := by
  exact
    TraceCloseness.natPointwiseClose_map_traceLogOfCounts_of_actionList_additiveEnvelope_aligned
      driftSourceSlowFast.toObservedAdditiveCompositionSource
      driftSourceFastSlow.toObservedAdditiveCompositionSource
      driftStatusScore burdenCount supportCount
      (driftSwitch_initial_emit_close_one burdenCount supportCount)
      driftSwitch_lengthAligned_step_close

/--
Nondegenerate concrete bounded-horizon surface.

The two interfaces use opposite action-channel assignments.  The first burden
steps are therefore slow on the source side and fast on the target side, so the
local one-step `+1` drift bound is doing work.  A fixed budget fails below.
-/
theorem driftSwitch_boundedHorizonApproxSurface
    (horizon : Nat) :
    driftInterfaceSlowFast.SameApproxCurrentSkeletonSurfaceUpTo
      (TraceCloseness.natPointwiseMapped
        driftStatusScore driftStatusScore_injective)
      (TraceCloseness.natAdditiveEnvelope 1 1 horizon)
      horizon driftInterfaceFastSlow := by
  exact
    driftInterfaceSlowFast
      |>.sameApproxCurrentSkeletonSurfaceUpTo_of_natPointwiseScoreTraceClose_boundedHorizon
        driftInterfaceFastSlow driftStatusScore driftStatusScore_injective
        1 1 horizon rfl
        (by
          intro burdenCount supportCount _hbound
          exact driftSwitch_traceLogOfCounts_close_additiveEnvelope
            burdenCount supportCount)

theorem driftSwitch_horizon_three_approxSurface :
    driftInterfaceSlowFast.SameApproxCurrentSkeletonSurfaceUpTo
      (TraceCloseness.natPointwiseMapped
        driftStatusScore driftStatusScore_injective)
      (TraceCloseness.natAdditiveEnvelope 1 1 3)
      3 driftInterfaceFastSlow :=
  driftSwitch_boundedHorizonApproxSurface 3

/--
Red test: the same concrete process-level pair is not handled by a fixed
one-unit budget.  The additive envelope is needed once the fast side takes two
`up` burden steps while the slow side stays.
-/
theorem not_driftSwitch_fixedBudget_one_traceLogOfCounts :
    ¬ TraceCloseness.natPointwiseClose 1
      (((driftSourceSlowFast.toObservedAdditiveCompositionSource).traceLogOfCounts
        2 0).map driftStatusScore)
      (((driftSourceFastSlow.toObservedAdditiveCompositionSource).traceLogOfCounts
        2 0).map driftStatusScore) := by
  intro h
  have htail : TraceCloseness.natPointwiseClose 1 [0] [2] := h.2
  have hbad : 2 <= 1 := htail.1.2
  exact Nat.not_succ_le_self 1 hbad

end ApproxProxyConcreteWitness

end Persistence.StructuralPersistence
