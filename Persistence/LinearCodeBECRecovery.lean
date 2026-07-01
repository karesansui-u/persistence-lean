import Persistence.BinaryPrefixEscapePMF
import Persistence.LinearCodeBECConcentrationBoundary
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear-Code BEC Recovery Core

This module records the finite linear-algebra core behind BEC erasure recovery.

For a fixed erased-column family `cols : Fin e -> (Fin r -> ZMod 2)`, the
erasure syndrome map sends erased-bit coefficients to the corresponding
syndrome contribution.  Unique recovery of the erased coordinates is represented
by this map having trivial kernel.  This is equivalent to linear independence
of the erased columns, and therefore to the negation of the usual rank-failure
event.

This is not a BEC probability theorem, not a decoding algorithm, not a capacity
theorem, and not Shannon achievability.  It is the deterministic linear-algebra
cover that later finite-block readouts can consume.
-/

namespace Persistence.LinearCodeBECRecovery

open Persistence.BinaryPrefixEscapePMF

noncomputable section

/-- Syndrome contribution map for a fixed erased-column family.

The domain coefficients are the erased coordinates; the codomain is the row
space of parity checks. -/
def erasureSyndromeMap {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) :
    (Fin e → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
  LinearMap.lsum (ZMod 2) (fun _ : Fin e => ZMod 2) ℕ
    fun i => LinearMap.id.smulRight (cols i)

/-- Unique erased-coordinate recovery: the syndrome map has trivial kernel. -/
def uniqueErasureRecovery {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) : Prop :=
  LinearMap.ker (erasureSyndromeMap cols) = ⊥

/-- Ambiguous erased-coordinate recovery: a nonzero erased-coordinate pattern
has zero syndrome. -/
def ambiguousErasureRecovery {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) : Prop :=
  ¬ uniqueErasureRecovery cols

/-- Ambiguous recovery is the existence of a nonzero erased-coordinate pattern
with zero syndrome contribution.

This is the operational no-uniqueness witness: two erased-coordinate candidates
that differ by such a nonzero vector have the same syndrome contribution. -/
theorem ambiguousErasureRecovery_iff_exists_nonzero_kernel {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) :
    ambiguousErasureRecovery cols ↔
      ∃ x : Fin e → ZMod 2, x ≠ 0 ∧ erasureSyndromeMap cols x = 0 := by
  unfold ambiguousErasureRecovery uniqueErasureRecovery
  change LinearMap.ker (erasureSyndromeMap cols) ≠ ⊥ ↔
    ∃ x : Fin e → ZMod 2, x ≠ 0 ∧ erasureSyndromeMap cols x = 0
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hxker, hxne⟩
    exact ⟨x, hxne, by simpa [LinearMap.mem_ker] using hxker⟩
  · rintro ⟨x, hxne, hxzero⟩
    exact ⟨x, by simpa [LinearMap.mem_ker] using hxzero, hxne⟩

/-- The syndrome-map kernel criterion is exactly linear independence of the
erased columns. -/
theorem uniqueErasureRecovery_iff_linearIndependent {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) :
    uniqueErasureRecovery cols ↔ LinearIndependent (ZMod 2) cols := by
  unfold uniqueErasureRecovery erasureSyndromeMap
  exact (Fintype.linearIndependent_iff' (R := ZMod 2) (v := cols)).symm

/-- Ambiguous erasure recovery is exactly failure of linear independence. -/
theorem ambiguousErasureRecovery_iff_not_linearIndependent {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) :
    ambiguousErasureRecovery cols ↔ ¬ LinearIndependent (ZMod 2) cols := by
  unfold ambiguousErasureRecovery
  exact not_congr (uniqueErasureRecovery_iff_linearIndependent cols)

/-- Ambiguous erasure recovery is exactly the finite rank-failure event for
the erased columns. -/
theorem ambiguousErasureRecovery_iff_rankFailure {r e : ℕ}
    (cols : Fin e → (Fin r → ZMod 2)) :
    ambiguousErasureRecovery cols ↔
      (Set.range cols).finrank (ZMod 2) ≠ e := by
  rw [ambiguousErasureRecovery_iff_not_linearIndependent]
  exact not_congr (finrank_span_eq_length_iff_linearIndependent cols).symm

/-- Forward cover form consumed by finite-block readouts: BEC ambiguity implies
the rank-failure event for the erased columns. -/
theorem rankFailure_of_ambiguousErasureRecovery {r e : ℕ}
    {cols : Fin e → (Fin r → ZMod 2)}
    (h : ambiguousErasureRecovery cols) :
    (Set.range cols).finrank (ZMod 2) ≠ e :=
  (ambiguousErasureRecovery_iff_rankFailure cols).mp h

/-- Conversely, rank failure gives ambiguous erasure recovery. -/
theorem ambiguousErasureRecovery_of_rankFailure {r e : ℕ}
    {cols : Fin e → (Fin r → ZMod 2)}
    (h : (Set.range cols).finrank (ZMod 2) ≠ e) :
    ambiguousErasureRecovery cols :=
  (ambiguousErasureRecovery_iff_rankFailure cols).mpr h

/-! ## Indexed erased-column families -/

/-- Syndrome contribution map for an arbitrary finite erased-coordinate index
type.

The `Fin e` version above is convenient for finite-block rank envelopes.  This
indexed version lets concrete erasure patterns use their natural subtype of
erased coordinates before any reindexing to `Fin`. -/
def erasureSyndromeMapIndexed {r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) :
    (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
  LinearMap.lsum (ZMod 2) (fun _ : ι => ZMod 2) ℕ
    fun i => LinearMap.id.smulRight (cols i)

/-- Indexed unique erased-coordinate recovery: the indexed syndrome map has
trivial kernel. -/
def uniqueErasureRecoveryIndexed {r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) : Prop :=
  LinearMap.ker (erasureSyndromeMapIndexed cols) = ⊥

/-- Indexed ambiguous erased-coordinate recovery. -/
def ambiguousErasureRecoveryIndexed {r : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) : Prop :=
  ¬ uniqueErasureRecoveryIndexed cols

/-- Indexed ambiguity is the existence of a nonzero erased-coordinate pattern
with zero syndrome contribution. -/
theorem ambiguousErasureRecoveryIndexed_iff_exists_nonzero_kernel {r : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) :
    ambiguousErasureRecoveryIndexed cols ↔
      ∃ x : ι → ZMod 2, x ≠ 0 ∧ erasureSyndromeMapIndexed cols x = 0 := by
  unfold ambiguousErasureRecoveryIndexed uniqueErasureRecoveryIndexed
  change LinearMap.ker (erasureSyndromeMapIndexed cols) ≠ ⊥ ↔
    ∃ x : ι → ZMod 2, x ≠ 0 ∧ erasureSyndromeMapIndexed cols x = 0
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, hxker, hxne⟩
    exact ⟨x, hxne, by simpa [LinearMap.mem_ker] using hxker⟩
  · rintro ⟨x, hxne, hxzero⟩
    exact ⟨x, by simpa [LinearMap.mem_ker] using hxzero, hxne⟩

/-- The indexed syndrome-map kernel criterion is linear independence of the
indexed erased columns. -/
theorem uniqueErasureRecoveryIndexed_iff_linearIndependent {r : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) :
    uniqueErasureRecoveryIndexed cols ↔ LinearIndependent (ZMod 2) cols := by
  unfold uniqueErasureRecoveryIndexed erasureSyndromeMapIndexed
  exact (Fintype.linearIndependent_iff' (R := ZMod 2) (v := cols)).symm

/-- Indexed ambiguous erasure recovery is failure of linear independence. -/
theorem ambiguousErasureRecoveryIndexed_iff_not_linearIndependent {r : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) :
    ambiguousErasureRecoveryIndexed cols ↔ ¬ LinearIndependent (ZMod 2) cols := by
  unfold ambiguousErasureRecoveryIndexed
  exact not_congr (uniqueErasureRecoveryIndexed_iff_linearIndependent cols)

/-- Rank/cardinality form of linear independence for an arbitrary finite
erased-coordinate index type. -/
theorem finrank_span_eq_card_iff_linearIndependent {r : ℕ}
    {ι : Type*} [Fintype ι]
    (cols : ι → (Fin r → ZMod 2)) :
    (Set.range cols).finrank (ZMod 2) = Fintype.card ι ↔
      LinearIndependent (ZMod 2) cols := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [eq_comm]

/-- Indexed ambiguous recovery is exactly rank failure of the indexed erased
columns. -/
theorem ambiguousErasureRecoveryIndexed_iff_rankFailure {r : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cols : ι → (Fin r → ZMod 2)) :
    ambiguousErasureRecoveryIndexed cols ↔
      (Set.range cols).finrank (ZMod 2) ≠ Fintype.card ι := by
  rw [ambiguousErasureRecoveryIndexed_iff_not_linearIndependent]
  exact not_congr (finrank_span_eq_card_iff_linearIndependent cols).symm

/-! ## Boolean erasure-pattern column selection -/

/-- The erased parity-check columns selected by a fixed Boolean erasure
pattern.

The domain is the subtype of erased coordinates.  This is deterministic
bookkeeping from a concrete erasure pattern to the erased-column family consumed
by the rank/ambiguity theorems.  It is not a BEC law or pushforward theorem. -/
def erasedColumnsOfBoolPattern {n r : ℕ}
    (H : Fin n → (Fin r → ZMod 2)) (ω : Fin n → Bool) :
    {i : Fin n // ω i = true} → (Fin r → ZMod 2) :=
  fun i => H i.1

/-- The erased-coordinate subtype has cardinality `boolErasureCount`.

This connects the subtype index set used by `erasedColumnsOfBoolPattern` with
the Boolean support count used by the row-slack tail layer. -/
theorem card_erasedIndexSubtype_eq_boolErasureCount {n : ℕ}
    (ω : Fin n → Bool) :
    Fintype.card {i : Fin n // ω i = true} =
      Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount ω := by
  unfold Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
  rw [Fintype.card_subtype]

/-- For the erased columns selected by a fixed Boolean erasure pattern,
ambiguous recovery is exactly rank failure on that selected column family.

This is still deterministic: it does not say how the pattern was sampled, and
it does not push a BEC law through the selected-column map. -/
theorem ambiguousErasureRecoveryIndexed_erasedColumnsOfBoolPattern_iff_rankFailure
    {n r : ℕ} (H : Fin n → (Fin r → ZMod 2)) (ω : Fin n → Bool) :
    ambiguousErasureRecoveryIndexed (erasedColumnsOfBoolPattern H ω) ↔
      (Set.range (erasedColumnsOfBoolPattern H ω)).finrank (ZMod 2) ≠
        Fintype.card {i : Fin n // ω i = true} :=
  ambiguousErasureRecoveryIndexed_iff_rankFailure (erasedColumnsOfBoolPattern H ω)

/-- Boolean-count form of
`ambiguousErasureRecoveryIndexed_erasedColumnsOfBoolPattern_iff_rankFailure`.

The right-hand side uses the same `boolErasureCount` appearing in the BEC
row-slack layer. -/
theorem ambiguousErasureRecoveryIndexed_erasedColumnsOfBoolPattern_iff_rankFailure_boolCount
    {n r : ℕ} (H : Fin n → (Fin r → ZMod 2)) (ω : Fin n → Bool) :
    ambiguousErasureRecoveryIndexed (erasedColumnsOfBoolPattern H ω) ↔
      (Set.range (erasedColumnsOfBoolPattern H ω)).finrank (ZMod 2) ≠
        Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount ω := by
  simpa [card_erasedIndexSubtype_eq_boolErasureCount ω] using
    (ambiguousErasureRecoveryIndexed_erasedColumnsOfBoolPattern_iff_rankFailure H ω)

/-! ## Deterministic selected-column pushforward -/

/-- A selected erased-column sample packages an erasure pattern together with
the column family indexed by its erased-coordinate subtype. -/
def SelectedErasedColumnsSample (n r : ℕ) : Type :=
  Sigma fun ω : Fin n → Bool =>
    {i : Fin n // ω i = true} → (Fin r → ZMod 2)

noncomputable instance instFintypeSelectedErasedColumnsSample {n r : ℕ} :
    Fintype (SelectedErasedColumnsSample n r) := by
  unfold SelectedErasedColumnsSample
  infer_instance

/-- Deterministically push a full Boolean-erasure/full-column sample to the
selected erased-column sample consumed by the indexed recovery core.

This is a map of samples only.  It does not assert a Bernoulli/BEC law, a
random-code model, or a rank probability bound. -/
def selectedErasedColumnsSample {n r : ℕ}
    (x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2))) :
    SelectedErasedColumnsSample n r :=
  ⟨x.1, erasedColumnsOfBoolPattern x.2 x.1⟩

/-- PMF pushforward along `selectedErasedColumnsSample`.

The source PMF is arbitrary; this is only the deterministic selected-column
pushforward, not a BEC channel law. -/
def selectedErasedColumnsPMF {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2)))) :
    PMF (SelectedErasedColumnsSample n r) :=
  P.map selectedErasedColumnsSample

/-- Ambiguity event on a selected erased-column sample. -/
def selectedAmbiguousRecovery {n r : ℕ}
    (s : SelectedErasedColumnsSample n r) : Prop :=
  ambiguousErasureRecoveryIndexed s.2

/-- Rank-failure event on a selected erased-column sample, with the selected
index cardinality read as `boolErasureCount`. -/
def selectedRankFailure {n r : ℕ}
    (s : SelectedErasedColumnsSample n r) : Prop :=
  (Set.range s.2).finrank (ZMod 2) ≠
    Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount s.1

/-- On selected erased-column samples, ambiguity is exactly selected-column
rank failure. -/
theorem selectedAmbiguousRecovery_iff_selectedRankFailure {n r : ℕ}
    (s : SelectedErasedColumnsSample n r) :
    selectedAmbiguousRecovery s ↔ selectedRankFailure s := by
  rcases s with ⟨ω, cols⟩
  unfold selectedAmbiguousRecovery selectedRankFailure
  simpa [card_erasedIndexSubtype_eq_boolErasureCount ω] using
    (ambiguousErasureRecoveryIndexed_iff_rankFailure cols)

/-- The selected-column pushforward preserves the ambiguity event by definition
of `PMF.map`.

This is the first sampled-space bridge for selected columns, but only as a
deterministic pushforward from an already supplied joint PMF.  It does not
derive the joint law or any rank/tail envelope. -/
theorem selectedErasedColumnsPMF_ambiguous_toOuterMeasure_eq
    {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2)))) :
    (selectedErasedColumnsPMF P).toOuterMeasure
        {s : SelectedErasedColumnsSample n r | selectedAmbiguousRecovery s} =
      P.toOuterMeasure
        {x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) |
          ambiguousErasureRecoveryIndexed
            (erasedColumnsOfBoolPattern x.2 x.1)} := by
  unfold selectedErasedColumnsPMF selectedErasedColumnsSample
    selectedAmbiguousRecovery
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- Pushforward form of the selected rank-failure event. -/
theorem selectedErasedColumnsPMF_rankFailure_toOuterMeasure_eq
    {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2)))) :
    (selectedErasedColumnsPMF P).toOuterMeasure
        {s : SelectedErasedColumnsSample n r | selectedRankFailure s} =
      P.toOuterMeasure
        {x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) |
          (Set.range (erasedColumnsOfBoolPattern x.2 x.1)).finrank
              (ZMod 2) ≠
            Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
              x.1} := by
  unfold selectedErasedColumnsPMF selectedErasedColumnsSample selectedRankFailure
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-! ## Real event-probability readouts for selected-column pushforward -/

/-- Real-valued `eventProb` form of the selected ambiguity pushforward.

This is the same deterministic `PMF.map` bookkeeping as
`selectedErasedColumnsPMF_ambiguous_toOuterMeasure_eq`, expressed in the
finite real-valued event-probability interface consumed by the finite-block
repair-affordability layer.  It still assumes an arbitrary supplied joint PMF;
it does not generate a BEC law or a rank envelope. -/
theorem selectedErasedColumnsPMF_ambiguous_eventProb_eq
    {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2))))
    [DecidablePred
      (fun s : SelectedErasedColumnsSample n r => selectedAmbiguousRecovery s)]
    [DecidablePred
      (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
        ambiguousErasureRecoveryIndexed
          (erasedColumnsOfBoolPattern x.2 x.1))] :
    Persistence.FiniteCSPFirstMomentCollapseBound.eventProb
        (selectedErasedColumnsPMF P) selectedAmbiguousRecovery =
      Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
          ambiguousErasureRecoveryIndexed
            (erasedColumnsOfBoolPattern x.2 x.1)) := by
  rw [finite_eventProb_eq_toOuterMeasure_toReal]
  rw [finite_eventProb_eq_toOuterMeasure_toReal]
  exact congrArg ENNReal.toReal
    (selectedErasedColumnsPMF_ambiguous_toOuterMeasure_eq P)

/-- Real-valued `eventProb` form of the selected rank-failure pushforward.

This keeps the selected-column rank event in the same finite event-probability
interface as the finite-block rank envelope.  It is still only a deterministic
pushforward from an already supplied joint PMF. -/
theorem selectedErasedColumnsPMF_rankFailure_eventProb_eq
    {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2))))
    [DecidablePred
      (fun s : SelectedErasedColumnsSample n r => selectedRankFailure s)]
    [DecidablePred
      (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
        (Set.range (erasedColumnsOfBoolPattern x.2 x.1)).finrank
            (ZMod 2) ≠
          Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
            x.1)] :
    Persistence.FiniteCSPFirstMomentCollapseBound.eventProb
        (selectedErasedColumnsPMF P) selectedRankFailure =
      Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
          (Set.range (erasedColumnsOfBoolPattern x.2 x.1)).finrank
              (ZMod 2) ≠
            Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
              x.1) := by
  rw [finite_eventProb_eq_toOuterMeasure_toReal]
  rw [finite_eventProb_eq_toOuterMeasure_toReal]
  exact congrArg ENNReal.toReal
    (selectedErasedColumnsPMF_rankFailure_toOuterMeasure_eq P)

/-- On the selected erased-column sample space, ambiguity and selected rank
failure have the same finite event probability.

This is the event-probability version of
`selectedAmbiguousRecovery_iff_selectedRankFailure`.  It is still deterministic
linear algebra on an already supplied PMF; no BEC law or random-code model is
introduced. -/
theorem selectedAmbiguousRecovery_eventProb_eq_selectedRankFailure
    {n r : ℕ}
    (P : PMF (SelectedErasedColumnsSample n r))
    [DecidablePred
      (fun s : SelectedErasedColumnsSample n r => selectedAmbiguousRecovery s)]
    [DecidablePred
      (fun s : SelectedErasedColumnsSample n r => selectedRankFailure s)] :
    Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        selectedAmbiguousRecovery =
      Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        selectedRankFailure := by
  classical
  unfold Persistence.FiniteCSPFirstMomentCollapseBound.eventProb
  refine Finset.sum_congr rfl ?_
  intro s _hs
  by_cases hAmb : selectedAmbiguousRecovery s
  · have hRank : selectedRankFailure s :=
      (selectedAmbiguousRecovery_iff_selectedRankFailure s).mp hAmb
    simp [hAmb, hRank]
  · have hRank : ¬ selectedRankFailure s := by
      intro h
      exact hAmb ((selectedAmbiguousRecovery_iff_selectedRankFailure s).mpr h)
    simp [hAmb, hRank]

/-- Joint-PMF event-probability equality for selected-column ambiguity and
selected-column rank failure.

This composes the deterministic `PMF.map` pushforward with the selected-sample
ambiguity/rank-failure equivalence.  The source PMF is arbitrary, so this does
not derive the joint BEC law, a selected-column rank envelope, or Shannon
achievability. -/
theorem selectedErasedColumnsPMF_jointAmbiguous_eventProb_eq_jointRankFailure
    {n r : ℕ}
    (P : PMF ((Fin n → Bool) × (Fin n → (Fin r → ZMod 2))))
    [DecidablePred
      (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
        ambiguousErasureRecoveryIndexed
          (erasedColumnsOfBoolPattern x.2 x.1))]
    [DecidablePred
      (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
        (Set.range (erasedColumnsOfBoolPattern x.2 x.1)).finrank
            (ZMod 2) ≠
          Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
            x.1)] :
    Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
          ambiguousErasureRecoveryIndexed
            (erasedColumnsOfBoolPattern x.2 x.1)) =
      Persistence.FiniteCSPFirstMomentCollapseBound.eventProb P
        (fun x : (Fin n → Bool) × (Fin n → (Fin r → ZMod 2)) =>
          (Set.range (erasedColumnsOfBoolPattern x.2 x.1)).finrank
              (ZMod 2) ≠
            Persistence.LinearCodeBECConcentrationBoundary.boolErasureCount
              x.1) := by
  classical
  rw [← selectedErasedColumnsPMF_ambiguous_eventProb_eq P]
  rw [selectedAmbiguousRecovery_eventProb_eq_selectedRankFailure
    (selectedErasedColumnsPMF P)]
  rw [selectedErasedColumnsPMF_rankFailure_eventProb_eq P]

end

end Persistence.LinearCodeBECRecovery
