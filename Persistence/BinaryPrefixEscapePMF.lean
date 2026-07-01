import Persistence.BinaryPrefixProcessState
import Persistence.BinaryFullRankEscapeProduct
import Persistence.BinarySpanEscapePMF
import Persistence.FiniteCSPFirstMomentCollapseBound
import Persistence.FiniteSequentialProductPMF
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Binary Prefix Escape PMF (one-step state event mass)

This module specializes the one-step span-escape PMF theorem to a certified
prefix state.

`BinaryPrefixProcessState` packages a deterministic state transition:
an escaping next column advances `PrefixState r k` to `PrefixState r (k+1)`.
This file first supplies the corresponding one-step finite-uniform PMF event
mass for the escape event of a *fixed* certified state.  It then uses the
generic IID recursive-event product skeleton to prove a finite random-matrix
full-column-rank readout for IID uniform binary columns.

## What this does not prove

This file proves the full-column-rank event mass and a row-slack-derived
rank-failure upper bound in the finite-block `hRank` shape.  It still does not
connect that readout to a coding construction, Shannon achievability theorem,
strong converse, or rate/capacity theorem.
-/

namespace Persistence.BinaryPrefixEscapePMF

open Persistence.FiniteUniformPMF
open Persistence.FiniteSequentialProductPMF
open Persistence.BinarySpanEscapeFraction
open Persistence.BinarySpanEscapePMF
open Persistence.BinaryFullRankEscapeProduct
open Persistence.BinaryPrefixProcessState
open Persistence.BinaryRankGrowth
open Persistence.FiniteCSPFirstMomentCollapseBound
open scoped BigOperators

noncomputable section

/-- The escape event attached to a certified prefix state.  Future probabilistic
process layers will use this as the one-step transition event. -/
def prefixEscapeEvent {r k : ℕ}
    (S : PrefixState r k) (w : Fin r → ZMod 2) : Prop :=
  w ∉ S.span

/-- For a fixed certified prefix state, the finite-uniform PMF mass of the
escape event is the span-escape fraction of its underlying prefix columns. -/
theorem prefixState_uniform_escape_toReal_eq_spanEscapeFraction {r k : ℕ}
    (S : PrefixState r k) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | prefixEscapeEvent S w}).toReal =
      spanEscapeFraction S.cols := by
  unfold prefixEscapeEvent
  simpa [PrefixState.span] using
    (uniformPMF_spanEscape_toReal_eq_spanEscapeFraction S.cols)

/-- `ENNReal` form of the fixed-state one-step escape mass.

For a certified rank-`k` prefix state, the uniform PMF mass of escaping its span
is the finite ratio `(2^r - 2^k) / 2^r` before converting to `Real`. -/
theorem prefixState_uniform_escape_toOuterMeasure_eq_escapeRatio {r k : ℕ}
    (S : PrefixState r k) :
    (uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | prefixEscapeEvent S w} =
      (escapeCount r k : ENNReal) / (ambientCount r : ENNReal) := by
  unfold prefixEscapeEvent
  simpa [PrefixState.span] using
    (uniformPMF_spanEscape_toOuterMeasure_eq_escapeRatio S.cols S.independent)

/-- For a fixed certified prefix state, the finite-uniform PMF mass of escaping
its span is the abstract escape fraction `escapeFraction r k`. -/
theorem prefixState_uniform_escape_toReal_eq_escapeFraction {r k : ℕ}
    (S : PrefixState r k) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | prefixEscapeEvent S w}).toReal =
      escapeFraction r k := by
  unfold prefixEscapeEvent
  simpa [PrefixState.span] using
    (uniformPMF_spanEscape_toReal_eq_escapeFraction S.cols S.independent)

/-- Combined one-step state readout: under the row-room condition `k ≤ r`, the
finite-uniform PMF mass of escaping the span of a certified rank-`k` prefix
state is `1 - 2^k / 2^r`. -/
theorem prefixState_uniform_escape_toReal_eq_one_sub_pow_ratio {r k : ℕ}
    (S : PrefixState r k) (hkr : k ≤ r) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | prefixEscapeEvent S w}).toReal =
      1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
  unfold prefixEscapeEvent
  simpa [PrefixState.span] using
    (uniformPMF_spanEscape_toReal_eq_one_sub_pow_ratio
      S.cols S.independent hkr)

/-- IID prefix one-step escape mass with a supplied fixed-rank state map.

Given a length-`n` prefix event `A` and a supplied map from each prefix to a
certified rank-`k` prefix state, the mass of the length-`n+1` event

* the length-`n` prefix satisfies `A`; and
* the fresh last sample escapes the supplied state for that prefix

is the prefix-event mass times the rank-`k` escape ratio.

This is the first arbitrary-prefix consumer of the generic IID one-step
conditional-mass rule.  The state map is still supplied; this is not yet a
random-prefix process, sampled-column independence theorem, random-matrix rank
theorem, or Shannon achievability theorem. -/
theorem iidSequencePMF_succ_prefixEscape_toOuterMeasure_eq_mul_escapeRatio
    {r n k : ℕ}
    (A : (Fin n → (Fin r → ZMod 2)) → Prop)
    (S : (Fin n → (Fin r → ZMod 2)) → PrefixState r k) :
    (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) (n + 1)).toOuterMeasure
        {xs : Fin (n + 1) → (Fin r → ZMod 2) |
          A (Fin.init xs) ∧
            prefixEscapeEvent (S (Fin.init xs)) (xs (Fin.last n))} =
      (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) n).toOuterMeasure
          {pref : Fin n → (Fin r → ZMod 2) | A pref} *
        ((escapeCount r k : ENNReal) / (ambientCount r : ENNReal)) := by
  exact iidSequencePMF_succ_dependentEvent_toOuterMeasure_eq_mul
    (p := uniformPMF (Fin r → ZMod 2))
    (n := n)
    (A := A)
    (B := fun pref w => prefixEscapeEvent (S pref) w)
    (c := (escapeCount r k : ENNReal) / (ambientCount r : ENNReal))
    (by
      intro pref _hpref
      exact prefixState_uniform_escape_toOuterMeasure_eq_escapeRatio (S pref))

/-- Real-valued form of
`iidSequencePMF_succ_prefixEscape_toOuterMeasure_eq_mul_escapeRatio`. -/
theorem iidSequencePMF_succ_prefixEscape_toReal_eq_mul_escapeFraction
    {r n k : ℕ}
    (A : (Fin n → (Fin r → ZMod 2)) → Prop)
    (S : (Fin n → (Fin r → ZMod 2)) → PrefixState r k) :
    ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) (n + 1)).toOuterMeasure
        {xs : Fin (n + 1) → (Fin r → ZMod 2) |
          A (Fin.init xs) ∧
            prefixEscapeEvent (S (Fin.init xs)) (xs (Fin.last n))}).toReal =
      ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) n).toOuterMeasure
          {pref : Fin n → (Fin r → ZMod 2) | A pref}).toReal *
        escapeFraction r k := by
  rw [iidSequencePMF_succ_prefixEscape_toOuterMeasure_eq_mul_escapeRatio A S]
  rw [ENNReal.toReal_mul]
  simp [escapeFraction]

/-- Power-ratio form of the arbitrary-prefix one-step escape readout. -/
theorem iidSequencePMF_succ_prefixEscape_toReal_eq_mul_one_sub_pow_ratio
    {r n k : ℕ}
    (A : (Fin n → (Fin r → ZMod 2)) → Prop)
    (S : (Fin n → (Fin r → ZMod 2)) → PrefixState r k)
    (hkr : k ≤ r) :
    ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) (n + 1)).toOuterMeasure
        {xs : Fin (n + 1) → (Fin r → ZMod 2) |
          A (Fin.init xs) ∧
            prefixEscapeEvent (S (Fin.init xs)) (xs (Fin.last n))}).toReal =
      ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) n).toOuterMeasure
          {pref : Fin n → (Fin r → ZMod 2) | A pref}).toReal *
        (1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r) := by
  rw [iidSequencePMF_succ_prefixEscape_toReal_eq_mul_escapeFraction A S]
  rw [escapeFraction_eq_one_sub_pow_ratio hkr]

/-- IID binary-column linear-independence event mass as a supplied escape-ratio
product.

For `m` independently sampled uniform binary columns in `(ZMod 2)^r`, the event
that the sampled prefix is linearly independent has `ENNReal` mass equal to the
product of the successive span-escape ratios.

This is a finite random-matrix full-column-rank readout for the IID binary
column sampler.  It is still not Shannon achievability, not a coding theorem,
and not a rate/capacity theorem. -/
theorem iidUniformBinaryColumns_linearIndependent_toOuterMeasure_eq_escapeRatioProduct
    (r : ℕ) :
    ∀ m,
      (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m).toOuterMeasure
          {cols : Fin m → (Fin r → ZMod 2) |
            LinearIndependent (ZMod 2) cols} =
        ∏ k ∈ Finset.range m,
          ((escapeCount r k : ENNReal) / (ambientCount r : ENNReal)) := by
  apply iidSequencePMF_recursiveEvent_toOuterMeasure_eq_prod
    (p := uniformPMF (Fin r → ZMod 2))
    (E := fun m cols => LinearIndependent (ZMod 2) cols)
    (c := fun k => (escapeCount r k : ENNReal) / (ambientCount r : ENNReal))
  · rw [iidSequencePMF_zero, PMF.toOuterMeasure_apply_eq_one_iff]
    intro cols _hcols
    exact linearIndependent_empty_type
  · intro n xs hxs
    exact (Persistence.BinaryPrefixState.linearIndependent_cols_iff_prefix_escape xs).mp hxs |>.1
  · intro n pref hpref
    let S : PrefixState r n := { cols := pref, independent := hpref }
    have hset :
        {a : Fin r → ZMod 2 | LinearIndependent (ZMod 2) (Fin.snoc pref a)}
          =
        {a : Fin r → ZMod 2 | prefixEscapeEvent S a} := by
      ext a
      change LinearIndependent (ZMod 2) (appendColumn pref a) ↔
        prefixEscapeEvent S a
      rw [linearIndependent_appendColumn_iff pref a]
      simp [S, prefixEscapeEvent, PrefixState.span, hpref]
    rw [hset]
    exact prefixState_uniform_escape_toOuterMeasure_eq_escapeRatio S

/-- The `ENNReal` product of finite binary escape ratios has real readout equal
to the deterministic `fullRankEscapeProduct`.

This is only an arithmetic bridge between the PMF-native `ENNReal` product and
the existing real-valued product envelope. -/
theorem escapeRatioProduct_toReal_eq_fullRankEscapeProduct (r m : ℕ) :
    ((∏ k ∈ Finset.range m,
          ((escapeCount r k : ENNReal) / (ambientCount r : ENNReal))).toReal) =
      fullRankEscapeProduct r m := by
  induction m with
  | zero =>
      simp [fullRankEscapeProduct]
  | succ m ih =>
      rw [Finset.prod_range_succ]
      rw [ENNReal.toReal_mul]
      rw [ih]
      rw [fullRankEscapeProduct_succ]
      simp [escapeFraction]

/-- Real-valued readout of the IID binary full-column-rank event mass.

The event that `m` uniformly sampled binary columns are linearly independent
has real-valued mass `fullRankEscapeProduct r m`.

This is a finite random-matrix full-column-rank PMF readout.  It is not
Shannon achievability, not a code construction, and not a rate/capacity
theorem. -/
theorem iidUniformBinaryColumns_linearIndependent_toReal_eq_fullRankEscapeProduct
    (r m : ℕ) :
    ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m).toOuterMeasure
        {cols : Fin m → (Fin r → ZMod 2) |
          LinearIndependent (ZMod 2) cols}).toReal =
      fullRankEscapeProduct r m := by
  rw [iidUniformBinaryColumns_linearIndependent_toOuterMeasure_eq_escapeRatioProduct]
  exact escapeRatioProduct_toReal_eq_fullRankEscapeProduct r m

/-- For an `m`-column binary prefix, span rank `m` is exactly linear
independence of the columns. -/
theorem finrank_span_eq_length_iff_linearIndependent {r m : ℕ}
    (cols : Fin m → (Fin r → ZMod 2)) :
    (Set.range cols).finrank (ZMod 2) = m ↔
      LinearIndependent (ZMod 2) cols := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp [Fintype.card_fin, eq_comm]

/-- Real-valued mass of the full-column-rank event for IID uniform binary
columns.

This is the rank-event form of
`iidUniformBinaryColumns_linearIndependent_toReal_eq_fullRankEscapeProduct`.
It is finite random-matrix infrastructure, not Shannon achievability. -/
theorem iidUniformBinaryColumns_fullRank_toReal_eq_fullRankEscapeProduct
    (r m : ℕ) :
    ((iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m).toOuterMeasure
        {cols : Fin m → (Fin r → ZMod 2) |
          (Set.range cols).finrank (ZMod 2) = m}).toReal =
      fullRankEscapeProduct r m := by
  have hset :
      {cols : Fin m → (Fin r → ZMod 2) |
        (Set.range cols).finrank (ZMod 2) = m}
        =
      {cols : Fin m → (Fin r → ZMod 2) |
        LinearIndependent (ZMod 2) cols} := by
    ext cols
    exact finrank_span_eq_length_iff_linearIndependent cols
  rw [hset]
  exact iidUniformBinaryColumns_linearIndependent_toReal_eq_fullRankEscapeProduct r m

/-- On a finite sample space, the finite real-valued `eventProb` agrees with
the real readout of the PMF outer-measure event mass. -/
theorem finite_eventProb_eq_toOuterMeasure_toReal
    {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (E : Ω → Prop) [DecidablePred E] :
    eventProb P E = (P.toOuterMeasure {ω : Ω | E ω}).toReal := by
  unfold eventProb
  rw [PMF.toOuterMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    by_cases hE : E ω <;> simp [Set.indicator, hE]
  · intro ω _hω
    by_cases hE : E ω <;> simp [Set.indicator, hE, P.apply_ne_top ω]

/-- `eventProb` form of the IID binary full-column-rank readout.

This is the form consumed by the finite-block `hRank` interface.  It still only
identifies the full-rank event probability; it does not yet derive a
rank-failure upper bound. -/
theorem iidUniformBinaryColumns_fullRank_eventProb_eq_fullRankEscapeProduct
    (r m : ℕ) :
    eventProb (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m)
        (fun cols : Fin m → (Fin r → ZMod 2) =>
          (Set.range cols).finrank (ZMod 2) = m) =
      fullRankEscapeProduct r m := by
  rw [finite_eventProb_eq_toOuterMeasure_toReal]
  exact iidUniformBinaryColumns_fullRank_toReal_eq_fullRankEscapeProduct r m

/-- Complement rule for finite real-valued `eventProb`. -/
theorem finite_eventProb_not_eq_one_sub
    {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (E : Ω → Prop) [DecidablePred E] :
    eventProb P (fun ω => ¬ E ω) = 1 - eventProb P E := by
  classical
  unfold eventProb
  have hsum : (∑ ω, (P ω).toReal) = 1 := by
    have hpmf : (∑ ω : Ω, P ω).toReal = 1 := by
      simpa using congrArg ENNReal.toReal (PMF.tsum_coe P)
    rw [ENNReal.toReal_sum] at hpmf
    · exact hpmf
    · intro ω _hω
      exact P.apply_ne_top ω
  calc
    ∑ ω, (P ω).toReal * (if ¬E ω then (1 : ℝ) else 0)
        = ∑ ω, ((P ω).toReal - (P ω).toReal * (if E ω then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro ω _hω
          by_cases hE : E ω <;> simp [hE]
    _ = (∑ ω, (P ω).toReal) -
          ∑ ω, (P ω).toReal * (if E ω then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ ω, (P ω).toReal * (if E ω then (1 : ℝ) else 0) := by
          rw [hsum]

/-- Rank-failure event probability for IID uniform binary columns, read as the
complement of the full-column-rank product. -/
theorem iidUniformBinaryColumns_rankFailure_eventProb_eq_one_sub_fullRankEscapeProduct
    (r m : ℕ) :
    eventProb (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m)
        (fun cols : Fin m → (Fin r → ZMod 2) =>
          (Set.range cols).finrank (ZMod 2) ≠ m) =
      1 - fullRankEscapeProduct r m := by
  rw [finite_eventProb_not_eq_one_sub
    (P := iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m)
    (E := fun cols : Fin m → (Fin r → ZMod 2) =>
      (Set.range cols).finrank (ZMod 2) = m)]
  rw [iidUniformBinaryColumns_fullRank_eventProb_eq_fullRankEscapeProduct]

/-- Rank-failure `hRank`-style upper bound from a supplied full-rank product
envelope.

This theorem consumes a supplied inequality
`1 - fullRankEscapeProduct r m ≤ 2^{-slack}` and converts the exact IID
rank-failure readout into the `eventProb rankFailure ≤ 2^{-slack}` shape used
by the finite-block coding bridge.  It does not derive the slack bound from
rate/capacity or from a coding construction. -/
theorem iidUniformBinaryColumns_rankFailure_eventProb_le_inv_two_pow_of_product_bound
    {r m slack : ℕ}
    (hbound : 1 - fullRankEscapeProduct r m ≤
      (1 : ℝ) / ((2 : ℝ) ^ slack)) :
    eventProb (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m)
        (fun cols : Fin m → (Fin r → ZMod 2) =>
          (Set.range cols).finrank (ZMod 2) ≠ m) ≤
      (1 : ℝ) / ((2 : ℝ) ^ slack) := by
  rw [iidUniformBinaryColumns_rankFailure_eventProb_eq_one_sub_fullRankEscapeProduct]
  exact hbound

/-- Rank-failure `hRank`-style upper bound from row slack.

The exact IID full-rank product gives the deterministic envelope
`1 - fullRankEscapeProduct r m ≤ 2^m / 2^r`; row slack `m + slack ≤ r`
then turns this into the finite-block `2^{-slack}` shape.

This is still a finite random-matrix rank-failure readout.  It does not derive
rate/capacity achievability, a coding construction, or a Shannon theorem. -/
theorem iidUniformBinaryColumns_rankFailure_eventProb_le_inv_two_pow_of_row_slack
    {r m slack : ℕ}
    (hrow : m + slack ≤ r) :
    eventProb (iidSequencePMF (uniformPMF (Fin r → ZMod 2)) m)
        (fun cols : Fin m → (Fin r → ZMod 2) =>
          (Set.range cols).finrank (ZMod 2) ≠ m) ≤
      (1 : ℝ) / ((2 : ℝ) ^ slack) := by
  refine iidUniformBinaryColumns_rankFailure_eventProb_le_inv_two_pow_of_product_bound ?_
  exact one_sub_fullRankEscapeProduct_le_inv_two_pow_of_row_surplus hrow

end

end Persistence.BinaryPrefixEscapePMF
