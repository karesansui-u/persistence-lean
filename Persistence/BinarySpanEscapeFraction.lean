import Persistence.BinaryVectorSpaceCard
import Persistence.FiniteUniformRatio
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary Span Escape Fractions (Shannon §3-b, ratio layer)

This module is the next small stone after `BinaryVectorSpaceCard`.

`BinaryVectorSpaceCard` proves the **counting** fact:

> if `k` binary columns are linearly independent in `(ZMod 2)^r`, then the
> number of fresh columns outside their span is `2^r - 2^k`.

This file turns that count into the finite-uniform **ratio**

> `(2^r - 2^k) / 2^r = 1 - 2^k / 2^r`.

It deliberately stops at a finite cardinality ratio.  It does **not** introduce
a PMF, random matrix, rank-failure probability, union bound, or Shannon coding
theorem.  Those later layers can consume this ratio as the conditional
"next-column escapes the current span" ingredient.
-/

namespace Persistence.BinarySpanEscapeFraction

open Persistence.BinaryVectorSpaceCard
open Persistence.FiniteUniformRatio

noncomputable section

/-- Numerator of the conditional escape fraction after `k` independent columns
inside an `r`-row binary column space. -/
def escapeCount (r k : ℕ) : ℕ :=
  2 ^ r - 2 ^ k

/-- Denominator of the conditional escape fraction: all binary columns of length
`r`. -/
def ambientCount (r : ℕ) : ℕ :=
  2 ^ r

/-- The finite-uniform escape fraction `(2^r - 2^k) / 2^r`.

This is a cardinality ratio, not yet a PMF statement. -/
def escapeFraction (r k : ℕ) : ℝ :=
  (escapeCount r k : ℝ) / (ambientCount r : ℝ)

/-- The ambient binary column space has nonzero finite cardinality. -/
theorem ambientCount_pos (r : ℕ) : 0 < ambientCount r := by
  unfold ambientCount
  exact pow_pos (by norm_num : (0 : ℕ) < 2) r

/-- The finite escape fraction is nonnegative. -/
theorem escapeFraction_nonneg (r k : ℕ) : 0 ≤ escapeFraction r k := by
  unfold escapeFraction
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The finite escape fraction is bounded above by one.  This is still only a
cardinality-ratio statement, not a probability theorem. -/
theorem escapeFraction_le_one (r k : ℕ) : escapeFraction r k ≤ 1 := by
  unfold escapeFraction
  have hnum_nat : escapeCount r k ≤ ambientCount r := by
    unfold escapeCount ambientCount
    exact Nat.sub_le (2 ^ r) (2 ^ k)
  have hnum : (escapeCount r k : ℝ) ≤ (ambientCount r : ℝ) := by
    exact_mod_cast hnum_nat
  have hden_nonneg : 0 ≤ (ambientCount r : ℝ) := by
    exact Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hnum hden_nonneg
  have hden_ne : (ambientCount r : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (ambientCount r : ℝ) := by
      exact_mod_cast ambientCount_pos r
    exact ne_of_gt hpos
  simpa [div_self hden_ne] using hdiv

/-- If the current span has dimension strictly below the ambient dimension, the
escape count is positive. -/
theorem escapeCount_pos_of_lt {r k : ℕ} (hkr : k < r) :
    0 < escapeCount r k := by
  unfold escapeCount
  have hpow : 2 ^ k < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) hkr
  exact Nat.sub_pos_of_lt hpow

/-- If the current span has dimension strictly below the ambient dimension, the
finite escape fraction is positive. -/
theorem escapeFraction_pos_of_lt {r k : ℕ} (hkr : k < r) :
    0 < escapeFraction r k := by
  unfold escapeFraction
  exact div_pos
    (by exact_mod_cast escapeCount_pos_of_lt hkr)
    (by exact_mod_cast ambientCount_pos r)

section SpanRatio

/-- Every subtype of the finite column space is itself finite.  This mirrors the
local instance in `BinaryVectorSpaceCard` and exists only to let `Fintype.card`
read the span complement subtype. -/
noncomputable local instance instFintypeSubtypeOfFinite
    {α : Type*} [Finite α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofFinite _

/-- The concrete span-complement ratio for a family of `k` columns in the
ambient binary column space `(ZMod 2)^r`. -/
def spanEscapeFraction {r k : ℕ} (v : Fin k → (Fin r → ZMod 2)) : ℝ :=
  (Fintype.card
      {w : Fin r → ZMod 2 // w ∉ Submodule.span (ZMod 2) (Set.range v)} : ℝ) /
    (Fintype.card (Fin r → ZMod 2) : ℝ)

/-- The concrete span-complement fraction is an instance of the generic finite
uniform event ratio.  This is still not a PMF statement; it only identifies the
finite cardinality-ratio layer. -/
theorem spanEscapeFraction_eq_finiteUniformRatio {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) :
    spanEscapeFraction v =
      finiteUniformRatio (Fin r → ZMod 2)
        (fun w => w ∉ Submodule.span (ZMod 2) (Set.range v)) := by
  rfl

/-- **§3-b, ratio form.**  For `k` linearly independent binary columns, the
finite-uniform fraction of fresh columns outside their span is
`(2^r - 2^k) / 2^r`.

This is the cardinality-ratio version of the conditional escape probability.
It is still not a random-matrix theorem; it is the reusable finite-counting
readout needed by that later step. -/
theorem spanEscapeFraction_eq_escapeFraction {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v) :
    spanEscapeFraction v = escapeFraction r k := by
  unfold spanEscapeFraction escapeFraction escapeCount ambientCount
  rw [card_notin_span_of_linearIndependent v hv, card_fin_arrow_zmod_two]

/-- Arithmetic form of the same escape fraction:
`(2^r - 2^k)/2^r = 1 - 2^k/2^r`, assuming `k ≤ r`.

The hypothesis is the row-room condition used downstream.  We keep it explicit
instead of deriving it from linear independence, so this lemma remains a small
arithmetic bridge and does not smuggle in a dimension theorem. -/
theorem escapeFraction_eq_one_sub_pow_ratio {r k : ℕ} (hkr : k ≤ r) :
    escapeFraction r k = 1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
  unfold escapeFraction escapeCount ambientCount
  have hpow_nat : 2 ^ k ≤ 2 ^ r := escape_count_nonneg hkr
  rw [Nat.cast_sub hpow_nat]
  norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  field_simp [hpos.ne']

/-- Combined form: a linearly independent span-complement ratio is
`1 - 2^k/2^r` under the explicit row-room condition `k ≤ r`. -/
theorem spanEscapeFraction_eq_one_sub_pow_ratio {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v)
    (hkr : k ≤ r) :
    spanEscapeFraction v = 1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
  rw [spanEscapeFraction_eq_escapeFraction v hv,
    escapeFraction_eq_one_sub_pow_ratio hkr]

end SpanRatio

end

end Persistence.BinarySpanEscapeFraction
