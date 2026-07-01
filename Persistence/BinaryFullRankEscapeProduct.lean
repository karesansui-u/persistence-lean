import Persistence.BinarySpanEscapeFraction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Binary Full-Rank Escape Product (Shannon §3-b, product layer)

This module stacks the finite span-escape fractions from
`BinarySpanEscapeFraction` into the product

`∏ k < m, (1 - 2^k / 2^r)`.

This is the finite product that appears in the standard sequential proof that a
random binary `r × m` matrix has full column rank with probability
`∏ k < m (1 - 2^k/2^r)`.

## What this proves

Given a supplied family of independent prefixes, the product of the concrete
span-escape fractions equals the abstract product of `escapeFraction r k`, and
under `m ≤ r` also equals the familiar power-ratio product.

## What this does not prove

No PMF is introduced here.  We do not yet prove that randomly sampled prefixes
have these conditional probabilities, nor any random-matrix theorem or Shannon
achievability.  This file does prove a deterministic row-slack envelope for the
complement `1 - fullRankEscapeProduct r m`; the later PMF layer consumes that
envelope after identifying the full-rank event mass with the product.
-/

namespace Persistence.BinaryFullRankEscapeProduct

open Persistence.BinarySpanEscapeFraction
open scoped BigOperators

noncomputable section

/-- Product of the abstract finite escape fractions for `m` sequential columns in
an `r`-row binary column space. -/
def fullRankEscapeProduct (r m : ℕ) : ℝ :=
  ∏ k ∈ Finset.range m, escapeFraction r k

/-- The familiar power-ratio form of the full-rank escape product:
`∏ k < m, (1 - 2^k / 2^r)`. -/
def fullRankPowRatioProduct (r m : ℕ) : ℝ :=
  ∏ k ∈ Finset.range m, (1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r)

/-- Product of concrete span-escape fractions for a supplied sequence of
prefixes.  The `prefix k` object should be read as the first `k` columns in a
rank-growth path. -/
def spanEscapeProduct {r : ℕ} (m : ℕ)
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2)) : ℝ :=
  ∏ k ∈ Finset.range m, spanEscapeFraction (pref k)

/-- Empty product sanity check. -/
@[simp] theorem fullRankEscapeProduct_zero (r : ℕ) :
    fullRankEscapeProduct r 0 = 1 := by
  simp [fullRankEscapeProduct]

/-- One-step recursion for the abstract escape product. -/
theorem fullRankEscapeProduct_succ (r m : ℕ) :
    fullRankEscapeProduct r (m + 1)
      = fullRankEscapeProduct r m * escapeFraction r m := by
  simp [fullRankEscapeProduct, Finset.prod_range_succ]

/-- If each supplied prefix is linearly independent, the concrete product of
span-escape fractions equals the abstract product of escape fractions.  This is
still a deterministic product identity, not a probability statement. -/
theorem spanEscapeProduct_eq_fullRankEscapeProduct {r m : ℕ}
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2))
    (hlin : ∀ k, k < m → LinearIndependent (ZMod 2) (pref k)) :
    spanEscapeProduct m pref = fullRankEscapeProduct r m := by
  unfold spanEscapeProduct fullRankEscapeProduct
  refine Finset.prod_congr rfl ?_
  intro k hk
  exact spanEscapeFraction_eq_escapeFraction (pref k)
    (hlin k (Finset.mem_range.mp hk))

/-- The abstract product of escape fractions is the familiar power-ratio
product when every prefix length `k < m` fits inside the ambient row dimension
`r`.  The row-room condition is explicit: no random matrix theorem is hidden
inside this algebraic rewrite. -/
theorem fullRankEscapeProduct_eq_powRatioProduct {r m : ℕ} (hm : m ≤ r) :
    fullRankEscapeProduct r m = fullRankPowRatioProduct r m := by
  unfold fullRankEscapeProduct fullRankPowRatioProduct
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hk_le_m : k ≤ m := Nat.le_of_lt (Finset.mem_range.mp hk)
  exact escapeFraction_eq_one_sub_pow_ratio (le_trans hk_le_m hm)

/-- Combined deterministic product form: for supplied independent prefixes and
`m ≤ r`, the product of concrete span-escape fractions is
`∏ k < m, (1 - 2^k / 2^r)`. -/
theorem spanEscapeProduct_eq_powRatioProduct {r m : ℕ}
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2))
    (hlin : ∀ k, k < m → LinearIndependent (ZMod 2) (pref k))
    (hm : m ≤ r) :
    spanEscapeProduct m pref = fullRankPowRatioProduct r m := by
  rw [spanEscapeProduct_eq_fullRankEscapeProduct pref hlin,
    fullRankEscapeProduct_eq_powRatioProduct hm]

/-! ## Bounds for the deterministic product envelope -/

/-- The abstract full-rank escape product is nonnegative. -/
theorem fullRankEscapeProduct_nonneg (r m : ℕ) :
    0 ≤ fullRankEscapeProduct r m := by
  unfold fullRankEscapeProduct
  exact Finset.prod_nonneg (fun k _ => escapeFraction_nonneg r k)

/-- The abstract full-rank escape product is bounded above by one.  This is a
finite product bound; it is not yet a PMF probability bound. -/
theorem fullRankEscapeProduct_le_one (r m : ℕ) :
    fullRankEscapeProduct r m ≤ 1 := by
  induction m with
  | zero =>
      simp [fullRankEscapeProduct]
  | succ m ih =>
      rw [fullRankEscapeProduct_succ]
      have hprod_nonneg : 0 ≤ fullRankEscapeProduct r m :=
        fullRankEscapeProduct_nonneg r m
      have hfactor_le : escapeFraction r m ≤ 1 :=
        escapeFraction_le_one r m
      have hmul_le :
          fullRankEscapeProduct r m * escapeFraction r m
            ≤ fullRankEscapeProduct r m :=
        mul_le_of_le_one_right hprod_nonneg hfactor_le
      exact le_trans hmul_le ih

/-- If the requested number of columns fits inside the ambient row dimension,
the abstract full-rank escape product is positive. -/
theorem fullRankEscapeProduct_pos {r m : ℕ} (hm : m ≤ r) :
    0 < fullRankEscapeProduct r m := by
  unfold fullRankEscapeProduct
  refine Finset.prod_pos ?_
  intro k hk
  exact escapeFraction_pos_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) hm)

/-- The power-ratio product is nonnegative under the explicit row-room
condition. -/
theorem fullRankPowRatioProduct_nonneg {r m : ℕ} (hm : m ≤ r) :
    0 ≤ fullRankPowRatioProduct r m := by
  rw [← fullRankEscapeProduct_eq_powRatioProduct hm]
  exact fullRankEscapeProduct_nonneg r m

/-- The power-ratio product is bounded above by one under the explicit row-room
condition. -/
theorem fullRankPowRatioProduct_le_one {r m : ℕ} (hm : m ≤ r) :
    fullRankPowRatioProduct r m ≤ 1 := by
  rw [← fullRankEscapeProduct_eq_powRatioProduct hm]
  exact fullRankEscapeProduct_le_one r m

/-- The power-ratio product is positive under the explicit row-room condition. -/
theorem fullRankPowRatioProduct_pos {r m : ℕ} (hm : m ≤ r) :
    0 < fullRankPowRatioProduct r m := by
  rw [← fullRankEscapeProduct_eq_powRatioProduct hm]
  exact fullRankEscapeProduct_pos hm

/-- Supplied independent prefixes give a nonnegative concrete escape product. -/
theorem spanEscapeProduct_nonneg {r m : ℕ}
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2))
    (hlin : ∀ k, k < m → LinearIndependent (ZMod 2) (pref k)) :
    0 ≤ spanEscapeProduct m pref := by
  rw [spanEscapeProduct_eq_fullRankEscapeProduct pref hlin]
  exact fullRankEscapeProduct_nonneg r m

/-- Supplied independent prefixes give a concrete escape product bounded by
one. -/
theorem spanEscapeProduct_le_one {r m : ℕ}
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2))
    (hlin : ∀ k, k < m → LinearIndependent (ZMod 2) (pref k)) :
    spanEscapeProduct m pref ≤ 1 := by
  rw [spanEscapeProduct_eq_fullRankEscapeProduct pref hlin]
  exact fullRankEscapeProduct_le_one r m

/-- Supplied independent prefixes give a positive concrete escape product when
`m ≤ r`. -/
theorem spanEscapeProduct_pos {r m : ℕ}
    (pref : (k : ℕ) → Fin k → (Fin r → ZMod 2))
    (hlin : ∀ k, k < m → LinearIndependent (ZMod 2) (pref k))
    (hm : m ≤ r) :
    0 < spanEscapeProduct m pref := by
  rw [spanEscapeProduct_eq_fullRankEscapeProduct pref hlin]
  exact fullRankEscapeProduct_pos hm

/-! ## Rank-failure envelope for the full-rank product -/

/-- Union-bound-style envelope for the deterministic full-rank escape product:
the complementary mass `1 - ∏(1 - 2^k/2^r)` is bounded by the sum of the
one-step span-hit ratios.

This is still a deterministic product estimate.  It does not mention PMFs,
codes, rate/capacity, or Shannon achievability. -/
theorem one_sub_fullRankEscapeProduct_le_sum_pow_ratio {r m : ℕ}
    (hm : m ≤ r) :
    1 - fullRankEscapeProduct r m ≤
      ∑ k ∈ Finset.range m, (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
  induction m with
  | zero =>
      simp [fullRankEscapeProduct]
  | succ m ih =>
      have hm_le_r : m ≤ r := le_trans (Nat.le_succ m) hm
      have hm_factor : m ≤ r := Nat.le_of_succ_le hm
      have ih' := ih hm_le_r
      rw [fullRankEscapeProduct_succ]
      rw [escapeFraction_eq_one_sub_pow_ratio hm_factor]
      rw [Finset.sum_range_succ]
      have hP_le : fullRankEscapeProduct r m ≤ 1 :=
        fullRankEscapeProduct_le_one r m
      have ha_nonneg : 0 ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ r := by
        exact div_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) m)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)
      have hPa_le :
          fullRankEscapeProduct r m * ((2 : ℝ) ^ m / (2 : ℝ) ^ r)
            ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ r := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hP_le ha_nonneg
      nlinarith

/-- The geometric-sum envelope for the one-step span-hit ratios:
`Σ_{k<m} 2^k/2^r ≤ 2^m/2^r`. -/
theorem sum_pow_ratio_le_pow_ratio (r m : ℕ) :
    (∑ k ∈ Finset.range m, (2 : ℝ) ^ k / (2 : ℝ) ^ r) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ r := by
  induction m with
  | zero =>
      positivity
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hden_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
      have hstep :
          (2 : ℝ) ^ m / (2 : ℝ) ^ r +
              (2 : ℝ) ^ m / (2 : ℝ) ^ r =
            (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ r := by
        field_simp [hden_pos.ne']
        rw [pow_succ]
        ring
      calc
        (∑ k ∈ Finset.range m, (2 : ℝ) ^ k / (2 : ℝ) ^ r) +
            (2 : ℝ) ^ m / (2 : ℝ) ^ r
            ≤ (2 : ℝ) ^ m / (2 : ℝ) ^ r +
              (2 : ℝ) ^ m / (2 : ℝ) ^ r := by
                simpa [add_comm] using
                  add_le_add_right ih ((2 : ℝ) ^ m / (2 : ℝ) ^ r)
        _ = (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ r := hstep

/-- Coarser row-surplus envelope:
`1 - fullRankEscapeProduct r m ≤ 2^m / 2^r`.

This is the first internally generated product/slack-shaped rank-failure
envelope; no rate/capacity theorem is used. -/
theorem one_sub_fullRankEscapeProduct_le_pow_ratio {r m : ℕ}
    (hm : m ≤ r) :
    1 - fullRankEscapeProduct r m ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ r := by
  exact le_trans (one_sub_fullRankEscapeProduct_le_sum_pow_ratio hm)
    (sum_pow_ratio_le_pow_ratio r m)

/-- If the row surplus is at least `slack`, then the deterministic product
failure envelope is at most `2^{-slack}`.

This turns the exact product readout into the shape consumed by the finite-block
`hRank` interface, but it is still only a finite binary-rank envelope, not a
Shannon coding theorem or a capacity-achieving construction. -/
theorem one_sub_fullRankEscapeProduct_le_inv_two_pow_of_row_surplus
    {r m slack : ℕ} (hslack : m + slack ≤ r) :
    1 - fullRankEscapeProduct r m ≤
      (1 : ℝ) / ((2 : ℝ) ^ slack) := by
  have hm : m ≤ r := le_trans (Nat.le_add_right m slack) hslack
  have henv := one_sub_fullRankEscapeProduct_le_pow_ratio hm
  have hpow_nat : 2 ^ (m + slack) ≤ 2 ^ r := by
    exact Nat.pow_le_pow_right (by norm_num) hslack
  have hpow : (2 : ℝ) ^ (m + slack) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast hpow_nat
  have hden_r_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) r
  have hden_s_pos : 0 < (2 : ℝ) ^ slack := pow_pos (by norm_num) slack
  have hratio :
      (2 : ℝ) ^ m / (2 : ℝ) ^ r ≤
        (1 : ℝ) / ((2 : ℝ) ^ slack) := by
    field_simp [hden_r_pos.ne', hden_s_pos.ne']
    rw [← pow_add]
    exact hpow
  exact le_trans henv hratio

end

end Persistence.BinaryFullRankEscapeProduct
