import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Binary Vector Space Cardinality (Shannon §3-1)

This module is the **first concrete stone** of the BEC random-coding
achievability skeleton (design note
`_design/shannon_step3_rankprob_decomposition.md`, step 3-1).

The single fact needed downstream is:

> a finite-dimensional `ZMod 2`-vector space `V` has `Fintype.card V = 2 ^ d`,
> where `d = finrank (ZMod 2) V`.

In the rank-probability argument this turns "the span of `k` independent
columns" into a set of size `2 ^ k`, which is what makes the conditional
"next column escapes the span" probability `1 - 2 ^ {k - r}` computable.

## What this proves

1. `binary_card_eq_pow_finrank` — the general `card = 2 ^ finrank` fact for any
   finite `ZMod 2`-space, specialising the existing
   `Module.card_eq_pow_finrank`.
2. `card_fin_arrow_zmod_two` — the column space `Fin r → ZMod 2` has card `2^r`.
3. `card_subspace_eq_pow_finrank` — a subspace `W : Submodule (ZMod 2) V` has
   card `2 ^ finrank W` (the `#span = 2^k` form used directly in step 3-b).
4. `card_compl_subspace_eq` — the complement of any subspace `U` of the column
   space has card `2 ^ r - 2 ^ finrank U` (step 3-b, abstract form).
5. `card_notin_span_of_linearIndependent` — for `k` linearly independent
   columns, the number of vectors outside their span is `2 ^ r - 2 ^ k` (step
   3-b, the escape-count numerator).

## What this does NOT do

Nothing probabilistic yet: no uniform measure, no rank failure bound, no union
bound. These are purely the counting lemmas that the later probabilistic steps
consume. It is the test stone for whether the Mathlib substrate is rich enough
to carry the full step 3 (it is: the general lemmas already exist).
-/

namespace Persistence.BinaryVectorSpaceCard

open Module

/-- `ZMod 2` is a field: supply the primality fact as an instance so that the
`DivisionRing (ZMod 2)` needed by `Module.card_eq_pow_finrank` (it builds a
basis, which requires a field) is found by typeclass resolution. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **§3-1, general form.** Any finite `ZMod 2`-vector space has cardinality
`2 ^ finrank`. This is `Module.card_eq_pow_finrank` specialised to `K = ZMod 2`,
with `Fintype.card (ZMod 2) = 2` rewritten via `ZMod.card`.

The `[Module (ZMod 2) V]` carries the vector-space structure; `ZMod 2` is a
field thanks to the primality instance above, which is what lets the underlying
basis-and-cardinality lemma fire. -/
theorem binary_card_eq_pow_finrank
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] :
    Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]

/-- **§3-1, the column space.** The space of length-`r` binary column vectors
`Fin r → ZMod 2` has `2 ^ r` elements. This is the ambient space in which the
parity-check columns live; its size `2^r` is the denominator of the conditional
escape probability `(2^r - 2^k)/2^r`. -/
theorem card_fin_arrow_zmod_two (r : ℕ) :
    Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **§3-1, subspace form (`#span = 2^k`).** A subspace `W` of a finite
`ZMod 2`-space has cardinality `2 ^ finrank W`. Applied to `W = span` of `k`
linearly independent columns (where `finrank W = k`), this is exactly the
`2^k` used in step 3-b's conditional-probability product. -/
theorem card_subspace_eq_pow_finrank
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W : Submodule (ZMod 2) V) [Fintype W] :
    Fintype.card W = 2 ^ Module.finrank (ZMod 2) W :=
  binary_card_eq_pow_finrank W

/-- Sanity instance: the escape count `2^r - 2^k` is nonneg when `k ≤ r`, the
shape the later step needs (`#{w ∉ span} = 2^r - 2^k ≥ 0`). Pure arithmetic
check that the cardinalities compose as intended. -/
theorem escape_count_nonneg {r k : ℕ} (h : k ≤ r) :
    (2 : ℕ) ^ k ≤ 2 ^ r :=
  Nat.pow_le_pow_right (by norm_num) h

/-!
## §3-b: counting the complement of a span

The two lemmas below close step 3-b: the number of binary vectors that lie
*outside* the span of `k` independent columns is `2 ^ r - 2 ^ k`. This escape
count is the numerator of the conditional probability `(2^r - 2^k)/2^r` that a
freshly drawn column avoids the span of the previous ones — the heart of the
rank-probability product.

The only subtlety the probe surfaced: `Fintype.card_subtype_compl` requires a
`Fintype` instance on the subtypes `{w // w ∈ U}` and `{w // w ∉ U}`, and these
are *not* supplied by `classical` (which only gives `Decidable`). The ambient
column space is `Finite`, so every subtype is finite; we supply that via
`Fintype.ofFinite` as a `noncomputable local instance`, scoped to this section
so it cannot leak a competing `Fintype` path to other modules. The value of
`Fintype.card` is independent of the chosen instance, so this composes cleanly
with `card_subspace_eq_pow_finrank` (which takes `[Fintype W]` as an argument).
-/

section ComplementCount

/-- Every subtype of the finite column space is itself finite. Supplied as a
`noncomputable local instance` (it routes through `Classical.choice`, hence
`noncomputable`) only so that `Fintype.card_subtype_compl` can fire; scoped to
this section to avoid leaking a competing `Fintype` instance elsewhere. -/
noncomputable local instance instFintypeSubtypeOfFinite
    {α : Type*} [Finite α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofFinite _

/-- **§3-b, abstract form.** The complement of any subspace `U` of the binary
column space `Fin r → ZMod 2` has cardinality `2 ^ r - 2 ^ finrank U`. Combines
`Fintype.card_subtype_compl` (complement = total − subspace), the ambient count
`card (Fin r → ZMod 2) = 2 ^ r`, and the subspace count `card U = 2 ^ finrank U`.
No linear independence yet — this holds for *any* subspace. -/
theorem card_compl_subspace_eq {r : ℕ}
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Fintype.card {w : Fin r → ZMod 2 // w ∉ U}
      = 2 ^ r - 2 ^ Module.finrank (ZMod 2) U := by
  rw [Fintype.card_subtype_compl (· ∈ U), card_fin_arrow_zmod_two]
  congr 1
  exact card_subspace_eq_pow_finrank U

/-- **§3-b, the escape count.** Given `k` linearly independent binary columns
`v : Fin k → (Fin r → ZMod 2)`, the number of vectors *outside* their span is
exactly `2 ^ r - 2 ^ k`. Specialises `card_compl_subspace_eq` to `U = span` and
rewrites `finrank (span (range v)) = k` via `finrank_span_eq_card`. This is the
numerator of the conditional escape probability `(2^r - 2^k)/2^r`. -/
theorem card_notin_span_of_linearIndependent {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v) :
    Fintype.card {w : Fin r → ZMod 2 // w ∉ Submodule.span (ZMod 2) (Set.range v)}
      = 2 ^ r - 2 ^ k := by
  rw [card_compl_subspace_eq, finrank_span_eq_card hv, Fintype.card_fin]

end ComplementCount

end Persistence.BinaryVectorSpaceCard
