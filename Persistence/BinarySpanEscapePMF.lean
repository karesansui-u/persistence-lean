import Persistence.BinarySpanEscapeFraction
import Persistence.FiniteUniformPMF

/-!
# Binary Span Escape PMF Bridge

This module specializes the generic finite-uniform PMF bridge to the binary
span-escape event used in the Shannon-facing rank substrate.

It upgrades the earlier cardinality-ratio statement

`spanEscapeFraction = #outside-span / #ambient`

to the corresponding finite-uniform PMF event-mass statement.

## What this does not prove

This is still a one-step finite-uniform event bridge.  It does not prove a
random-prefix process, independence of sampled columns, random-matrix
rank-failure probability, or Shannon achievability.
-/

namespace Persistence.BinarySpanEscapePMF

open Persistence.BinarySpanEscapeFraction
open Persistence.BinaryVectorSpaceCard
open Persistence.FiniteUniformRatio
open Persistence.FiniteUniformPMF

noncomputable section

/-- Every subtype of a finite type is finite.  This local instance lets the
finite-uniform PMF theorem see the span-complement event as a finite event. -/
noncomputable local instance instFintypeSubtypeOfFinite
    {α : Type*} [Finite α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofFinite _

/-- Under the finite-uniform PMF on the binary column space `(Fin r → ZMod 2)`,
the event mass of the span-complement event is the concrete span escape
fraction. -/
theorem uniformPMF_spanEscape_toReal_eq_spanEscapeFraction {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | w ∉ Submodule.span (ZMod 2) (Set.range v)}).toReal =
      spanEscapeFraction v := by
  rw [uniformPMF_event_toReal_eq_finiteUniformRatio]
  exact (spanEscapeFraction_eq_finiteUniformRatio v).symm

/-- `ENNReal` form of the span-escape PMF mass.

For a linearly independent prefix, the uniform PMF mass of the span-complement
event is the concrete finite ratio `(2^r - 2^k) / 2^r`, before converting to
`Real`.  This is useful for sequential `PMF.bind` product calculations, whose
native event masses live in `ENNReal`. -/
theorem uniformPMF_spanEscape_toOuterMeasure_eq_escapeRatio {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v) :
    (uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | w ∉ Submodule.span (ZMod 2) (Set.range v)} =
      (escapeCount r k : ENNReal) / (ambientCount r : ENNReal) := by
  rw [uniformPMF_event_toOuterMeasure_eq]
  unfold eventCount totalCount escapeCount ambientCount
  rw [card_notin_span_of_linearIndependent v hv, card_fin_arrow_zmod_two]

/-- If the supplied prefix is linearly independent, the finite-uniform PMF
event mass equals the abstract finite escape fraction. -/
theorem uniformPMF_spanEscape_toReal_eq_escapeFraction {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | w ∉ Submodule.span (ZMod 2) (Set.range v)}).toReal =
      escapeFraction r k := by
  rw [uniformPMF_spanEscape_toReal_eq_spanEscapeFraction v,
    spanEscapeFraction_eq_escapeFraction v hv]

/-- Combined one-step PMF readout: for an independent prefix and explicit
row-room condition `k ≤ r`, the uniform PMF mass of escaping the current span is
`1 - 2^k / 2^r`. -/
theorem uniformPMF_spanEscape_toReal_eq_one_sub_pow_ratio {r k : ℕ}
    (v : Fin k → (Fin r → ZMod 2)) (hv : LinearIndependent (ZMod 2) v)
    (hkr : k ≤ r) :
    ((uniformPMF (Fin r → ZMod 2)).toOuterMeasure
        {w : Fin r → ZMod 2 | w ∉ Submodule.span (ZMod 2) (Set.range v)}).toReal =
      1 - (2 : ℝ) ^ k / (2 : ℝ) ^ r := by
  rw [uniformPMF_spanEscape_toReal_eq_escapeFraction v hv,
    escapeFraction_eq_one_sub_pow_ratio hkr]

end

end Persistence.BinarySpanEscapePMF
