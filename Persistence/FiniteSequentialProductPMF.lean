import Persistence.FiniteUniformProductPMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite Sequential Product PMF

This module adds the first monadic product-PMF layer above the finite-uniform
ratio/product bridge.

Given `p : PMF α` and `q : PMF β`, `sequentialProductPMF p q` samples
`a ~ p`, then samples `b ~ q`, and returns `(a, b)`.  For rectangular events,
the event mass factors as the product of the two marginal event masses.

The file also defines `iidSequencePMF p n`, the bare IID sequential PMF on
`Fin n → α`, obtained by appending one fresh `p`-sample at each step.

For finite uniform PMFs, this gives the same real-valued readout as the earlier
finite-uniform rectangular product calculation.  It also includes a small
dependent-event variant: if the second-coordinate event depends on the first
sample but has a constant supplied mass over the first event, then the
sequential event mass is the first event mass times that constant.

## What this proves

This is a genuine two-coordinate sequential PMF product calculation for
rectangular events, plus a constant-conditional-mass dependent-event skeleton.

## What this does not prove

This does not prove a rank-aware random-prefix process theorem, conditional
rank-growth theorem, random-matrix rank theorem, or Shannon achievability
theorem.  It only supplies the elementary `PMF.bind` product rule and bare IID
sequence sampler that later process layers can consume.
-/

namespace Persistence.FiniteSequentialProductPMF

open Persistence.FiniteUniformRatio
open Persistence.FiniteUniformPMF
open Persistence.FiniteUniformProductPMF
open scoped BigOperators

noncomputable section

/-- Sequential independent product PMF: sample `a ~ p`, then `b ~ q`, and
return `(a, b)`. -/
def sequentialProductPMF {α β : Type*} (p : PMF α) (q : PMF β) :
    PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

/-- Bare IID sequential PMF on `Fin n → α`.

At step `n + 1`, it samples a length-`n` prefix and then appends one fresh
sample from `p`.  This is only the sampler; no event/rank theorem is attached
here. -/
def iidSequencePMF {α : Type*} (p : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure (Fin.elim0 : Fin 0 → α)
  | n + 1 => (iidSequencePMF p n).bind fun pref =>
      p.map fun a => Fin.snoc pref a

@[simp]
theorem iidSequencePMF_zero {α : Type*} (p : PMF α) :
    iidSequencePMF p 0 = PMF.pure (Fin.elim0 : Fin 0 → α) := rfl

@[simp]
theorem iidSequencePMF_succ {α : Type*} (p : PMF α) (n : ℕ) :
    iidSequencePMF p (n + 1) =
      (iidSequencePMF p n).bind fun pref =>
        p.map fun a => Fin.snoc pref a := rfl

/-- View a pair as a length-two prefix. -/
def pairToFinTwo {α : Type*} (x : α × α) : Fin 2 → α :=
  Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → α) x.1) x.2

set_option linter.flexible false in
/-- The length-two IID sequence sampler agrees with the existing sequential
two-coordinate product, after viewing a pair as a `Fin 2`-indexed prefix.

This is only a compatibility lemma between two local PMF presentations. -/
theorem iidSequencePMF_two_eq_sequentialProductPMF_map {α : Type*}
    (p : PMF α) :
    iidSequencePMF p 2 = (sequentialProductPMF p p).map pairToFinTwo := by
  simp [iidSequencePMF, sequentialProductPMF, PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  rfl

/-- Rectangular event mass for the sequential product PMF factors as the
product of the two marginal event masses. -/
theorem sequentialProductPMF_productEvent_toOuterMeasure_eq_mul {α β : Type*}
    (p : PMF α) (q : PMF β) (A : α → Prop) (B : β → Prop) :
    (sequentialProductPMF p q).toOuterMeasure
        {x : α × β | productEvent A B x} =
      p.toOuterMeasure {a : α | A a} *
        q.toOuterMeasure {b : β | B b} := by
  classical
  unfold sequentialProductPMF
  rw [PMF.toOuterMeasure_bind_apply]
  have hmap : ∀ a : α,
      (PMF.map (fun b : β => (a, b)) q).toOuterMeasure
          {x : α × β | productEvent A B x} =
        if A a then q.toOuterMeasure {b : β | B b} else 0 := by
    intro a
    rw [PMF.toOuterMeasure_map_apply]
    by_cases ha : A a <;> simp [productEvent, ha]
  calc
    ∑' (a : α), p a *
        (PMF.map (fun b : β => (a, b)) q).toOuterMeasure
          {x : α × β | productEvent A B x}
        = ∑' a : α, p a *
            (if A a then q.toOuterMeasure {b : β | B b} else 0) := by
          apply tsum_congr
          intro a
          rw [hmap]
    _ = ∑' a : α, (if A a then p a else 0) *
          q.toOuterMeasure {b : β | B b} := by
          apply tsum_congr
          intro a
          by_cases ha : A a <;> simp [ha]
    _ = (∑' a : α, if A a then p a else 0) *
          q.toOuterMeasure {b : β | B b} := by
          rw [ENNReal.tsum_mul_right]
    _ = p.toOuterMeasure {a : α | A a} *
          q.toOuterMeasure {b : β | B b} := by
          have hp :
              p.toOuterMeasure {a : α | A a} =
                ∑' a : α, if A a then p a else 0 := by
            rw [PMF.toOuterMeasure_apply]
            rfl
          rw [hp]

/-- The second-coordinate marginal event mass for a sequential product PMF.

This is a small product-PMF bookkeeping lemma: if the event ignores the first
sample, its mass is the second marginal event mass. -/
theorem sequentialProductPMF_secondEvent_toOuterMeasure_eq {α β : Type*}
    (p : PMF α) (q : PMF β) (B : β → Prop) :
    (sequentialProductPMF p q).toOuterMeasure
        {x : α × β | B x.2} =
      q.toOuterMeasure {b : β | B b} := by
  have htrue : p.toOuterMeasure {a : α | True} = 1 := by
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro a _ha
    trivial
  rw [← one_mul (q.toOuterMeasure {b : β | B b})]
  rw [← htrue]
  rw [← sequentialProductPMF_productEvent_toOuterMeasure_eq_mul
    (p := p) (q := q) (A := fun _ : α => True) (B := B)]
  congr 1
  ext x
  simp [productEvent]

/-- Dependent rectangular event mass for the sequential product PMF.

If the second-coordinate event may depend on the first sampled value `a`, but
has the same `q`-mass `c` for every `a` satisfying the first-coordinate event,
then the sequential event mass is the first event mass times `c`.

This is the first small conditional-product skeleton; it still assumes the
constant conditional mass as a hypothesis. -/
theorem sequentialProductPMF_dependentEvent_toOuterMeasure_eq_mul {α β : Type*}
    (p : PMF α) (q : PMF β)
    (A : α → Prop) (B : α → β → Prop) (c : ENNReal)
    (hB : ∀ a, A a → q.toOuterMeasure {b : β | B a b} = c) :
    (sequentialProductPMF p q).toOuterMeasure
        {x : α × β | A x.1 ∧ B x.1 x.2} =
      p.toOuterMeasure {a : α | A a} * c := by
  classical
  unfold sequentialProductPMF
  rw [PMF.toOuterMeasure_bind_apply]
  have hmap : ∀ a : α,
      (PMF.map (fun b : β => (a, b)) q).toOuterMeasure
          {x : α × β | A x.1 ∧ B x.1 x.2} =
        if ha : A a then q.toOuterMeasure {b : β | B a b} else 0 := by
    intro a
    rw [PMF.toOuterMeasure_map_apply]
    by_cases ha : A a <;> simp [ha]
  calc
    ∑' (a : α), p a *
        (PMF.map (fun b : β => (a, b)) q).toOuterMeasure
          {x : α × β | A x.1 ∧ B x.1 x.2}
        = ∑' a : α, p a *
            (if ha : A a then q.toOuterMeasure {b : β | B a b} else 0) := by
          apply tsum_congr
          intro a
          rw [hmap]
    _ = ∑' a : α, (if A a then p a else 0) * c := by
          apply tsum_congr
          intro a
          by_cases ha : A a
          · simp [ha, hB a ha]
          · simp [ha]
    _ = (∑' a : α, if A a then p a else 0) * c := by
          rw [ENNReal.tsum_mul_right]
    _ = p.toOuterMeasure {a : α | A a} * c := by
          have hp :
              p.toOuterMeasure {a : α | A a} =
                ∑' a : α, if A a then p a else 0 := by
            rw [PMF.toOuterMeasure_apply]
            rfl
          rw [hp]

/-- One-step conditional-mass rule for the bare IID sequence sampler.

At length `n + 1`, sample a length-`n` prefix, then append one fresh sample
from `p`.  If the last-step event has constant `p`-mass `c` on every prefix
satisfying `A`, then the full prefix event mass is the prefix-event mass times
`c`.

This is the arbitrary-prefix analogue of
`sequentialProductPMF_dependentEvent_toOuterMeasure_eq_mul`.  It is only a
monadic one-step product skeleton; it does not prove any rank-process,
random-matrix, or Shannon theorem. -/
theorem iidSequencePMF_succ_dependentEvent_toOuterMeasure_eq_mul {α : Type*}
    (p : PMF α) (n : ℕ)
    (A : (Fin n → α) → Prop) (B : (Fin n → α) → α → Prop)
    (c : ENNReal)
    (hB : ∀ pref, A pref → p.toOuterMeasure {a : α | B pref a} = c) :
    (iidSequencePMF p (n + 1)).toOuterMeasure
        {xs : Fin (n + 1) → α |
          A (Fin.init xs) ∧ B (Fin.init xs) (xs (Fin.last n))} =
      (iidSequencePMF p n).toOuterMeasure {pref : Fin n → α | A pref} * c := by
  classical
  rw [iidSequencePMF_succ]
  rw [PMF.toOuterMeasure_bind_apply]
  have hmap : ∀ pref : Fin n → α,
      (PMF.map (fun a : α => Fin.snoc pref a) p).toOuterMeasure
          {xs : Fin (n + 1) → α |
            A (Fin.init xs) ∧ B (Fin.init xs) (xs (Fin.last n))} =
        if hpref : A pref then p.toOuterMeasure {a : α | B pref a} else 0 := by
    intro pref
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hpref : A pref
    · simp [hpref]
    · simp [hpref]
  calc
    ∑' (pref : Fin n → α), (iidSequencePMF p n) pref *
        (PMF.map (fun a : α => Fin.snoc pref a) p).toOuterMeasure
          {xs : Fin (n + 1) → α |
            A (Fin.init xs) ∧ B (Fin.init xs) (xs (Fin.last n))}
        = ∑' pref : Fin n → α, (iidSequencePMF p n) pref *
            (if hpref : A pref then p.toOuterMeasure {a : α | B pref a} else 0) := by
          apply tsum_congr
          intro pref
          rw [hmap]
    _ = ∑' pref : Fin n → α, (if A pref then (iidSequencePMF p n) pref else 0) * c := by
          apply tsum_congr
          intro pref
          by_cases hpref : A pref
          · simp [hpref, hB pref hpref]
          · simp [hpref]
    _ = (∑' pref : Fin n → α, if A pref then (iidSequencePMF p n) pref else 0) * c := by
          rw [ENNReal.tsum_mul_right]
    _ = (iidSequencePMF p n).toOuterMeasure {pref : Fin n → α | A pref} * c := by
          have hp :
              (iidSequencePMF p n).toOuterMeasure {pref : Fin n → α | A pref} =
                ∑' pref : Fin n → α, if A pref then (iidSequencePMF p n) pref else 0 := by
            rw [PMF.toOuterMeasure_apply]
            rfl
          rw [hp]

/-- Product rule for recursively specified IID sequence events.

Suppose `E n` is an event on length-`n` prefixes.  If:

* the length-zero event has mass `1`;
* every length-`n+1` event implies its length-`n` prefix event; and
* on every prefix satisfying `E n`, the fresh-sample event that extends to
  `E (n+1)` has constant `p`-mass `c n`;

then the length-`m` event mass under the IID sequence sampler is the product
of the supplied one-step masses `c 0, ..., c (m-1)`.

This is an IID conditional-product skeleton with supplied recursive event
data.  It does not construct rank events, random-prefix state maps,
random-matrix rank probabilities, or Shannon achievability witnesses. -/
theorem iidSequencePMF_recursiveEvent_toOuterMeasure_eq_prod {α : Type*}
    (p : PMF α)
    (E : (n : ℕ) → (Fin n → α) → Prop)
    (c : ℕ → ENNReal)
    (h0mass :
      (iidSequencePMF p 0).toOuterMeasure {xs : Fin 0 → α | E 0 xs} = 1)
    (hprefix : ∀ n (xs : Fin (n + 1) → α),
      E (n + 1) xs → E n (Fin.init xs))
    (hmass : ∀ n (pref : Fin n → α), E n pref →
      p.toOuterMeasure {a : α | E (n + 1) (Fin.snoc pref a)} = c n) :
    ∀ m,
      (iidSequencePMF p m).toOuterMeasure {xs : Fin m → α | E m xs} =
        ∏ k ∈ Finset.range m, c k := by
  intro m
  induction m with
  | zero =>
      simpa using h0mass
  | succ n ih =>
      have hset :
          {xs : Fin (n + 1) → α | E (n + 1) xs} =
            {xs : Fin (n + 1) → α |
              E n (Fin.init xs) ∧
                E (n + 1) (Fin.snoc (Fin.init xs) (xs (Fin.last n)))} := by
        ext xs
        have hxs : Fin.snoc (Fin.init xs) (xs (Fin.last n)) = xs :=
          Fin.snoc_init_self xs
        constructor
        · intro hx
          exact ⟨hprefix n xs hx, by simpa [hxs] using hx⟩
        · intro hx
          simpa [hxs] using hx.2
      rw [hset]
      rw [iidSequencePMF_succ_dependentEvent_toOuterMeasure_eq_mul
        (p := p)
        (n := n)
        (A := E n)
        (B := fun pref a => E (n + 1) (Fin.snoc pref a))
        (c := c n)
        (by
          intro pref hpref
          exact hmass n pref hpref)]
      rw [ih]
      rw [Finset.prod_range_succ]

/-- Finite-uniform real-valued version of the sequential product rule. -/
theorem sequentialUniformPMF_productEvent_toReal_eq_ratio_mul {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (A : α → Prop) (B : β → Prop)
    [Fintype {a : α // A a}] [Fintype {b : β // B b}] :
    ((sequentialProductPMF (uniformPMF α) (uniformPMF β)).toOuterMeasure
        {x : α × β | productEvent A B x}).toReal =
      finiteUniformRatio α A * finiteUniformRatio β B := by
  rw [sequentialProductPMF_productEvent_toOuterMeasure_eq_mul]
  rw [ENNReal.toReal_mul]
  rw [uniformPMF_event_toReal_eq_finiteUniformRatio α A]
  rw [uniformPMF_event_toReal_eq_finiteUniformRatio β B]

end

end Persistence.FiniteSequentialProductPMF
