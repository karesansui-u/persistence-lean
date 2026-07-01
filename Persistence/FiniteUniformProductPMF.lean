import Persistence.FiniteUniformPMF
import Mathlib.Data.Fintype.Prod

/-!
# Finite Uniform Product PMF

This module adds the first small product event lemma above
`FiniteUniformPMF`.

For finite nonempty types `α` and `β`, and rectangular events
`p : α → Prop` and `q : β → Prop`, the uniform event mass of

`{x : α × β | p x.1 ∧ q x.2}`

is the product of the two one-coordinate finite-uniform ratios.

## What this proves

This is a genuine finite-uniform product event calculation for rectangular
events.

## What this does not prove

This is not yet a sampled-column process, conditional independence theorem,
random-matrix rank theorem, or Shannon achievability theorem.  It only supplies
the elementary rectangular-product mass rule that later process layers can
consume.
-/

namespace Persistence.FiniteUniformProductPMF

open Persistence.FiniteUniformRatio
open Persistence.FiniteUniformPMF

noncomputable section

/-- Rectangular event on a product finite type. -/
def productEvent {α β : Type*} (p : α → Prop) (q : β → Prop) :
    α × β → Prop :=
  fun x => p x.1 ∧ q x.2

/-- The rectangular event subtype is equivalent to the product of event
subtypes. -/
def productEventSubtypeEquiv {α β : Type*}
    (p : α → Prop) (q : β → Prop) :
    {x : α × β // productEvent p q x} ≃ {a : α // p a} × {b : β // q b} where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  left_inv := by
    intro x
    ext <;> rfl
  right_inv := by
    intro y
    ext <;> rfl

/-- Count of a rectangular event in a finite product space. -/
theorem eventCount_productEvent {α β : Type*}
    [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop)
    [Fintype {a : α // p a}] [Fintype {b : β // q b}]
    [Fintype {x : α × β // productEvent p q x}] :
    eventCount (α × β) (productEvent p q) =
      eventCount α p * eventCount β q := by
  unfold eventCount
  calc
    Fintype.card {x : α × β // productEvent p q x}
        = Fintype.card ({a : α // p a} × {b : β // q b}) := by
          exact Fintype.card_congr (productEventSubtypeEquiv p q)
    _ = Fintype.card {a : α // p a} * Fintype.card {b : β // q b} := by
          rw [Fintype.card_prod]

/-- Total count of a finite product space. -/
theorem totalCount_prod (α β : Type*) [Fintype α] [Fintype β] :
    totalCount (α × β) = totalCount α * totalCount β := by
  unfold totalCount
  rw [Fintype.card_prod]

/-- Finite-uniform ratio of a rectangular event factors as the product of the
two one-coordinate finite-uniform ratios. -/
theorem finiteUniformRatio_productEvent {α β : Type*}
    [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop)
    [Fintype {a : α // p a}] [Fintype {b : β // q b}]
    [Fintype {x : α × β // productEvent p q x}] :
    finiteUniformRatio (α × β) (productEvent p q) =
      finiteUniformRatio α p * finiteUniformRatio β q := by
  unfold finiteUniformRatio
  rw [eventCount_productEvent p q, totalCount_prod α β]
  by_cases hα : (totalCount α : ℝ) = 0
  · simp [hα]
  by_cases hβ : (totalCount β : ℝ) = 0
  · simp [hβ]
  field_simp [hα, hβ]
  norm_num [Nat.cast_mul]
  ring

/-- Uniform PMF mass of a rectangular event factors through the product of the
two finite-uniform ratios. -/
theorem uniformPMF_productEvent_toReal_eq_ratio_mul_ratio {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (p : α → Prop) (q : β → Prop)
    [Fintype {a : α // p a}] [Fintype {b : β // q b}]
    [Fintype {x : α × β // productEvent p q x}] :
    ((uniformPMF (α × β)).toOuterMeasure
        {x : α × β | productEvent p q x}).toReal =
      finiteUniformRatio α p * finiteUniformRatio β q := by
  rw [uniformPMF_event_toReal_eq_finiteUniformRatio (α × β) (productEvent p q)]
  exact finiteUniformRatio_productEvent p q

end

end Persistence.FiniteUniformProductPMF
