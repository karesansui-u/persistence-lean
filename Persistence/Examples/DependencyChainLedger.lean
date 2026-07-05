import Persistence.FosterLyapunovSignBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite Series Two-Coordinate Accounting Example

A finite set of dependency stages, each carrying a survival ratio (the
series-reliability setting) and a freely declared nonnegative support quantity,
tracked by a two-coordinate ledger `(total burden, total support)`.

The burden coordinate is `structuralPotential id`, matching the finite series
reliability log-loss example.

What is proved:

* a bookkeeping identity: the ledger of a disjoint union of stage sets is the
  componentwise sum of the subsystem ledgers;
* the stage set's composite burden equals the ledger's burden coordinate;
* viability, defined in this example as survival-only `theta <= chainSurvival`,
  is equivalent to a burden budget.  Support does not enter this readout
  because the readout is defined that way;
* a burden-only scalar with support weight zero decides this viability readout;
* when nonnegative support can be freely declared, a netted scalar that
  discounts support against burden can assign identical scores to two
  single-stage systems with opposite viability.

Scope limitations:

* stages form a finite set; the ledger is order-invariant, and genuine path or
  DAG structure, routing, shared nodes, feedback, and correlated failures are
  not modeled;
* support is freely declared in ledger units.  What counts as support, how it is
  measured, and what constraints license it remain domain-side obligations;
* series (AND) dependency only, as in the series reliability example;
* this is a toy accounting counterexample, not a general theorem about all real
  support metrics or all netting rules.
-/

open Finset

namespace Persistence.Examples.DependencyChainLedger

noncomputable section

/-- The burden coordinate, `-log r` in structural nats. -/
def burden : ℝ -> ℝ :=
  Persistence.FosterLyapunovSignBridge.structuralPotential (id : ℝ -> ℝ)

theorem burden_def (x : ℝ) : burden x = -Real.log x := rfl

variable {ι : Type*}

/-- Total burden of a stage set with survival ratios `r`. -/
def totalBurden (s : Finset ι) (r : ι -> ℝ) : ℝ :=
  ∑ i ∈ s, burden (r i)

/-- Total declared support of a stage set. -/
def totalSupport (s : Finset ι) (u : ι -> ℝ) : ℝ :=
  ∑ i ∈ s, u i

/-- The two-coordinate audit ledger: burden and support are carried as a pair. -/
def ledger (s : Finset ι) (r u : ι -> ℝ) : ℝ × ℝ :=
  (totalBurden s r, totalSupport s u)

/-- Composite survival of the chain: series (AND) dependency. -/
def chainSurvival (s : Finset ι) (r : ι -> ℝ) : ℝ :=
  ∏ i ∈ s, r i

/-- Viability against a survival threshold, defined here as survival-only. -/
def Viable (s : Finset ι) (r : ι -> ℝ) (theta : ℝ) : Prop :=
  theta <= chainSurvival s r

/--
A fixed-weight netted score: burden weighted by `wb`, with support discounted
against it at rate `ws`.

The counterexample below shows that, under unconstrained support declaration
and positive weights, this score can identify systems with opposite viability.
-/
def nettedScore (s : Finset ι) (r u : ι -> ℝ) (wb ws : ℝ) : ℝ :=
  wb * totalBurden s r - ws * totalSupport s u

/--
Bookkeeping identity: the ledger of a disjoint union of stage sets is the
componentwise sum of the subsystem ledgers.

This is finite-set additivity of the two totals, not a path, DAG, or shared-node
composition theorem.
-/
theorem ledger_union [DecidableEq ι] {s1 s2 : Finset ι} (r u : ι -> ℝ)
    (hdisj : Disjoint s1 s2) :
    ledger (s1 ∪ s2) r u = ledger s1 r u + ledger s2 r u := by
  unfold ledger totalBurden totalSupport
  rw [Prod.mk_add_mk, Finset.sum_union hdisj, Finset.sum_union hdisj]

variable (s : Finset ι) (r u : ι -> ℝ)
variable (hr0 : ∀ i ∈ s, 0 < r i) (hr1 : ∀ i ∈ s, r i <= 1)

include hr0 in
/--
The composite burden of a series stage set is the sum of its stage burdens,
i.e. the ledger's burden coordinate.
-/
theorem burden_chainSurvival_eq_totalBurden :
    burden (chainSurvival s r) = totalBurden s r := by
  unfold chainSurvival totalBurden
  rw [burden_def, Real.log_prod (fun i hi => ne_of_gt (hr0 i hi)),
    ← Finset.sum_neg_distrib]
  simp [burden_def]

include hr0 in
omit hr1 in
/--
Burden-budget form of the survival-only viability readout.

`Viable` is defined as `theta <= chainSurvival`, so support does not enter by
definition.  The theorem's content is the equivalent linear budget in the
burden coordinate.
-/
theorem viable_iff_burden_budget (theta : ℝ) (htheta : 0 < theta) :
    Viable s r theta ↔ totalBurden s r <= burden theta := by
  have hpos : 0 < chainSurvival s r := Finset.prod_pos hr0
  unfold Viable
  rw [← burden_chainSurvival_eq_totalBurden s r hr0, burden_def, burden_def]
  constructor
  · intro h
    have := Real.log_le_log htheta h
    linarith
  · intro h
    have hlog : Real.log theta <= Real.log (chainSurvival s r) := by
      linarith
    calc theta = Real.exp (Real.log theta) := (Real.exp_log htheta).symm
      _ <= Real.exp (Real.log (chainSurvival s r)) :=
        Real.exp_le_exp.mpr hlog
      _ = chainSurvival s r := Real.exp_log hpos

include hr0 in
omit hr1 in
/-- A burden-only scalar (`ws = 0`) decides the survival-only viability readout. -/
theorem burden_only_scalar_decides
    (theta wb : ℝ) (htheta : 0 < theta) (hwb : 0 < wb) :
    Viable s r theta ↔
      nettedScore s r u wb 0 <= wb * burden theta := by
  unfold nettedScore
  rw [zero_mul, sub_zero, viable_iff_burden_budget s r hr0 theta htheta]
  constructor <;> intro h <;> nlinarith

/--
Toy counterexample for unconstrained support declaration.

For every positive burden weight and every positive support-discount weight,
there are two single-stage systems with identical netted score and opposite
survival-only viability.  This shows possible information loss under freely
declared support; it does not show that every constrained real-world support
metric or every netting rule fails.
-/
theorem exists_same_nettedScore_opposite_viability_unconstrainedSupport
    (wb ws theta : ℝ) (hwb : 0 < wb) (hws : 0 < ws)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ r1 u1 r2 u2 : Fin 1 -> ℝ,
      (∀ i, 0 < r1 i ∧ r1 i <= 1) ∧
      (∀ i, 0 < r2 i ∧ r2 i <= 1) ∧
      (∀ i, 0 <= u1 i) ∧
      (∀ i, 0 <= u2 i) ∧
      nettedScore Finset.univ r1 u1 wb ws =
        nettedScore Finset.univ r2 u2 wb ws ∧
      Viable Finset.univ r1 theta ∧
      ¬ Viable Finset.univ r2 theta := by
  set beta : ℝ := -Real.log theta with hbeta_def
  have hbeta : 0 < beta := by
    have : Real.log theta < 0 := Real.log_neg htheta0 htheta1
    simp [hbeta_def]
    linarith
  refine
    ⟨fun _ => theta, fun _ => 0, fun _ => theta ^ 2,
      fun _ => wb * beta / ws,
      fun _ => ⟨htheta0, le_of_lt htheta1⟩,
      fun _ => ⟨pow_pos htheta0 2, ?_⟩,
      fun _ => le_rfl,
      fun _ => ?_,
      ?_, ?_, ?_⟩
  · nlinarith
  · exact div_nonneg (mul_nonneg (le_of_lt hwb) (le_of_lt hbeta))
      (le_of_lt hws)
  · unfold nettedScore totalBurden totalSupport
    simp only [Fin.sum_univ_one, burden_def]
    have hlogsq : Real.log (theta ^ 2) = 2 * Real.log theta := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlogsq, hbeta_def]
    field_simp
    ring
  · unfold Viable chainSurvival
    simp
  · unfold Viable chainSurvival
    simp only [Fin.prod_univ_one, not_le]
    nlinarith

end

end Persistence.Examples.DependencyChainLedger
