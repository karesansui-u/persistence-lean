# Claim Dependency Map

This note maps the current Lean-backed claims to the files and theorem routes
that support them.  It is meant as a citation and reviewer guide, not as an
expansion of the public theory scope.

Structural Persistence Theory does not provide a universal persistence score.
It gives a coordinate discipline: after the maintained condition `G`, viable
region `V_G`, measure `m`, and before/after comparison are fixed, the
continuous additive ratio-loss coordinate is forced up to unit scale.  Under
the adopted current-view same-calculation scope, the G1 route gives a scoped
skeleton/boundary surface.

Notation guard: `F/K/V_K` is the structural-interface notation for maintained
target, realizing structure, and the viable region for that structure.
`G/V_G/m` is the log-ratio theorem's abstract fixed-problem notation:
maintained condition, viable region, and measure.  `V_K` or `V_G` is not the
boundary itself; it is the viable region whose edge licenses the boundary
readout.

## Import Surfaces

| Surface | Lean import | Role |
| --- | --- | --- |
| Minimal root spine | `import Persistence` | The narrow public core: log-ratio uniqueness, the G1 semantic spine, and finite theorem anchors. |
| Selected second layer | `import Persistence.CorePlus` | Proof-bearing boundary laws, recovery examples, drift guards, and bounded-horizon proxy stability.  This is not part of the minimal root spine. |

## Root Claim Map

| Claim | Lean anchor | Immediate support | Boundary |
| --- | --- | --- | --- |
| Continuous additive ratio-loss on `(0, 1]` is `-k * log r`, with `k >= 0`. | `Persistence.log_ratio_uniqueness` in `Persistence/LogUniqueness.lean` | `logSubstitute_add`, `logSubstitute_continuous`, and `continuous_additive_is_linear` in `Persistence/CauchyExponential.lean` | The theorem assumes the ratio domain, additivity, continuity, normalization, and nonnegativity.  It does not choose `G`, `V_G`, `m`, or the comparison. |
| The coefficient is unique for a fixed loss function. | `Persistence.log_ratio_coefficient_unique` | Evaluation at `exp (-1)` after the log-form characterization | Uniqueness is within the already fixed coordinate and unit convention. |
| Any `PersistenceFunctional` loss must be log-ratio loss. | `Persistence.RepresentationTheorem.loss_must_be_log` | Direct application of `log_ratio_uniqueness` | This packages the loss-function theorem.  It is not an empirical selection rule. |
| Positive mass sequences telescope as `m n = m 0 * exp (-sum stageLoss)`. | `Persistence.RepresentationTheorem.telescoping_kernel_form` and `Persistence.TelescopingExp.measure_eq_initial_mul_exp_neg_cumulative_loss` | Ratio product telescoping and `exp (sum log ratio)` algebra | This is algebra on a positive mass sequence, not a probabilistic independence theorem. |
| Under current-view same-calculation scope, source and competitor reach the same current skeleton surface. | `Persistence.StructuralPersistence.G1SemanticSpine.g1_scopedInevitabilitySkeleton_of_currentViewSameCalculation` | Fixed action coverage, fixed translator existence, trace behavior, skeleton interface construction, scoped L/M separation | This is scoped.  It is not automatic adapter discovery, hidden-state universality, full native `L/B` recovery, or qualified-support `M` measurement. |
| A finite first-moment exposure bound controls nonemptiness probability. | `Persistence.FiniteCSPFirstMomentCollapseBound.nonemptyProbability_le_exp_neg_margin` | Markov/first-moment inequality plus `A * exp (-L) <= exp (-lambda)` | The first-moment bound is supplied by the exposure model.  The theorem does not prove a sharp CSP threshold or solver dynamics. |
| A finite Bernoulli path lower-tail event has a Chernoff/KL upper bound. | `Persistence.BernoulliCSPPathChernoff.exactCountFailureBound_le_chernoffFailureBound_of_interior` and `cumulativeLowerTailMeasure_le_chernoffFailureBound_of_interior` | Exact path-space MGF product from `BernoulliCSPPathMeasure` plus optimized Chernoff algebra from `BernoulliCSPTemplate` | This is a finite Bernoulli path bound, not a full LDP, effective-bandwidth theorem, or Shannon theorem. |

## G1 Proof Route

The current G1 route is best read as three layers: observation-only input,
scoped same-calculation wall, and output skeleton surface.

| Layer | Main object | Meaning |
| --- | --- | --- |
| Observation-only input | `ObservationallyRigorousCalc` | Stores observable process dynamics/readouts, a maintained target, and the fact that viable readout licenses maintenance.  It does not store `K`, `V_K`, `L/B`, `M`, adapters, or certificates. |
| Minimal response difference | `ResponseSeparated` | There are two actions at one state with different observable one-step responses. |
| Derived core scaffold | `coreInterface` | Builds the current state-carrier `F/K/V_K` scaffold from the observation-only input. |
| Derived boundary agreement | `core_inducedViableState_iff` | The induced viable-state predicate agrees with the observable viable readout. |
| Non-collapse | `nonCollapse_of_responseSeparated` | Response separation rules out representation by one global constant response. |
| Scoped L/M entrance | `responseSeparated_forces_scopedAdditiveMLSeparation` | Response-separated generated two-channel traces reach the scoped additive L/M-separation conclusion. |
| Output package | `CurrentInevitabilitySkeletonInterface` | Packages the derived core, boundary agreement, non-collapse, response-separated source, and scoped L/M entrance as an output. |

The single-calculation route is:

```text
ObservationallyRigorousCalc
+ ResponseSeparated
-> coreInterface
-> core_inducedViableState_iff
-> nonCollapse_of_responseSeparated
-> responseSeparated_forces_scopedAdditiveMLSeparation
-> nonempty_currentInevitabilitySkeletonInterface
```

The two-calculation scoped route is:

```text
CurrentViewObservationalSameCalculation
= CurrentViewFixedActionCoverage
-> CurrentViewFixedActionTranslatorExists
-> traceBehaviorRelated
-> observationOnly_traceBehavior_forces_traceAlignedSkeletonInterfaces
-> g1_scopedInevitabilitySkeleton_of_fixedActionCoverage
-> g1_scopedInevitabilitySkeleton_of_currentViewSameCalculation
```

The key design point is that `CurrentViewObservationalSameCalculation` is a
definitionally observation-only condition:

```lean
def CurrentViewObservationalSameCalculation ... : Prop :=
  CurrentViewFixedActionCoverage A B
```

For each source action, it requires one target action that preserves the
observable one-step response uniformly over all same-current-view state pairs.
In the general theorem, converting this coverage into a fixed translator uses
`Classical.choice`.  That is a scope boundary, not an empirical adapter
discovery algorithm.

## Weaker Routes And Walls

Several weaker current-view conditions are formalized because they are useful,
but the current aligned G1 skeleton needs the fixed-action-coverage wall.

| Condition | What it can support | Why it stops |
| --- | --- | --- |
| `CurrentViewResponseImageComplete` | Target-side unaligned skeleton interfaces | It realizes one-step response images, but does not choose one uniform action translator for finite generated traces. |
| `CurrentViewGlobalResponseImageEquivalent` plus injectivity | Target-side scoped additive L/M entrance | Global image equivalence folds to local current-view equivalence under extensionality, but does not by itself give generated-prefix trace alignment. |
| `traceBehaviorRelated` with supplied `toAction` | Trace-aligned skeleton interfaces | This is strong enough, but the translator is supplied. |
| `CurrentViewFixedActionCoverage` | Canonical scoped G1 skeleton surface | This is the adopted same-calculation scope. |

The file `Persistence/StructuralPersistenceG1FixedTranslatorWall.lean` records
why the fixed translator wall remains explicit: response-image completeness can
hold while no fixed action translator preserves all finite prefix logs.

## Core-Plus Boundary

`Persistence.CorePlus` is proof-bearing but not root-core.  Its safe reading is:

| Group | Lean files | Safe claim |
| --- | --- | --- |
| Coarse-graining / processing | `DataProcessingBridge` | Readout-level monotonicity under explicit saturation-defect hypotheses. |
| Drift guards | `FosterLyapunovSignBridge`, `MartingaleDrift` | Finite expectation/telescoping and drift-sign consequences. |
| Recovery | `AdditiveRecoveryNecessity` | Recovery composes additively inside the log-ratio coordinate. |
| Finite BEC recovery | `LinearCodeBECRecovery` | Deterministic finite erasure-recovery linear algebra. |
| Approximate G1 stability | `StructuralPersistenceG1ApproxProxyStability` | Bounded-horizon approximate skeleton-surface stability under explicit score, drift, horizon, and margin certificates. |

Core-plus does not add native information-theoretic DPI, full
Foster-Lyapunov recurrence, BEC capacity, real-domain proxy validity, or
scope-free G1.

## Obligations Outside Lean Core

The following are not supplied by the root Lean theorems:

- selecting the right maintained condition `G`;
- validating the viable region `V_G`;
- choosing and justifying the measure `m`;
- identifying a real-domain resource/capacity `M`;
- proving a proxy measures the intended native quantity;
- proving empirical prediction, population generalization, or external-domain
  transfer;
- deriving arbitrary adapters from hidden-state alternatives;
- proving full native `L/B` recovery or qualified-support `M` measurement.

These are not gaps in the Lean statements.  They are deliberately separate
domain, proxy, or certificate obligations.

## Paper-Safe Wording

English:

> Structural Persistence Theory is a Lean-formalized meta-theory for making
> persistence and collapse claims explicit in common coordinates, boundary
> readouts, and scoped same-calculation invariants.  It does not provide a
> universal persistence score.  After `G`, `V_G`, `m`, and the comparison are
> fixed, any continuous additive ratio-loss is forced to have the form
> `-k log r`, unique up to unit scale.  Under the adopted visible/current-view
> same-calculation scope, the G1 semantic spine constructs output
> `F/K/V_K` skeleton interfaces, reaches a scoped `L/M` separation surface,
> and aligns the generated two-channel traces.  Domain measurements, proxy
> validity, native resource/capacity claims, and empirical prediction remain
> separate obligations.

Japanese:

> 構造持続理論は、持続・崩壊の主張を共通の座標、境界 readout、
> scoped same-calculation invariants の中で明示するための
> Lean 形式化されたメタ理論である。普遍的な持続スコアは与えない。
> `G`, `V_G`, `m`, および比較が固定された後では、連続かつ加法的な
> ratio-loss は `-k log r` の形に強制され、単位スケールを除いて一意で
> ある。採用された visible/current-view same-calculation scope の下で、
> G1 semantic spine は出力としての `F/K/V_K` skeleton interface を構成し、
> scoped `L/M` separation surface に到達し、生成された二成分 trace を
> 整合させる。具体ドメインでの測定、proxy 妥当性、native な
> resource/capacity 主張、経験的予測は別途の義務として残る。

## Citation Route

For a first technical citation, cite in this order:

1. `Persistence/LogUniqueness.lean` and `Persistence/RepresentationTheorem.lean`
   for the forced log-ratio coordinate.
2. `Persistence/StructuralPersistenceG1SemanticSpine.lean` for scoped G1.
3. `Persistence/FiniteCSPFirstMomentCollapseBound.lean` and
   `Persistence/BernoulliCSPPathChernoff.lean` for finite theorem anchors.
4. `Persistence/CorePlus.lean` only when the claim needs selected
   second-layer boundary laws or proxy guards.
