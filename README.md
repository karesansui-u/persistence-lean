# persistence-lean-new

Curated Lean core for Structural Persistence Theory.

Structural Persistence Theory is not a unification theory and does not provide
a universal persistence score.  It is a Lean-formalized meta-theory for making
structural persistence and collapse claims explicit in common coordinates,
boundary readouts, and scoped same-calculation invariants.

The current core is:

1. **Coordinates**: `F/K/V_K/L/B/M` make explicit what is maintained, what
   carries it, what burden accumulates, and what support is qualified.
2. **Boundary**: the readout says where persistence, collapse, stopping, or
   recovery is licensed.
3. **Forced loss coordinate after fixing the problem**: once the maintained
   condition `G`, viable region `V_G`, measure `m`, and before/after comparison
   are fixed, any continuous additive ratio-loss is `-k log r`, unique up to
   unit scale.  With nat units, `k = 1`.
4. **Scoped invariance**: under the visible/current-view same-calculation
   scope, G1 returns competing observation-only calculations to the same
   skeleton surface.

A second import surface, `Persistence.CorePlus`, adds selected conditional
boundary laws and proxy/approximation guards.  These are proof-bearing modules,
but they are deliberately kept out of the minimal root import so the smallest
closed claim stays easy to audit.

The theory does **not** infer the right `G`, `V_G`, `m`, `M`, or empirical
proxy from a domain automatically.  Domain measurements, proxy validity, and
prediction remain separate obligations.

In short:

```text
No universal persistence score.
After G, V_G, m, and the comparison are fixed, the loss number is forced.
Under same-calculation scope, the skeleton/boundary surface is scoped invariant.
```

## What Is Kept

This repository has two curated import surfaces.

### Minimal Root Spine

`import Persistence` imports only three load-bearing groups:

- `Persistence.LogUniqueness` and `Persistence.RepresentationTheorem`
  for the classical log-ratio loss-form characterization;
- `Persistence.StructuralPersistenceG1SemanticSpine`
  for the scoped current-view G1 semantic spine;
- `Persistence.FiniteCSPFirstMomentCollapseBound` and
  `Persistence.BernoulliCSPPathChernoff`
  for finite theorem anchors.

### Core-Plus

`import Persistence.CorePlus` imports selected proof-bearing modules that are
useful for reading the wider coordinates/boundary meta-theory:

- `Persistence.DataProcessingBridge`
  for readout-level coarse-graining / processing monotonicity under explicit
  saturation-defect hypotheses;
- `Persistence.FosterLyapunovSignBridge` and `Persistence.MartingaleDrift`
  for drift-sign and finite expectation/telescoping guards;
- `Persistence.AdditiveRecoveryNecessity`
  for additive recovery inside the log-ratio coordinate;
- `Persistence.LinearCodeBECRecovery`
  for deterministic finite erasure-recovery linear algebra, not Shannon
  achievability;
- `Persistence.StructuralPersistenceG1ApproxProxyStability`
  for bounded-horizon approximate skeleton-surface stability under explicit
  score, drift, margin, and horizon certificates.

## What Is Not Kept

This copy intentionally excludes:

- generated status ledgers, wrappers, capstones, and audit surfaces;
- operational proxy experiments such as UCI/DataSF response-route diagnostics;
- broad domain bridges that only restate native facts as dictionary entries;
- Shannon-grade, LDP, capacity, or policy ledgers;
- "unification theory" framing.

Not every file named `*Bridge` is excluded.  The exclusion is about theorem
substance, not file names: proof-bearing files such as `DataProcessingBridge`
and `FosterLyapunovSignBridge` are kept in `CorePlus`; dictionary-only bridges
remain in the archive.

The old repository can remain as the historical archive.  This repository is
for the small core that should be read, maintained, and extended first.

## Core-Plus

The minimal root import stays small on purpose.  A second layer is available
for selected proof-bearing modules that are useful for reading the wider
coordinates/boundary meta-theory:

```lean
import Persistence.CorePlus
```

See `docs/theory/CORE_PLUS_MAP.md`.  Core-plus is not the root core; it is a
curated surface for conditional boundary laws, finite examples, and
approximation/proxy guards.

## Build

```bash
lake build Persistence
lake build Persistence.CorePlus
```

## Reading

- `docs/theory/SHORT_EVIDENCE_MAP.md`
- `docs/theory/THEORY_CORE_CLOSED_SCOPE.md`
- `docs/theory/G1_SCOPED_SEMANTIC_SPINE.md`
- `docs/theory/CORE_PLUS_MAP.md`
