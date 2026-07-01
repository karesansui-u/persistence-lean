# persistence-lean-new

Curated Lean core for Structural Persistence Theory.

Structural Persistence Theory is a Lean-formalized meta-theory for structural
persistence and collapse claims.  Its current core is:

1. **Coordinates**: `F/K/V_K/L/B/M` make explicit what is maintained, what
   carries it, what burden accumulates, and what support is qualified.
2. **Boundary**: the readout says where persistence, collapse, stopping, or
   recovery is licensed.
3. **Scoped invariance**: under the visible/current-view same-calculation
   scope, G1 returns competing observation-only calculations to the same
   skeleton surface.

## What Is Kept

The curated Lean spine imports only three load-bearing groups:

- `Persistence.LogUniqueness` and `Persistence.RepresentationTheorem`
  for the classical log-ratio loss-form characterization;
- `Persistence.StructuralPersistenceG1SemanticSpine`
  for the scoped current-view G1 semantic spine;
- `Persistence.FiniteCSPFirstMomentCollapseBound` and
  `Persistence.BernoulliCSPPathChernoff`
  for finite theorem anchors.

## What Is Not Kept

This copy intentionally excludes:

- generated status ledgers, wrappers, capstones, and audit surfaces;
- operational proxy experiments such as UCI/DataSF response-route diagnostics;
- broad domain bridges that only restate native facts as dictionary entries;
- Shannon-grade, LDP, capacity, or policy ledgers;
- "unification theory" framing.

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
