# persistence-lean

Curated Lean core for Structural Persistence Theory.

Structural Persistence Theory is not a universal prediction theory, not a
unification theory, and not a universal persistence score.  It is a
Lean-formalized claim-discipline meta-theory for putting structural persistence
and collapse claims onto an explicit interface: maintained target, viable
region, measure, boundary readout, burden/support, and proxy obligations.

The Lean core proves what is forced after those choices are fixed: log-ratio
loss uniqueness, scoped same-calculation invariance, finite anchors, and
selected conditional boundary/proxy laws in `Persistence.CorePlus`.

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

Notation note: the structural interface writes `F/K/V_K` for maintained target,
realizing structure, and the viable region for that structure.  The log-ratio
theorem often writes the same fixed-problem role abstractly as `G/V_G/m`:
maintained condition, viable region, and measure.  `V_K` or `V_G` is the viable
region, not the boundary itself; the boundary readout is taken at or relative to
that region's edge.

A second import surface, `Persistence.CorePlus`, adds selected conditional
boundary laws and proxy/approximation guards.  These are proof-bearing modules,
but they are deliberately kept out of the minimal root import so the smallest
closed claim stays easy to audit.

The scoped G1 core is not a finite-IID theorem: it is an abstract
visible/current-view observational-process theorem.  Finite CSP and
Bernoulli/Chernoff files are anchors, not the scope of G1.  Approximate/proxy
stability lives in `Persistence.CorePlus` under explicit bounded-horizon score,
error-drift, margin, and horizon certificates; real-domain proxy validity
remains a separate obligation.

Measurement and proxy discipline are part of the interface, not automatic
discoveries.  A domain adapter must state the native measure `m`, the
observable proxy if `m` is not directly observed, the boundary readout, and the
error/margin certificate that licenses the proxy near that boundary.  A proxy is
not evidence by name; it is only licensed when the domain-side certificate says
what it measures and how far it may deviate.

Structural Persistence Theory has two intended values.  First, within a native
domain, it can make prediction, diagnosis, and intervention claims more precise
by forcing the maintained target, burden, support, measure, proxy, and collapse
boundary to be stated explicitly.  Second, across domains, it provides a common
persistence coordinate for reading individuals, organizations, municipalities,
natural systems, institutions, and long-lived AI systems in comparable terms.
This supports audits of burden transfer, dependency, cascading collapse,
recovery support, and institutional design.  The first is a precision value;
the second is a connection value.  They solve different problems.

This does not replace native domain theories.  Queueing theory, control theory,
epidemiology, reliability engineering, software analysis, and other native
theories remain the sources of precise domain claims.  Predictive use, when
available, must come from a domain adapter, native dynamics, and proxy
certificates.

The theory does **not** infer the right `G`, `V_G`, `m`, `M`, or empirical
proxy from a domain automatically.  Domain measurements, proxy validity, and
prediction remain separate obligations.

In short:

```text
No universal prediction theory.
No universal persistence score.
After the maintained target, viable region, measure, and comparison are fixed,
the loss coordinate is forced.
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

The private `persistence-lean-lab` repository remains the place for draft
proofs, exploratory diagnostics, and historical route material.  This public
repository is for the small core that should be read, maintained, and extended
first.

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

- `docs/theory/FAQ.md`
- `docs/theory/SHORT_EVIDENCE_MAP.md`
- `docs/theory/THEORY_CORE_CLOSED_SCOPE.md`
- `docs/theory/CLAIM_DEPENDENCY_MAP.md`
- `docs/theory/G1_SCOPED_SEMANTIC_SPINE.md`
- `docs/theory/CORE_PLUS_MAP.md`
