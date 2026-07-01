# Core-Plus Map

`Persistence.lean` is the minimal public spine.  It should stay small.

`Persistence.CorePlus` is a selected second layer: proof-bearing modules that
are useful for reading Structural Persistence Theory as a wider
coordinates/boundary meta-theory, but that are not the root core.

This layer exists because not every file named `*Bridge` is a dictionary
bridge.  The criterion is proof load: files with real theorem bodies and clear
native-domain non-claims can live here; files that only rename native facts
stay in the archive.

## Imports

```lean
import Persistence.CorePlus
```

This imports:

| Group | Lead file | Safe reading |
| --- | --- | --- |
| Coarse-graining / processing | `Persistence.DataProcessingBridge` | Under an explicit finite saturation-defect readout and a defect sign condition, coarse-grained structural loss is bounded below by micro loss, and retention cannot increase. |
| Drift / stability guards | `Persistence.FosterLyapunovSignBridge`, `Persistence.MartingaleDrift` | Sign conventions and finite expectation-level drift/telescoping guards. |
| Recovery corollary | `Persistence.AdditiveRecoveryNecessity` | Once loss is read in the log-ratio coordinate, contraction and recovery compose additively in log space. |
| Finite BEC recovery | `Persistence.LinearCodeBECRecovery` | Deterministic finite linear-algebra criteria for unique erasure recovery: trivial syndrome-map kernel / linear independence of erased columns. |
| Approximate G1 stability | `Persistence.StructuralPersistenceG1ApproxProxyStability` | Bounded-horizon approximate skeleton-surface stability under explicit frozen score, error-drift, horizon, and margin certificates. |

## What Core-Plus Is Not

Core-plus is not a promotion of these modules to the minimal root core.

It does not claim:

- native information-theoretic DPI;
- full Foster-Lyapunov recurrence, ergodicity, or queueing theory;
- a universal recovery model excluding all non-log coordinates;
- BEC capacity, Shannon achievability, or a decoding algorithm;
- real-domain proxy validity or empirical support;
- unbounded global epsilon stability for additive drift;
- automatic adapter discovery or scope-free G1.

## Keep Rule

A module belongs in `CorePlus` only if it satisfies all of the following:

1. it is not a status/wrapper/ledger file;
2. it is not a broad dictionary bridge;
3. it has real theorem bodies;
4. its docstring states the native-domain non-claims;
5. it builds through `lake build Persistence.CorePlus`.

If a candidate fails one of these checks, leave it in the archive repository or
put it in a future examples/history layer instead.
