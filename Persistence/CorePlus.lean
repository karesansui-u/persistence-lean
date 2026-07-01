/-
Structural Persistence Theory -- selected core-adjacent theorem surface.

This module is intentionally *not* imported by `Persistence.lean`.

`Persistence.lean` is the minimal public spine.  `Persistence.CorePlus` is the
second layer for proof-bearing modules that are useful for reading the
meta-theory as a wider coordinates/boundary program, but that should not blur
the smaller root core.

Included here:

1. readout-level coarse-graining / processing monotonicity;
2. Foster-Lyapunov sign and finite drift guards;
3. additive recovery consequences of the log-ratio coordinate;
4. deterministic finite BEC recovery linear algebra;
5. bounded-horizon approximate/proxy G1 stability under explicit certificates.

Excluded here:

* status ledgers, route wrappers, public capstones, and audit surfaces;
* operational proxy experiments and empirical diagnostics;
* broad domain bridges that only rename native facts.
-/

import Persistence.DataProcessingBridge
import Persistence.FosterLyapunovSignBridge
import Persistence.MartingaleDrift
import Persistence.AdditiveRecoveryNecessity
import Persistence.LinearCodeBECRecovery
import Persistence.StructuralPersistenceG1ApproxProxyStability
