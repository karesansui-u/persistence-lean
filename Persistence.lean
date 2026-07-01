/-
Structural Persistence Theory -- curated Lean core.

This spine intentionally imports only the load-bearing core:

1. log-ratio uniqueness;
2. scoped G1 semantic spine;
3. finite theorem anchors.

Generated ledgers, operational proxy reports, domain bridges, and experimental
diagnostics are intentionally omitted from this repository.
-/

import Persistence.LogUniqueness
import Persistence.RepresentationTheorem
import Persistence.StructuralPersistenceG1SemanticSpine
import Persistence.FiniteCSPFirstMomentCollapseBound
import Persistence.BernoulliCSPPathChernoff
