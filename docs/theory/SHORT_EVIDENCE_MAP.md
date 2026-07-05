# Short Core Map

This is the fastest map for a first-time reviewer.  It intentionally keeps the
load-bearing core small.  Benchmark, operational, and proxy reports are history
and diagnostics; they are not part of the theory core.

## Essence

Structural Persistence Theory does not give a universal persistence score and
does not reduce domains to one native law.  It is a meta-theory of:

1. common coordinates for persistence/collapse claims;
2. boundary readouts for persistence, collapse, stopping, and recovery;
3. conditional/scoped invariance under a same-calculation criterion;
4. conditional boundary laws and proxy guards when explicit certificates are
   supplied.

The main numeric uniqueness result is conditional.  Once the maintained
condition `G`, viable region `V_G`, measure `m`, and before/after comparison
are fixed, the loss coordinate is not arbitrary: every continuous additive
ratio-loss has the form `-k log r`, unique up to unit scale.  This does not
select the correct `G`, `V_G`, `m`, `M`, or empirical proxy for a real domain.

Notation: the structural interface uses `F/K/V_K` for maintained target,
realizing structure, and the viable region for that structure.  The log-ratio
kernel often abstracts this fixed-problem role as `G/V_G/m`.  `V_K` and `V_G`
are viable regions, not the boundary itself; boundary readouts are taken at or
relative to their edges.

## Load-Bearing Core

| Group | Files | What is real | What not to claim |
| --- | --- | --- | --- |
| Log-ratio uniqueness | `Persistence/LogUniqueness.lean`, `Persistence/RepresentationTheorem.lean` | A Lean-checked version of the classical characterization: ratio additivity, continuity, normalization, and nonnegativity on shrinkage force the `-k log r` loss form. | New entropy theory, empirical prediction, or a claim that every real system decays exponentially. |
| G1 semantic spine | `Persistence/StructuralPersistenceG1SemanticSpine.lean` | In the visible/current-view scope, observable same-calculation criteria force target-side scoped `L/M` separation and output `F/K/V_K` skeleton surfaces with aligned generated traces. | Scope-free no-alternative theorem, automatic adapter discovery, full native `L/B/M` recovery, hidden-state universality, or empirical prediction. |
| Finite theorem anchors | `Persistence/FiniteCSPFirstMomentCollapseBound.lean`, `Persistence/BernoulliCSPPathChernoff.lean` | A finite CSP first-moment bound and a finite Bernoulli path Chernoff upper bound. | Universal CSP threshold theory, full LDP, effective-bandwidth theorem, Shannon theorem, or tight lower/converse theorem. |

These three groups are the material a first citation should start from.

The G1 semantic spine is not a finite-IID theorem.  It is an abstract
visible/current-view observational-process theorem.  Finite CSP and
Bernoulli/Chernoff are finite anchors, not the scope of G1.

## Core-Plus: Selected Second Layer

`Persistence.CorePlus` is not the minimal root core, but it is part of this
curated repository.  It keeps proof-bearing modules that add useful thickness
to the coordinates/boundary meta-theory without mixing them into the smallest
public spine.

| Group | Lead files | Safe reading |
| --- | --- | --- |
| Coarse-graining / processing | `Persistence/DataProcessingBridge.lean` | Readout-level monotonicity under explicit saturation-defect hypotheses; not native information-theoretic data-processing. |
| Drift / stability guards | `Persistence/FosterLyapunovSignBridge.lean`, `Persistence/MartingaleDrift.lean` | Sign conventions and finite expectation/telescoping guards; not full Foster-Lyapunov recurrence or queueing theory. |
| Recovery corollary | `Persistence/AdditiveRecoveryNecessity.lean` | Additive recovery inside the log-ratio coordinate; not a universal recovery model. |
| Finite BEC recovery | `Persistence/LinearCodeBECRecovery.lean` | Deterministic finite erasure-recovery linear algebra; not BEC capacity, Shannon achievability, or a decoder. |
| Approximate G1 stability | `Persistence/StructuralPersistenceG1ApproxProxyStability.lean` | Bounded-horizon approximate skeleton-surface stability under explicit score, drift, margin, and horizon certificates; not real-domain proxy validity. |

Names are not decisive.  Some `*Bridge` files are proof-bearing and kept here;
dictionary-only bridges remain outside the curated repository.

The example module `Persistence/Examples/SmallWitness.lean` contains
kernel-level nonvacuity checks for the G1 semantic interface.  The first reuses
the finite three-state visible process and separates maintained-target
realization from the viable boundary region, proving
`viable ⊊ maintains ⊊ all states` by explicit witnesses and routing the process
through `currentViewTraceLogExtensional_of_oneStepExtensional`.  The second
adds a four-state hidden semantic witness where two states have the same
current view and boundary readout but different maintained-target realization,
and where current-view injectivity fails while state-dependent one-step
responses still satisfy one-step current-view extensionality and route into
trace-log extensionality.  These are kernel-level nonvacuity checks, not
real-domain validation or empirical proxy claims.

The example module `Persistence/Examples/QueueGeoGeo1Drift.lean` contains a
finite-buffer drift-sign adapter for the Foster-Lyapunov sign bridge.  It
models a three-state Geo/Geo/1 queue with blocked arrivals at capacity and
proves that the interior expected net change is `p - q`; after the safe set
`{empty}` is fixed, the negative-drift readout agrees with `p < q`.  A
contrast theorem shows that widening the safe set changes the drift obligation.
This is a finite-buffer drift-sign example, not an infinite-buffer stability,
positive-recurrence, or full queueing-theory theorem.

The example module `Persistence/Examples/SeriesReliabilityLogLoss.lean`
contains a finite series-reliability log-loss adapter.  Taking the series law
`R = ∏ r_i` as a domain-side composition input, it proves that component
survivals in `(0, 1]` remain in the Core ratio domain, that series burden is
additive in the shared `-log r` coordinate, and that every admissible scalar
continuous log-additive Core loss reads the same burden sum up to nonnegative
scale.  It also gives a threshold/burden-budget readout and a series-only red
test for single-component burden overshoot.  This is not a derivation of the
series law, independence assumptions, parallel redundancy, repair dynamics, or
general reliability theory.

In particular, approximate/proxy stability is a theorem-side conditional guard:
explicit bounded-horizon score, error-drift, margin, and horizon certificates
can license approximate skeleton-surface stability.  It does not discover or
validate real-domain proxies automatically.

## Diagnostics Outside Core

The following are useful to keep for audit history, but they should not be
presented as additional proof of the theory core:

- QSA and synthetic SRE-H1 benchmarks: controlled diagnostics for proxy
  behavior, not external SRE support or recovery theorems.
- UCI/DataSF operational probes: response-route or operational-classification
  diagnostics, not direct measurements of native resource/capacity `M` such as
  staff, distance, workload, queue capacity, or service time.
- M-axis role-specificity screens: exploratory diagnostics and no-support /
  inconclusive records, not theorem-level connections to the Lean G1/log core.
- G2/G3/G4 readout ledgers: certificate-relative route maps for capacity,
  exponent, and policy-body claims, not native Shannon/LDP/capacity theorems.

## Downstream Readout Routes

| Route | Status | Safe reading |
| --- | --- | --- |
| G2 capacity readouts | Certificate-relative / audit layer | Organizes which native capacity, optimizer, EB, or LDP certificates would be needed.  It is not the log/G1 theory core. |
| G3 exponent readouts | Certificate-relative / audit layer | Organizes concrete-event exponent readouts under supplied route certificates. |
| G4 policy readouts | Certificate-relative / audit layer | Organizes policy-body readout surfaces under supplied certificates. |
| `unresolved` entries | Open slots | They mark native-domain obligations that remain open.  They are not mathematical closures. |

## Scaffolding Warning

Many repository files are route wrappers or audit surfaces rather than
load-bearing theory.  Names such as `StatusLanding`, `ResidualSplit`,
`PublicWrapper`, `Capstone`, `AuditBody`, and `ObligationStatus` should be read
as bookkeeping unless this page lists the file or theorem as part of the core
or finite anchors.

This is intentional, but easy to misread: audit granularity is not mathematical
depth.  A first review should follow the kernel and finite anchors above before
opening generated route ledgers.

## Application Layer

Application readings show how a domain can be described through the interface.
They are not native-domain theorems, prediction models, or additional evidence
for the core.  Read them only after the three load-bearing groups above are
clear.

## One Safe Citation

> Structural Persistence Theory is a Lean-formalized meta-theory for rigorous
> persistence/collapse boundary-interface claims.  It does not provide a
> universal persistence score.  After `G`, `V_G`, `m`, and the comparison are
> fixed, the log-ratio loss coordinate is forced up to unit scale; under the
> visible/current-view same-calculation scope, G1 gives a scoped invariant
> skeleton/boundary surface.  Its current load-bearing pieces are the
> log-ratio uniqueness kernel, the scoped G1 semantic spine, and finite theorem
> anchors.  Benchmark and operational reports are diagnostics, not proof of
> native resource/capacity `M`, empirical generalization, or a theorem-level
> connection to the Lean core.

## Reader Route

1. Read this page first.
2. Read [`THEORY_CORE_CLOSED_SCOPE.md`](THEORY_CORE_CLOSED_SCOPE.md) for the exact closed scope.
3. Read [the scoped G1 semantic statement](G1_SCOPED_SEMANTIC_SPINE.md) for the paper-facing current-view G1 scope.
