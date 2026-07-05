# FAQ

This page answers common first-review questions about this curated repository.
It is intentionally conservative: when a criticism is partly right, it says so.

## Is Structural Persistence Theory an established field?

No.  This is an independent formalization project.  The public repository
should be read as a Lean-checked proposal for a coordinates/boundary
meta-theory, not as an established academic field.

## Is this a unification theory or a universal persistence score?

No.  The theory does not reduce domains to one native law and does not output a
universal persistence score.

It gives a discipline for making persistence/collapse claims explicit:

```text
maintained target
+ realizing structure
+ viable region
+ loss/burden
+ qualified support
+ boundary readout
+ observation / adapter / certificate
```

Domain measurement, proxy validity, prediction, causality, and transfer remain
separate obligations.

## Why is this meaningful if it is not a predictor?

The value is not prediction by itself.  The value is claim audit: making
explicit what must be fixed before a persistence/collapse claim is well formed.

Statements such as "this system is stable", "this organization is resilient",
or "this model is robust" often mix the maintained target, realizing structure,
viable region, burden, support, boundary readout, and proxy validity.
Structural Persistence Theory forces those roles apart.

In that sense it is closer to a modeling grammar than to a predictor.  Its
practical value depends on whether concrete domains can supply natural choices
of maintained target, structure, viable region, burden, support, boundary
readout, and proxy certificates.

## Is the coordinate split just vocabulary?

No, but the claim should stay modest.  The repository now contains a small
Examples ladder showing that the coordinate split is not merely decorative:

1. `SmallWitness` constructs a hidden semantic witness where two states have
   the same boundary readout and current view but different maintained-target
   realization.
2. `ProjectionIncompleteness` proves that if a claim surface uses only the
   reduced readout, that maintained-target distinction cannot be recovered from
   the reduced interface alone.
3. The same module proves the reduced/enriched form: dropping the
   maintained-target flag loses the distinction, while the enriched interface
   that keeps the flag still separates the states.
4. `StrictRealizationExtension` uses the structural field
   `viable_implies_maintained` to prove that, under strict extension, the
   viable region is a proper subregion of the realization region.
5. With the local example-side hypothesis `collapsed -> not maintains`, a
   maintained-but-not-viable state is forced to have the `stopped` readout
   rather than the `collapsed` readout.

This does not prove a new deep theorem, and it does not prove that other
frameworks cannot encode the same distinctions.  It proves a narrower point:
if these coordinates are collapsed at the claim interface, specific
distinctions are lost; if the viable/maintains ordering and boundary statuses
are kept, they can drive small Lean-checked consequences.

## Is the log-ratio theorem new mathematics?

No.  The log-ratio theorem is a Lean formalization of a classical
Cauchy/Hartley/Shannon-style characterization:

```text
ratio additivity + continuity + normalization + nonnegativity
-> f(r) = -k log r
```

The contribution is not a new logarithm theorem.  The point is that, once
`G`, `V_G`, `m`, and the comparison are fixed, the loss coordinate is not
arbitrary: continuous additive ratio-loss is forced up to unit scale.

The project is not primarily trying to contribute a new standalone theorem to
analysis or probability.  Its mathematical target is a meta-theory: which
coordinates and boundary readouts must be explicit for persistence/collapse
claims to be well formed, and which quantities become forced after those
objects are fixed.

## If `G`, `V_G`, and `m` must be fixed first, what does the theory choose?

The Lean core does not choose them.  It proves conditional statements after the
maintained condition, viable region, measure, and comparison have been supplied.

Choosing the right domain object is an adapter/proxy/certificate task outside
the root core.

## What is the difference between `F/K/V_K` and `G/V_G/m`?

`F/K/V_K` is the structural-interface notation:

- `F`: maintained target;
- `K`: realizing or maintaining structure;
- `V_K`: viable region for that structure.

`G/V_G/m` is the abstract notation used in the log-ratio theorem:

- `G`: maintained condition;
- `V_G`: viable region;
- `m`: measure.

They are not two competing ontologies.  `G/V_G/m` is the fixed-problem
abstraction used to state the forced log-ratio coordinate.

## Is `V_K` the boundary?

No.  `V_K` is the viable region.  Its edge is where a persistence/collapse
boundary readout is taken.

```text
viable region: V_K
boundary: edge of V_K
readout: inside / near-boundary / outside relative to V_K
```

## Is G1 a scope-free no-alternative theorem?

No.  G1 is currently a scoped semantic spine theorem.

Safe reading:

```text
visible/current-view same-calculation scope
-> output F/K/V_K skeleton surface
-> scoped L/M separation surface
-> aligned generated traces
```

It does not prove automatic adapter discovery, hidden-state universality, full
native `L/B/M` recovery, empirical prediction, or free external-domain transfer.

## Is the G1 scope a weakness?

Scope is not a retreat from the theorem; it is the object of the theorem.

As a channel model fixes what counts as the communication problem in
information theory, the visible/current-view same-calculation criterion fixes
when two persistence/collapse calculations are being compared as the same
calculation.

The fair limitation is different: whether that scope is natural for a concrete
domain remains a separate adapter/proxy-certificate obligation.

## Is this trying to be a new deep native-mathematics theory?

Not primarily.  The project should not be evaluated as if its main target were
to discover a new theorem like a coding theorem, a second law, or a new
probability inequality.

The target is a coordinates/boundary meta-theory: a formal discipline for what
must be specified before a persistence/collapse claim is well formed, and what
is invariant once the same-calculation scope is fixed.

So the right question is not only:

```text
Did it discover a surprising new native theorem?
```

but also:

```text
Does it make the claim interface precise?
Does it separate coordinates, boundary readouts, and domain obligations?
Does it prove the fixed-after quantities and scoped invariants it says it proves?
```

## Is G1 just definition plumbing?

G1 is a scoped well-definedness theorem for the chosen interface.  It is not
advertised here as a scope-free native theorem or a new law of nature.

So both of the following are true:

- the theorem is conditional and interface-driven;
- the theorem is still useful as a Lean-checked semantic spine that makes the
  comparison criterion and output skeleton surface explicit.

## Are finite CSP and Bernoulli/Chernoff the theory core?

They are finite anchors, not the scope of G1 and not universal collapse
theorems.

- `FiniteCSPFirstMomentCollapseBound` is a finite first-moment bound.
- `BernoulliCSPPathChernoff` is a finite Bernoulli path Chernoff upper bound.

They show that finite native examples can be expressed through the interface.
They do not prove full CSP threshold theory, full LDP, effective bandwidth, or
Shannon-style theorems.

## Does the repository prove proxy validity?

No.  It proves theorem-side conditional proxy stability.

`Persistence.StructuralPersistenceG1ApproxProxyStability` says, roughly:

```text
frozen score
+ explicit error/drift bound
+ margin
+ bounded horizon
-> approximate skeleton-surface stability
```

It does not discover a real-domain proxy, prove that the proxy measures the
intended native quantity, or give unbounded-horizon global epsilon stability.

## Why is `CorePlus` separate from `import Persistence`?

`import Persistence` is the minimal root spine: log-ratio uniqueness, scoped
G1, and finite theorem anchors.

`import Persistence.CorePlus` is a selected second layer: proof-bearing boundary
laws, drift guards, finite recovery examples, and bounded-horizon proxy
stability.

Keeping them separate prevents the smallest public claim from becoming noisy
while still preserving useful theorem-side material.

## Are all `*Bridge` files dictionary-only?

No.  File names are not decisive.

Some bridge files are proof-bearing and kept in `CorePlus`, such as
`DataProcessingBridge` and `FosterLyapunovSignBridge`.  Dictionary-only bridges
and native-fact aliases remain outside this curated repository.

## What is the strongest honest one-paragraph summary?

Structural Persistence Theory is a Lean-formalized coordinates/boundary
meta-theory for persistence and collapse claims.  It does not provide a
universal persistence score.  After a maintained condition, viable region,
measure, and comparison are fixed, continuous additive ratio-loss is forced to
be log-ratio loss up to unit scale.  Under the visible/current-view
same-calculation scope, G1 gives a scoped invariant skeleton/boundary surface.
Finite CSP and Bernoulli/Chernoff files are anchors; proxy stability is
available only under explicit bounded-horizon certificates.  Domain measurement,
real proxy validity, empirical prediction, and external adoption remain open
obligations.
