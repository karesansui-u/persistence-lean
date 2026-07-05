# Impact-Difference Network

This note states a design direction, not a closed theorem.

Structural Persistence Theory can be read as a common coordinate system for
reading persistence and collapse as impact differences across connected
claims.  The point is not to replace native domain models, and not to predict
the future by itself.  The point is to keep visible what changed:

```text
What target was maintained?
What structure carried it?
What burden increased?
What support decreased or moved?
Which boundary moved closer?
Which proxy improved while the maintained target degraded?
Whose support became someone else's burden?
```

Native theories still own the measurements, dynamics, and forecasts.  This
interface owns the discipline of not mixing the roles.

## Single Node

A single persistence claim can be written as a node:

```text
Node i:
  F_i        maintained target
  K_i        realizing structure
  V_i        viable region
  L_i        burden / loss / adverse pressure
  M_i        qualified support / effective resource
  B_i        boundary readout
  proxy_i    observation and certificate obligations
```

This is the claim-audit layer.  It asks whether a sentence such as "the system
is resilient" has specified what is being maintained, what carries it, what
loads it, what supports it, and where the boundary is read.

## Edges

The network layer starts when one node's persistence claim changes another
node's burden, support, boundary, or target.

Typical edge types:

| Edge type | Reading |
| --- | --- |
| support edge | `M_i` helps maintain `F_j` |
| burden-transfer edge | an action that supports `F_i` adds `L_j` |
| dependency edge | collapse of node `i` removes `M_j` |
| boundary edge | a policy or condition changes the boundary readout for node `j` |
| proxy edge | improving a proxy for node `i` hides or worsens the target state of node `j` |
| recovery-support edge | support from node `i` moves node `j` back toward its viable region |

The core question is:

```text
Who is maintaining what, by using whose support, and by moving burden where?
```

That is the intended difference from a single-node claim audit.  The object of
attention is the movement of burden/support/boundary differences across the
network.

## One Edge Across Domains

The same burden-transfer edge can be read across domains.

```text
A is kept viable by adding load to B.
```

Examples:

| Domain | `A` maintained | Added support for `A` | `B` burdened |
| --- | --- | --- | --- |
| Company | customer support SLA | overtime and escalation | staff health, attention, trust |
| Individual | income and obligations | longer work hours | sleep, health, relationships |
| Municipality | central service continuity | deferred maintenance / peripheral load | infrastructure, staff, remote neighborhoods |
| Natural system | upstream production | extraction or discharge | downstream water, soil, habitat |
| AI operation | benchmark or service metric | more context/tooling/manual intervention | memory quality, operator load, downstream trust |

The point is not that the same equation predicts all of these.  It does not.
The point is that the same impact-difference question can be asked without
mixing the roles:

```text
Was this persistence bought by increasing another burden?
Was support moved, consumed, or degraded?
Did a proxy improve while another maintained target worsened?
```

## Difference Coordinates

An intervention or shock can be described by the coordinates it changes:

| Difference | Meaning |
| --- | --- |
| `Delta L_i` | burden or adverse pressure on node `i` changed |
| `Delta M_i` | effective support for node `i` changed |
| `Delta K_i` | realizing structure for node `i` changed |
| `Delta B_i` | boundary readout or margin for node `i` changed |
| `Delta F_i` | the maintained target itself changed |
| `Delta proxy_i` | the observation changed, possibly without target improvement |
| transfer `L_i -> L_j` | burden moved from one node to another |
| transfer `M_i -> L_j` | support for one node became burden for another |

These are reading coordinates, not automatic measurements.  A domain adapter
must still define the native quantities, units, proxies, and error certificates.

## Relationship To Viability Theory

Viability theory can encode multi-target and burden-transfer systems by
building a larger state space, dynamics, controls, and constraint set.  This
note does not claim otherwise.

The difference is not computational power.  The difference is the display
discipline:

```text
Viability analysis:
  given state space, dynamics, controls, and constraints,
  analyze whether the system can remain viable.

Impact-difference reading:
  before or alongside that analysis,
  keep visible which maintained targets, burdens, supports, boundaries,
  proxies, and inter-node transfers the claim is using.
```

A large coupled viability model can contain the same information.  The risk is
that the impact differences become implicit inside the state vector and
constraint set.  This coordinate system is useful only if preserving those
differences at the claim surface helps reviewers, modelers, or agents see what
is being supported, depleted, transferred, or hidden.

## Relationship To Resilience Vocabulary

Resilience terms can be mapped into the same reading:

| Term | Coordinate reading | Do not conflate with |
| --- | --- | --- |
| robustness | `F_i` remains maintained under increased `L_i` | recovery after failure |
| redundancy | multiple support paths for `M_i` | actual effective capacity |
| recovery | movement back toward `V_i` after leaving it | never leaving the boundary |
| adaptation | change in `K_i`, `M_i`, `V_i`, or sometimes `F_i` | unchanged persistence |
| vulnerability | small changes in `L_i` or `M_i` move the node near boundary | observed damage alone |
| exposure | external source and frequency of `L_i` | sensitivity to that load |
| transformability | transition to a different maintained target or structure | ordinary recovery |

This vocabulary map is not a claim that these terms are new.  It is a way to
ask what a resilience claim is actually saying.

## Current Status

This note is a programmatic reading layer.  The Lean repository currently proves
only smaller pieces:

- the log-ratio coordinate after the maintained condition, viable region,
  measure, and comparison are fixed;
- the scoped G1 semantic spine;
- finite anchors;
- example-layer coordinate-separation witnesses and no-go consequences.

It does not yet prove a full network theorem for burden transfer, cascading
collapse, externalization, or cross-domain prediction.  Those remain future
adapter or theorem-design tasks.

Safe summary:

> Structural Persistence Theory can be used to read persistence and collapse as
> mixed-but-separable impact differences across a network of maintained targets.
> It does not replace the domain models that measure or predict those changes.
