# Agent Guide

This repository is the curated core copy of `persistence-lean`.

Keep the public claim narrow:

- The project is a meta-theory of coordinates, boundary, and scoped invariance
  for structural persistence/collapse claims.
- It is not a unification theory and does not provide a universal persistence
  score.  Numeric loss is forced only after `G`, `V_G`, `m`, and the comparison
  are fixed.
- Write the project name as `Structural Persistence Theory` in English and
  `構造持続理論` in Japanese.  Do not use the three-letter abbreviation from
  the English initials in public docs, comments, or new identifiers.
- The load-bearing Lean core is:
  1. `LogUniqueness` / `RepresentationTheorem`;
  2. `StructuralPersistenceG1SemanticSpine`;
  3. `FiniteCSPFirstMomentCollapseBound` and `BernoulliCSPPathChernoff`.
- `Persistence.CorePlus` is a second-layer selected theorem surface.  Do not
  move its imports into `Persistence.lean` unless the user explicitly decides
  to expand the minimal root core.
- Do not classify files by name alone.  Some `*Bridge` files are proof-bearing
  and belong in `CorePlus`; dictionary-only bridges and native-fact aliases
  stay in the archive.
- Do not reintroduce generated ledgers, route wrappers, operational proxy
  experiments, broad domain bridges, or "unification theory" framing into this
  curated repository.
- If a new Lean file is added, it should either be a direct dependency of the
  three groups above or a genuinely new theorem that strengthens the
  coordinates/boundary/scoped-invariance core.

For docs-only changes, run:

```bash
git diff --check
```

For Lean changes, run:

```bash
lake build Persistence
```
