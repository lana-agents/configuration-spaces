# configuration-spaces

Ordered configuration spaces of curves and their fundamental-group sequences.

## Status

**Not started.** The repository is the initial project scaffold (a single commit,
2026-07-20). The library `ConfigurationSpaces` contains only the placeholder module
`ConfigurationSpaces/Basic.lean`, which has no declarations: there are no definitions or theorems yet
(and so no `sorry`, `axiom` or `admit`). Everything under *Goals* below is planned, not
formalised.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise ordered configuration spaces of curves

```
Conf_n(X) = Xⁿ minus the union of the pairwise diagonals
```

Develop the symmetric-group action, the forgetful maps `Conf_{n+1}(X) → Conf_n(X)`, the description of their fibres as punctured curves, and the resulting topological and étale fundamental-group exact sequences — including the Fadell–Neuwirth sequence in the classical setting.

Package the functoriality needed by anabelian reconstruction arguments.

This supplies independently established configuration-space infrastructure used in *Topics in Absolute Anabelian Geometry II*, and is separate from the Belyi-map existence theorem in `belyi`.

## Established sources

* Fadell–Neuwirth, *Configuration spaces* (1962).
* SGA 1.
* Mochizuki–Tamagawa, *The algebraic and anabelian geometry of configuration spaces*, Hokkaido Math. J. 37 (2008), 75–131.

## Related repositories

Intended as an input to the anabelian machinery of `iut`; not used by it. Separate
from the Belyi-map existence theorem in `belyi`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `ConfigurationSpaces/`, and every file must be imported from
the root module `ConfigurationSpaces.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib ConfigurationSpaces --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#15](https://taxis.lana.merten.dev/issues/15)

License: Apache 2.0 (see LICENSE).
