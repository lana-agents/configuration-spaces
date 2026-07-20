# configuration-spaces

Ordered configuration spaces of curves and their fundamental-group sequences.

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

An independently established input to the anabelian machinery used by `iut`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
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
