# configuration-spaces

Ordered configuration spaces of curves and their fundamental-group sequences.

## Status

**Topological and algebraic layers complete; étale sequence not formalised.** Everything listed below is proved
without `sorry`, `admit` or new axioms (only `propext`, `Classical.choice`, `Quot.sound`). The
lemma-level plan and its status are in [`Blueprint.md`](Blueprint.md).

Formalised (`ConfigurationSpaces/Topology/`):

* `Conf n X` (injective `n`-tuples, open in `Xⁿ` for Hausdorff `X`), the free action of
  `Equiv.Perm (Fin n)` by homeomorphisms, the forgetful maps `Conf.forget`, their equivariance,
  the identification `Conf (n+1) X ≃ₜ {(y, p) | p ∉ range y}` and of the fibre over `y` with
  `X ∖ {y₀, …, yₙ₋₁}`, and functoriality for injective maps, embeddings and homeomorphisms
  (`Basic.lean`).
* Locally trivial maps (`IsLocallyTrivial`) have the homotopy lifting property for all cubes
  (they are Serre fibrations), in particular path and square lifting (`CubeLifting.lean`).
* For a locally trivial `p : E → B` with fibre `F` through `e₀`: `ker p_* = range i_*` in
  `π₁(E, e₀)`; `p_*` is surjective if `F` is path-connected; `i_*` is injective if
  `π₂(B, p e₀)` is trivial (`FundamentalGroupSequence.lean`).
* Point-pushing homeomorphisms in complete real normed spaces and in Hausdorff topological
  manifolds modelled on finite-dimensional real normed spaces, and simultaneous pushes of
  finitely many points (`Push.lean`); complements of finite sets in connected manifolds of
  dimension `> 1` are path-connected (`Punctured.lean`).
* **Fadell–Neuwirth**: for `X` Hausdorff with local pushes (e.g. any such manifold, any Riemann
  surface) `Conf.forget : Conf (n+1) X → Conf n X` is locally trivial; for `X` a connected
  manifold of dimension `> 1` (e.g. a connected surface) the sequence
  `π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact, and the first map is
  injective when `π₂(Conf n X)` is trivial (`Conf.fadellNeuwirth_range_eq_ker`,
  `Conf.fadellNeuwirth_surjective`, `Conf.fadellNeuwirth_injective` in `FadellNeuwirth.lean`),
  together with naturality of the induced maps on `π₁` for injective maps and for the
  symmetric-group action; the case of Riemann surfaces is `Conf.fadellNeuwirth_complex`.

Formalised (`ConfigurationSpaces/AlgebraicGeometry/Basic.lean`), for `X` separated over `S`:

* the configuration scheme `AlgebraicGeometry.ConfScheme X n`, the open subscheme of the fibre
  power `Xⁿ` complementary to the closed partial diagonals `Δᵢⱼ = (prᵢ, prⱼ)⁻¹ Δ`;
* the action `Equiv.Perm (Fin n) →* Aut (ConfScheme X n)` by `S`-automorphisms and the
  equivariant forgetful morphisms `ConfScheme.forget`;
* `Conf_{n+1}(X)` is the open subscheme of `Conf_n(X) ×_S X` complementary to the graphs of the
  tautological sections (`ConfScheme.isOpenImmersion_toProd`, `ConfScheme.range_toProd`);
* points with values in a field (more generally in a reduced one-point `S`-scheme) are tuples of
  pairwise distinct points (`ConfScheme.homEquiv`, `ConfScheme.homEquivSpec`), and the fibre of
  `forget` over such a point `z` is `X ∖ {z₀,…,zₙ₋₁}` on points (`ConfScheme.fiberEquiv`).

Not formalised:

* The étale fundamental-group (homotopy) exact sequence for configuration spaces of algebraic
  curves: it needs the étale homotopy exact sequence (SGA 1, X and XIII), which is far beyond
  what `lana-agents/pi1` currently provides (the Galois-category definition of `π₁ᵉᵗ`).
* Asphericity of `Conf n X` (`π₂ = 0`) for surfaces other than the sphere and projective plane;
  the injectivity statement is proved under this hypothesis.

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
