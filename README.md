# configuration-spaces

Ordered configuration spaces of curves and their fundamental-group sequences.

## Status

**Topological and algebraic layers complete, including the full (left-exact) Fadell–Neuwirth
sequence for surfaces covered by plane domains (in particular once-punctured elliptic curves and
punctured complex planes); étale layer: scheme-theoretic fibres of `forget`, their geometric
irreducibility, and the surjectivity `π₁ᵉᵗ(Conf_{n+1}) ↠ π₁ᵉᵗ(Conf_n)` (granting universal openness
of `X → S`); exactness of the étale sequence in the middle and on the left not formalised.** Everything listed below is proved
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
* `π₂` (Mathlib's `π_ 2`, homotopy classes of maps `I² → X` sending `∂I²` to the base point,
  relative to `∂I²`) (`SecondHomotopy.lean`): it is trivial for convex subsets of real normed
  spaces and transfers along retracts/homeomorphisms; a covering map `E → X` with
  `π₂(E) = 0` has `π₂(X) = 0` (`IsCoveringMap.subsingleton_homotopyGroup_two`); for a locally
  trivial `p : E → B` with fibre `F`, `π₂(F) = π₂(B) = 0` implies `π₂(E) = 0`
  (`IsLocallyTrivial.subsingleton_homotopyGroup_two`, exactness of `π₂(F) → π₂(E) → π₂(B)`).
* **Asphericity in degree 2** (`Aspherical.lean`): if `X` is Hausdorff with local pushes and
  `π₂(X ∖ S) = 0` for every finite `S` (`PuncturedAspherical₂ X`), then `π₂(Conf n X) = 0` for all
  `n` (`Conf.subsingleton_pi_two`, induction along the Fadell–Neuwirth fibrations), hence
  `1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact for connected Riemann
  surfaces with this property (`Conf.fadellNeuwirth_exact_complex`).
* **Plane domains** (`PlanarDomain.lean`): every open `U ⊆ ℂ` has `π₂(U) = 0` at every base point
  (`Complex.subsingleton_pi_two_of_isOpen`): a sphere lies in a connected component `Ω`, which is
  `ℂ` (convex), `ℂ ∖ {a}` (covered by `exp`), or omits two points and is then covered by the disc
  by the Koebe uniformisation theorem of `lana-agents/oka`
  (`Uniformization.PlaneData.exists_covering`; the initial covering is built from the modular
  `j`-function, `PlaneUniformization.exists_covering`). Consequently `PuncturedAspherical₂ X`
  holds for every T₁ space `X` with a surjective covering map from a space embedding openly in
  `ℂ` (`puncturedAspherical₂_of_isCoveringMap`), and for such Hausdorff connected `X`
  `π₂(Conf n X) = 0` and the Fadell–Neuwirth sequence is exact on the left as well
  (`Conf.subsingleton_pi_two_of_isCoveringMap`, `Conf.fadellNeuwirth_exact_of_isCoveringMap`;
  the `ℂ`-atlas of `X` is constructed from the covering). Concrete instances, with no further
  hypotheses: connected open subsets of `ℂ` (`Conf.fadellNeuwirth_exact_of_isOpen`; e.g. `ℂ`
  minus finitely many points, i.e. `ℙ¹` minus `≥ 1` points, punctured discs), complex tori
  `ℂ/Λ` (`PeriodPair.Torus`, `Conf.fadellNeuwirth_exact_torus`) and **once-punctured elliptic
  curves** `E ∖ {O} = (ℂ/Λ) ∖ {0}` (`PeriodPair.PuncturedTorus`,
  `Conf.subsingleton_pi_two_puncturedTorus`, `Conf.fadellNeuwirth_exact_puncturedTorus`).

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

Formalised (`ConfigurationSpaces/AlgebraicGeometry/Fibers.lean`), for `X` separated over `S`:

* **scheme-theoretic fibres of `forget`**: for `z : Spec K ⟶ Conf_n(X)`, the fibre
  `Conf_{n+1}(X) ×_{Conf_n(X)} Spec K` is isomorphic to the open subscheme `ConfScheme.fiberOpens z`
  of `X_K` (`ConfScheme.fiberIso`; `ConfScheme.isPullback_fiberBase` identifies the ambient scheme
  with `X ×_S Spec K`), whose complement is the union of the images of the `n` tautological
  sections `Spec K ⟶ X_K` (`ConfScheme.compl_fiberOpens`), i.e. `X_K ∖ {z₀, …, zₙ₋₁}`;
* if the geometric fibres of `X → S` are irreducible and infinite
  (`geometrically ConfScheme.GeomIrreducibleInfinite X.hom`, e.g. a geometrically irreducible curve
  over a field), these fibres are non-empty open subschemes of irreducible schemes, hence
  `forget` is geometrically irreducible and geometrically connected
  (`ConfScheme.geometricallyIrreducible_forget`, `ConfScheme.geometricallyConnected_forget`);
* `forget` is universally open if `X → S` is (`ConfScheme.universallyOpen_forget`), and then all
  `Conf_n(X)` are connected for connected `S` (`ConfScheme.connectedSpace`).

Formalised (`ConfigurationSpaces/Etale/GaloisSurjective.lean`, using `lana-agents/pi1`):
**`π₁ᵉᵗ(Conf_{n+1}(X), ξ) ↠ π₁ᵉᵗ(Conf_n(X), ξ ≫ forget)`** (SGA 1 V.6.9;
`ConfScheme.fundamentalGroupMap_forget_surjective`) for connected `S` and `X → S` universally open
with irreducible infinite geometric fibres. The Galois-theoretic and functoriality input is in
`pi1` (`Pi1/FundamentalGroup/Functoriality.lean`: `FiniteEtale.fundamentalGroupMap`,
`FiniteEtale.isConnected_iff_connectedSpace`,
`FiniteEtale.fundamentalGroupMap_surjective_of_geometricallyConnected`;
`Pi1/Mathlib/CategoryTheory/Galois/FiberAutMap.lean`: `PreGaloisCategory.toAut_comp_surjective`,
moved there from this repository). The only hypothesis not discharged for a smooth curve over a
field is `[UniversallyOpen X.hom]` (EGA IV 2.4.6: flat + locally of finite presentation ⇒
universally open; or EGA IV 2.4.10: every scheme over a field is universally open over it); this
is not in Mathlib.

Scope of the asphericity results: they cover exactly the Hausdorff spaces `X` that admit a
surjective covering map from a space embedding openly in `ℂ` and are given together with that
covering. By the uniformisation theorem these are all Riemann surfaces other than `ℙ¹` (and
`π₂(ℙ¹) ≠ 0`), but general uniformisation is not formalised: for a hyperbolic Riemann surface
other than the concrete ones above (e.g. a compact curve of genus `≥ 2`, or an abstract
`ChartedSpace ℂ X`), the covering `𝔻 → X` (or `ℍ → X`) must be supplied as a hypothesis. Real
surfaces that are not Riemann surfaces (e.g. non-orientable ones, surfaces with boundary) are not
treated.

Not formalised (out of scope; reasons):

* **The étale Fadell–Neuwirth sequence** `π₁ᵉᵗ(X_ȳ ∖ {y₀,…,yₙ₋₁}) → π₁ᵉᵗ(Conf_{n+1} X) →
  π₁ᵉᵗ(Conf_n X) → 1` for configuration schemes of curves. Exactness in the middle and on the
  left needs the homotopy exact sequence for smooth, non-proper morphisms with geometrically
  connected fibres, i.e. SGA 1 XIII 4.1–4.3 (tame fundamental groups of complements of relative
  étale divisors in smooth proper curves) together with SGA 1 X.1.4 (homotopy exact sequence for
  proper separable morphisms) and, over `ℂ`, the comparison with the topological sequence via the
  Riemann existence theorem (SGA 1 XII); none of this is in Mathlib or `lana-agents/pi1`. The
  surjectivity on the right is formalised (see above), up to universal openness of `X → S`
  (EGA IV 2.4.6 / 2.4.10, not in Mathlib), which is kept as a hypothesis.

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
(commit `81a5d25`). The second direct dependency is
[`lana-agents/oka`](https://github.com/lana-agents/oka) pinned at commit `043c179` (the commit
pinned by `orbicurve-cores`), for the plane uniformisation theorem used in `PlanarDomain.lean`;
it pulls in `lana-agents/heights` at `3539e2a` (same Mathlib commit). Only the 16 `oka` and 7
`heights` modules imported by `Oka.Uniformization.LatticeComplement` are built (about 190 MB for
both packages including sources and build output). The third direct dependency is
[`lana-agents/pi1`](https://github.com/lana-agents/pi1) pinned at its `master` commit `94acf94`
(same Mathlib commit), for the étale fundamental group, its functoriality and the SGA 1 V.6.9
surjectivity criterion used in `Etale/GaloisSurjective.lean`; only the `pi1` modules imported
there (`Pi1.FundamentalGroup.Functoriality` and its dependencies) are built.
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
