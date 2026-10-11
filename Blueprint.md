# Blueprint: ordered configuration spaces and their fundamental-group sequences

This file lists the lemma-level milestones of the formalisation, in dependency order.
Each milestone names the Lean declaration(s) that discharge it and the file containing them.
Status markers: **[done]** proved without `sorry`, **[open]** not yet formalised,
**[out of scope]** deliberately not attempted (reason given).

Notation: `X` a topological space, `Conf n X = {x : Fin n → X // Injective x}` with the subspace
topology of `Xⁿ`, `π : Conf (n+1) X → Conf n X` the map forgetting the last point.

## T. Topological layer (general spaces) — `ConfigurationSpaces/Topology/Basic.lean`

* **T1** [done] Definition of `Conf n X` as a topological space; `Conf n X` is open in `Fin n → X` when
  `X` is `T2` (`Conf.isOpen_range_val`, `Conf.isOpenEmbedding_val`).
* **T2** [done] Action of `Equiv.Perm (Fin n)` by `σ • x = x ∘ σ⁻¹` by homeomorphisms; the action is
  free (`Conf.permAction`, `Conf.continuous_smul`, `Conf.smul_eq_self_iff`).
* **T3** [done] Forgetful map `Conf.forget : C(Conf (n+1) X, Conf n X)` (drop the last point),
  equivariant for `Perm (Fin n) ↪ Perm (Fin (n+1))` (`Conf.forget_smul`).
* **T4** [done] Fibre identification: `Conf (n+1) X ≃ₜ {(y, p) : Conf n X × X // p ∉ range y}` over
  `Conf n X`, and the homeomorphism of the fibre over `y` with the punctured space
  `(range y)ᶜ` (`Conf.snocHomeomorph`, `Conf.fiberHomeomorph`).
* **T5** [done] Functoriality: an injective continuous map / embedding / open embedding /
  homeomorphism `X → Y` induces a map `Conf n X → Conf n Y` of the same kind, commuting with the
  `Sₙ`-action and with `forget` (`Conf.map`, `Conf.map_smul`, `Conf.forget_map`,
  `Conf.mapHomeomorph`).

## L. Locally trivial maps and homotopy lifting — `Topology/LocallyTrivial.lean`, `Topology/CubeLifting.lean`

* **L1** [done] `IsLocallyTrivial p`: every point of the base has an open neighbourhood `U` with a
  homeomorphism `p⁻¹ U ≃ₜ U × F` over `U` (fibre type `F` allowed to vary).
* **L2** [done] Retraction of a box `∏ [aᵢ, bᵢ]` onto the union of a nonempty set `S` of its lower faces:
  `x ↦ x - (minᵢ∈S (xᵢ - aᵢ)) · 1_S` (`CubeLifting.retract`, `CubeLifting.lowerFaces`,
  `CubeLifting.retract_mem_lowerFaces`, `CubeLifting.retract_eq_self`).
* **L3** [done] Grid: for every open cover of the cube `Fin k → I` there is `m` such that every grid cell
  of side `1/m` lies in one member (Lebesgue number).
* **L4** [done] Homotopy lifting for cubes (Serre-fibration property): for `p` locally trivial,
  `H : C(I × Iᵏ, B)` and a lift `g₀` of `H(0, ·)`, there is `G : C(I × Iᵏ, E)` with
  `p ∘ G = H`, `G (0, ·) = g₀` (`CubeLifting.exists_lift_cube` on `Fin (k+1) → I`,
  `IsLocallyTrivial.exists_lift_homotopy` on `I × (Fin k → I)`). Proof: cells processed in
  lexicographic order, each cell lifted through a trivialisation using the retraction **L2**.
* **L5** [done] Path lifting (`IsLocallyTrivial.exists_path_lift`) and square lifting
  (`IsLocallyTrivial.exists_lift_square`) as special cases.

## S. The fundamental-group sequence of a locally trivial map — `Topology/FundamentalGroupSequence.lean`

Let `p : E → B` be continuous and locally trivial, `e₀ : E`, `F = p⁻¹{p e₀}`, `i : F → E`.

* **S1** [done] `p_* ∘ i_* = 1` (`FundamentalGroup.map_comp_map_fiberIncl`).
* **S2** [done] Exactness at `π₁(E)`: `ker p_* = range i_*`
  (`FundamentalGroup.ker_map_eq_range_map_fiberIncl`; uses square lifting and the square lemma
  `Path.homotopic_square`, proved via simple connectivity of `I × I`).
* **S3** [done] If `F` is path-connected, `p_*` is surjective
  (`FundamentalGroup.map_surjective_of_isPathConnected`; uses path lifting).
* **S4** [done] If `π₂(B, p e₀)` is trivial, `i_*` is injective
  (`FundamentalGroup.map_fiberIncl_injective`; lifts the null-homotopy of the 2-sphere `p ∘ H`,
  **L4** with `k = 2`, and combines the square lemma on five faces of the cube).
* Together: `1 → π₁(F) → π₁(E) → π₁(B) → 1` is exact under the hypotheses of **S3**, **S4**.

## P. Point-pushing homeomorphisms — `Topology/Push.lean`

* **P1** [done] `HasLocalPushes X`: every `x` and neighbourhood `U` admit a neighbourhood `V` and a family
  of homeomorphisms `hᵥ` (`v ∈ V`), jointly continuous with jointly continuous inverses, supported
  in a closed set inside `U`, with `hᵥ x = v`.
* **P2** [done] Complete real normed spaces have local pushes (`NormedSpace.hasLocalPushes`): `hᵥ(y) = y + max(0, 1 - ‖y - x‖/r) • (v - x)`; its
  inverse is a fixed point of a contraction, jointly Lipschitz in `(v, y)`.
* **P3** [done] Hausdorff topological manifolds modelled on a finite-dimensional real normed space have
  local pushes (`ChartedSpace.hasLocalPushes`: transport through a chart, extend by the identity;
  the support is compact).
* **P4** [done] Multi-point pushes: for `y ∈ Conf n X` and an open `O ⊇ range y` there are a
  neighbourhood `W` of `y` and a jointly continuous family of homeomorphisms `Φ_z` (`z ∈ W`),
  supported in `O`, with `Φ_z ∘ y = z` (`HasLocalPushes.exists_multiPush`).

## F. Fadell–Neuwirth — `Topology/FadellNeuwirth.lean`

* **F1** [done] For `X` Hausdorff with local pushes, `Conf.forget : Conf (n+1) X → Conf n X` is locally
  trivial, with fibre `(range y)ᶜ` over `y` (`Conf.isLocallyTrivial_forget`).
* **F2** [done] For a connected Hausdorff manifold of dimension `≥ 2` the complement of a finite set is
  path-connected (`ChartedSpace.isPathConnected_compl_of_finite`, via
  `IsPreconnected.diff_singleton`); hence all fibres of `forget` are path-connected
  (`Conf.isPathConnected_fiber`).
* **F3** [done] Fadell–Neuwirth sequence: for such `X` (e.g. a connected surface, any Riemann surface)
  `π₁(X ∖ {y₁,…,yₙ}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact, and the first map is
  injective when `π₂(Conf n X)` is trivial (`Conf.puncturedToConf`, `Conf.fadellNeuwirth_range_eq_ker`,
  `Conf.fadellNeuwirth_surjective`, `Conf.fadellNeuwirth_injective`; the fibre is identified with
  the punctured manifold by `FundamentalGroup.mulEquivOfHomeomorph`).

## A. Algebraic layer — `ConfigurationSpaces/AlgebraicGeometry/Basic.lean`

For `X : Over S` with separated structure morphism (namespace `AlgebraicGeometry.ConfScheme`):

* **A1** [done] `power X n` (the `n`-fold fibre power, the product in `Over S`), the closed partial
  diagonals `partialDiagonal X n i j = (prᵢ, prⱼ)⁻¹ Δ` (`isClosed_partialDiagonal`, using that
  `(diag X).left` is a closed immersion), the open complement `opens X n`, the configuration
  scheme `AlgebraicGeometry.ConfScheme X n : Over S` and its open immersion `ConfScheme.ι`.
* **A2** [done] `permHom`, `perm`, `permAut : Equiv.Perm (Fin n) →* Aut (ConfScheme X n)`:
  the `Sₙ`-action by `S`-automorphisms.
* **A3** [done] `forgetHom`, `forget : ConfScheme X (n+1) ⟶ ConfScheme X n`, equivariance
  `perm_extendPerm_forget`.
* **A4** [done] Points: for `T` over `S` reduced with exactly one point (e.g. `Spec K`, `K` a field),
  `homEquiv : (T ⟶ Conf_n X) ≃ {x : Fin n → (T ⟶ X) // Injective x}` (`homEquivSpec` for
  `Spec K`); based on `mem_partialDiagonal_of_eq` / `eq_of_mem_partialDiagonal` (the latter uses
  that a surjective closed immersion onto a reduced scheme is an isomorphism).
* **A5** [done] Fibres: `toProd : Conf_{n+1} X ⟶ Conf_n X ⨯ X` is an open immersion
  (`isOpenImmersion_toProd`) with image the complement of the graphs of the `n` tautological
  sections (`range_toProd`); on field-valued points the fibre of `forget` over `z` is
  `X ∖ {z₀,…,zₙ₋₁}` (`fiberEquiv`).

## Out of scope (with reasons)

* **F4** [done] Riemann surfaces (`ChartedSpace ℂ X`): `Conf.fadellNeuwirth_complex`.

* The étale Fadell–Neuwirth / homotopy exact sequence: needs the étale homotopy exact sequence
  for proper/smooth morphisms with geometrically connected fibres (SGA 1 X, XIII), far beyond
  the current `lana-agents/pi1` (which provides the Galois-category definition of `π₁ᵉᵗ`).
* Asphericity of `Conf n X` for hyperbolic surfaces (needs `π₂` of punctured surfaces, i.e.
  uniformisation / classification); the injectivity statement **F3** is therefore stated under the
  hypothesis `π₂(Conf n X) = 0`.
