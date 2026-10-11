# Blueprint: ordered configuration spaces and their fundamental-group sequences

This file lists the lemma-level milestones of the formalisation, in dependency order.
Each milestone names the Lean declaration(s) that discharge it and the file containing them.
Status markers: **[done]** proved without `sorry`, **[open]** not yet formalised,
**[out of scope]** deliberately not attempted (reason given).

Notation: `X` a topological space, `Conf n X = {x : Fin n → X // Injective x}` with the subspace
topology of `Xⁿ`, `π : Conf (n+1) X → Conf n X` the map forgetting the last point.

## T. Topological layer (general spaces) — `ConfigurationSpaces/Topology/Basic.lean`

* **T1** Definition of `Conf n X` as a topological space; `Conf n X` is open in `Fin n → X` when
  `X` is `T2` (`Conf.isOpen_range_val`, `Conf.isOpenEmbedding_val`).
* **T2** Action of `Equiv.Perm (Fin n)` by `σ • x = x ∘ σ⁻¹` by homeomorphisms; the action is
  free (`Conf.permAction`, `Conf.continuous_smul`, `Conf.smul_eq_self_iff`).
* **T3** Forgetful map `Conf.forget : C(Conf (n+1) X, Conf n X)` (drop the last point),
  equivariant for `Perm (Fin n) ↪ Perm (Fin (n+1))` (`Conf.forget_smul`).
* **T4** Fibre identification: `Conf (n+1) X ≃ₜ {(y, p) : Conf n X × X // p ∉ range y}` over
  `Conf n X`, and the homeomorphism of the fibre over `y` with the punctured space
  `(range y)ᶜ` (`Conf.snocHomeomorph`, `Conf.fiberHomeomorph`).
* **T5** Functoriality: an injective continuous map / embedding / open embedding /
  homeomorphism `X → Y` induces a map `Conf n X → Conf n Y` of the same kind, commuting with the
  `Sₙ`-action and with `forget` (`Conf.map`, `Conf.map_smul`, `Conf.forget_map`,
  `Conf.mapHomeomorph`).

## L. Locally trivial maps and homotopy lifting — `Topology/LocallyTrivial.lean`, `Topology/CubeLifting.lean`

* **L1** `IsLocallyTrivial p`: every point of the base has an open neighbourhood `U` with a
  homeomorphism `p⁻¹ U ≃ₜ U × F` over `U` (fibre type `F` allowed to vary).
* **L2** Retraction of a box `∏ [aᵢ, bᵢ]` onto the union of a nonempty set `S` of its lower faces:
  `x ↦ x - (minᵢ∈S (xᵢ - aᵢ)) · 1_S` (`boxRetract`, continuity and retraction properties).
* **L3** Grid: for every open cover of the cube `Fin k → I` there is `m` such that every grid cell
  of side `1/m` lies in one member (Lebesgue number).
* **L4** Homotopy lifting for cubes (Serre-fibration property): for `p` locally trivial,
  `H : C(I × Iᵏ, B)` and a lift `g₀` of `H(0, ·)`, there is `G : C(I × Iᵏ, E)` with
  `p ∘ G = H`, `G (0, ·) = g₀` (`IsLocallyTrivial.exists_lift_cube`). Proof: cells processed in
  lexicographic order, each cell lifted through a trivialisation using the retraction **L2**.
* **L5** Path lifting (`IsLocallyTrivial.exists_path_lift`) and square lifting
  (`IsLocallyTrivial.exists_lift_square`) as special cases.

## S. The fundamental-group sequence of a locally trivial map — `Topology/FundamentalGroupSequence.lean`

Let `p : E → B` be continuous and locally trivial, `e₀ : E`, `F = p⁻¹{p e₀}`, `i : F → E`.

* **S1** `p_* ∘ i_* = 1`.
* **S2** Exactness at `π₁(E)`: `ker p_* = range i_*` (uses **L5**, square lifting, and the
  "three sides of a square" homotopy in the simply connected square).
* **S3** If `F` is path-connected, `p_*` is surjective (uses path lifting).
* **S4** If `π₂(B, p e₀)` is trivial, `i_*` is injective (uses **L4** with `k = 2`).
* Together: `1 → π₁(F) → π₁(E) → π₁(B) → 1` is exact under the hypotheses of **S3**, **S4**.

## P. Point-pushing homeomorphisms — `Topology/Push.lean`

* **P1** `HasLocalPushes X`: every `x` and neighbourhood `U` admit a neighbourhood `V` and a family
  of homeomorphisms `hᵥ` (`v ∈ V`), jointly continuous with jointly continuous inverses, supported
  in a closed set inside `U`, with `hᵥ x = v`.
* **P2** Real normed spaces have local pushes: `hᵥ(y) = y + max(0, 1 - ‖y - x‖/r) • (v - x)`; its
  inverse is a fixed point of a contraction, jointly Lipschitz in `(v, y)`.
* **P3** Hausdorff topological manifolds modelled on a finite-dimensional real normed space have
  local pushes (transport through a chart, extend by the identity; the support is compact).
* **P4** Multi-point pushes: for `y ∈ Conf n X` and an open `O ⊇ range y` there are a
  neighbourhood `W` of `y` and a jointly continuous family of homeomorphisms `Φ_z` (`z ∈ W`),
  supported in `O`, with `Φ_z ∘ y = z`.

## F. Fadell–Neuwirth — `Topology/FadellNeuwirth.lean`

* **F1** For `X` Hausdorff with local pushes, `Conf.forget : Conf (n+1) X → Conf n X` is locally
  trivial, with fibre `(range y)ᶜ` over `y` (`Conf.isLocallyTrivial_forget`).
* **F2** For a connected Hausdorff manifold of dimension `≥ 2` the complement of a finite set is
  path-connected; hence all fibres of `forget` are path-connected.
* **F3** Fadell–Neuwirth sequence: for such `X` (e.g. a connected surface, any Riemann surface)
  `π₁(X ∖ {y₁,…,yₙ}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact, and the first map is
  injective when `π₂(Conf n X)` is trivial.

## A. Algebraic layer — `ConfigurationSpaces/AlgebraicGeometry/Basic.lean`

For a separated morphism `X → S` of schemes:

* **A1** `Xⁿ` the `n`-fold fibre product (product in `Over S`); the closed partial diagonals
  `Δᵢⱼ`; `Conf n X` the open subscheme complementary to `⋃_{i ≠ j} Δᵢⱼ`, with its open immersion
  into `Xⁿ`.
* **A2** The `Sₙ`-action on `Xⁿ` over `S` preserves `Conf n X`, giving a group homomorphism
  `Perm (Fin n) → Aut_S(Conf n X)`.
* **A3** The forgetful morphisms `Conf (n+1) X → Conf n X` over `S`.
* **A4** Points over a field: for `K` a field, `S`-morphisms `Spec K → Conf n X` correspond to
  `n`-tuples of pairwise distinct `S`-morphisms `Spec K → X`.

## Out of scope (with reasons)

* The étale Fadell–Neuwirth / homotopy exact sequence: needs the étale homotopy exact sequence
  for proper/smooth morphisms with geometrically connected fibres (SGA 1 X, XIII), far beyond
  the current `lana-agents/pi1` (which provides the Galois-category definition of `π₁ᵉᵗ`).
* Asphericity of `Conf n X` for hyperbolic surfaces (needs `π₂` of punctured surfaces, i.e.
  uniformisation / classification); the injectivity statement **F3** is therefore stated under the
  hypothesis `π₂(Conf n X) = 0`.
