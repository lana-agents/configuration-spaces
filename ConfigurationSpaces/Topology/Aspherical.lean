/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.FadellNeuwirth
import ConfigurationSpaces.Topology.SecondHomotopy

/-!
# `π₂` of configuration spaces

Let `X` be a Hausdorff space with local pushes (e.g. a Hausdorff topological manifold), such that
`π₂(X ∖ S) = 0` at every base point for every finite set `S ⊆ X` (`PuncturedAspherical₂ X`).
Then `π₂(Conf n X) = 0` for all `n` (`Conf.subsingleton_pi_two`): by induction on `n`, using the
Fadell–Neuwirth fibration `Conf (n+1) X → Conf n X` with fibre `X ∖ {y₀, …, yₙ₋₁}` and the
exactness of `π₂(F) → π₂(E) → π₂(B)` (`IsLocallyTrivial.subsingleton_homotopyGroup_two`).

Consequently the Fadell–Neuwirth sequence
`1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact for every connected
Hausdorff manifold `X` of dimension `> 1` with `PuncturedAspherical₂ X`
(`Conf.fadellNeuwirth_injective_of_puncturedAspherical₂`). Spaces satisfying the hypothesis
(open subsets of `ℂ`, and every space covered by an open subset of `ℂ`) are provided in
`ConfigurationSpaces/Topology/PlanarDomain.lean`.
-/

open Set Function Topology

universe u

/-- `X` has trivial `π₂` after removing any finite set of points, at every base point. -/
def PuncturedAspherical₂ (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ S : Set X, S.Finite → ∀ x : (Sᶜ : Set X), Subsingleton (π_ 2 (Sᶜ : Set X) x)

namespace Conf

variable {X : Type u} [TopologicalSpace X]

instance subsingleton_zero : Subsingleton (Conf 0 X) :=
  ⟨fun _ _ ↦ Conf.ext fun i ↦ i.elim0⟩

/-- **Asphericity in degree 2 of configuration spaces.** If `X` is Hausdorff with local pushes
and `π₂(X ∖ S) = 0` for all finite `S`, then `π₂(Conf n X) = 0` at every base point. -/
theorem subsingleton_pi_two [T2Space X] (hX : HasLocalPushes X) (h : PuncturedAspherical₂ X) :
    ∀ (n : ℕ) (y : Conf n X), Subsingleton (π_ 2 (Conf n X) y)
  | 0, y => HomotopyGroup.subsingleton_of_subsingleton y
  | n + 1, y => (isLocallyTrivial_forget hX n).subsingleton_homotopyGroup_two forget y
      (HomotopyGroup.subsingleton_of_homeomorph (fiberHomeomorph (forget y)) _
        (h _ (finite_range _) _))
      (subsingleton_pi_two hX h n (forget y))

/-- **Fadell–Neuwirth, injectivity, unconditionally** for manifolds `X` with
`PuncturedAspherical₂ X`: `π₁(X ∖ {y₀, …, yₙ₋₁}) → π₁(Conf (n+1) X)` is injective. -/
theorem fadellNeuwirth_injective_of_puncturedAspherical₂ {n : ℕ} (x₀ : Conf (n + 1) X)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space X]
    [ChartedSpace E X] (h : PuncturedAspherical₂ X) :
    Injective (puncturedToConf x₀) :=
  fadellNeuwirth_injective x₀ E
    (subsingleton_pi_two (ChartedSpace.hasLocalPushes E X) h n (forget x₀))

/-- **The Fadell–Neuwirth short exact sequence** for a connected Riemann surface `X` (more
generally a connected Hausdorff space with a `ℂ`-atlas) with `PuncturedAspherical₂ X`:
`1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact. -/
theorem fadellNeuwirth_exact_complex {n : ℕ} [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    (h : PuncturedAspherical₂ X) (x₀ : Conf (n + 1) X) :
    Injective (puncturedToConf x₀) ∧
      (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker ∧
      Surjective (FundamentalGroup.map forget x₀) :=
  ⟨fadellNeuwirth_injective_of_puncturedAspherical₂ x₀ ℂ h, fadellNeuwirth_complex x₀⟩

end Conf
