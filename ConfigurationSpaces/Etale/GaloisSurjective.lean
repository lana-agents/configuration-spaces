/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Mathlib.CategoryTheory.Galois.FiberAutMap
import Pi1.FundamentalGroup.Functoriality
import ConfigurationSpaces.AlgebraicGeometry.Fibers

/-!
# Surjectivity of `π₁ᵉᵗ(Conf_{n+1}(X)) → π₁ᵉᵗ(Conf_n(X))`

The Galois-theoretic input (SGA 1 V.6.9) lives in `lana-agents/pi1`:

* `CategoryTheory.PreGaloisCategory.toAut_comp_surjective`,
  `PreGaloisCategory.fiberAutMap_surjective` (`Pi1/Mathlib/CategoryTheory/Galois/FiberAutMap`):
  if `H : D ⥤ C` sends connected objects to connected objects, `Aut F → Aut (H ⋙ F)` is
  surjective (this file used to contain these; they were moved to `pi1`);
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap f h : π₁ᵉᵗ(ξ) →ₜ* π₁ᵉᵗ(η)` for
  `f : Y ⟶ X`, `ξ ≫ f = η`, and `fundamentalGroupMap_surjective_of_geometricallyConnected`: for
  `f` universally open with geometrically connected fibres between connected schemes it is
  surjective (`Pi1/FundamentalGroup/Functoriality`).

The geometric input for `forget : Conf_{n+1}(X) ⟶ Conf_n(X)` is
`ConfigurationSpaces/AlgebraicGeometry/Fibers.lean`: its fibres over field-valued points are the
open subschemes `X_K ∖ {z₀, …, zₙ₋₁}`, hence geometrically irreducible when the geometric fibres of
`X ⟶ S` are irreducible and infinite, and `forget` is universally open when `X ⟶ S` is.

**Theorem** (`ConfScheme.fundamentalGroupMap_forget_surjective`). Let `S` be connected and `X` a
separated `S`-scheme such that `X ⟶ S` is universally open with irreducible infinite geometric
fibres (e.g. a geometrically irreducible curve over a field, granting universal openness, which is
EGA IV 2.4.6 / 2.4.10 and not in Mathlib). Then `π₁ᵉᵗ(Conf_{n+1}(X), ξ) → π₁ᵉᵗ(Conf_n(X), ξ')`
is surjective for every geometric point `ξ` of `Conf_{n+1}(X)`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.ConfScheme

variable {S : Scheme.{u}} {X : Over S} [IsSeparated X.hom]

/-- **Surjectivity of `π₁ᵉᵗ(Conf_{n+1}(X)) → π₁ᵉᵗ(Conf_n(X))`** (SGA 1 V.6.9), for `S` connected
and `X ⟶ S` universally open with irreducible infinite geometric fibres. -/
theorem fundamentalGroupMap_forget_surjective [ConnectedSpace S] [UniversallyOpen X.hom]
    (hX : geometrically GeomIrreducibleInfinite X.hom) (n : ℕ) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ (ConfScheme X (n + 1)).left)
    {η : Spec (.of Ω) ⟶ (ConfScheme X n).left} (h : ξ ≫ (forget X n).left = η) :
    Function.Surjective (FiniteEtale.fundamentalGroupMap (forget X n).left h) := by
  haveI := connectedSpace hX n
  haveI := connectedSpace hX (n + 1)
  haveI := geometricallyConnected_forget n hX
  haveI := universallyOpen_forget X n
  exact FiniteEtale.fundamentalGroupMap_surjective_of_geometricallyConnected _ h

end AlgebraicGeometry.ConfScheme
