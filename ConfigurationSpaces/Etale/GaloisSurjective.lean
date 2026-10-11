/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Topology

/-!
# Surjectivity of induced maps of fundamental groups of Galois categories

Let `F` be a fibre functor on a Galois category `C` and `H : D ⥤ C` a functor from a Galois
category `D` such that `H ⋙ F` is again a fibre functor. Then `Aut F` acts on the fibres of
`H ⋙ F`, which gives the homomorphism `Aut F →* Aut (H ⋙ F)`, `σ ↦ σ ◫ H` (whiskering).

**Theorem** (`PreGaloisCategory.toAut_comp_surjective`, SGA 1 V.6.9, "if" direction). If `H`
sends connected objects to connected objects, then `Aut F → Aut (H ⋙ F)` is surjective.

Proof: `Aut F` is compact and acts continuously on all fibres, and it acts transitively on the
fibre of every connected object of `C`, in particular on `F (H Y)` for connected `Y : D`
(`FiberFunctor.isPretransitive_of_isConnected`); conclude by
`PreGaloisCategory.toAut_surjective_of_isPretransitive`.

For the étale fundamental group (`lana-agents/pi1`: `π₁ᵉᵗ(ξ) = Aut (fiber ξ)` on the Galois
category of finite étale `X`-schemes) and a morphism `f : X ⟶ Y`, this is the Galois-theoretic
half of the surjectivity of `π₁ᵉᵗ(X, ξ) → π₁ᵉᵗ(Y, f ∘ ξ)`, with `H` the pullback functor
`f^*`. The geometric half — `f^*` preserves connectedness when `f` is universally open with
geometrically connected fibres, and the identification `f^* ⋙ fiber ξ ≅ fiber (ξ ≫ f)` — is not
formalised here; see the README for what is missing to apply this to
`Conf_{n+1}(X) → Conf_n(X)`.
-/

universe u₁ u₂ u₃ u₄

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type u₃} [Category.{u₄} D]
  (F : C ⥤ FintypeCat.{u₂}) (H : D ⥤ C)

/-- `Aut F` acts on the fibres of `H ⋙ F`. -/
instance mulActionComp (Y : D) : MulAction (Aut F) ((H ⋙ F).obj Y) :=
  inferInstanceAs (MulAction (Aut F) (F.obj (H.obj Y)))

instance : IsNaturalSMul (H ⋙ F) (Aut F) where
  naturality σ _ _ f x := (mulAction_naturality F σ (H.map f) x).symm

/-- The homomorphism `Aut F →* Aut (H ⋙ F)` is whiskering with `H`. -/
theorem toAut_comp_hom_app (σ : Aut F) (Y : D) :
    (toAut (H ⋙ F) (Aut F) σ).hom.app Y = σ.hom.app (H.obj Y) := by
  ext x
  exact toAut_hom_app_apply (H ⋙ F) σ x

/-- **SGA 1 V.6.9 (Galois-theoretic part).** If `H : D ⥤ C` sends connected objects to connected
objects and `H ⋙ F` is a fibre functor, then `Aut F → Aut (H ⋙ F)` is surjective. -/
theorem toAut_comp_surjective [GaloisCategory C] [FiberFunctor F] [GaloisCategory D]
    [FiberFunctor (H ⋙ F)] (hH : ∀ Y : D, IsConnected Y → IsConnected (H.obj Y)) :
    Function.Surjective (toAut (H ⋙ F) (Aut F)) := by
  haveI (Y : D) : ContinuousSMul (Aut F) ((H ⋙ F).obj Y) := continuousSMul_aut_fiber F (H.obj Y)
  refine toAut_surjective_of_isPretransitive (H ⋙ F) (Aut F) fun Y _ ↦ ?_
  haveI := hH Y inferInstance
  exact FiberFunctor.isPretransitive_of_isConnected F (H.obj Y)

end CategoryTheory.PreGaloisCategory
