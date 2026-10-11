/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn

/-!
# Locally trivial maps

A map `p : E → B` is *locally trivial* if every point of `B` has an open neighbourhood `U` such
that `p⁻¹ U` is homeomorphic to `U × F` over `U`, for some space `F` (which may depend on the
point). This is the notion of a fibre bundle without a fixed model fibre; it is the hypothesis of
the homotopy lifting theorem `IsLocallyTrivial.exists_lift_cube`.

The main technical statement here is `extend_through_trivialization`: over a trivialising open
set, a lift defined on a retract `L` of a set `s` extends to a lift on `s`.
-/

open Set Function Topology

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A map `p : E → B` is locally trivial if every `b : B` has an open neighbourhood `U` and a
homeomorphism `p⁻¹ U ≃ₜ U × F` commuting with the projections to `U`. -/
def IsLocallyTrivial (p : E → B) : Prop :=
  ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ (F : Type u) (_ : TopologicalSpace F)
    (φ : p ⁻¹' U ≃ₜ U × F), ∀ x, ((φ x).1 : B) = p x

/-- A trivialisation over a set `U` gives back `x` from its base point and fibre coordinate. -/
theorem trivialization_symm_apply_fst_snd {p : E → B} {U : Set B} {F : Type*}
    [TopologicalSpace F] (φ : p ⁻¹' U ≃ₜ U × F) (hφ : ∀ x, ((φ x).1 : B) = p x)
    (x : p ⁻¹' U) {b : U} (hb : (b : B) = p x) : φ.symm (b, (φ x).2) = x := by
  have : (b, (φ x).2) = φ x := Prod.ext (Subtype.ext (by rw [hb, hφ])) rfl
  rw [this, Homeomorph.symm_apply_apply]

/-- **Lifting over one trivialising set.** Let `φ` trivialise `p` over `U`, let `r` be a retraction
of `s` onto `L ⊆ s` (continuous on `s`), let `H` be continuous on `s` with values in `U`, and let
`g` be a lift of `H` on `L`, continuous on `L`. Then `g` extends to a lift of `H` on `s`,
continuous on `s`: in the trivialisation, keep the base point `H x` and take the fibre coordinate
of `g (r x)`. -/
theorem extend_through_trivialization {Q : Type*} [TopologicalSpace Q] {p : E → B}
    {U : Set B} {F : Type*} [TopologicalSpace F] (φ : p ⁻¹' U ≃ₜ U × F)
    (hφ : ∀ x, ((φ x).1 : B) = p x) {s L : Set Q} (hLs : L ⊆ s) {r : Q → Q}
    (hr : ContinuousOn r s) (hrL : MapsTo r s L) (hrfix : ∀ x ∈ L, r x = x) {H : Q → B}
    (hH : ContinuousOn H s) (hHU : MapsTo H s U) {g : Q → E} (hg : ContinuousOn g L)
    (hgH : ∀ x ∈ L, p (g x) = H x) :
    ∃ g' : Q → E, ContinuousOn g' s ∧ (∀ x ∈ s, p (g' x) = H x) ∧ ∀ x ∈ L, g' x = g x := by
  classical
  have hmem : ∀ x : s, g (r x) ∈ p ⁻¹' U := fun x ↦ by
    rw [mem_preimage, hgH _ (hrL x.2)]
    exact hHU (hLs (hrL x.2))
  let f : s → E := fun x ↦ (φ.symm (⟨H x, hHU x.2⟩, (φ ⟨g (r x), hmem x⟩).2)).1
  have hf : Continuous f := by
    refine continuous_subtype_val.comp (φ.symm.continuous.comp ?_)
    refine Continuous.prodMk (hH.restrict.subtype_mk _) (continuous_snd.comp ?_)
    exact φ.continuous.comp (((hg.comp hr hrL).restrict).subtype_mk _)
  have hfp : ∀ x : s, p (f x) = H x := fun x ↦ by
    rw [← hφ, Homeomorph.apply_symm_apply]
  have hfL : ∀ (x : s), (x : Q) ∈ L → f x = g x := fun x hx ↦ by
    have h1 : r x = x := hrfix _ hx
    have key : φ.symm (⟨H x, hHU x.2⟩, (φ ⟨g (r x), hmem x⟩).2) = ⟨g (r x), hmem x⟩ :=
      trivialization_symm_apply_fst_snd φ hφ _ (by simp [h1, hgH _ hx])
    change (φ.symm (⟨H x, hHU x.2⟩, (φ ⟨g (r x), hmem x⟩).2)).1 = g x
    rw [key]
    exact congrArg g h1
  refine ⟨fun x ↦ if h : x ∈ s then f ⟨x, h⟩ else g x, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    convert hf using 1
    ext x
    simp [x.2]
  · intro x hx
    simp only [hx, dite_true]
    exact hfp ⟨x, hx⟩
  · intro x hx
    simp only [hLs hx, dite_true]
    exact hfL ⟨x, hLs hx⟩ hx
