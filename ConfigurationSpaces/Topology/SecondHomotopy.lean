/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.CubeLifting
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Vanishing of second homotopy groups

We work with Mathlib's homotopy groups `π_ n X x` (homotopy classes of maps `Iⁿ → X` sending the
boundary `∂Iⁿ` to `x`, relative to `∂Iⁿ`) and prove that `π₂` vanishes in the following
situations.

* `HomotopyGroup.subsingleton_of_retract`, `HomotopyGroup.subsingleton_of_homeomorph`: `π_ n` of
  a retract (in particular of a homeomorphic space) of a space with trivial `π_ n` is trivial.
* `HomotopyGroup.subsingleton_of_convex`: `π_ n` of a convex subset of a real normed space is
  trivial (straight-line homotopy).
* `IsCoveringMap.subsingleton_homotopyGroup_two`: if `p : E → X` is a covering map and
  `π₂(E, e)` is trivial, then `π₂(X, p e)` is trivial: a map of the square sending the boundary to
  `p e` lifts to `E` (homotopy lifting), the lift sends the boundary into the discrete fibre and
  hence to `e`, and a null-homotopy of the lift projects to a null-homotopy.
* `IsLocallyTrivial.subsingleton_homotopyGroup_two`: for a locally trivial map `p : E → B` with
  fibre `F` through `e₀`, if `π₂(F, e₀)` and `π₂(B, p e₀)` are trivial then so is `π₂(E, e₀)`
  (exactness of `π₂(F) → π₂(E) → π₂(B)`). Proof: lift a null-homotopy `K : I × I² → B` of
  `p ∘ γ` (fixing `∂I²`) to `L : I × I² → E` starting at `γ`. The five faces of the cube other
  than the bottom face `{0} × I²` are mapped into `F`; reparametrising them by the radial
  projection `ρ` from the point `(-1, ½, ½)` gives a map `δ = L ∘ ρ : I² → F` with
  `δ (∂I²) = e₀`, and the straight-line homotopy from `(0, y)` to `ρ y` inside the cube shows
  `γ ≃ δ` relative to `∂I²`. Finally `δ` is null-homotopic in `F`.
-/

open Set Function Topology unitInterval

universe u v

namespace GenLoop

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- Two generalised loops are homotopic (relative to the boundary) as soon as a continuous map
of `I × Iᴺ` interpolates between them and maps `I × ∂Iᴺ` to the base point. -/
theorem homotopic_of_map (γ δ : GenLoop N X x) (H : C(I × (N → I), X)) (h0 : ∀ y, H (0, y) = γ y)
    (h1 : ∀ y, H (1, y) = δ y) (hb : ∀ t, ∀ y ∈ Cube.boundary N, H (t, y) = x) :
    Homotopic γ δ :=
  ⟨{ toContinuousMap := H
     map_zero_left := h0
     map_one_left := h1
     prop' := fun t y hy ↦ by
       change H (t, y) = γ y
       rw [hb t y hy, GenLoop.boundary γ y hy] }⟩

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `π_ N X x` is trivial iff every generalised loop is homotopic to the constant one. -/
theorem subsingleton_iff_forall {x : X} :
    Subsingleton (HomotopyGroup N X x) ↔
      ∀ γ : GenLoop N X x, GenLoop.Homotopic γ GenLoop.const := by
  refine ⟨fun h γ ↦ Quotient.exact (Subsingleton.elim (α := HomotopyGroup N X x) ⟦γ⟧
    ⟦GenLoop.const⟧), fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  induction a using Quotient.inductionOn with | h a => ?_
  induction b using Quotient.inductionOn with | h b => ?_
  exact Quotient.sound ((h a).trans (h b).symm)

/-- The generalised loop `f ∘ γ`. -/
def _root_.GenLoop.map (f : C(X, Y)) {x : X} (γ : GenLoop N X x) : GenLoop N Y (f x) :=
  ⟨f.comp γ.1, fun y hy ↦ by
    change f (γ y) = f x
    rw [GenLoop.boundary γ y hy]⟩

/-- If `X` is a retract of `Y` (via `f : X → Y`, `g : Y → X`, `g ∘ f = id`) and
`π_ N Y (f x)` is trivial, then `π_ N X x` is trivial. -/
theorem subsingleton_of_retract (f : C(X, Y)) (g : C(Y, X)) (hgf : ∀ x, g (f x) = x) (x : X)
    (h : Subsingleton (HomotopyGroup N Y (f x))) : Subsingleton (HomotopyGroup N X x) := by
  rw [subsingleton_iff_forall] at h ⊢
  intro γ
  have := (h (GenLoop.map f γ)).comp_continuousMap g
  unfold GenLoop.Homotopic
  convert this using 1
  · ext y
    exact (hgf _).symm
  · ext y
    exact (hgf _).symm

/-- Homeomorphic spaces: triviality of `π_ N` transfers. -/
theorem subsingleton_of_homeomorph (e : X ≃ₜ Y) (x : X)
    (h : Subsingleton (HomotopyGroup N Y (e x))) : Subsingleton (HomotopyGroup N X x) :=
  subsingleton_of_retract (e : C(X, Y)) (e.symm : C(Y, X)) e.symm_apply_apply x h

/-- The homotopy groups of a subsingleton space are trivial. -/
theorem subsingleton_of_subsingleton [Subsingleton X] (x : X) :
    Subsingleton (HomotopyGroup N X x) :=
  subsingleton_iff_forall.2 fun γ ↦ by
    have : γ = GenLoop.const := GenLoop.ext _ _ fun _ ↦ Subsingleton.elim _ _
    rw [this]

/-- The homotopy groups of a convex subset of a real normed space are trivial. -/
theorem subsingleton_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) (x : s) : Subsingleton (HomotopyGroup N s x) := by
  rw [subsingleton_iff_forall]
  intro γ
  have hmem : ∀ q : I × (N → I),
      (1 - (q.1 : ℝ)) • (γ q.2 : E) + (q.1 : ℝ) • (x : E) ∈ s := fun q ↦
    hs (γ q.2).2 x.2 (sub_nonneg.2 q.1.2.2) q.1.2.1 (by ring)
  refine GenLoop.homotopic_of_map γ _
    ⟨fun q ↦ ⟨_, hmem q⟩, Continuous.subtype_mk (by fun_prop) _⟩ (fun y ↦ ?_) (fun y ↦ ?_)
    (fun t y hy ↦ ?_)
  · exact Subtype.ext (by simp)
  · exact Subtype.ext (by simp [GenLoop.const_apply])
  · refine Subtype.ext ?_
    simp only [ContinuousMap.coe_mk, GenLoop.boundary γ y hy]
    rw [← add_smul, sub_add_cancel, one_smul]

/-- The homotopy groups of a real normed space are trivial. -/
theorem subsingleton_of_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : Subsingleton (HomotopyGroup N E x) :=
  subsingleton_of_homeomorph (Homeomorph.Set.univ E).symm x
    (subsingleton_of_convex convex_univ _)

end HomotopyGroup

/-! ### Covering maps -/

section Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- The point `![t, s]` of the square `I²`. -/
def sqPt' (q : I × I) : Fin 2 → I := ![q.1, q.2]

theorem continuous_sqPt' : Continuous sqPt' :=
  continuous_pi fun i ↦ by fin_cases i <;> [exact continuous_fst; exact continuous_snd]

theorem sqPt'_mem_boundary {t s : I} (h : t = 0 ∨ t = 1 ∨ s = 0 ∨ s = 1) :
    sqPt' (t, s) ∈ Cube.boundary (Fin 2) := by
  rcases h with h | h | h | h
  · exact ⟨0, Or.inl h⟩
  · exact ⟨0, Or.inr h⟩
  · exact ⟨1, Or.inl h⟩
  · exact ⟨1, Or.inr h⟩

/-- A path in `E` lying over a single point of the base of a covering map is constant. -/
theorem IsCoveringMap.eq_of_forall_eq {p : E → X} (hp : IsCoveringMap p) (c : C(I, E)) {e : E}
    (hc : ∀ t, p (c t) = p e) {t₀ : I} (h₀ : c t₀ = e) (t : I) : c t = e := by
  have := hp.eq_of_comp_eq c.continuous continuous_const (funext hc) t₀ h₀
  exact congrFun this t

/-- **Covering maps and `π₂`.** If `p : E → X` is a covering map and `π₂(E, e)` is trivial, then
`π₂(X, p e)` is trivial. -/
theorem IsCoveringMap.subsingleton_homotopyGroup_two {p : E → X} (hp : IsCoveringMap p) (e : E)
    (h : Subsingleton (π_ 2 E e)) : Subsingleton (π_ 2 X (p e)) := by
  rw [HomotopyGroup.subsingleton_iff_forall] at h ⊢
  intro γ
  let H : C(I × I, X) := γ.1.comp ⟨sqPt', continuous_sqPt'⟩
  have hHb : ∀ t s : I, (t = 0 ∨ t = 1 ∨ s = 0 ∨ s = 1) → H (t, s) = p e := fun t s hts ↦
    GenLoop.boundary γ _ (sqPt'_mem_boundary hts)
  let L := hp.liftHomotopy H (ContinuousMap.const I e) fun s ↦ hHb 0 s (Or.inl rfl)
  have hL : ∀ q, p (L q) = H q := fun q ↦ congrFun (hp.liftHomotopy_lifts _ _ _) q
  have hL0 : ∀ s, L (0, s) = e := fun s ↦ hp.liftHomotopy_zero _ _ _ s
  -- the lift is constant on the boundary of the square
  have hs0 : ∀ t, L (t, 0) = e := hp.eq_of_forall_eq (L.comp ⟨fun t ↦ (t, 0), by fun_prop⟩)
    (fun t ↦ (hL _).trans (hHb t 0 (Or.inr (Or.inr (Or.inl rfl))))) (t₀ := 0) (hL0 0)
  have hs1 : ∀ t, L (t, 1) = e := hp.eq_of_forall_eq (L.comp ⟨fun t ↦ (t, 1), by fun_prop⟩)
    (fun t ↦ (hL _).trans (hHb t 1 (Or.inr (Or.inr (Or.inr rfl))))) (t₀ := 0) (hL0 1)
  have ht1 : ∀ s, L (1, s) = e := hp.eq_of_forall_eq (L.comp ⟨fun s ↦ (1, s), by fun_prop⟩)
    (fun s ↦ (hL _).trans (hHb 1 s (Or.inr (Or.inl rfl)))) (t₀ := 0) (hs0 1)
  let G : GenLoop (Fin 2) E e := ⟨L.comp ⟨fun y ↦ (y 0, y 1), by fun_prop⟩, by
    rintro y ⟨i, hi⟩
    fin_cases i <;> rcases hi with hi | hi <;>
      simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hi, hL0, ht1, hs0, hs1]⟩
  have hG := (h G).comp_continuousMap ⟨p, hp.continuous⟩
  unfold GenLoop.Homotopic
  convert hG using 1
  · ext y
    change γ y = p (L (y 0, y 1))
    rw [hL]
    change γ y = γ (sqPt' (y 0, y 1))
    congr 1
    funext i
    fin_cases i <;> rfl
  · ext; rfl

end Covering

/-! ### Locally trivial maps: exactness of `π₂(F) → π₂(E) → π₂(B)` -/

namespace RadialProjection

/-- `max (½, |2y₀ - 1|, |2y₁ - 1|)`, the sup-norm distance of `y` from the centre of the
square, rescaled, and at least `½`. -/
noncomputable def radius (y : Fin 2 → I) : ℝ :=
  max (max (1 / 2) |2 * (y 0 : ℝ) - 1|) |2 * (y 1 : ℝ) - 1|

@[fun_prop] theorem continuous_radius : Continuous radius := by
  unfold radius; fun_prop

theorem half_le_radius (y : Fin 2 → I) : 1 / 2 ≤ radius y :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem radius_pos (y : Fin 2 → I) : 0 < radius y :=
  lt_of_lt_of_le (by norm_num) (half_le_radius y)

theorem abs_le_one (s : I) : |2 * (s : ℝ) - 1| ≤ 1 :=
  abs_le.2 ⟨by linarith [s.2.1], by linarith [s.2.2]⟩

theorem radius_le_one (y : Fin 2 → I) : radius y ≤ 1 :=
  max_le (max_le (by norm_num) (abs_le_one _)) (abs_le_one _)

/-- Projection of a real number to `I`. -/
noncomputable abbrev clamp (r : ℝ) : I := projIcc 0 1 zero_le_one r

/-- The radial projection of the bottom face `{0} × I²` of the cube `I × I²` from the point
`(-1, ½, ½)` onto the union of the other five faces. -/
noncomputable def proj (y : Fin 2 → I) : I × (Fin 2 → I) :=
  (clamp (1 / radius y - 1), fun i ↦ clamp (1 / 2 + 1 / radius y * ((y i : ℝ) - 1 / 2)))

@[fun_prop] theorem continuous_proj : Continuous proj := by
  have hr : Continuous fun y ↦ 1 / radius y :=
    continuous_const.div continuous_radius fun y ↦ (radius_pos y).ne'
  refine (continuous_projIcc.comp (hr.sub continuous_const)).prodMk
    (continuous_pi fun i ↦ continuous_projIcc.comp ?_)
  fun_prop

theorem proj_of_mem_boundary {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    proj y = (0, y) := by
  obtain ⟨i, hi⟩ := hy
  have hai : |2 * (y i : ℝ) - 1| = 1 := by
    rcases hi with hi | hi <;> norm_num [hi]
  have hr : radius y = 1 := by
    refine le_antisymm (radius_le_one y) ?_
    rw [← hai]
    fin_cases i
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · simp [proj, hr]
  · simp only [proj, hr, div_one, one_mul]
    rw [show (1 / 2 : ℝ) + ((y j : ℝ) - 1 / 2) = y j by ring]
    exact projIcc_val zero_le_one (y j)

theorem clamp_eq_one {r : ℝ} (h : 1 ≤ r) : clamp r = 1 := by
  rw [clamp, projIcc_of_right_le _ h]; rfl

theorem clamp_eq_zero {r : ℝ} (h : r ≤ 0) : clamp r = 0 := by
  rw [clamp, projIcc_of_le_left _ h]; rfl

/-- The radial projection lands on the top face or on the sides of the cube. -/
theorem proj_mem (y : Fin 2 → I) : (proj y).1 = 1 ∨ (proj y).2 ∈ Cube.boundary (Fin 2) := by
  have hpos := radius_pos y
  have side : ∀ i, radius y = |2 * (y i : ℝ) - 1| → (proj y).2 ∈ Cube.boundary (Fin 2) := by
    intro i hi
    refine ⟨i, ?_⟩
    simp only [proj]
    rcases abs_eq hpos.le |>.1 hi.symm with h | h
    · right
      apply clamp_eq_one
      have : (y i : ℝ) - 1 / 2 = radius y / 2 := by linarith
      rw [this]; field_simp; linarith
    · left
      apply clamp_eq_zero
      have : (y i : ℝ) - 1 / 2 = -(radius y / 2) := by linarith
      rw [this]; field_simp; linarith
  rcases max_choice (max (1 / 2) |2 * (y 0 : ℝ) - 1|) |2 * (y 1 : ℝ) - 1| with h | h
  · rcases max_choice (1 / 2 : ℝ) |2 * (y 0 : ℝ) - 1| with h' | h'
    · left
      have hr : radius y = 1 / 2 := by rw [radius, h, h']
      exact clamp_eq_one (by rw [hr]; norm_num)
    · exact Or.inr (side 0 (by rw [radius, h, h']))
  · exact Or.inr (side 1 (by rw [radius, h]))

end RadialProjection

namespace IsLocallyTrivial

open RadialProjection

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- **`π₂` of the total space of a locally trivial map.** Let `p : E → B` be locally trivial and
`F = p⁻¹(p e₀)`. If `π₂(F, e₀)` and `π₂(B, p e₀)` are trivial, then `π₂(E, e₀)` is trivial. -/
theorem subsingleton_homotopyGroup_two (p : C(E, B)) (hp : IsLocallyTrivial p) (e₀ : E)
    (hF : Subsingleton (π_ 2 (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩)) (hB : Subsingleton (π_ 2 B (p e₀))) :
    Subsingleton (π_ 2 E e₀) := by
  rw [HomotopyGroup.subsingleton_iff_forall] at hF hB ⊢
  intro γ
  obtain ⟨K⟩ := hB (GenLoop.map p γ)
  obtain ⟨L, hL, hL0⟩ := hp.exists_lift_homotopy K.toContinuousMap γ.1 fun y ↦ by
    simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap, K.apply_zero]; rfl
  have hLK : ∀ q, p (L q) = K q := fun q ↦ congrFun hL q
  have hside : ∀ u, ∀ y ∈ Cube.boundary (Fin 2), p (L (u, y)) = p e₀ := fun u y hy ↦ by
    rw [hLK, K.eq_fst u hy]
    change p (γ y) = p e₀
    rw [GenLoop.boundary γ y hy]
  have htop : ∀ y, p (L (1, y)) = p e₀ := fun y ↦ by
    rw [hLK, K.apply_one]; rfl
  have hfib : ∀ y, L (proj y) ∈ p ⁻¹' {p e₀} := fun y ↦ by
    rcases proj_mem y with h | h
    · rw [← Prod.mk.eta (p := proj y), h]; exact htop _
    · rw [← Prod.mk.eta (p := proj y)]; exact hside _ _ h
  have hγb : ∀ y ∈ Cube.boundary (Fin 2), L (proj y) = e₀ := fun y hy ↦ by
    rw [proj_of_mem_boundary hy, hL0]; exact GenLoop.boundary γ y hy
  -- the map `δ = L ∘ ρ` into the fibre
  let δ : GenLoop (Fin 2) (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩ :=
    ⟨⟨fun y ↦ ⟨L (proj y), hfib y⟩, (L.continuous.comp continuous_proj).subtype_mk _⟩,
      fun y hy ↦ Subtype.ext (hγb y hy)⟩
  -- `γ` is homotopic to `δ` (as a loop in `E`)
  let δE : GenLoop (Fin 2) E e₀ :=
    GenLoop.map ⟨Subtype.val, continuous_subtype_val⟩ δ
  have h1 : GenLoop.Homotopic γ δE := by
    let H : I × (Fin 2 → I) → E := fun q ↦ L (clamp ((q.1 : ℝ) * ((proj q.2).1 : ℝ)),
      fun i ↦ clamp ((1 - (q.1 : ℝ)) * (q.2 i : ℝ) + (q.1 : ℝ) * ((proj q.2).2 i : ℝ)))
    have hH : Continuous H := by
      have hp1 : Continuous fun q : I × (Fin 2 → I) ↦ ((proj q.2).1 : ℝ) :=
        continuous_subtype_val.comp (continuous_fst.comp (continuous_proj.comp continuous_snd))
      have hp2 : ∀ i, Continuous fun q : I × (Fin 2 → I) ↦ ((proj q.2).2 i : ℝ) := fun i ↦
        continuous_subtype_val.comp ((continuous_apply i).comp
          (continuous_snd.comp (continuous_proj.comp continuous_snd)))
      have ht : Continuous fun q : I × (Fin 2 → I) ↦ (q.1 : ℝ) := by fun_prop
      refine L.continuous.comp ((continuous_projIcc.comp (ht.mul hp1)).prodMk
        (continuous_pi fun i ↦ continuous_projIcc.comp ?_))
      exact (by fun_prop : Continuous fun q : I × (Fin 2 → I) ↦
        (1 - (q.1 : ℝ)) * (q.2 i : ℝ)).add (ht.mul (hp2 i))
    refine GenLoop.homotopic_of_map γ δE ⟨H, hH⟩ (fun y ↦ ?_) (fun y ↦ ?_) (fun t y hy ↦ ?_)
    · change L _ = γ y
      refine (congrArg L ?_).trans (hL0 y)
      refine Prod.ext ?_ (funext fun i ↦ ?_)
      · simp [clamp]
      · simp only [Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
        exact projIcc_val zero_le_one _
    · change L _ = L (proj y)
      congr 1
      refine Prod.ext ?_ (funext fun i ↦ ?_)
      · simp only [Icc.coe_one, one_mul]
        exact projIcc_val zero_le_one _
      · simp only [Icc.coe_one, sub_self, zero_mul, zero_add, one_mul]
        exact projIcc_val zero_le_one _
    · change L _ = e₀
      rw [← hγb y hy, proj_of_mem_boundary hy]
      congr 1
      refine Prod.ext ?_ (funext fun i ↦ ?_)
      · simp [clamp]
      · change clamp _ = y i
        rw [show (1 - (t : ℝ)) * (y i : ℝ) + (t : ℝ) * (y i : ℝ) = y i by ring]
        exact projIcc_val zero_le_one _
  -- and `δ` is null-homotopic in the fibre
  have h2 : GenLoop.Homotopic δE GenLoop.const :=
    (hF δ).comp_continuousMap ⟨Subtype.val, continuous_subtype_val⟩
  exact h1.trans h2

end IsLocallyTrivial
