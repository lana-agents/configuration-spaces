/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.Aspherical
import Mathlib.Analysis.Complex.CoveringMap
import Oka.Uniformization.LatticeComplement

/-!
# Open subsets of `ℂ` have trivial `π₂`

**Theorem** (`Complex.subsingleton_pi_two_of_isOpen`). For every open `U ⊆ ℂ` and `u ∈ U`,
`π₂(U, u) = 0`.

Proof. A map `I² → U` with boundary at `u` has connected image, so it lies in the connected
component `Ω` of `u` in `U`, which is open and connected. If `Ω = ℂ`, it is convex. If `ℂ ∖ Ω`
is a single point `a`, then `z ↦ a + exp z` is a covering `ℂ → Ω`. Otherwise `Ω` omits two
points `a ≠ b`, and the plane uniformisation theorem of `lana-agents/oka`
(`Uniformization.PlaneData.exists_covering`, by the Koebe iteration) gives a covering of `Ω` by the
unit disc. Its input, a holomorphic covering of `Ω` by an open subset of the disc containing `0`,
is built as in `oka`'s uniformisation of lattice complements (`Oka/Uniformization/
LatticeComplement.lean`, which treats `Ω = ℂ ∖ Λ`): an affine map `T` sends `a, b` onto the two
branch values of the modular function `j`, and `T⁻¹ ∘ j` (precomposed with a Cayley transform and a
disc automorphism) is a covering of `ℂ ∖ T⁻¹{j(i), j(ρ)} ⊇ Ω`. In both cases `π₂` of the covering
space is trivial (convexity), hence so is `π₂(Ω)` (`IsCoveringMap.subsingleton_homotopyGroup_two`).

**Consequences.**
* `puncturedAspherical₂_of_isCoveringMap`: a T₁ space `X` admitting a surjective covering map
  from a space that embeds openly in `ℂ` satisfies `PuncturedAspherical₂ X` (removing a finite
  set from `X` corresponds to removing a closed discrete set upstairs). By the uniformisation
  theorem every Riemann surface other than the Riemann sphere admits such a covering (by `ℂ` or by
  the disc); e.g. a once-punctured elliptic curve `E ∖ {O}` is covered by `ℂ ∖ Λ`, a compact
  torus `ℂ/Λ` by `ℂ`, and open subsets of `ℂ` (punctured planes, `ℙ¹` minus `≥ 1` points) by
  themselves. The covering must be supplied as a hypothesis: general uniformisation is not
  formalised.
* `Conf.fadellNeuwirth_exact_of_isCoveringMap`: for such a connected Riemann surface `X`, the
  Fadell–Neuwirth sequence `1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is
  exact, and `π₂(Conf n X) = 0` (`Conf.subsingleton_pi_two_of_isCoveringMap`).
* `Conf.fadellNeuwirth_exact_of_isOpen`: the same for every connected open subset of `ℂ`, with
  no further hypothesis.
-/

open Set Function Topology Metric Complex

open UpperHalfPlane hiding I

namespace PlaneUniformization

open Uniformization Uniformization.LatticeData

/-! ### A holomorphic covering of `Ω` by an open subset of the disc

Throughout, `a ≠ b` are two points outside the open connected set `Ω`, and `z₀ ∈ Ω`. This is the
construction of `Uniformization.LatticeData` (in `lana-agents/oka`) with the lattice `Λ` replaced
by the two-point set `{a, b}`. -/

variable (a b z₀ : ℂ)

/-- The slope of the affine map `T`. -/
noncomputable def slope : ℂ := by
  classical
  exact if b₂ = b₁ then 1 else (b₂ - b₁) / (b - a)

/-- The affine map `T z = j(i) + c (z - a)`, sending `a ↦ j(i)` and `b ↦ j(ρ)`. -/
noncomputable def aff (z : ℂ) : ℂ := b₁ + slope a b * (z - a)

/-- The inverse of `aff`. -/
noncomputable def affInv (y : ℂ) : ℂ := (y - b₁) / slope a b + a

variable {a b}

theorem slope_ne_zero (hab : a ≠ b) : slope a b ≠ 0 := by
  unfold slope
  split_ifs with h
  · exact one_ne_zero
  · exact div_ne_zero (sub_ne_zero.mpr h) (sub_ne_zero.mpr hab.symm)

theorem affInv_aff (hab : a ≠ b) (z : ℂ) : affInv a b (aff a b z) = z := by
  simp [affInv, aff, mul_div_cancel_left₀ _ (slope_ne_zero hab)]

theorem aff_affInv (hab : a ≠ b) (y : ℂ) : aff a b (affInv a b y) = y := by
  simp [affInv, aff, mul_div_cancel₀ _ (slope_ne_zero hab)]

theorem jBranch_subset (hab : a ≠ b) : jBranch ⊆ aff a b '' {a, b} := by
  rintro y (rfl | rfl)
  · exact ⟨a, Or.inl rfl, by simp [aff]⟩
  · by_cases h : b₂ = b₁
    · exact ⟨a, Or.inl rfl, by simp [aff, h]⟩
    · refine ⟨b, Or.inr rfl, ?_⟩
      have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
      simp only [aff, slope, h, if_false]
      field_simp
      ring

theorem aff_notMem_jBranch (hab : a ≠ b) {z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    aff a b z ∉ jBranch := by
  intro h
  obtain ⟨l, hl, hlz⟩ := jBranch_subset hab h
  have := congrArg (affInv a b) hlz
  rw [affInv_aff hab, affInv_aff hab] at this
  rcases hl with rfl | rfl
  · exact hza this.symm
  · exact hzb this.symm

variable (a b)

/-- A point of `ℍ` over `T(z₀)`. -/
noncomputable def τ₁ : ℍ := (Heights.modularJ_surjective (aff a b z₀)).choose

theorem jC_τ₁ : jC (τ₁ a b z₀) = aff a b z₀ := by
  rw [jC_coe]; exact (Heights.modularJ_surjective _).choose_spec

/-- The base point of the disc. -/
noncomputable def t : ℂ := cayley (τ₁ a b z₀)

theorem t_mem : t a b z₀ ∈ ball (0 : ℂ) 1 := cayley_mem_ball (τ₁ a b z₀).im_pos

/-- The map `𝔻 → ℍ`, `w ↦ C⁻¹ (mob t w)`. -/
noncomputable def hmap (w : ℂ) : ℂ := cayleyInv (mob (t a b z₀) w)

/-- Its inverse `ℍ → 𝔻`. -/
noncomputable def hinv (z : ℂ) : ℂ := mob (-t a b z₀) (cayley z)

variable {a b z₀}

theorem im_hmap_pos {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : 0 < (hmap a b z₀ w).im :=
  im_cayleyInv_pos (mob_mem_ball (t_mem a b z₀) hw)

theorem hinv_mem {z : ℂ} (hz : 0 < z.im) : hinv a b z₀ z ∈ ball (0 : ℂ) 1 :=
  mob_mem_ball (by simpa using t_mem a b z₀) (cayley_mem_ball hz)

theorem hinv_hmap {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : hinv a b z₀ (hmap a b z₀ w) = w := by
  rw [hinv, hmap, cayley_cayleyInv (mob_mem_ball (t_mem a b z₀) hw),
    mob_neg_mob (t_mem a b z₀) hw]

theorem hmap_hinv {z : ℂ} (hz : 0 < z.im) : hmap a b z₀ (hinv a b z₀ z) = z := by
  rw [hinv, hmap, mob_mob_neg (t_mem a b z₀) (cayley_mem_ball hz), cayleyInv_cayley hz]

theorem continuousOn_hmap : ContinuousOn (hmap a b z₀) (ball 0 1) :=
  differentiableOn_cayleyInv.continuousOn.comp (continuousOn_mob (t_mem a b z₀))
    fun _ hw ↦ mob_mem_ball (t_mem a b z₀) hw

theorem differentiableOn_hmap : DifferentiableOn ℂ (hmap a b z₀) (ball 0 1) :=
  differentiableOn_cayleyInv.comp (differentiableOn_mob (t_mem a b z₀))
    fun _ hw ↦ mob_mem_ball (t_mem a b z₀) hw

theorem continuousOn_hinv : ContinuousOn (hinv a b z₀) {z | 0 < z.im} :=
  (continuousOn_mob (by simpa using t_mem a b z₀)).comp differentiableOn_cayley.continuousOn
    fun _ hz ↦ cayley_mem_ball hz

theorem hmap_zero : hmap a b z₀ 0 = τ₁ a b z₀ := by
  rw [hmap, mob_zero, t, cayleyInv_cayley (τ₁ a b z₀).im_pos]

variable (a b z₀)

/-- The starting covering `p₀ = T⁻¹ ∘ j ∘ hmap` on the disc, `a` outside. -/
noncomputable def p₀ (w : ℂ) : ℂ := by
  classical
  exact if w ∈ ball (0 : ℂ) 1 then affInv a b (jC (hmap a b z₀ w)) else a

variable {a b z₀}

theorem p₀_of_mem {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    p₀ a b z₀ w = affInv a b (jC (hmap a b z₀ w)) := by
  simp [p₀, hw]

variable {Ω : Set ℂ}

theorem mem_ball_of_p₀_mem (ha : a ∉ Ω) {w : ℂ} (h : p₀ a b z₀ w ∈ Ω) :
    w ∈ ball (0 : ℂ) 1 := by
  by_contra hw
  simp only [p₀, hw, if_false] at h
  exact ha h

theorem continuousOn_p₀ : ContinuousOn (p₀ a b z₀) (ball 0 1) := by
  have : ContinuousOn (fun w ↦ affInv a b (jC (hmap a b z₀ w))) (ball 0 1) :=
    (((continuousOn_id.sub continuousOn_const).div_const _).add continuousOn_const).comp
      (continuousOn_jC.comp continuousOn_hmap fun _ hw ↦ im_hmap_pos hw) (mapsTo_univ _ _)
  exact this.congr fun w hw ↦ p₀_of_mem hw

theorem differentiableOn_p₀ : DifferentiableOn ℂ (p₀ a b z₀) (ball 0 1) := by
  have : DifferentiableOn ℂ (fun w ↦ (jC (hmap a b z₀ w) - b₁) / slope a b + a) (ball 0 1) :=
    (((differentiableOn_jC.comp differentiableOn_hmap fun _ hw ↦ im_hmap_pos hw).sub_const
      _).div_const _).add_const _
  exact this.congr fun w hw ↦ p₀_of_mem hw

theorem isOpen_preimage_p₀ (hΩ : IsOpen Ω) (ha : a ∉ Ω) : IsOpen (p₀ a b z₀ ⁻¹' Ω) := by
  have : p₀ a b z₀ ⁻¹' Ω = ball 0 1 ∩ p₀ a b z₀ ⁻¹' Ω :=
    ext fun w ↦ ⟨fun h ↦ ⟨mem_ball_of_p₀_mem ha h, h⟩, fun h ↦ h.2⟩
  rw [this]
  exact continuousOn_p₀.isOpen_inter_preimage isOpen_ball hΩ

theorem jC_hmap_of_p₀ (hab : a ≠ b) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    jC (hmap a b z₀ w) = aff a b (p₀ a b z₀ w) := by
  rw [p₀_of_mem hw, aff_affInv hab]

theorem ne_of_mem (ha : a ∉ Ω) {z : ℂ} (hz : z ∈ Ω) : z ≠ a := fun h ↦ ha (h ▸ hz)

theorem isCoveringMapOn_p₀ (hΩ : IsOpen Ω) (ha : a ∉ Ω) (hb : b ∉ Ω) (hab : a ≠ b) :
    IsCoveringMapOn (p₀ a b z₀) Ω := by
  refine isCoveringMapOn_of_sections (isOpen_preimage_p₀ hΩ ha)
    (continuousOn_p₀.mono fun w hw ↦ mem_ball_of_p₀_mem ha hw) ?_ ?_
  · -- local injectivity
    intro e he
    have heD := mem_ball_of_p₀_mem ha he
    have hB : jC (hmap a b z₀ e) ∉ jBranch := by
      rw [jC_hmap_of_p₀ hab heD]; exact aff_notMem_jBranch hab (ne_of_mem ha he) (ne_of_mem hb he)
    obtain ⟨W, hW, hWinj⟩ := exists_nhds_injOn_jC hB
    refine ⟨ball 0 1 ∩ hmap a b z₀ ⁻¹' W, Filter.inter_mem (isOpen_ball.mem_nhds heD)
      ((continuousOn_hmap.continuousAt (isOpen_ball.mem_nhds heD)).preimage_mem_nhds hW), ?_⟩
    intro x hx y hy hxy
    rw [p₀_of_mem hx.1, p₀_of_mem hy.1] at hxy
    have h1 : jC (hmap a b z₀ x) = jC (hmap a b z₀ y) := by
      have := congrArg (aff a b) hxy; rwa [aff_affInv hab, aff_affInv hab] at this
    have h2 := hWinj hx.2 hy.2 h1
    rw [← hinv_hmap hx.1, ← hinv_hmap hy.1, h2]
  · -- sections
    intro x hx
    obtain ⟨ε, hε, -, hsec⟩ :=
      exists_section_jC (aff_notMem_jBranch hab (ne_of_mem ha hx) (ne_of_mem hb hx))
    obtain ⟨δ', hδ', hδ'Ω⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hc := norm_pos_iff.mpr (slope_ne_zero hab)
    set δ := min δ' (ε / ‖slope a b‖)
    have hδ : 0 < δ := lt_min hδ' (div_pos hε hc)
    have hVΩ : ball x δ ⊆ Ω := (ball_subset_ball (min_le_left _ _)).trans hδ'Ω
    have hVaff : ∀ y ∈ ball x δ, aff a b y ∈ ball (aff a b x) ε := by
      intro y hy
      rw [mem_ball, dist_eq_norm, aff, aff, add_sub_add_left_eq_sub, ← mul_sub, norm_mul,
        sub_sub_sub_cancel_right]
      have : ‖y - x‖ < ε / ‖slope a b‖ := by
        rw [← dist_eq_norm]; exact hy.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀' hc] at this
    refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, hVΩ, (convex_ball x δ).isPreconnected,
      fun e he ↦ ?_⟩
    have heD := mem_ball_of_p₀_mem ha (hVΩ he)
    have hje : jC (hmap a b z₀ e) ∈ ball (aff a b x) ε := by
      rw [jC_hmap_of_p₀ hab heD]; exact hVaff _ he
    obtain ⟨s, hsc, hsj, hsim, hse⟩ := hsec _ hje
    refine ⟨fun y ↦ hinv a b z₀ (s (aff a b y)), ?_, fun y hy ↦ ?_, ?_⟩
    · refine continuousOn_hinv.comp (hsc.comp (continuous_const.add
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn hVaff)
        fun y hy ↦ hsim _ (hVaff y hy)
    · have hmem := hinv_mem (z₀ := z₀) (a := a) (b := b) (hsim _ (hVaff y hy))
      rw [p₀_of_mem hmem, hmap_hinv (hsim _ (hVaff y hy)), hsj _ (hVaff y hy), affInv_aff hab]
    · simp only
      rw [← jC_hmap_of_p₀ hab heD, hse, hinv_hmap heD]

theorem planeData (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (ha : a ∉ Ω) (hb : b ∉ Ω)
    (hab : a ≠ b) (hz₀ : z₀ ∈ Ω) : PlaneData Ω (p₀ a b z₀ ⁻¹' Ω) (p₀ a b z₀) where
  good :=
    { isOpen := isOpen_preimage_p₀ hΩ ha
      subset_ball := fun _ h ↦ mem_ball_of_p₀_mem ha h
      zero_mem := by
        change p₀ a b z₀ 0 ∈ Ω
        rw [p₀_of_mem (mem_ball_self one_pos), hmap_zero, jC_τ₁, affInv_aff hab]
        exact hz₀ }
  isOpen := hΩ
  isPreconnected := hc
  covering := isCoveringMapOn_p₀ hΩ ha hb hab
  preimage_eq := rfl
  differentiableOn := differentiableOn_p₀.mono fun _ h ↦ mem_ball_of_p₀_mem ha h

/-- **Uniformisation of plane domains omitting two points.** An open connected `Ω ⊆ ℂ` omitting
two distinct points is covered by the unit disc. -/
theorem exists_covering (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (ha : a ∉ Ω) (hb : b ∉ Ω)
    (hab : a ≠ b) (hz₀ : z₀ ∈ Ω) :
    ∃ ψ : ℂ → ℂ, IsCoveringMapOn ψ Ω ∧ ψ ⁻¹' Ω = ball 0 1 ∧ SurjOn ψ (ball 0 1) Ω := by
  obtain ⟨ψ, hcov, hpre, -, -, hsurj⟩ := (planeData hΩ hc ha hb hab hz₀).exists_covering ha
  exact ⟨ψ, hcov, hpre, hsurj⟩

end PlaneUniformization

/-! ### `π₂` of open subsets of `ℂ` -/

namespace Complex

/-- `π₂(ℂ ∖ {a}) = 0`, via the covering `exp`. -/
theorem subsingleton_pi_two_compl_singleton (a : ℂ) (u : ({a}ᶜ : Set ℂ)) :
    Subsingleton (π_ 2 ({a}ᶜ : Set ℂ) u) := by
  let e : ({a}ᶜ : Set ℂ) ≃ₜ {z : ℂ // z ≠ 0} :=
    { toFun := fun z ↦ ⟨z - a, sub_ne_zero.2 z.2⟩
      invFun := fun z ↦ ⟨z + a, fun h ↦ z.2 (by simpa using h)⟩
      left_inv := fun z ↦ by simp
      right_inv := fun z ↦ by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine HomotopyGroup.subsingleton_of_homeomorph e u ?_
  have hv : (e u : ℂ) ≠ 0 := (e u).2
  have h := isCoveringMap_exp.subsingleton_homotopyGroup_two (log (e u))
    (HomotopyGroup.subsingleton_of_normedSpace ℂ _)
  have heq : (⟨exp (log (e u)), exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) = e u :=
    Subtype.ext (exp_log hv)
  exact heq ▸ h

/-- `π₂` of an open connected subset of `ℂ` is trivial. -/
theorem subsingleton_pi_two_of_isPreconnected {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) (u : Ω) : Subsingleton (π_ 2 Ω u) := by
  by_cases h2 : ∃ a b, a ∉ Ω ∧ b ∉ Ω ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := h2
    obtain ⟨ψ, hcov, hpre, hsurj⟩ := PlaneUniformization.exists_covering hΩ hc ha hb hab u.2
    obtain ⟨w, hw, hwu⟩ := hsurj u.2
    have hw' : w ∈ ψ ⁻¹' Ω := by rw [hpre]; exact hw
    have hconv : Convex ℝ (ψ ⁻¹' Ω) := by rw [hpre]; exact convex_ball 0 1
    have h := hcov.isCoveringMap_restrictPreimage.subsingleton_homotopyGroup_two ⟨w, hw'⟩
      (HomotopyGroup.subsingleton_of_convex hconv _)
    have heq : Ω.restrictPreimage ψ ⟨w, hw'⟩ = u := Subtype.ext hwu
    exact heq ▸ h
  · by_cases hu : Ω = univ
    · subst hu
      exact HomotopyGroup.subsingleton_of_convex convex_univ u
    · obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by
        by_contra! h
        exact hu (eq_univ_of_forall h)
      have hΩa : Ω = {a}ᶜ := Set.ext fun z ↦ ⟨fun hz hza ↦ ha (hza ▸ hz), fun hz ↦ by
        by_contra hzΩ
        exact h2 ⟨z, a, hzΩ, ha, hz⟩⟩
      subst hΩa
      exact subsingleton_pi_two_compl_singleton a u

/-- **Open subsets of `ℂ` have trivial `π₂`** (at every base point). -/
theorem subsingleton_pi_two_of_isOpen {U : Set ℂ} (hU : IsOpen U) (u : U) :
    Subsingleton (π_ 2 U u) := by
  set Ω := connectedComponentIn U (u : ℂ)
  have hΩU : Ω ⊆ U := connectedComponentIn_subset _ _
  have huΩ : (u : ℂ) ∈ Ω := mem_connectedComponentIn u.2
  have hΩ := subsingleton_pi_two_of_isPreconnected hU.connectedComponentIn
    isPreconnected_connectedComponentIn ⟨u, huΩ⟩
  rw [HomotopyGroup.subsingleton_iff_forall] at hΩ ⊢
  intro γ
  have hrange : range (fun y ↦ (γ y : ℂ)) ⊆ Ω := by
    refine (isPreconnected_range (by fun_prop)).subset_connectedComponentIn ?_ ?_
    · exact ⟨fun _ ↦ 0, congrArg Subtype.val
        (GenLoop.boundary γ (fun _ : Fin 2 ↦ (0 : unitInterval)) ⟨0, Or.inl rfl⟩)⟩
    · rintro _ ⟨y, rfl⟩; exact (γ y).2
  let γ' : GenLoop (Fin 2) Ω ⟨u, huΩ⟩ :=
    ⟨⟨fun y ↦ ⟨γ y, hrange ⟨y, rfl⟩⟩, ((continuous_subtype_val.comp
      (γ : C(Fin 2 → unitInterval, U)).continuous).subtype_mk _)⟩, fun y hy ↦ Subtype.ext
      (show ((γ y : U) : ℂ) = u from congrArg Subtype.val (GenLoop.boundary γ y hy))⟩
  have := (hΩ γ').comp_continuousMap ⟨inclusion hΩU, continuous_inclusion hΩU⟩
  unfold GenLoop.Homotopic
  convert this using 1 <;> ext <;> rfl

/-- A space embedding openly in `ℂ` has trivial `π₂`. -/
theorem subsingleton_pi_two_of_isOpenEmbedding {Z : Type*} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsOpenEmbedding f) (z : Z) : Subsingleton (π_ 2 Z z) :=
  HomotopyGroup.subsingleton_of_homeomorph hf.isEmbedding.toHomeomorph z
    (subsingleton_pi_two_of_isOpen hf.isOpen_range _)

end Complex

/-! ### Spaces covered by plane domains -/

/-- If a T₁ space `X` admits a surjective covering map `p : Y → X` from a space `Y` that embeds
openly in `ℂ`, then `π₂(X ∖ S) = 0` for every finite `S ⊆ X`. -/
theorem puncturedAspherical₂_of_isCoveringMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T1Space X] {p : Y → X} (hp : IsCoveringMap p) (hsurj : Surjective p)
    {f : Y → ℂ} (hf : IsOpenEmbedding f) : PuncturedAspherical₂ X := by
  intro S hS x
  have hSo : IsOpen (p ⁻¹' Sᶜ) := hS.isClosed.isOpen_compl.preimage hp.continuous
  have hcov : IsCoveringMapOn p Sᶜ := fun x _ ↦ hp x
  obtain ⟨y, hy⟩ := hsurj x
  have hy' : y ∈ p ⁻¹' Sᶜ := by rw [mem_preimage, hy]; exact x.2
  have h := hcov.isCoveringMap_restrictPreimage.subsingleton_homotopyGroup_two ⟨y, hy'⟩
    (Complex.subsingleton_pi_two_of_isOpenEmbedding (hf.comp hSo.isOpenEmbedding_subtypeVal) _)
  have heq : Sᶜ.restrictPreimage p ⟨y, hy'⟩ = x := Subtype.ext hy
  exact heq ▸ h

/-- A space embedding openly in `ℂ` satisfies `PuncturedAspherical₂`. -/
theorem puncturedAspherical₂_of_isOpenEmbedding {X : Type*} [TopologicalSpace X] [T1Space X]
    {f : X → ℂ} (hf : IsOpenEmbedding f) : PuncturedAspherical₂ X :=
  puncturedAspherical₂_of_isCoveringMap
    (Uniformization.isCoveringMap_homeomorph (Homeomorph.refl X)) (Equiv.refl X).surjective hf

/-- A space `X` with a surjective covering map `p : Y → X` from a space `Y` embedding openly in `ℂ`
is a `ℂ`-manifold: the charts are local inverses of `p` followed by the embedding. -/
@[reducible] noncomputable def chartedSpaceOfIsCoveringMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty Y] {p : Y → X} (hp : IsCoveringMap p) (hsurj : Surjective p)
    {f : Y → ℂ} (hf : IsOpenEmbedding f) : ChartedSpace ℂ X :=
  letI := hf.singletonChartedSpace
  hp.isLocalHomeomorph.chartedSpace hsurj

/-- A Hausdorff space with a surjective covering map from a space embedding openly in `ℂ` has
local pushes. -/
theorem hasLocalPushes_of_isCoveringMap {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] {p : Y → X} (hp : IsCoveringMap p) (hsurj : Surjective p) {f : Y → ℂ}
    (hf : IsOpenEmbedding f) : HasLocalPushes X := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact fun x ↦ (hY.false (hsurj x).choose).elim
  · letI := chartedSpaceOfIsCoveringMap hp hsurj hf
    exact ChartedSpace.hasLocalPushes ℂ X

namespace Conf

variable {X : Type*} [TopologicalSpace X]

/-- **`π₂(Conf n X) = 0`** for a Hausdorff space `X` admitting a surjective covering map from a
space embedding openly in `ℂ` (by uniformisation: any Riemann surface other than `ℙ¹`). -/
theorem subsingleton_pi_two_of_isCoveringMap [T2Space X] {Y : Type*} [TopologicalSpace Y]
    {p : Y → X} (hp : IsCoveringMap p) (hsurj : Surjective p) {f : Y → ℂ}
    (hf : IsOpenEmbedding f) (n : ℕ) (y : Conf n X) : Subsingleton (π_ 2 (Conf n X) y) :=
  subsingleton_pi_two (hasLocalPushes_of_isCoveringMap hp hsurj hf)
    (puncturedAspherical₂_of_isCoveringMap hp hsurj hf) n y

/-- **The Fadell–Neuwirth short exact sequence for Riemann surfaces covered by plane domains.**
Let `X` be a connected Hausdorff space admitting a surjective covering map from a space embedding
openly in `ℂ` (by uniformisation: any connected Riemann surface other than `ℙ¹`; e.g.
`ℂ ∖ Λ → E ∖ {O}` for a once-punctured elliptic curve, see `PeriodPair.PuncturedTorus`). Then
`1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact. -/
theorem fadellNeuwirth_exact_of_isCoveringMap {n : ℕ} [T2Space X] [ConnectedSpace X]
    {Y : Type*} [TopologicalSpace Y] {p : Y → X} (hp : IsCoveringMap p)
    (hsurj : Surjective p) {f : Y → ℂ} (hf : IsOpenEmbedding f) (x₀ : Conf (n + 1) X) :
    Injective (puncturedToConf x₀) ∧
      (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker ∧
      Surjective (FundamentalGroup.map forget x₀) :=
  haveI : Nonempty Y := ⟨(hsurj (Classical.arbitrary X)).choose⟩
  letI := chartedSpaceOfIsCoveringMap hp hsurj hf
  fadellNeuwirth_exact_complex (puncturedAspherical₂_of_isCoveringMap hp hsurj hf) x₀

/-- `π₂(Conf n U) = 0` for every open subset `U` of `ℂ`. -/
theorem subsingleton_pi_two_of_isOpen (U : TopologicalSpace.Opens ℂ) (n : ℕ) (y : Conf n U) :
    Subsingleton (π_ 2 (Conf n U) y) :=
  subsingleton_pi_two (X := U) (ChartedSpace.hasLocalPushes ℂ U)
    (puncturedAspherical₂_of_isOpenEmbedding U.isOpen.isOpenEmbedding_subtypeVal) n y

/-- **The Fadell–Neuwirth short exact sequence for plane domains.** For every connected open
`U ⊆ ℂ` (e.g. `ℂ` minus finitely many points, a punctured disc),
`1 → π₁(U ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) U) → π₁(Conf n U) → 1` is exact. -/
theorem fadellNeuwirth_exact_of_isOpen (U : TopologicalSpace.Opens ℂ) [ConnectedSpace U] {n : ℕ}
    (x₀ : Conf (n + 1) U) :
    Injective (puncturedToConf x₀) ∧
      (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker ∧
      Surjective (FundamentalGroup.map forget x₀) :=
  fadellNeuwirth_exact_complex (X := U)
    (puncturedAspherical₂_of_isOpenEmbedding U.isOpen.isOpenEmbedding_subtypeVal) x₀

end Conf

/-! ### Complex tori and once-punctured elliptic curves -/

namespace PeriodPair

variable (L : PeriodPair)

/-- The complex torus `ℂ / Λ` (the complex points of an elliptic curve). -/
abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

instance : IsClosed (L.lattice.toAddSubgroup : Set ℂ) := L.isClosed_lattice

instance : T2Space L.Torus := inferInstance

theorem isCoveringMap_mk : IsCoveringMap (QuotientAddGroup.mk : ℂ → L.Torus) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm _
    (show DiscreteTopology L.lattice from inferInstance).isDiscrete).isCoveringMap

/-- The once-punctured torus `E ∖ {O}` (the complex points of a once-punctured elliptic curve),
an open subspace of `L.Torus`. -/
def PuncturedTorus : TopologicalSpace.Opens L.Torus :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

theorem mk_preimage_puncturedTorus :
    (QuotientAddGroup.mk : ℂ → L.Torus) ⁻¹' (L.PuncturedTorus : Set L.Torus) =
      (L.lattice : Set ℂ)ᶜ := by
  ext z
  simp [PuncturedTorus, QuotientAddGroup.eq_zero_iff]

/-- The covering `ℂ ∖ Λ → E ∖ {O}`. -/
noncomputable def puncturedCover : ((L.lattice : Set ℂ)ᶜ : Set ℂ) → L.PuncturedTorus :=
  fun z ↦ ⟨QuotientAddGroup.mk (z : ℂ), 
    (Set.ext_iff.1 L.mk_preimage_puncturedTorus z).2 z.2⟩

theorem isCoveringMap_puncturedCover : IsCoveringMap L.puncturedCover := by
  have h := (L.isCoveringMap_mk.isCoveringMapOn.mono (subset_univ
    (L.PuncturedTorus : Set L.Torus))).isCoveringMap_restrictPreimage
  have e : (QuotientAddGroup.mk : ℂ → L.Torus) ⁻¹' (L.PuncturedTorus : Set L.Torus) =
      (L.lattice : Set ℂ)ᶜ := L.mk_preimage_puncturedTorus
  exact h.comp_homeomorph (Homeomorph.setCongr e).symm

theorem surjective_puncturedCover : Surjective L.puncturedCover := by
  rintro ⟨x, hx⟩
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have : z ∈ (L.lattice : Set ℂ)ᶜ := by
    rw [← mk_preimage_puncturedTorus]; exact hx
  exact ⟨⟨z, this⟩, rfl⟩

instance : ConnectedSpace L.PuncturedTorus := by
  haveI : ConnectedSpace ((L.lattice : Set ℂ)ᶜ : Set ℂ) :=
    isConnected_iff_connectedSpace.mp
      ⟨⟨_, L.ω₂_div_two_notMem_lattice⟩, Uniformization.LatticeData.isPreconnected_Ω L⟩
  exact L.surjective_puncturedCover.connectedSpace
    L.isCoveringMap_puncturedCover.continuous

/-- `π₂` of the torus minus any finite set vanishes. -/
theorem puncturedAspherical₂_torus : PuncturedAspherical₂ L.Torus :=
  puncturedAspherical₂_of_isCoveringMap L.isCoveringMap_mk QuotientAddGroup.mk_surjective
    (f := id) IsOpenEmbedding.id

/-- `π₂` of the once-punctured torus minus any finite set vanishes. -/
theorem puncturedAspherical₂_puncturedTorus : PuncturedAspherical₂ L.PuncturedTorus :=
  puncturedAspherical₂_of_isCoveringMap L.isCoveringMap_puncturedCover
    L.surjective_puncturedCover (L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal)

end PeriodPair

namespace Conf

/-- `π₂(Conf n (E ∖ {O})) = 0` for a once-punctured elliptic curve `E ∖ {O} = (ℂ / Λ) ∖ {0}`. -/
theorem subsingleton_pi_two_puncturedTorus (L : PeriodPair) (n : ℕ)
    (y : Conf n L.PuncturedTorus) : Subsingleton (π_ 2 (Conf n L.PuncturedTorus) y) :=
  subsingleton_pi_two_of_isCoveringMap L.isCoveringMap_puncturedCover
    L.surjective_puncturedCover L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal n y

/-- **The Fadell–Neuwirth short exact sequence for a once-punctured elliptic curve**
`X = E ∖ {O} = (ℂ / Λ) ∖ {0}`:
`1 → π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1` is exact. -/
theorem fadellNeuwirth_exact_puncturedTorus (L : PeriodPair) {n : ℕ}
    (x₀ : Conf (n + 1) L.PuncturedTorus) :
    Injective (puncturedToConf x₀) ∧
      (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker ∧
      Surjective (FundamentalGroup.map forget x₀) :=
  fadellNeuwirth_exact_of_isCoveringMap L.isCoveringMap_puncturedCover
    L.surjective_puncturedCover L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal x₀

/-- **The Fadell–Neuwirth short exact sequence for a complex torus** `X = ℂ / Λ`. -/
theorem fadellNeuwirth_exact_torus (L : PeriodPair) {n : ℕ} (x₀ : Conf (n + 1) L.Torus) :
    Injective (puncturedToConf x₀) ∧
      (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker ∧
      Surjective (FundamentalGroup.map forget x₀) :=
  haveI : ConnectedSpace L.Torus :=
    QuotientAddGroup.mk_surjective.connectedSpace L.isCoveringMap_mk.continuous
  fadellNeuwirth_exact_of_isCoveringMap L.isCoveringMap_mk QuotientAddGroup.mk_surjective
    (f := id) IsOpenEmbedding.id x₀

end Conf
