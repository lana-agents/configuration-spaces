/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.Basic
import ConfigurationSpaces.Topology.FundamentalGroupSequence
import ConfigurationSpaces.Topology.Push
import ConfigurationSpaces.Topology.Punctured

/-!
# The Fadell–Neuwirth fibration and its fundamental-group sequence

* `Conf.isLocallyTrivial_forget`: for a Hausdorff space `X` with local pushes (e.g. any Hausdorff
  topological manifold modelled on a finite-dimensional real normed space), the forgetful map
  `Conf (n + 1) X → Conf n X` is locally trivial, with fibre `X ∖ {y₀, …, yₙ₋₁}` over `y`
  (Fadell–Neuwirth). The trivialisation over a neighbourhood of `y` is
  `x ↦ (forget x, Ψ_{forget x} (last x))`, where `Φ_z` is a family of homeomorphisms pushing `y`
  to `z` (`HasLocalPushes.exists_multiPush`) and `Ψ_z = Φ_z⁻¹`.
* `Conf.isPathConnected_fiber`: for a connected Hausdorff manifold of dimension `> 1`, the fibres
  are path-connected.
* The **Fadell–Neuwirth exact sequence** `π₁(X ∖ {y₀,…,yₙ₋₁}) → π₁(Conf (n+1) X) → π₁(Conf n X) → 1`
  for such `X`, with injectivity on the left when `π₂(Conf n X)` is trivial:
  `Conf.fadellNeuwirth_range_eq_ker`, `Conf.fadellNeuwirth_surjective`,
  `Conf.fadellNeuwirth_injective`. Here the fibre is identified with the punctured manifold via
  `Conf.fiberHomeomorph` and `FundamentalGroup.mulEquivOfHomeomorph`.
-/

open Set Function Topology

universe u

/-! ### Fundamental groups of homeomorphic spaces -/

namespace FundamentalGroup

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism induces an isomorphism of fundamental groups. -/
noncomputable def mulEquivOfHomeomorph (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MonoidHom.toMulEquiv (map (e : C(X, Y)) x)
    (mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x))
    (by
      ext g
      obtain ⟨γ⟩ := g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, mapOfEq_apply]
      change Path.Homotopic.Quotient.mk (((γ.map e.continuous).map e.symm.continuous).cast _ _) =
        Path.Homotopic.Quotient.mk γ
      congr 1
      ext t
      exact e.symm_apply_apply _)
    (by
      ext g
      obtain ⟨γ⟩ := g
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, mapOfEq_apply]
      change Path.Homotopic.Quotient.mk (((γ.map e.symm.continuous).cast _ _).map e.continuous) =
        Path.Homotopic.Quotient.mk γ
      congr 1
      ext t
      simp)

@[simp] theorem mulEquivOfHomeomorph_apply (e : X ≃ₜ Y) (x : X) (g : FundamentalGroup X x) :
    mulEquivOfHomeomorph e x g = map (e : C(X, Y)) x g := rfl

end FundamentalGroup

namespace Conf

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-! ### Local triviality -/

/-- **Fadell–Neuwirth.** If `X` is Hausdorff and has local pushes, the forgetful map
`Conf (n + 1) X → Conf n X` is locally trivial. -/
theorem isLocallyTrivial_forget [T2Space X] (hX : HasLocalPushes X) (n : ℕ) :
    IsLocallyTrivial (forget : Conf (n + 1) X → Conf n X) := by
  intro y
  obtain ⟨W, hW, Φ, Ψ, hΦc, hΨc, hΦΨ, hΨΦ, hΦy, -⟩ :=
    hX.exists_multiPush n y y.injective univ isOpen_univ fun _ ↦ mem_univ _
  let U : Set (Conf n X) := (fun z : Conf n X ↦ (z : Fin n → X)) ⁻¹' interior W
  have hUo : IsOpen U := isOpen_interior.preimage continuous_coe
  have hyU : y ∈ U := mem_interior_iff_mem_nhds.2 hW
  have hUW : ∀ z ∈ U, (z : Fin n → X) ∈ W := fun z hz ↦ interior_subset hz
  -- the fibre coordinate of `x` lies in the punctured space
  have hΨmem : ∀ x : Conf (n + 1) X, forget x ∈ U →
      Ψ (forget x) x.last ∈ (range y)ᶜ := by
    rintro x hx ⟨i, hi⟩
    apply last_notMem_range x
    refine ⟨i, ?_⟩
    have := congrArg (Φ (forget x)) hi
    rw [hΦΨ _ (hUW _ hx), hΦy _ (hUW _ hx)] at this
    exact this
  have hΦmem : ∀ z ∈ U, ∀ q ∈ (range y)ᶜ, Φ z q ∉ range z := by
    rintro z hz q hq ⟨i, hi⟩
    apply hq
    refine ⟨i, ?_⟩
    have := congrArg (Ψ z) hi
    rw [← hΦy _ (hUW _ hz) i, hΨΦ _ (hUW _ hz), hΨΦ _ (hUW _ hz)] at this
    exact this
  let φ : (forget ⁻¹' U : Set (Conf (n + 1) X)) ≃ₜ U × ((range y)ᶜ : Set X) :=
  { toFun := fun x ↦ (⟨forget x.1, x.2⟩, ⟨Ψ (forget x.1) x.1.last, hΨmem x.1 x.2⟩)
    invFun := fun q ↦ ⟨snoc q.1.1 (Φ q.1.1 q.2.1) (hΦmem _ q.1.2 _ q.2.2), by
      simp⟩
    left_inv := fun x ↦ by
      obtain ⟨x, hx⟩ := x
      have h' := hΦΨ _ (hUW _ hx)
      simp only [forget_apply] at h'
      apply Subtype.ext
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp [snoc, last, h']
      · simp [snoc]
    right_inv := fun q ↦ by
      obtain ⟨⟨z, hz⟩, ⟨p, hp⟩⟩ := q
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · simp
      · simp [hΨΦ _ (hUW _ hz) p]
    continuous_toFun := by
      refine Continuous.prodMk ((forget.continuous.comp continuous_subtype_val).subtype_mk _) ?_
      refine Continuous.subtype_mk ?_ _
      refine hΨc.comp_continuous ((continuous_coe.comp (forget.continuous.comp
        continuous_subtype_val)).prodMk (continuous_last.comp continuous_subtype_val)) ?_
      exact fun x ↦ ⟨hUW _ x.2, mem_univ _⟩
    continuous_invFun := by
      refine Continuous.subtype_mk (continuous_iff.2 ?_) _
      refine Continuous.finSnoc (A := fun _ ↦ X)
        (f := fun q : U × ((range y)ᶜ : Set X) ↦ ((q.1 : Conf n X) : Fin n → X)) (by fun_prop) ?_
      refine hΦc.comp_continuous ((continuous_coe.comp (continuous_subtype_val.comp
        continuous_fst)).prodMk (continuous_subtype_val.comp continuous_snd)) ?_
      exact fun q ↦ ⟨hUW _ q.1.2, mem_univ _⟩ }
  exact ⟨U, hUo, hyU, ((range y)ᶜ : Set X), inferInstance, φ, fun _ ↦ rfl⟩

/-- The forgetful map of configuration spaces of a Hausdorff topological manifold is locally
trivial (Fadell–Neuwirth). -/
theorem isLocallyTrivial_forget_of_chartedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space X] [ChartedSpace E X] (n : ℕ) :
    IsLocallyTrivial (forget : Conf (n + 1) X → Conf n X) :=
  isLocallyTrivial_forget (ChartedSpace.hasLocalPushes E X) n

/-! ### Path-connected fibres -/

/-- The fibre of `forget` over `y` is the image of the punctured space `(range y)ᶜ`. -/
theorem forget_preimage_singleton (y : Conf n X) :
    (forget ⁻¹' {y} : Set (Conf (n + 1) X)) =
      range (fun p : ((range y)ᶜ : Set X) ↦ snoc y p.1 p.2) := by
  ext x
  constructor
  · intro hx
    have h : forgetFun x = y := hx
    refine ⟨⟨x.last, by rw [← h]; exact last_notMem_range x⟩, ?_⟩
    ext i
    have h1 := congrArg (fun z : Conf (n + 1) X ↦ z i) (snoc_forgetFun_last x)
    simp only [snoc, mk_apply] at h1 ⊢
    rw [← h]
    exact h1
  · rintro ⟨p, rfl⟩
    simp

theorem isPathConnected_fiber_of_isPathConnected (y : Conf n X)
    (hy : IsPathConnected ((range y)ᶜ : Set X)) :
    IsPathConnected (forget ⁻¹' {y} : Set (Conf (n + 1) X)) := by
  rw [forget_preimage_singleton]
  haveI := isPathConnected_iff_pathConnectedSpace.1 hy
  have hc : Continuous fun p : ((range y)ᶜ : Set X) ↦ snoc y p.1 p.2 :=
    ((fiberHomeomorph y).symm.continuous.comp continuous_id).subtype_val
  rw [← image_univ]
  exact isPathConnected_univ.image hc

/-- For a connected Hausdorff manifold of dimension `> 1`, the fibres of the forgetful map are
path-connected. -/
theorem isPathConnected_fiber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : 1 < Module.rank ℝ E) [T2Space X] [ConnectedSpace X] [ChartedSpace E X]
    (y : Conf n X) : IsPathConnected (forget ⁻¹' {y} : Set (Conf (n + 1) X)) :=
  isPathConnected_fiber_of_isPathConnected y
    (ChartedSpace.isPathConnected_compl_of_finite hE (finite_range y))

/-! ### The Fadell–Neuwirth exact sequence -/

section FadellNeuwirth

variable (x₀ : Conf (n + 1) X)

/-- The point `last x₀` of the punctured space `X ∖ {y₀, …, yₙ₋₁}`, `y = forget x₀`. -/
def puncturedBase : ((range (forget x₀))ᶜ : Set X) := fiberHomeomorph (forget x₀) ⟨x₀, rfl⟩

/-- The map `π₁(X ∖ {y₀, …, yₙ₋₁}, last x₀) → π₁(Conf (n + 1) X, x₀)` induced by
`p ↦ (y₀, …, yₙ₋₁, p)`. -/
noncomputable def puncturedToConf :
    FundamentalGroup ((range (forget x₀))ᶜ : Set X) (puncturedBase x₀) →*
      FundamentalGroup (Conf (n + 1) X) x₀ :=
  (FundamentalGroup.mapFiberIncl forget x₀).comp
    (FundamentalGroup.mulEquivOfHomeomorph (fiberHomeomorph (forget x₀))
      (FundamentalGroup.fiberBase forget x₀)).symm.toMonoidHom

theorem range_puncturedToConf :
    (puncturedToConf x₀).range = (FundamentalGroup.mapFiberIncl forget x₀).range := by
  rw [puncturedToConf, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
    ← MonoidHom.range_eq_map]

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [T2Space X] [ChartedSpace E X]
include E

/-- **Fadell–Neuwirth, exactness in the middle**: the kernel of `π₁(Conf (n+1) X) → π₁(Conf n X)`
is the image of `π₁(X ∖ {y₀, …, yₙ₋₁})`. -/
theorem fadellNeuwirth_range_eq_ker :
    (puncturedToConf x₀).range = (FundamentalGroup.map forget x₀).ker := by
  rw [range_puncturedToConf, FundamentalGroup.ker_map_eq_range_map_fiberIncl _ _
    (isLocallyTrivial_forget_of_chartedSpace E n)]

/-- **Fadell–Neuwirth, surjectivity**: for a connected manifold of dimension `> 1`,
`π₁(Conf (n+1) X) → π₁(Conf n X)` is surjective. -/
theorem fadellNeuwirth_surjective (hE : 1 < Module.rank ℝ E) [ConnectedSpace X] :
    Surjective (FundamentalGroup.map forget x₀) :=
  FundamentalGroup.map_surjective_of_isPathConnected _ _
    (isLocallyTrivial_forget_of_chartedSpace E n) (isPathConnected_fiber hE _)

/-- **Fadell–Neuwirth, injectivity**: if `π₂(Conf n X)` is trivial, then
`π₁(X ∖ {y₀, …, yₙ₋₁}) → π₁(Conf (n+1) X)` is injective. -/
theorem fadellNeuwirth_injective (h2 : Subsingleton (π_ 2 (Conf n X) (forget x₀))) :
    Injective (puncturedToConf x₀) :=
  (FundamentalGroup.map_fiberIncl_injective _ _ (isLocallyTrivial_forget_of_chartedSpace E n)
    h2).comp (MulEquiv.injective _)

end FadellNeuwirth

end Conf
