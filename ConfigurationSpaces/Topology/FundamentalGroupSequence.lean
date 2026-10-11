/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.CubeLifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Connected.PathConnected

/-!
# The fundamental-group sequence of a locally trivial map

Let `p : E → B` be continuous and locally trivial, `e₀ : E`, `F = p⁻¹ {p e₀}` the fibre through
`e₀` and `i : F → E` the inclusion. We prove the exactness properties of
```
π₂(B) → π₁(F, e₀) → π₁(E, e₀) → π₁(B, p e₀) → π₀(F)
```
in the following concrete form:

* `FundamentalGroup.map_comp_map_fiberIncl`: `p_* ∘ i_* = 1`;
* `FundamentalGroup.ker_map_eq_range_map_fiberIncl`: `ker p_* = range i_*`;
* `FundamentalGroup.map_surjective_of_isPathConnected`: `p_*` is surjective if `F` is
  path-connected;
* `FundamentalGroup.map_fiberIncl_injective`: `i_*` is injective if `π₂(B, p e₀)` is trivial.

The proofs use the homotopy lifting property of `IsLocallyTrivial.exists_lift_homotopy` (for
squares and cubes) and the "square lemma" `Path.homotopic_square`: for a map `Q` of the square, the
paths along the left and top edges and along the bottom and right edges are homotopic.
-/

open CategoryTheory unitInterval Topology Function

universe u v w

instance unitInterval.contractibleSpace : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩

/-! ### The square lemma -/

namespace Path

/-- The left edge `s ↦ (0, s)` of the square. -/
def sqLeft : Path ((0 : I), (0 : I)) (0, 1) := (Path.refl 0).prod Path.id
/-- The top edge `t ↦ (t, 1)` of the square. -/
def sqTop : Path ((0 : I), (1 : I)) (1, 1) := Path.id.prod (Path.refl 1)
/-- The bottom edge `t ↦ (t, 0)` of the square. -/
def sqBottom : Path ((0 : I), (0 : I)) (1, 0) := Path.id.prod (Path.refl 0)
/-- The right edge `s ↦ (1, s)` of the square. -/
def sqRight : Path ((1 : I), (0 : I)) (1, 1) := (Path.refl 1).prod Path.id

variable {Y : Type w} [TopologicalSpace Y]

/-- **Square lemma.** For a map `Q : I × I → Y` and paths `l, t, b, r` running along the left, top,
bottom and right edges of `Q`, the paths `l ⬝ t` and `b ⬝ r` are homotopic. -/
theorem homotopic_square (Q : C(I × I, Y)) {a b c d : Y} (l : Path a b) (t : Path b d)
    (bo : Path a c) (r : Path c d) (hl : ∀ s, l s = Q (0, s)) (ht : ∀ v, t v = Q (v, 1))
    (hb : ∀ v, bo v = Q (v, 0)) (hr : ∀ s, r s = Q (1, s)) :
    (l.trans t).Homotopic (bo.trans r) := by
  obtain rfl : a = Q (0, 0) := by simpa using hl 0
  obtain rfl : b = Q (0, 1) := by simpa using hl 1
  obtain rfl : c = Q (1, 0) := by simpa using hb 1
  obtain rfl : d = Q (1, 1) := by simpa using hr 1
  have e1 : l = sqLeft.map Q.continuous := by ext s; simp [hl, sqLeft]
  have e2 : t = sqTop.map Q.continuous := by ext s; simp [ht, sqTop]
  have e3 : bo = sqBottom.map Q.continuous := by ext s; simp [hb, sqBottom]
  have e4 : r = sqRight.map Q.continuous := by ext s; simp [hr, sqRight]
  rw [e1, e2, e3, e4, ← Path.map_trans, ← Path.map_trans]
  exact (SimplyConnectedSpace.paths_homotopic _ _).map Q

/-- The square lemma in the fundamental groupoid. -/
theorem fromPath_comp_square (Q : C(I × I, Y)) {a b c d : Y} (l : Path a b) (t : Path b d)
    (bo : Path a c) (r : Path c d) (hl : ∀ s, l s = Q (0, s)) (ht : ∀ v, t v = Q (v, 1))
    (hb : ∀ v, bo v = Q (v, 0)) (hr : ∀ s, r s = Q (1, s)) :
    (FundamentalGroupoid.fromPath (.mk l) ≫ FundamentalGroupoid.fromPath (.mk t) :
      FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk d) =
    FundamentalGroupoid.fromPath (.mk bo) ≫ FundamentalGroupoid.fromPath (.mk r) :=
  Quotient.sound (homotopic_square Q l t bo r hl ht hb hr)

/-- A path in a subset `S`, built from a path in the ambient space with values in `S`. -/
def ofMemSubset {S : Set Y} (f : C(I, Y)) (hf : ∀ t, f t ∈ S) {a b : S} (ha : f 0 = a)
    (hb : f 1 = b) : Path a b where
  toFun t := ⟨f t, hf t⟩
  continuous_toFun := f.continuous.subtype_mk _
  source' := Subtype.ext ha
  target' := Subtype.ext hb

@[simp] theorem ofMemSubset_apply {S : Set Y} (f : C(I, Y)) (hf : ∀ t, f t ∈ S) {a b : S}
    (ha : f 0 = a) (hb : f 1 = b) (t : I) : (ofMemSubset f hf ha hb t : Y) = f t := rfl

end Path

/-! ### The sequence -/

noncomputable section

namespace FundamentalGroup

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
  (e₀ : E)

/-- The inclusion of the fibre `p⁻¹ {p e₀}` into `E`. -/
def fiberIncl : C(p ⁻¹' {p e₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The base point `e₀` of the fibre `p⁻¹ {p e₀}`. -/
def fiberBase : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩

@[simp] theorem fiberIncl_apply (x : p ⁻¹' {p e₀}) : fiberIncl p e₀ x = x := rfl

/-- The map `π₁(F, e₀) → π₁(E, e₀)` induced by the inclusion of the fibre. -/
def mapFiberIncl : FundamentalGroup (p ⁻¹' {p e₀}) (fiberBase p e₀) →* FundamentalGroup E e₀ :=
  map (fiberIncl p e₀) (fiberBase p e₀)

theorem mem_fiber_iff {x : E} : x ∈ p ⁻¹' {p e₀} ↔ p x = p e₀ := Iff.rfl

/-- The composite `π₁(F) → π₁(E) → π₁(B)` is trivial. -/
theorem map_comp_map_fiberIncl :
    (map p e₀).comp (mapFiberIncl p e₀) = 1 := by
  ext g
  obtain ⟨γ⟩ := g
  change Path.Homotopic.Quotient.mk ((γ.map (fiberIncl p e₀).continuous).map p.continuous) =
    Path.Homotopic.Quotient.mk (.refl _)
  congr 1
  ext t
  exact (γ t).2

theorem range_le_ker : (mapFiberIncl p e₀).range ≤ (map p e₀).ker := by
  rintro _ ⟨g, rfl⟩
  have := DFunLike.congr_fun (map_comp_map_fiberIncl p e₀) g
  rw [MonoidHom.mem_ker]
  exact this

/-- **Exactness at `π₁(E)`**: for a locally trivial map, the kernel of `p_*` is the image of the
fundamental group of the fibre. -/
theorem ker_map_eq_range_map_fiberIncl (hp : IsLocallyTrivial p) :
    (map p e₀).ker = (mapFiberIncl p e₀).range := by
  refine le_antisymm ?_ (range_le_ker p e₀)
  intro g hg
  obtain ⟨γ⟩ := g
  obtain ⟨K⟩ : (γ.map p.continuous).Homotopic (Path.refl (p e₀)) := Quotient.exact hg
  obtain ⟨G, hG, hG0⟩ := hp.exists_lift_square K.toContinuousMap γ.toContinuousMap
    fun s ↦ by simp
  have hGK : ∀ q, p (G q) = K q := fun q ↦ congrFun hG q
  have mem0 : ∀ v, G (v, 0) ∈ p ⁻¹' {p e₀} := fun v ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hGK]
    exact K.source v
  have mem1 : ∀ v, G (v, 1) ∈ p ⁻¹' {p e₀} := fun v ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hGK]
    exact K.target v
  have memr : ∀ s, G (1, s) ∈ p ⁻¹' {p e₀} := fun s ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hGK]
    simp
  let f₁ : p ⁻¹' {p e₀} := ⟨G (1, 0), mem0 1⟩
  let f₂ : p ⁻¹' {p e₀} := ⟨G (1, 1), mem1 1⟩
  let bo : Path (fiberBase p e₀) f₁ := Path.ofMemSubset (G.comp ⟨fun v ↦ (v, 0), by fun_prop⟩)
    mem0 (by simp [hG0, fiberBase]) rfl
  let r : Path f₁ f₂ := Path.ofMemSubset (G.comp ⟨fun s ↦ (1, s), by fun_prop⟩) memr rfl rfl
  let t : Path (fiberBase p e₀) f₂ := Path.ofMemSubset (G.comp ⟨fun v ↦ (v, 1), by fun_prop⟩)
    mem1 (by simp [hG0, fiberBase]) rfl
  have hsq := Path.fromPath_comp_square G γ (t.map (fiberIncl p e₀).continuous)
    (bo.map (fiberIncl p e₀).continuous) (r.map (fiberIncl p e₀).continuous)
    (fun s ↦ (hG0 s).symm) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  refine ⟨FundamentalGroupoid.fromPath (.mk bo) ≫ FundamentalGroupoid.fromPath (.mk r) ≫
    inv (FundamentalGroupoid.fromPath (.mk t)), ?_⟩
  change (FundamentalGroupoid.map (fiberIncl p e₀)).map _ = _
  rw [Functor.map_comp, Functor.map_comp, Functor.map_inv, ← Category.assoc, IsIso.comp_inv_eq]
  exact hsq.symm

/-- **Exactness at `π₁(B)`**: if the fibre is path-connected, `p_*` is surjective. -/
theorem map_surjective_of_isPathConnected (hp : IsLocallyTrivial p)
    (hF : IsPathConnected (p ⁻¹' {p e₀})) : Surjective (map p e₀) := by
  intro g
  obtain ⟨β⟩ := g
  obtain ⟨Γ, hΓ, hΓ0⟩ := hp.exists_path_lift β.toContinuousMap e₀ (by simp)
  have hΓp : ∀ t, p (Γ t) = β t := fun t ↦ congrFun hΓ t
  have hmem : Γ 1 ∈ p ⁻¹' {p e₀} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hΓp]; simp
  let δ := (hF.joinedIn _ hmem _ rfl).somePath
  have hδ : ∀ t, p (δ t) = p e₀ := fun t ↦ (hF.joinedIn _ hmem _ rfl).somePath_mem t
  let Γp : Path e₀ (Γ 1) := ⟨Γ, hΓ0, rfl⟩
  refine ⟨Path.Homotopic.Quotient.mk (Γp.trans δ), ?_⟩
  change Path.Homotopic.Quotient.mk ((Γp.trans δ).map p.continuous) = Path.Homotopic.Quotient.mk β
  have : (Γp.trans δ).map p.continuous = β.trans (Path.refl (p e₀)) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.trans_apply, Path.refl_apply]
    split_ifs
    · exact hΓp _
    · exact hδ _
  rw [this]
  exact Quotient.sound ⟨Path.Homotopy.transRefl β⟩

/-- The point `(t, s)` of the cube `I²`, as a map `Fin 2 → I`. -/
def sqPt (q : I × I) : Fin 2 → I := ![q.1, q.2]

@[fun_prop] theorem continuous_sqPt : Continuous sqPt :=
  continuous_pi fun i ↦ by fin_cases i <;> [exact continuous_fst; exact continuous_snd]

@[simp] theorem sqPt_zero (q : I × I) : sqPt q 0 = q.1 := rfl
@[simp] theorem sqPt_one (q : I × I) : sqPt q 1 = q.2 := rfl

/-- **Exactness at `π₁(F)`**: if `π₂(B, p e₀)` is trivial, `i_*` is injective. -/
theorem map_fiberIncl_injective (hp : IsLocallyTrivial p)
    (h2 : Subsingleton (π_ 2 B (p e₀))) :
    Injective (mapFiberIncl p e₀) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨α⟩ := g
  obtain ⟨Hh⟩ : (α.map (fiberIncl p e₀).continuous).Homotopic (Path.refl e₀) := Quotient.exact hg
  -- the 2-sphere `p ∘ Hh` in `B`
  let c2 : C(Fin 2 → I, I × I) := ⟨fun y ↦ (y 0, y 1), by fun_prop⟩
  have hHh : ∀ y : Fin 2 → I, y ∈ Cube.boundary (Fin 2) → p (Hh (y 0, y 1)) = p e₀ := by
    rintro y ⟨i, hi⟩
    fin_cases i <;> rcases hi with hi | hi <;> simp only [Fin.zero_eta, Fin.mk_one] at hi
    · have := Hh.apply_zero (y 1)
      rw [hi, this]
      exact (α (y 1)).2
    · have := Hh.apply_one (y 1)
      rw [hi, this]; rfl
    · rw [hi]; simp; rfl
    · rw [hi]; simp; rfl
  let sph : GenLoop (Fin 2) B (p e₀) := ⟨p.comp (Hh.toContinuousMap.comp c2), hHh⟩
  obtain ⟨K⟩ : GenLoop.Homotopic sph GenLoop.const :=
    Quotient.exact (Subsingleton.elim (α := π_ 2 B (p e₀)) ⟦sph⟧ ⟦GenLoop.const⟧)
  -- lift the null-homotopy of the sphere
  obtain ⟨L, hL, hL0⟩ := hp.exists_lift_homotopy K.toContinuousMap
    (Hh.toContinuousMap.comp c2) fun y ↦ by
      simp only [ContinuousMap.HomotopyWith.coe_toContinuousMap, K.apply_zero]; rfl
  have hLK : ∀ q, p (L q) = K q := fun q ↦ congrFun hL q
  have memB : ∀ u, ∀ y ∈ Cube.boundary (Fin 2), L (u, y) ∈ p ⁻¹' {p e₀} := fun u y hy ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hLK]
    exact (K.eq_fst u hy).trans (sph.2 y hy)
  have mem1 : ∀ y, L (1, y) ∈ p ⁻¹' {p e₀} := fun y ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hLK]
    exact (K.apply_one y).trans rfl
  have hbd0 : ∀ t s : I, s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1 → sqPt (t, s) ∈ Cube.boundary (Fin 2) := by
    rintro t s (h | h | h | h)
    · exact ⟨1, Or.inl h⟩
    · exact ⟨1, Or.inr h⟩
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
  have hL0' : ∀ t s, L (0, sqPt (t, s)) = Hh (t, s) := fun t s ↦ hL0 _
  -- the corner points of the top face `u = 1`
  let w : I → I → p ⁻¹' {p e₀} := fun t s ↦ ⟨L (1, sqPt (t, s)), mem1 _⟩
  let base := fiberBase p e₀
  -- edges in the `u`-direction, from `e₀` to `w t s`
  have hcorner : ∀ t s : I, (t = 0 ∨ t = 1) → (s = 0 ∨ s = 1) → L (0, sqPt (t, s)) = e₀ := by
    intro t s ht hs
    rw [hL0']
    rcases hs with rfl | rfl
    · exact Hh.source t
    · exact Hh.target t
  let eu : ∀ t s : I, (t = 0 ∨ t = 1) → (s = 0 ∨ s = 1) → Path base (w t s) :=
    fun t s ht hs ↦ Path.ofMemSubset (L.comp ⟨fun u ↦ (u, sqPt (t, s)), by fun_prop⟩)
      (fun u ↦ memB u _ (hbd0 t s (by rcases hs with h | h <;> simp [h])))
      (hcorner t s ht hs) rfl
  -- edges in the `t`-direction on the top face
  let et : ∀ s : I, Path (w 0 s) (w 1 s) := fun s ↦ Path.ofMemSubset
    (L.comp ⟨fun t ↦ (1, sqPt (t, s)), by fun_prop⟩) (fun _ ↦ mem1 _) rfl rfl
  -- edges in the `s`-direction on the top face
  let es : ∀ t : I, Path (w t 0) (w t 1) := fun t ↦ Path.ofMemSubset
    (L.comp ⟨fun s ↦ (1, sqPt (t, s)), by fun_prop⟩) (fun _ ↦ mem1 _) rfl rfl
  have h00 : ((0 : I) = 0 ∨ (0 : I) = 1) := Or.inl rfl
  have h11 : ((1 : I) = 0 ∨ (1 : I) = 1) := Or.inr rfl
  -- the faces of the cube other than `u = 0`, as maps into the fibre
  let F := p ⁻¹' {p e₀}
  -- the faces of the cube other than `u = 0`, as maps into the fibre
  let face : ∀ φ : C(I × I, I × (Fin 2 → I)), (∀ q, L (φ q) ∈ F) → C(I × I, F) :=
    fun φ hφ ↦ ⟨fun q ↦ ⟨L (φ q), hφ q⟩, (L.continuous.comp φ.continuous).subtype_mk _⟩
  let R0 := face ⟨fun q ↦ (q.1, sqPt (q.2, 0)), by fun_prop⟩
    fun q ↦ memB _ _ (hbd0 _ _ (Or.inl rfl))
  let R1 := face ⟨fun q ↦ (q.1, sqPt (q.2, 1)), by fun_prop⟩
    fun q ↦ memB _ _ (hbd0 _ _ (Or.inr (Or.inl rfl)))
  let T0 := face ⟨fun q ↦ (q.1, sqPt (0, q.2)), by fun_prop⟩
    fun q ↦ memB _ _ (hbd0 _ _ (Or.inr (Or.inr (Or.inl rfl))))
  let T1 := face ⟨fun q ↦ (q.1, sqPt (1, q.2)), by fun_prop⟩
    fun q ↦ memB _ _ (hbd0 _ _ (Or.inr (Or.inr (Or.inr rfl))))
  let U1 := face ⟨fun q ↦ (1, sqPt (q.1, q.2)), by fun_prop⟩ fun q ↦ mem1 _
  have hs0 : ∀ s : I, base = R0 (0, s) := fun s ↦ Subtype.ext <| by
    simp only [base, fiberBase]; exact ((hL0' s 0).trans (Hh.source s)).symm
  have hs1 : ∀ s : I, base = R1 (0, s) := fun s ↦ Subtype.ext <| by
    simp only [base, fiberBase]; exact ((hL0' s 1).trans (Hh.target s)).symm
  have ht1 : ∀ s : I, base = T1 (0, s) := fun s ↦ Subtype.ext <| by
    simp only [base, fiberBase]; exact ((hL0' 1 s).trans (Hh.apply_one s)).symm
  have ht0 : ∀ s : I, α s = T0 (0, s) := fun s ↦ Subtype.ext <| by
    exact ((hL0' 0 s).trans (Hh.apply_zero s)).symm
  have h1 := Path.fromPath_comp_square R0 (Path.refl base) (eu 1 0 h11 h00) (eu 0 0 h00 h00)
    (et 0) hs0 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h2 := Path.fromPath_comp_square R1 (Path.refl base) (eu 1 1 h11 h11) (eu 0 1 h00 h11)
    (et 1) hs1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h3 := Path.fromPath_comp_square T0 α (eu 0 1 h00 h11) (eu 0 0 h00 h00)
    (es 0) ht0 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h4 := Path.fromPath_comp_square T1 (Path.refl base) (eu 1 1 h11 h11) (eu 1 0 h11 h00)
    (es 1) ht1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have h5 := Path.fromPath_comp_square U1 (es 0) (et 1) (et 0) (es 1)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have e : FundamentalGroupoid.fromPath (.mk (Path.refl base)) = 𝟙 _ := rfl
  rw [e, Category.id_comp] at h1 h2 h4
  change FundamentalGroupoid.fromPath (.mk α) = 𝟙 _
  set a := FundamentalGroupoid.fromPath (.mk α)
  set u00 := FundamentalGroupoid.fromPath (.mk (eu 0 0 h00 h00))
  set u01 := FundamentalGroupoid.fromPath (.mk (eu 0 1 h00 h11))
  set u10 := FundamentalGroupoid.fromPath (.mk (eu 1 0 h11 h00))
  set u11 := FundamentalGroupoid.fromPath (.mk (eu 1 1 h11 h11))
  set t0 := FundamentalGroupoid.fromPath (.mk (et 0))
  set t1 := FundamentalGroupoid.fromPath (.mk (et 1))
  set s0 := FundamentalGroupoid.fromPath (.mk (es 0))
  set s1 := FundamentalGroupoid.fromPath (.mk (es 1))
  have key : inv u01 = t1 ≫ inv u11 := by rw [h2]; simp
  calc a = a ≫ u01 ≫ inv u01 := by simp
    _ = u00 ≫ s0 ≫ inv u01 := by rw [← Category.assoc, h3, Category.assoc]
    _ = u00 ≫ s0 ≫ t1 ≫ inv u11 := by rw [key]
    _ = u00 ≫ t0 ≫ s1 ≫ inv u11 := by rw [← Category.assoc s0, h5, Category.assoc]
    _ = u10 ≫ s1 ≫ inv u11 := by rw [← Category.assoc, ← h1]
    _ = 𝟙 _ := by rw [← Category.assoc, ← h4]; simp

end FundamentalGroup

end
