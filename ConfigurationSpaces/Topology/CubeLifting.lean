/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ConfigurationSpaces.Topology.LocallyTrivial
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Finset.Sort

/-!
# Homotopy lifting for locally trivial maps

We prove that a locally trivial map `p : E → B` has the homotopy lifting property for all cubes
(i.e. it is a Serre fibration): every homotopy `H : I × Iᵏ → B` whose restriction to `{0} × Iᵏ`
has a lift `g₀` lifts to `E`, extending `g₀` (`IsLocallyTrivial.exists_lift_homotopy`).

## Proof

Subdivide the cube `Iᵏ⁺¹` into a grid of cells of side `1/m`, so fine (Lebesgue number) that each
cell is mapped by `H` into a trivialising open set. Process the cells in lexicographic order. When
cell `a` is reached, the lift is already defined and continuous on the initial face and on all
lexicographically smaller cells; these meet the cell `a` only in the union `L` of some of its lower
faces (the face `xᵢ = aᵢ/m` for each `i` with `aᵢ > 0`, and the face `x₀ = 0` when `a₀ = 0`). The
cell retracts onto `L` by `x ↦ x - (minᵢ∈S (xᵢ - aᵢ/m)) · 1_S`, and
`extend_through_trivialization` extends the lift over the cell.

## Main results

* `CubeLifting.exists_lift_cube`: the statement for the cube `Fin (k + 1) → I`, the initial face
  being `x 0 = 0`;
* `IsLocallyTrivial.exists_lift_homotopy`: homotopies `I × (Fin k → I) → B`;
* `IsLocallyTrivial.exists_lift_square`, `IsLocallyTrivial.exists_path_lift`: the cases
  `I × I` and paths.
-/

open Set Function Topology unitInterval

universe u v

namespace CubeLifting

variable {K : ℕ}

/-- The closed grid cell of index `c` and mesh `1 / m` in the cube `Fin K → I`. -/
def cell (m : ℕ) (c : Fin K → Fin m) : Set (Fin K → I) :=
  {x | ∀ i, ((c i : ℕ) : ℝ) / m ≤ x i ∧ (x i : ℝ) ≤ ((c i : ℕ) + 1) / m}

theorem isClosed_cell (m : ℕ) (c : Fin K → Fin m) : IsClosed (cell m c) := by
  simp only [cell, setOf_forall]
  refine isClosed_iInter fun i ↦ IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (show Continuous fun x : Fin K → I ↦ (x i : ℝ) by fun_prop)
  · exact isClosed_le (show Continuous fun x : Fin K → I ↦ (x i : ℝ) by fun_prop) continuous_const

theorem exists_mem_cell {m : ℕ} (hm : 0 < m) (x : Fin K → I) : ∃ c, x ∈ cell m c := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨fun i ↦ ⟨min ⌊(x i : ℝ) * m⌋₊ (m - 1), by omega⟩, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [div_le_iff₀ hm']
    dsimp only
    calc ((min ⌊(x i : ℝ) * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ (⌊(x i : ℝ) * m⌋₊ : ℝ) := by
          exact_mod_cast min_le_left _ _
      _ ≤ x i * m := Nat.floor_le (mul_nonneg (x i).2.1 hm'.le)
  · rw [le_div_iff₀ hm']
    dsimp only
    rcases le_total ⌊(x i : ℝ) * m⌋₊ (m - 1) with h | h
    · rw [min_eq_left h]
      exact (Nat.lt_floor_add_one _).le
    · rw [min_eq_right h]
      have h1 : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [h1]
      nlinarith [(x i).2.2]

/-- **Lebesgue number for grids**: every open cover of the cube is refined by the grid of mesh
`1 / m` for some `m > 0`. -/
theorem exists_grid {ι : Type*} {U : ι → Set (Fin K → I)} (hU : ∀ i, IsOpen (U i))
    (hcov : univ ⊆ ⋃ i, U i) : ∃ m, 0 < m ∧ ∀ c : Fin K → Fin m, ∃ i, cell m c ⊆ U i := by
  obtain ⟨δ, δpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcov
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hm0 : (0 : ℝ) < m := (one_div_pos.2 δpos).trans hm
  have hm0' : 0 < m := by exact_mod_cast hm0
  refine ⟨m, hm0', fun c ↦ ?_⟩
  let x₀ : Fin K → I := fun i ↦ ⟨((c i : ℕ) : ℝ) / m, div_nonneg (Nat.cast_nonneg _) hm0.le, by
    rw [div_le_one hm0]; exact_mod_cast (c i).2.le⟩
  obtain ⟨j, hj⟩ := hδ x₀ (mem_univ _)
  refine ⟨j, fun y hy ↦ hj ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff δpos]
  intro i
  rw [Subtype.dist_eq, Real.dist_eq]
  obtain ⟨h1, h2⟩ := hy i
  have : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hm0]; rw [div_lt_iff₀ δpos] at hm; linarith
  rw [abs_lt]
  constructor
  · simp only [x₀]; linarith [div_nonneg zero_le_one hm0.le]
  · simp only [x₀]
    have : ((c i : ℕ) + 1 : ℝ) / m = (c i : ℕ) / m + 1 / m := by ring
    linarith

section Retraction

variable {m : ℕ} (a : Fin K → Fin m) {S : Finset (Fin K)} (hS : S.Nonempty)

/-- The union of the lower faces `xᵢ = aᵢ / m`, `i ∈ S`, of the cell `a`. -/
def lowerFaces (S : Finset (Fin K)) : Set (Fin K → I) :=
  cell m a ∩ {x | ∃ i ∈ S, (x i : ℝ) = ((a i : ℕ) : ℝ) / m}

/-- The distance of `x` to the union of the lower faces `S` of the cell `a`, in the direction
`(1, …, 1)`. -/
noncomputable def depth (x : Fin K → I) : ℝ := S.inf' hS fun i ↦ (x i : ℝ) - ((a i : ℕ) : ℝ) / m

/-- The retraction of the cell `a` onto its lower faces in `S`: subtract `depth` from the
coordinates in `S` (clamped to `I`, which does nothing on the cell). -/
noncomputable def retract (x : Fin K → I) : Fin K → I :=
  fun i ↦ if i ∈ S then projIcc 0 1 zero_le_one ((x i : ℝ) - depth a hS x) else x i

theorem continuous_depth : Continuous (depth a hS) := by
  unfold depth
  exact Continuous.finset_inf'_apply hS fun i _ ↦ by fun_prop

theorem continuous_retract : Continuous (retract a hS) := by
  refine continuous_pi fun i ↦ ?_
  unfold retract
  split_ifs
  · have := continuous_depth a hS
    exact continuous_projIcc.comp (by fun_prop)
  · exact continuous_apply i

theorem depth_le {x : Fin K → I} {i : Fin K} (hi : i ∈ S) :
    depth a hS x ≤ (x i : ℝ) - ((a i : ℕ) : ℝ) / m :=
  Finset.inf'_le (fun i ↦ (x i : ℝ) - ((a i : ℕ) : ℝ) / m) hi

theorem depth_nonneg {x : Fin K → I} (hx : x ∈ cell m a) : 0 ≤ depth a hS x :=
  (Finset.le_inf'_iff hS _).2 fun i _ ↦ sub_nonneg.2 (hx i).1

theorem retract_apply_of_mem {x : Fin K → I} (hx : x ∈ cell m a) {i : Fin K} (hi : i ∈ S) :
    (retract a hS x i : ℝ) = x i - depth a hS x := by
  simp only [retract, hi, if_true]
  have hmem : (x i : ℝ) - depth a hS x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have := depth_le a hS (x := x) hi
      have : (0 : ℝ) ≤ ((a i : ℕ) : ℝ) / m := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    · linarith [depth_nonneg a hS hx, (x i).2.2]
  rw [projIcc_of_mem _ hmem]

theorem retract_mem_lowerFaces {x : Fin K → I} (hx : x ∈ cell m a) :
    retract a hS x ∈ lowerFaces a S := by
  refine ⟨fun i ↦ ?_, ?_⟩
  · by_cases hi : i ∈ S
    · rw [retract_apply_of_mem a hS hx hi]
      have := depth_le a hS (x := x) hi
      have := depth_nonneg a hS hx
      exact ⟨by linarith, by linarith [(hx i).2]⟩
    · simp only [retract, hi, if_false]
      exact hx i
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' hS fun i ↦ (x i : ℝ) - ((a i : ℕ) : ℝ) / m
    refine ⟨i, hi, ?_⟩
    rw [retract_apply_of_mem a hS hx hi]
    simp only [depth, hmin]
    ring

theorem lowerFaces_subset_cell : lowerFaces a S ⊆ cell m a := inter_subset_left

theorem retract_eq_self {x : Fin K → I} (hx : x ∈ lowerFaces a S) : retract a hS x = x := by
  obtain ⟨hx, i, hi, hxi⟩ := hx
  have h0 : depth a hS x = 0 :=
    le_antisymm ((depth_le a hS hi).trans (by rw [hxi, sub_self])) (depth_nonneg a hS hx)
  funext j
  by_cases hj : j ∈ S
  · apply Subtype.ext
    rw [retract_apply_of_mem a hS hx hj, h0, sub_zero]
  · simp [retract, hj]

end Retraction

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- **Homotopy lifting for cubes.** Let `p` be locally trivial, `H : Iᵏ⁺¹ → B` continuous and `g₀`
a continuous map which lifts `H` on the face `x 0 = 0`. Then there is a continuous lift `G` of
`H` agreeing with `g₀` on that face. -/
theorem exists_lift_cube {p : E → B} (hp : IsLocallyTrivial p) {k : ℕ}
    (H : C(Fin (k + 1) → I, B)) (g₀ : C(Fin (k + 1) → I, E))
    (hg₀ : ∀ x : Fin (k + 1) → I, x 0 = 0 → p (g₀ x) = H x) :
    ∃ G : C(Fin (k + 1) → I, E), p ∘ G = H ∧ ∀ x, x 0 = 0 → G x = g₀ x := by
  classical
  choose U hUo hbU F instF φ hφ using hp
  obtain ⟨m, hm, hgrid⟩ := exists_grid (U := fun b ↦ H ⁻¹' U b)
    (fun b ↦ (hUo b).preimage H.continuous) (fun x _ ↦ mem_iUnion.2 ⟨H x, hbU (H x)⟩)
  choose b hb using hgrid
  set N := Fintype.card (Lex (Fin (k + 1) → Fin m))
  let e : Fin N ≃o Lex (Fin (k + 1) → Fin m) := Fintype.orderIsoFinOfCardEq _ rfl
  let A₀ : Set (Fin (k + 1) → I) := {x | x 0 = 0}
  let D : ℕ → Set (Fin (k + 1) → I) := fun j ↦
    A₀ ∪ ⋃ (j' : Fin N) (_ : (j' : ℕ) < j), cell m (ofLex (e j'))
  have hA₀ : IsClosed A₀ := isClosed_eq (continuous_apply 0) continuous_const
  have hD : ∀ j, IsClosed (D j) := fun j ↦
    hA₀.union (isClosed_iUnion_of_finite fun j' ↦ isClosed_iUnion_of_finite fun _ ↦
      isClosed_cell _ _)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  suffices ∀ j ≤ N, ∃ G : (Fin (k + 1) → I) → E, ContinuousOn G (D j) ∧
      (∀ x ∈ D j, p (G x) = H x) ∧ ∀ x ∈ A₀, G x = g₀ x by
    obtain ⟨G, hGc, hGp, hG0⟩ := this N le_rfl
    have hDN : D N = univ := by
      refine eq_univ_of_forall fun x ↦ ?_
      obtain ⟨c, hc⟩ := exists_mem_cell hm x
      refine Or.inr (mem_iUnion₂.2 ⟨e.symm (toLex c), (e.symm (toLex c)).2, ?_⟩)
      simpa using hc
    rw [hDN, continuousOn_univ] at hGc
    exact ⟨⟨G, hGc⟩, funext fun x ↦ hGp x (hDN ▸ mem_univ x), hG0⟩
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨g₀, g₀.continuous.continuousOn, fun x hx ↦ ?_, fun _ _ ↦ rfl⟩
    rcases hx with hx | hx
    · exact hg₀ x hx
    · simp at hx
  | succ j ih =>
    intro hj
    replace hj : j < N := hj
    obtain ⟨G, hGc, hGp, hG0⟩ := ih (by omega)
    set a : Fin (k + 1) → Fin m := ofLex (e ⟨j, hj⟩) with ha
    let S : Finset (Fin (k + 1)) := Finset.univ.filter fun i ↦ i = 0 ∨ 0 < (a i : ℕ)
    have hS : S.Nonempty := ⟨0, by simp [S]⟩
    -- the part of the cell already treated is contained in the lower faces `L`
    have hDL : D j ∩ cell m a ⊆ lowerFaces a S := by
      rintro x ⟨hxD, hxa⟩
      refine ⟨hxa, ?_⟩
      rcases hxD with hx0 | hxD
      · refine ⟨0, by simp [S], ?_⟩
        have h1 := (hxa 0).1
        rw [show x 0 = 0 from hx0] at h1 ⊢
        have : (0 : ℝ) ≤ ((a 0 : ℕ) : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hm'.le
        simp only [Icc.coe_zero] at h1 ⊢
        linarith
      · obtain ⟨j', hj', hx'⟩ := mem_iUnion₂.1 hxD
        have hlt : e j' < toLex a := by
          rw [ha, toLex_ofLex]; exact e.strictMono (Fin.mk_lt_mk.2 hj')
        obtain ⟨i, -, hi⟩ := hlt
        have hai : 0 < (a i : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hi
        refine ⟨i, by simp [S, hai], le_antisymm ?_ (hxa i).1⟩
        calc (x i : ℝ) ≤ (((ofLex (e j')) i : ℕ) + 1 : ℝ) / m := (hx' i).2
          _ ≤ ((a i : ℕ) : ℝ) / m := by
            gcongr
            exact_mod_cast hi
    -- the lower faces `L` have already been treated
    have hLD : lowerFaces a S ⊆ D j := by
      rintro x ⟨hxa, i, hiS, hxi⟩
      rcases Nat.eq_zero_or_pos (a i : ℕ) with hai | hai
      · have hi0 : i = 0 := by simpa [S, hai] using hiS
        subst hi0
        left
        apply Subtype.ext
        simp [hxi, hai]
      · right
        let c : Fin (k + 1) → Fin m := update a i ⟨(a i : ℕ) - 1, by have := (a i).2; omega⟩
        have hc : toLex c < toLex a := by
          rw [Pi.toLex_update_lt_self_iff]
          exact Fin.lt_def.2 (Nat.sub_lt hai one_pos)
        refine mem_iUnion₂.2 ⟨e.symm (toLex c), ?_, ?_⟩
        · have : e.symm (toLex c) < ⟨j, hj⟩ := by
            rw [← e.symm_apply_apply ⟨j, hj⟩]
            exact e.symm.strictMono (by simpa [ha] using hc)
          exact this
        · simp only [OrderIso.apply_symm_apply, ofLex_toLex]
          intro l
          by_cases hl : l = i
          · subst hl
            simp only [c, update_self]
            rw [Nat.cast_sub (by omega), hxi]
            refine ⟨by gcongr; linarith, le_of_eq (by ring)⟩
          · simp only [c, update_of_ne hl]
            exact hxa l
    obtain ⟨g', hg'c, hg'p, hg'L⟩ := extend_through_trivialization (φ (b a)) (hφ (b a))
      (lowerFaces_subset_cell a) (continuous_retract a hS).continuousOn
      (fun x hx ↦ retract_mem_lowerFaces a hS hx) (fun x hx ↦ retract_eq_self a hS hx)
      H.continuous.continuousOn (hb a) (hGc.mono hLD) (fun x hx ↦ hGp x (hLD hx))
    refine ⟨fun x ↦ if x ∈ cell m a then g' x else G x, ?_, ?_, ?_⟩
    · have hsub : D (j + 1) ⊆ D j ∪ cell m a := by
        rintro x (hx | hx)
        · exact Or.inl (Or.inl hx)
        · obtain ⟨j', hj', hx'⟩ := mem_iUnion₂.1 hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | h
          · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨j', h, hx'⟩))
          · right
            have : j' = ⟨j, hj⟩ := Fin.ext h
            rw [this] at hx'
            exact hx'
      refine ContinuousOn.mono ?_ hsub
      refine ContinuousOn.union_of_isClosed ?_ ?_ (hD j) (isClosed_cell m a)
      · refine hGc.congr fun x hx ↦ ?_
        by_cases hxa : x ∈ cell m a
        · simp only [hxa, if_true]
          exact hg'L x (hDL ⟨hx, hxa⟩)
        · simp [hxa]
      · exact hg'c.congr fun x hx ↦ by simp [hx]
    · intro x hx
      by_cases hxa : x ∈ cell m a
      · simp only [hxa, if_true]; exact hg'p x hxa
      · simp only [hxa, if_false]
        rcases hx with hx | hx
        · exact hGp x (Or.inl hx)
        · obtain ⟨j', hj', hx'⟩ := mem_iUnion₂.1 hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | h
          · exact hGp x (Or.inr (mem_iUnion₂.2 ⟨j', h, hx'⟩))
          · exact absurd (by rw [show j' = ⟨j, hj⟩ from Fin.ext h] at hx'; exact hx') hxa
    · intro x hx
      by_cases hxa : x ∈ cell m a
      · simp only [hxa, if_true]
        rw [hg'L x (hDL ⟨Or.inl hx, hxa⟩)]
        exact hG0 x hx
      · simp only [hxa, if_false]
        exact hG0 x hx

/-- The cube `Iᵏ⁺¹` as `I × Iᵏ` (first coordinate split off). -/
def cubeHomeomorph (k : ℕ) : (Fin (k + 1) → I) ≃ₜ I × (Fin k → I) where
  toFun x := (x 0, Fin.tail x)
  invFun q := Fin.cons q.1 q.2
  left_inv x := Fin.cons_self_tail x
  right_inv q := by simp
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun _ ↦ continuous_apply _)
  continuous_invFun := Continuous.finCons continuous_fst continuous_snd

end CubeLifting

open CubeLifting

namespace IsLocallyTrivial

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- **Homotopy lifting property for cubes** (locally trivial maps are Serre fibrations): a
homotopy `H : I × Iᵏ → B` together with a lift `g₀` of `H (0, ·)` lifts to a homotopy
`G : I × Iᵏ → E` with `G (0, ·) = g₀`. -/
theorem exists_lift_homotopy (hp : IsLocallyTrivial p) {k : ℕ} (H : C(I × (Fin k → I), B))
    (g₀ : C(Fin k → I, E)) (hg₀ : ∀ y, p (g₀ y) = H (0, y)) :
    ∃ G : C(I × (Fin k → I), E), p ∘ G = H ∧ ∀ y, G (0, y) = g₀ y := by
  let c := cubeHomeomorph k
  obtain ⟨G, hG, hG0⟩ := exists_lift_cube hp (H.comp c) (g₀.comp ⟨Fin.tail, continuous_pi
    fun _ ↦ continuous_apply _⟩) (fun x hx ↦ by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [hg₀]
      congr 1
      exact Prod.ext hx.symm rfl)
  refine ⟨G.comp c.symm, ?_, fun y ↦ ?_⟩
  · funext q
    have := congrFun hG (c.symm q)
    simpa using this
  · have := hG0 (c.symm (0, y)) rfl
    simpa [c, cubeHomeomorph] using this

/-- Homotopy lifting for maps of the square `I × I`. -/
theorem exists_lift_square (hp : IsLocallyTrivial p) (H : C(I × I, B)) (g₀ : C(I, E))
    (hg₀ : ∀ s, p (g₀ s) = H (0, s)) :
    ∃ G : C(I × I, E), p ∘ G = H ∧ ∀ s, G (0, s) = g₀ s := by
  let e1 : (Fin 1 → I) ≃ₜ I := Homeomorph.funUnique (Fin 1) I
  let c : I × (Fin 1 → I) ≃ₜ I × I := (Homeomorph.refl I).prodCongr e1
  obtain ⟨G, hG, hG0⟩ := exists_lift_homotopy hp (H.comp (c : C(I × (Fin 1 → I), I × I)))
    (g₀.comp (e1 : C(Fin 1 → I, I))) fun y ↦ by simpa [c] using hg₀ (e1 y)
  refine ⟨G.comp (c.symm : C(I × I, I × (Fin 1 → I))), ?_, fun s ↦ ?_⟩
  · funext q
    have := congrFun hG (c.symm q)
    simpa using this
  · have := hG0 (e1.symm s)
    simpa [c] using this

/-- **Path lifting** for locally trivial maps. -/
theorem exists_path_lift (hp : IsLocallyTrivial p) (γ : C(I, B)) (e : E) (he : p e = γ 0) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e := by
  obtain ⟨G, hG, hG0⟩ := exists_lift_homotopy hp (k := 0) (γ.comp ⟨Prod.fst, continuous_fst⟩)
    (ContinuousMap.const _ e) fun _ ↦ he
  refine ⟨G.comp ⟨fun t ↦ (t, Fin.elim0), continuous_id.prodMk continuous_const⟩, ?_, ?_⟩
  · funext t
    exact congrFun hG (t, Fin.elim0)
  · exact hG0 Fin.elim0

end IsLocallyTrivial
