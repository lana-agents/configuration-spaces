/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Punctured manifolds are connected

For a connected Hausdorff topological manifold `X` modelled on a real normed space `E` of
dimension `> 1` (e.g. a connected surface or a connected Riemann surface), the complement of a
finite set is path-connected (`ChartedSpace.isPathConnected_compl_of_finite`).

The proof removes one point at a time, using `IsPreconnected.diff_singleton`: removing a point `s`
from a preconnected set `T` keeps it preconnected as soon as `s` has an open neighbourhood
`U ⊆ T` with `U ∖ {s}` preconnected; in a manifold, `U` is a chart ball.
-/

open Set Function Topology Metric

variable {X : Type*} [TopologicalSpace X]

/-- Removing a point `s` from a preconnected set `T` keeps it preconnected if `s` has an open
neighbourhood `U ⊆ T` such that `U ∖ {s}` is preconnected. -/
theorem IsPreconnected.diff_singleton [T1Space X] {T U : Set X} {s : X} (hT : IsPreconnected T)
    (hsT : s ∈ T) (hU : IsOpen U) (hsU : s ∈ U) (hUT : U ⊆ T) (hC : IsPreconnected (U \ {s})) :
    IsPreconnected (T \ {s}) := by
  rw [isPreconnected_iff_subset_of_disjoint] at hT hC ⊢
  have key : ∀ u v, IsOpen u → IsOpen v → T \ {s} ⊆ u ∪ v → T \ {s} ∩ (u ∩ v) = ∅ →
      U \ {s} ⊆ u → T \ {s} ⊆ u := by
    intro u v hu hv hcov hdisj hCu
    have h := hT (u ∪ U) (v ∩ {s}ᶜ) (hu.union hU) (hv.inter isOpen_compl_singleton) ?_ ?_
    · rcases h with h | h
      · intro z hz
        rcases h hz.1 with h' | h'
        · exact h'
        · exact hCu ⟨h', hz.2⟩
      · exact absurd rfl (h hsT).2
    · intro z hz
      by_cases hzs : z = s
      · exact Or.inl (Or.inr (hzs ▸ hsU))
      · rcases hcov ⟨hz, hzs⟩ with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr ⟨h', hzs⟩
    · rw [eq_empty_iff_forall_notMem]
      rintro z ⟨hzT, hzu, hzv, hzs⟩
      have hz' : z ∈ T \ {s} := ⟨hzT, hzs⟩
      rcases hzu with hzu | hzU
      · exact (hdisj ▸ (⟨hz', hzu, hzv⟩ : z ∈ T \ {s} ∩ (u ∩ v)) : z ∈ (∅ : Set X))
      · exact (hdisj ▸ (⟨hz', hCu ⟨hzU, hzs⟩, hzv⟩ : z ∈ T \ {s} ∩ (u ∩ v)) : z ∈ (∅ : Set X))
  intro u v hu hv hcov hdisj
  have hCT : U \ {s} ⊆ T \ {s} := sdiff_subset_sdiff_left hUT
  rcases hC u v hu hv (hCT.trans hcov) (subset_empty_iff.1 (hdisj ▸ inter_subset_inter_left _ hCT))
    with h | h
  · exact Or.inl (key u v hu hv hcov hdisj h)
  · refine Or.inr (key v u hv hu (by rwa [union_comm]) (by rwa [inter_comm v u]) h)

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of dimension `> 1`, a punctured ball is path-connected. -/
theorem isPathConnected_ball_diff_center (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball c r \ {c}) := by
  set φ := OpenPartialHomeomorph.univBall c r
  have himg : φ '' {0}ᶜ = ball c r \ {c} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, fun h ↦ hw ?_⟩
      · rw [← OpenPartialHomeomorph.univBall_target c hr]
        exact φ.map_source (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
      · refine φ.injOn (by simp [φ, OpenPartialHomeomorph.univBall_source])
          (by simp [φ, OpenPartialHomeomorph.univBall_source]) ?_
        rw [h, OpenPartialHomeomorph.univBall_apply_zero]
    · rintro ⟨hz, hzc⟩
      rw [← OpenPartialHomeomorph.univBall_target c hr] at hz
      refine ⟨φ.symm z, fun h ↦ hzc ?_, φ.right_inv hz⟩
      rw [← φ.right_inv hz, mem_singleton_iff.1 h, OpenPartialHomeomorph.univBall_apply_zero]
      rfl
  rw [← himg]
  exact (isPathConnected_compl_singleton_of_one_lt_rank hE 0).image'
    (φ.continuousOn.mono (by simp [φ, OpenPartialHomeomorph.univBall_source]))

variable [ChartedSpace E X]

/-- In a manifold of dimension `> 1`, every neighbourhood of a point `s` contains an open
neighbourhood `U` with `U ∖ {s}` connected. -/
theorem ChartedSpace.exists_isOpen_isConnected_diff (hE : 1 < Module.rank ℝ E) (s : X)
    {N : Set X} (hN : N ∈ 𝓝 s) :
    ∃ U, IsOpen U ∧ s ∈ U ∧ U ⊆ N ∧ IsConnected (U \ {s}) := by
  set c := chartAt E s
  have hss : s ∈ c.source := mem_chart_source E s
  have hN' : c.target ∩ c.symm ⁻¹' (N ∩ c.source) ∈ 𝓝 (c s) := by
    refine Filter.inter_mem (c.open_target.mem_nhds (c.map_source hss)) ?_
    refine (c.continuousAt_symm (c.map_source hss)).preimage_mem_nhds ?_
    rw [c.left_inv hss]
    exact Filter.inter_mem hN (c.open_source.mem_nhds hss)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN'
  refine ⟨c.source ∩ c ⁻¹' ball (c s) r, c.isOpen_inter_preimage isOpen_ball,
    ⟨hss, mem_ball_self hr⟩, fun q hq ↦ ?_, ?_⟩
  · have := (hrN hq.2).2.1
    rwa [c.left_inv hq.1] at this
  · have himg : c.symm '' (ball (c s) r \ {c s}) = (c.source ∩ c ⁻¹' ball (c s) r) \ {s} := by
      ext q
      constructor
      · rintro ⟨z, ⟨hz, hzs⟩, rfl⟩
        have hzt : z ∈ c.target := (hrN hz).1
        refine ⟨⟨c.map_target hzt, by rw [mem_preimage, c.right_inv hzt]; exact hz⟩, fun h ↦ hzs ?_⟩
        rw [← c.right_inv hzt, mem_singleton_iff.1 h]
        rfl
      · rintro ⟨⟨hq, hqb⟩, hqs⟩
        refine ⟨c q, ⟨hqb, fun h ↦ hqs ?_⟩, c.left_inv hq⟩
        exact c.injOn hq hss (mem_singleton_iff.1 h)
    rw [← himg]
    exact ((isPathConnected_ball_diff_center hE (c s) hr).image'
      (c.continuousOn_symm.mono fun z hz ↦ (hrN hz.1).1)).isConnected

variable [T2Space X] [ConnectedSpace X]

/-- In a connected Hausdorff manifold of dimension `> 1`, the complement of a finite set is
connected. -/
theorem ChartedSpace.isConnected_compl_of_finite (hE : 1 < Module.rank ℝ E) {S : Set X}
    (hS : S.Finite) : IsConnected Sᶜ := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using isConnected_univ
  | @insert a S haS hS ih =>
    have hSo : IsOpen Sᶜ := hS.isClosed.isOpen_compl
    obtain ⟨U, hU, haU, hUS, hUc⟩ :=
      ChartedSpace.exists_isOpen_isConnected_diff hE a (hSo.mem_nhds haS)
    have : (insert a S)ᶜ = Sᶜ \ {a} := by ext; simp [and_comm]
    rw [this]
    exact ⟨hUc.nonempty.mono (sdiff_subset_sdiff_left hUS),
      ih.isPreconnected.diff_singleton haS hU haU hUS hUc.isPreconnected⟩

/-- In a connected Hausdorff manifold of dimension `> 1`, the complement of a finite set is
path-connected. -/
theorem ChartedSpace.isPathConnected_compl_of_finite (hE : 1 < Module.rank ℝ E) {S : Set X}
    (hS : S.Finite) : IsPathConnected Sᶜ := by
  haveI := ChartedSpace.locallyPathConnectedSpace E X
  exact (hS.isClosed.isOpen_compl.isConnected_iff_isPathConnected).1
    (ChartedSpace.isConnected_compl_of_finite hE hS)

end Manifold
