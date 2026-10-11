/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Hausdorff

/-!
# Point-pushing homeomorphisms

A space `X` *has local pushes* if every point `x` and every neighbourhood `U` of `x` admit a
neighbourhood `V` of `x` and a family of homeomorphisms `h v : X ≃ X` (`v ∈ V`), jointly
continuous in `(v, y)` together with their inverses, with `h v x = v` and `h v = id` outside `U`.

* `NormedSpace.hasLocalPushes`: complete real normed spaces have local pushes, via
  `y ↦ y + max 0 (1 - ‖y - x‖ / r) • (v - x)`, whose inverse is the fixed point of a contraction;
* `ChartedSpace.hasLocalPushes`: Hausdorff topological manifolds modelled on a
  finite-dimensional real normed space have local pushes (transport through a chart and extend
  by the identity);
* `HasLocalPushes.exists_multiPush`: pushes of finitely many distinct points simultaneously.

These are the local trivialisations of the Fadell–Neuwirth fibrations
(`Conf.isLocallyTrivial_forget`).
-/

open Set Function Topology Metric Filter

/-- `X` has local pushes: see the module docstring. -/
def HasLocalPushes (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, ∃ h h' : X → X → X,
    ContinuousOn (uncurry h) (V ×ˢ univ) ∧ ContinuousOn (uncurry h') (V ×ˢ univ) ∧
    (∀ v ∈ V, ∀ y, h v (h' v y) = y) ∧ (∀ v ∈ V, ∀ y, h' v (h v y) = y) ∧
    (∀ v ∈ V, h v x = v) ∧ (∀ v ∈ V, ∀ y ∉ U, h v y = y)

/-! ### Pushes in normed spaces -/

namespace Push

variable {E : Type*} [NormedAddCommGroup E]

/-- The bump function `max (1 - ‖y - x‖ / r) 0`. -/
noncomputable def bump (x : E) (r : ℝ) (y : E) : ℝ := max (1 - ‖y - x‖ / r) 0

theorem bump_nonneg (x : E) (r : ℝ) (y : E) : 0 ≤ bump x r y := le_max_right _ _

theorem bump_le_one {x : E} {r : ℝ} (hr : 0 < r) (y : E) : bump x r y ≤ 1 :=
  max_le (by linarith [div_nonneg (norm_nonneg (y - x)) hr.le]) zero_le_one

@[simp] theorem bump_self (x : E) (r : ℝ) : bump x r x = 1 := by simp [bump]

theorem bump_eq_zero {x : E} {r : ℝ} (hr : 0 < r) {y : E} (hy : r ≤ ‖y - x‖) :
    bump x r y = 0 :=
  max_eq_right (by rw [sub_nonpos, le_div_iff₀ hr]; linarith)

theorem abs_bump_sub_le {x : E} {r : ℝ} (hr : 0 < r) (y y' : E) :
    |bump x r y - bump x r y'| ≤ ‖y - y'‖ / r := by
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [show (1 - ‖y - x‖ / r) - (1 - ‖y' - x‖ / r) = (‖y' - x‖ - ‖y - x‖) / r by ring, abs_div,
    abs_of_pos hr]
  gcongr
  rw [abs_sub_comm]
  calc |‖y - x‖ - ‖y' - x‖| ≤ ‖(y - x) - (y' - x)‖ := abs_norm_sub_norm_le _ _
    _ = ‖y - y'‖ := by rw [sub_sub_sub_cancel_right]

theorem continuous_bump (x : E) (r : ℝ) : Continuous (bump x r) := by
  unfold bump; fun_prop

variable [NormedSpace ℝ E]

/-- The push of `x` to `v`, supported in the ball of radius `r` around `x`. -/
noncomputable def push (x : E) (r : ℝ) (v y : E) : E := y + bump x r y • (v - x)

@[simp] theorem push_self (x : E) (r : ℝ) (v : E) : push x r v x = v := by simp [push]

theorem push_of_le {x : E} {r : ℝ} (hr : 0 < r) (v : E) {y : E} (hy : r ≤ ‖y - x‖) :
    push x r v y = y := by
  simp [push, bump_eq_zero hr hy]

theorem continuous_push (x : E) (r : ℝ) : Continuous (uncurry (push x r)) := by
  have := continuous_bump x r
  unfold push; fun_prop

theorem push_mem_ball {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) {y : E}
    (hy : y ∈ ball x r) : push x r v y ∈ ball x r := by
  rw [mem_ball, dist_eq_norm] at hy ⊢
  have hb : bump x r y = 1 - ‖y - x‖ / r := max_eq_left (by
    rw [sub_nonneg, div_le_one hr]; exact hy.le)
  have hle : ‖y - x‖ / r ≤ 1 := by rw [div_le_one hr]; exact hy.le
  calc ‖push x r v y - x‖ = ‖(y - x) + bump x r y • (v - x)‖ := by
        rw [push]; congr 1; abel
    _ ≤ ‖y - x‖ + bump x r y * ‖v - x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg (bump_nonneg _ _ _)]
    _ ≤ ‖y - x‖ + (1 - ‖y - x‖ / r) * (r / 2) := by
        rw [hb]; gcongr
    _ = ‖y - x‖ / 2 + r / 2 := by field_simp; ring
    _ < r := by linarith

/-- The map whose fixed point is the inverse push of `y`. -/
noncomputable def pushT (x : E) (r : ℝ) (v y : E) (w : E) : E := y - bump x r w • (v - x)

theorem lipschitzWith_pushT {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2)
    (y : E) : LipschitzWith (1 / 2 : NNReal) (pushT x r v y) := by
  refine LipschitzWith.of_dist_le_mul fun w w' ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, pushT, pushT, sub_sub_sub_cancel_left, ← sub_smul, norm_smul,
    Real.norm_eq_abs, abs_sub_comm]
  calc |bump x r w - bump x r w'| * ‖v - x‖ ≤ ‖w - w'‖ / r * (r / 2) := by
        gcongr
        exact abs_bump_sub_le hr _ _
    _ = ((1 / 2 : NNReal) : ℝ) * ‖w - w'‖ := by push_cast; field_simp

theorem contractingWith_pushT {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2)
    (y : E) : ContractingWith (1 / 2 : NNReal) (pushT x r v y) :=
  ⟨by norm_num, lipschitzWith_pushT hr hv y⟩

variable [CompleteSpace E]

open Classical in
/-- The inverse of `push x r v` (for `‖v - x‖ ≤ r / 2`). -/
noncomputable def pushInv (x : E) (r : ℝ) (v y : E) : E :=
  if h : 0 < r ∧ ‖v - x‖ ≤ r / 2 then ContractingWith.fixedPoint _ (contractingWith_pushT h.1 h.2 y)
  else y

theorem pushInv_eq {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) (y : E) :
    pushInv x r v y = y - bump x r (pushInv x r v y) • (v - x) := by
  have h : 0 < r ∧ ‖v - x‖ ≤ r / 2 := ⟨hr, hv⟩
  simp only [pushInv, h, and_self, dite_true]
  exact ((contractingWith_pushT hr hv y).fixedPoint_isFixedPt).symm

theorem push_pushInv {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) (y : E) :
    push x r v (pushInv x r v y) = y := by
  have hw := pushInv_eq hr hv y
  set w := pushInv x r v y
  exact (congrArg (· + bump x r w • (v - x)) hw).trans (sub_add_cancel _ _)

theorem pushInv_push {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) (y : E) :
    pushInv x r v (push x r v y) = y := by
  have h : 0 < r ∧ ‖v - x‖ ≤ r / 2 := ⟨hr, hv⟩
  simp only [pushInv, h, and_self, dite_true]
  refine ((contractingWith_pushT hr hv _).fixedPoint_unique ?_).symm
  simp [IsFixedPt, pushT, push]

theorem pushInv_of_le {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) {y : E}
    (hy : r ≤ ‖y - x‖) : pushInv x r v y = y := by
  conv_lhs => rw [← push_of_le hr v hy]
  exact pushInv_push hr hv y

theorem pushInv_mem_ball {x : E} {r : ℝ} (hr : 0 < r) {v : E} (hv : ‖v - x‖ ≤ r / 2) {y : E}
    (hy : y ∈ ball x r) : pushInv x r v y ∈ ball x r := by
  have hw := pushInv_eq hr hv y
  set w := pushInv x r v y
  by_contra h
  rw [mem_ball, dist_eq_norm, not_lt] at h
  have : w = y := hw.trans (by rw [bump_eq_zero hr h, zero_smul, sub_zero])
  rw [this] at h
  rw [mem_ball, dist_eq_norm] at hy
  linarith

theorem norm_pushInv_sub_le {x : E} {r : ℝ} (hr : 0 < r) {v v' : E} (hv : ‖v - x‖ ≤ r / 2)
    (hv' : ‖v' - x‖ ≤ r / 2) (y y' : E) :
    ‖pushInv x r v y - pushInv x r v' y'‖ ≤ 2 * (‖y - y'‖ + ‖v - v'‖) := by
  have hw := pushInv_eq hr hv y
  have hw' := pushInv_eq hr hv' y'
  set w := pushInv x r v y
  set w' := pushInv x r v' y'
  have key : w - w' = (y - y') - ((bump x r w - bump x r w') • (v - x) +
      bump x r w' • (v - v')) := by
    calc w - w' = (y - bump x r w • (v - x)) - (y' - bump x r w' • (v' - x)) := by
          rw [← hw, ← hw']
      _ = _ := by simp only [sub_smul, smul_sub]; abel
  have h1 : ‖(bump x r w - bump x r w') • (v - x)‖ ≤ ‖w - w'‖ / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |bump x r w - bump x r w'| * ‖v - x‖ ≤ ‖w - w'‖ / r * (r / 2) := by
          gcongr; exact abs_bump_sub_le hr _ _
      _ = ‖w - w'‖ / 2 := by field_simp
  have h2 : ‖bump x r w' • (v - v')‖ ≤ ‖v - v'‖ := by
    rw [norm_smul, Real.norm_of_nonneg (bump_nonneg _ _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (bump_le_one hr _)
  have : ‖w - w'‖ ≤ ‖y - y'‖ + (‖w - w'‖ / 2 + ‖v - v'‖) := by
    calc ‖w - w'‖ = ‖(y - y') - ((bump x r w - bump x r w') • (v - x) +
          bump x r w' • (v - v'))‖ := by rw [key]
      _ ≤ ‖y - y'‖ + ‖(bump x r w - bump x r w') • (v - x) + bump x r w' • (v - v')‖ :=
          norm_sub_le _ _
      _ ≤ _ := by gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
  linarith

theorem continuousOn_pushInv {x : E} {r : ℝ} (hr : 0 < r) :
    ContinuousOn (uncurry (pushInv x r)) (closedBall x (r / 2) ×ˢ univ) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨v, y⟩ ⟨hv, -⟩ ε hε
  refine ⟨ε / 4, by positivity, ?_⟩
  rintro ⟨v', y'⟩ ⟨hv', -⟩ hd
  rw [mem_closedBall, dist_eq_norm] at hv hv'
  rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hd
  rw [dist_eq_norm]
  calc ‖pushInv x r v' y' - pushInv x r v y‖ ≤ 2 * (‖y' - y‖ + ‖v' - v‖) :=
        norm_pushInv_sub_le hr hv' hv y' y
    _ < ε := by linarith [hd.1, hd.2]

end Push

open Push in
/-- Complete real normed spaces have local pushes. -/
theorem NormedSpace.hasLocalPushes (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] : HasLocalPushes E := by
  intro x U hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hV : ∀ v ∈ ball x (r / 2), ‖v - x‖ ≤ r / 2 := fun v hv ↦ by
    rw [mem_ball, dist_eq_norm] at hv; exact hv.le
  refine ⟨ball x (r / 2), ball_mem_nhds x (by positivity), push x r, pushInv x r,
    (continuous_push x r).continuousOn, (continuousOn_pushInv hr).mono
      (prod_mono ball_subset_closedBall le_rfl), fun v hv y ↦ push_pushInv hr (hV v hv) y,
    fun v hv y ↦ pushInv_push hr (hV v hv) y, fun v _ ↦ push_self x r v, fun v _ y hy ↦ ?_⟩
  refine push_of_le hr v ?_
  by_contra h
  exact hy (hrU (by rw [mem_ball, dist_eq_norm]; exact lt_of_not_ge h))

/-! ### Pushes on manifolds -/

namespace Push

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
  {X : Type*} [TopologicalSpace X] [T2Space X]

open Classical in
/-- Transport a family `f` of self-maps of `E`, supported in `closedBall z ρ` and preserving
`ball z ρ`, through a partial homeomorphism `c : X → E` whose target contains `closedBall z ρ`,
extending by the identity: the result is continuous. -/
theorem continuousOn_transfer (c : OpenPartialHomeomorph X E) {z : E} {ρ : ℝ}
    (hρ : closedBall z ρ ⊆ c.target) {W : Set E} (f : E → E → E)
    (hf : ContinuousOn (uncurry f) (W ×ˢ univ)) (hfix : ∀ w ∈ W, ∀ y, ρ ≤ ‖y - z‖ → f w y = y)
    (hball : ∀ w ∈ W, ∀ y ∈ ball z ρ, f w y ∈ ball z ρ) {V : Set X} (hVo : IsOpen V)
    (hV : V ⊆ c.source ∩ c ⁻¹' W) :
    ContinuousOn (uncurry fun v q ↦ if q ∈ c.source then c.symm (f (c v) (c q)) else q)
      (V ×ˢ univ) := by
  classical
  set K := c.symm '' closedBall z ρ
  have hK : IsClosed K :=
    ((isCompact_closedBall z ρ).image_of_continuousOn (c.continuousOn_symm.mono hρ)).isClosed
  have htarget : ∀ w ∈ W, ∀ q ∈ c.source, f w (c q) ∈ c.target := fun w hw q hq ↦ by
    by_cases h : c q ∈ ball z ρ
    · exact hρ (ball_subset_closedBall (hball w hw _ h))
    · rw [mem_ball, dist_eq_norm, not_lt] at h
      rw [hfix w hw _ h]; exact c.map_source hq
  have hid : ∀ v ∈ V, ∀ q ∉ K, (if q ∈ c.source then c.symm (f (c v) (c q)) else q) = q := by
    intro v hv q hq
    split_ifs with hs
    · have : ρ ≤ ‖c q - z‖ := by
        by_contra h
        exact hq ⟨c q, by rw [mem_closedBall, dist_eq_norm]; linarith, c.left_inv hs⟩
      rw [hfix _ (hV hv).2 _ this, c.left_inv hs]
    · rfl
  refine continuousOn_of_forall_continuousAt fun ⟨v, q⟩ hvq ↦ ?_
  have hv : v ∈ V := hvq.1
  by_cases hq : q ∈ c.source
  · have hopen : IsOpen (V ×ˢ c.source) := hVo.prod c.open_source
    have hcont : ContinuousOn (fun p : X × X ↦ c.symm (f (c p.1) (c p.2))) (V ×ˢ c.source) := by
      refine c.continuousOn_symm.comp ?_ fun p hp ↦ htarget _ (hV hp.1).2 _ hp.2
      refine hf.comp (ContinuousOn.prodMk ?_ ?_) fun p hp ↦ ⟨(hV hp.1).2, mem_univ _⟩
      · exact c.continuousOn.comp continuous_fst.continuousOn fun p hp ↦ (hV hp.1).1
      · exact c.continuousOn.comp continuous_snd.continuousOn fun p hp ↦ hp.2
    refine (hcont.continuousAt (hopen.mem_nhds ⟨hv, hq⟩)).congr ?_
    filter_upwards [hopen.mem_nhds ⟨hv, hq⟩] with p hp
    change _ = if p.2 ∈ c.source then _ else _
    rw [if_pos hp.2]
  · have hqK : q ∉ K := fun h ↦ by
      obtain ⟨y, hy, rfl⟩ := h
      exact hq (c.map_target (hρ hy))
    have hopen : IsOpen (V ×ˢ Kᶜ) := hVo.prod hK.isOpen_compl
    refine continuous_snd.continuousAt.congr ?_
    filter_upwards [hopen.mem_nhds ⟨hv, hqK⟩] with p hp
    exact (hid p.1 hp.1 p.2 hp.2).symm

end Push

open Push in
/-- Hausdorff topological manifolds modelled on a finite-dimensional real normed space have local
pushes. -/
theorem ChartedSpace.hasLocalPushes (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace E X] :
    HasLocalPushes X := by
  classical
  intro x U hU
  set c := chartAt E x
  have hxs : x ∈ c.source := mem_chart_source E x
  have hN : c.target ∩ c.symm ⁻¹' (U ∩ c.source) ∈ 𝓝 (c x) := by
    refine inter_mem (c.open_target.mem_nhds (c.map_source hxs)) ?_
    refine (c.continuousAt_symm (c.map_source hxs)).preimage_mem_nhds ?_
    rw [c.left_inv hxs]
    exact inter_mem hU (c.open_source.mem_nhds hxs)
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  set ρ := r / 2
  have hρ : 0 < ρ := by positivity
  have hρN : closedBall (c x) ρ ⊆ c.target ∩ c.symm ⁻¹' (U ∩ c.source) :=
    (closedBall_subset_ball (by simp only [ρ]; linarith)).trans hrN
  set V := c.source ∩ c ⁻¹' ball (c x) (ρ / 2)
  have hVo : IsOpen V := c.isOpen_inter_preimage isOpen_ball
  have hVW : V ⊆ c.source ∩ c ⁻¹' closedBall (c x) (ρ / 2) :=
    fun v hv ↦ ⟨hv.1, ball_subset_closedBall hv.2⟩
  have hvle : ∀ v ∈ V, ‖c v - c x‖ ≤ ρ / 2 := fun v hv ↦ by
    have := hv.2; rw [mem_preimage, mem_ball, dist_eq_norm] at this; exact this.le
  let H : X → X → X := fun v q ↦ if q ∈ c.source then c.symm (push (c x) ρ (c v) (c q)) else q
  let H' : X → X → X := fun v q ↦
    if q ∈ c.source then c.symm (pushInv (c x) ρ (c v) (c q)) else q
  have hpush_t : ∀ v ∈ V, ∀ q ∈ c.source, push (c x) ρ (c v) (c q) ∈ c.target := by
    intro v hv q hq
    by_cases h : c q ∈ ball (c x) ρ
    · exact (hρN (ball_subset_closedBall (push_mem_ball hρ (hvle v hv) h))).1
    · rw [mem_ball, dist_eq_norm, not_lt] at h
      rw [push_of_le hρ _ h]; exact c.map_source hq
  have hpushInv_t : ∀ v ∈ V, ∀ q ∈ c.source, pushInv (c x) ρ (c v) (c q) ∈ c.target := by
    intro v hv q hq
    by_cases h : c q ∈ ball (c x) ρ
    · exact (hρN (ball_subset_closedBall (pushInv_mem_ball hρ (hvle v hv) h))).1
    · rw [mem_ball, dist_eq_norm, not_lt] at h
      rw [pushInv_of_le hρ (hvle v hv) h]; exact c.map_source hq
  refine ⟨V, hVo.mem_nhds ⟨hxs, by simp [hρ]⟩, H, H', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_transfer c (hρN.trans inter_subset_left) _
      (continuous_push (c x) ρ).continuousOn (fun _ _ _ h ↦ push_of_le hρ _ h)
      (fun w hw _ hy ↦ push_mem_ball hρ (by
        rw [mem_closedBall, dist_eq_norm] at hw; exact hw) hy) hVo hVW
  · exact continuousOn_transfer c (hρN.trans inter_subset_left) _
      (continuousOn_pushInv hρ) (fun w hw _ h ↦ pushInv_of_le hρ (by
        rw [mem_closedBall, dist_eq_norm] at hw; exact hw) h)
      (fun w hw _ hy ↦ pushInv_mem_ball hρ (by
        rw [mem_closedBall, dist_eq_norm] at hw; exact hw) hy) hVo hVW
  · intro v hv q
    by_cases hq : q ∈ c.source
    · have hm := hpushInv_t v hv q hq
      simp only [H, H', hq, if_true, c.map_target hm, c.right_inv hm, push_pushInv hρ (hvle v hv),
        c.left_inv hq]
    · simp [H, H', hq]
  · intro v hv q
    by_cases hq : q ∈ c.source
    · have hm := hpush_t v hv q hq
      simp only [H, H', hq, if_true, c.map_target hm, c.right_inv hm, pushInv_push hρ (hvle v hv),
        c.left_inv hq]
    · simp [H, H', hq]
  · intro v hv
    simp only [H, hxs, if_true, push_self, c.left_inv hv.1]
  · intro v hv q hq
    simp only [H]
    split_ifs with hs
    · have : ρ ≤ ‖c q - c x‖ := by
        by_contra h
        have := (hρN (by rw [mem_closedBall, dist_eq_norm]; linarith : c q ∈ _)).2.1
        rw [c.left_inv hs] at this
        exact hq this
      rw [push_of_le hρ _ this, c.left_inv hs]
    · rfl

/-! ### Pushing finitely many points -/

namespace HasLocalPushes

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **Multi-point pushes.** Given distinct points `y₀, …, yₙ₋₁` inside an open set `O`, there is a
neighbourhood `W` of `y` in `Xⁿ` and a jointly continuous family of homeomorphisms `Φ z`
(`z ∈ W`), with jointly continuous inverses `Ψ z`, supported in `O`, such that `Φ z yᵢ = zᵢ`. -/
theorem exists_multiPush (hX : HasLocalPushes X) : ∀ (n : ℕ) (y : Fin n → X), Injective y →
    ∀ O : Set X, IsOpen O → (∀ i, y i ∈ O) → ∃ W ∈ 𝓝 y, ∃ Φ Ψ : (Fin n → X) → X → X,
      ContinuousOn (uncurry Φ) (W ×ˢ univ) ∧ ContinuousOn (uncurry Ψ) (W ×ˢ univ) ∧
      (∀ z ∈ W, ∀ q, Φ z (Ψ z q) = q) ∧ (∀ z ∈ W, ∀ q, Ψ z (Φ z q) = q) ∧
      (∀ z ∈ W, ∀ i, Φ z (y i) = z i) ∧ (∀ z ∈ W, ∀ q ∉ O, Φ z q = q) := by
  intro n
  induction n with
  | zero =>
    intro y _ O _ _
    exact ⟨univ, univ_mem, fun _ q ↦ q, fun _ q ↦ q, continuous_snd.continuousOn,
      continuous_snd.continuousOn, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ i ↦ i.elim0,
      fun _ _ _ _ ↦ rfl⟩
  | succ n ih =>
    intro y hy O hO hyO
    set y' : Fin n → X := Fin.tail y
    have hy' : Injective y' := hy.comp (Fin.succ_injective n)
    have hy0 : y 0 ∉ range y' := by
      rintro ⟨i, hi⟩
      exact Fin.succ_ne_zero i (hy hi)
    obtain ⟨U₀, U', hU₀, hU', h0U, hU'S, hdisj⟩ :=
      SeparatedNhds.of_isCompact_isCompact (isCompact_singleton (x := y 0))
        (finite_range y').isCompact (disjoint_singleton_left.2 hy0)
    obtain ⟨W', hW', Φ', Ψ', hΦ'c, hΨ'c, hΦΨ', hΨΦ', hΦy', hΦO'⟩ :=
      ih y' hy' (O ∩ U') (hO.inter hU') fun i ↦ ⟨hyO _, hU'S (mem_range_self i)⟩
    obtain ⟨V, hV, h, h', hhc, hh'c, hhh', hh'h, hhx, hhU⟩ :=
      hX (y 0) (O ∩ U₀) (inter_mem (hO.mem_nhds (hyO 0)) (hU₀.mem_nhds (h0U rfl)))
    have hU'n : {w : Fin n → X | ∀ i, w i ∈ U'} ∈ 𝓝 y' := by
      have := (isOpen_set_pi finite_univ fun _ _ ↦ hU').mem_nhds
        fun i (_ : i ∈ univ) ↦ hU'S (mem_range_self (f := y') i)
      simpa [Set.pi] using this
    have htail : Continuous (Fin.tail : (Fin (n + 1) → X) → Fin n → X) :=
      continuous_pi fun i ↦ continuous_apply _
    let W : Set (Fin (n + 1) → X) :=
      (fun z ↦ z 0) ⁻¹' V ∩ Fin.tail ⁻¹' (W' ∩ {w | ∀ i, w i ∈ U'})
    have hW : W ∈ 𝓝 y := inter_mem ((continuous_apply 0).continuousAt.preimage_mem_nhds hV)
      (htail.continuousAt.preimage_mem_nhds (inter_mem hW' hU'n))
    refine ⟨W, hW, fun z q ↦ h (z 0) (Φ' (Fin.tail z) q),
      fun z q ↦ Ψ' (Fin.tail z) (h' (z 0) q), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hin : ContinuousOn (fun p : (Fin (n + 1) → X) × X ↦
          (p.1 0, uncurry Φ' (Fin.tail p.1, p.2))) (W ×ˢ univ) := by
        refine ContinuousOn.prodMk ((continuous_apply 0).comp continuous_fst).continuousOn ?_
        exact hΦ'c.comp (htail.comp continuous_fst |>.prodMk continuous_snd).continuousOn
          fun p hp ↦ ⟨hp.1.2.1, mem_univ _⟩
      exact hhc.comp hin fun p hp ↦ ⟨hp.1.1, mem_univ _⟩
    · have hin : ContinuousOn (fun p : (Fin (n + 1) → X) × X ↦
          (Fin.tail p.1, uncurry h' (p.1 0, p.2))) (W ×ˢ univ) := by
        refine ContinuousOn.prodMk (htail.comp continuous_fst).continuousOn ?_
        exact hh'c.comp (((continuous_apply 0).comp continuous_fst).prodMk
          continuous_snd).continuousOn fun p hp ↦ ⟨hp.1.1, mem_univ _⟩
      exact hΨ'c.comp hin fun p hp ↦ ⟨hp.1.2.1, mem_univ _⟩
    · intro z hz q
      simp only [hΦΨ' _ hz.2.1, hhh' _ hz.1]
    · intro z hz q
      simp only [hh'h _ hz.1, hΨΦ' _ hz.2.1]
    · intro z hz i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · have : Φ' (Fin.tail z) (y 0) = y 0 :=
          hΦO' _ hz.2.1 _ fun h ↦ hdisj.le_bot ⟨h0U rfl, h.2⟩
        simp only [this, hhx _ hz.1]
      · have h1 : Φ' (Fin.tail z) (y i.succ) = z i.succ := hΦy' _ hz.2.1 i
        simp only [h1]
        exact hhU _ hz.1 _ fun h ↦ hdisj.le_bot ⟨h.2, hz.2.2 i⟩
    · intro z hz q hq
      simp only [hΦO' _ hz.2.1 q fun h ↦ hq h.1]
      exact hhU _ hz.1 _ fun h ↦ hq h.1

end HasLocalPushes
