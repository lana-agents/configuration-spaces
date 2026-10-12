/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import ConfigurationSpaces.AlgebraicGeometry.Basic

/-!
# Fibres of the forgetful morphism `Conf_{n+1}(X) ⟶ Conf_n(X)`

Let `X` be a separated `S`-scheme and `z : Spec K ⟶ Conf_n(X)` a point with values in a field
`K`, with coordinates `z₀, …, zₙ₋₁ : Spec K ⟶ X`. Write `Q = (Conf_n(X) ×_S X) ×_{Conf_n(X)} Spec K`
(`ConfScheme.fiberBase z`); it is the base change `X_K = X ×_S Spec K`
(`ConfScheme.isPullback_fiberBase`), and the `zᵢ` give sections `ConfScheme.fiberSection z i` of
`Q ⟶ Spec K`.

* `ConfScheme.fiberOpens z`: the open subscheme of `Q` complementary to the images of the
  sections, `compl_fiberOpens : (fiberOpens z)ᶜ = ⋃ i, range (fiberSection z i)`, i.e.
  `X_K ∖ {z₀, …, zₙ₋₁}`;
* `ConfScheme.fiberIso z`: the scheme-theoretic fibre `Conf_{n+1}(X) ×_{Conf_n(X)} Spec K` of
  `forget` over `z` is isomorphic to this open subscheme.

Consequently, if `X ⟶ S` is geometrically irreducible with infinite geometric fibres (e.g. a
geometrically irreducible curve over a field), every fibre of `forget` over a field-valued point
is a non-empty open subscheme of an irreducible scheme, hence irreducible:

* `ConfScheme.geometricallyIrreducible_forget`, `ConfScheme.geometricallyConnected_forget`;
* `ConfScheme.universallyOpen_forget`: `forget` is universally open if `X ⟶ S` is (it is the
  restriction of the projection `Conf_n(X) ×_S X ⟶ Conf_n(X)` to an open subscheme);
* `ConfScheme.connectedSpace_succ`: if `Conf_n(X)` is connected, so is `Conf_{n+1}(X)`.

The results above are stated under the hypothesis `[UniversallyOpen X.hom]`, which Mathlib
discharges automatically in the cases of interest:

* `AlgebraicGeometry.UniversallyOpen.of_flat` (EGA IV 2.4.6, Stacks 01UA): flat morphisms locally
  of finite presentation are universally open;
* the instance for morphisms to an integral one-point scheme (EGA IV 2.4.10): every scheme over a
  field `k` is universally open over `Spec k` (no finiteness needed).

Accordingly `ConfScheme.connectedSpace_of_field` and `ConfScheme.connectedSpace_of_flat` carry no
universal openness hypothesis.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace ConfScheme

/-- Binary products in `Over S` are pullbacks of schemes. -/
theorem isPullback_prod {S : Scheme.{u}} (A B : Over S) :
    IsPullback (prod.fst : A ⨯ B ⟶ A).left (prod.snd : A ⨯ B ⟶ B).left A.hom B.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd) (prodIsProd A B)

variable {S : Scheme.{u}} (X : Over S) [IsSeparated X.hom] (n : ℕ)

/-- `forget` is the restriction of the first projection `Conf_n(X) ×_S X ⟶ Conf_n(X)`. -/
theorem forget_left :
    (forget X n).left = (toProd X n).left ≫ (prod.fst : ConfScheme X n ⨯ X ⟶ _).left := by
  rw [← Over.comp_left, toProd, prod.lift_fst]

/-- `forget` is universally open if `X ⟶ S` is. -/
theorem universallyOpen_forget [UniversallyOpen X.hom] : UniversallyOpen (forget X n).left := by
  have : UniversallyOpen (prod.fst : ConfScheme X n ⨯ X ⟶ _).left :=
    MorphismProperty.of_isPullback (isPullback_prod _ _).flip ‹_›
  rw [forget_left]
  infer_instance

section Fiber

variable {X n} {K : Type u} [Field K] (z : Spec (.of K) ⟶ (ConfScheme X n).left)

/-- The base change `Q = (Conf_n(X) ×_S X) ×_{Conf_n(X)} Spec K` of `X` to the point `z`. -/
noncomputable abbrev fiberBase : Scheme.{u} :=
  pullback (prod.fst : ConfScheme X n ⨯ X ⟶ _).left z

/-- The map `Q ⟶ Conf_n(X) ×_S X`. -/
noncomputable abbrev fiberBaseι : fiberBase z ⟶ (ConfScheme X n ⨯ X).left := pullback.fst _ _

/-- `Q` is the base change `X ×_S Spec K` of `X` along `Spec K ⟶ Conf_n(X) ⟶ S`. -/
theorem isPullback_fiberBase :
    IsPullback (fiberBaseι z ≫ (prod.snd : ConfScheme X n ⨯ X ⟶ X).left) (pullback.snd _ _)
      X.hom (z ≫ (ConfScheme X n).hom) :=
  (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_prod _ _).flip

/-- The `i`-th tautological section `Spec K ⟶ Q`, given by the coordinate `zᵢ`. -/
noncomputable def fiberSection (i : Fin n) : Spec (.of K) ⟶ fiberBase z :=
  pullback.lift ((isPullback_prod (ConfScheme X n) X).lift z (z ≫ (ι X n ≫ proj X n i).left)
    (by rw [Category.assoc, Over.w])) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
theorem fiberSection_snd (i : Fin n) : fiberSection z i ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem fiberSection_ι_fst (i : Fin n) :
    fiberSection z i ≫ fiberBaseι z ≫ (prod.fst : ConfScheme X n ⨯ X ⟶ _).left = z := by
  rw [fiberSection, pullback.lift_fst_assoc, IsPullback.lift_fst]

@[reassoc (attr := simp)]
theorem fiberSection_ι_snd (i : Fin n) :
    fiberSection z i ≫ fiberBaseι z ≫ (prod.snd : ConfScheme X n ⨯ X ⟶ X).left =
      z ≫ (ι X n ≫ proj X n i).left := by
  rw [fiberSection, pullback.lift_fst_assoc, IsPullback.lift_snd]

/-- The map `Conf_n(X) ×_S X ⟶ X ×_S X`, `(w, p) ↦ (wᵢ, p)`; the preimage of the diagonal is the
graph of the `i`-th tautological section. -/
noncomputable abbrev graphMap (i : Fin n) : ConfScheme X n ⨯ X ⟶ X ⨯ X :=
  prod.lift (prod.fst ≫ ι X n ≫ proj X n i) prod.snd

theorem graphMap_fst (i : Fin n) :
    (graphMap (X := X) i).left ≫ (prod.fst : X ⨯ X ⟶ X).left =
      (prod.fst : ConfScheme X n ⨯ X ⟶ _).left ≫ (ι X n ≫ proj X n i).left := by
  rw [← Over.comp_left, prod.lift_fst, Over.comp_left]

theorem graphMap_snd (i : Fin n) :
    (graphMap (X := X) i).left ≫ (prod.snd : X ⨯ X ⟶ X).left =
      (prod.snd : ConfScheme X n ⨯ X ⟶ _).left := by
  rw [← Over.comp_left, prod.lift_snd]

omit [IsSeparated X.hom] in
theorem diag_left_fst : (diag X).left ≫ (prod.fst : X ⨯ X ⟶ X).left = 𝟙 _ := by
  rw [← Over.comp_left, diag, prod.lift_fst, Over.id_left]

omit [IsSeparated X.hom] in
theorem diag_left_snd : (diag X).left ≫ (prod.snd : X ⨯ X ⟶ X).left = 𝟙 _ := by
  rw [← Over.comp_left, diag, prod.lift_snd, Over.id_left]

/-- The sections land in the graphs. -/
theorem fiberSection_graphMap (i : Fin n) :
    fiberSection z i ≫ fiberBaseι z ≫ (graphMap i).left =
      (z ≫ (ι X n ≫ proj X n i).left) ≫ (diag X).left := by
  apply (isPullback_prod X X).hom_ext
  · rw [Category.assoc, Category.assoc, graphMap_fst, Category.assoc, diag_left_fst,
      Category.comp_id, pullback.condition_assoc, fiberSection_snd_assoc]
  · rw [Category.assoc, Category.assoc, graphMap_snd, Category.assoc, diag_left_snd,
      Category.comp_id, fiberSection_ι_snd]

/-- A point of `Q` whose image in `Conf_n(X) ×_S X` lies on the graph of the `i`-th
tautological section is the image of the `i`-th section. -/
theorem mem_range_fiberSection {i : Fin n} {q : fiberBase z}
    (hq : (graphMap i).left (fiberBaseι z q) ∈ Set.range (diag X).left) :
    q ∈ Set.range (fiberSection z i) := by
  set a := fiberBaseι z ≫ (graphMap i).left
  have hq' : q ∈ Set.range (pullback.fst a (diag X).left) := by
    rw [Scheme.Pullback.range_fst]
    simpa [a] using hq
  obtain ⟨w, rfl⟩ := hq'
  have key : pullback.fst a (diag X).left =
      (pullback.fst a (diag X).left ≫ pullback.snd _ z) ≫ fiberSection z i := by
    have h₁ := congrArg (· ≫ (prod.fst : X ⨯ X ⟶ X).left) (pullback.condition (f := a)
      (g := (diag X).left))
    have h₂ := congrArg (· ≫ (prod.snd : X ⨯ X ⟶ X).left) (pullback.condition (f := a)
      (g := (diag X).left))
    simp only [a, Category.assoc, graphMap_fst, graphMap_snd, diag_left_fst, diag_left_snd,
      Category.comp_id] at h₁ h₂
    apply pullback.hom_ext
    · apply (isPullback_prod (ConfScheme X n) X).hom_ext
      · simp only [Category.assoc, fiberSection_ι_fst]
        rw [pullback.condition]
      · rw [Category.assoc, Category.assoc, Category.assoc, fiberSection_ι_snd, h₂,
          ← h₁, pullback.condition_assoc, Category.assoc]
    · rw [Category.assoc, Category.assoc, fiberSection_snd, Category.comp_id]
  refine ⟨(pullback.fst a (diag X).left ≫ pullback.snd _ z) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← key]

/-- The open subscheme `X_K ∖ {z₀, …, zₙ₋₁}` of `Q`: the preimage of `Conf_{n+1}(X)`. -/
noncomputable def fiberOpens : (fiberBase z).Opens :=
  fiberBaseι z ⁻¹ᵁ (toProd X n).left.opensRange

/-- **The fibre of `forget` over `z`, set-theoretically**: the complement of `fiberOpens z` is the
union of the images of the `n` tautological sections. -/
theorem compl_fiberOpens :
    (fiberOpens z : Set (fiberBase z))ᶜ = ⋃ i, Set.range (fiberSection z i) := by
  ext q
  simp only [Set.mem_compl_iff, Set.mem_iUnion]
  change fiberBaseι z q ∉ Set.range (toProd X n).left ↔ _
  rw [range_toProd]
  simp only [Set.mem_setOf_eq, not_forall, not_not]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, mem_range_fiberSection z hi⟩
  · rintro ⟨i, t, rfl⟩
    refine ⟨i, (z ≫ (ι X n ≫ proj X n i).left) t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← fiberSection_graphMap, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]

/-- **The scheme-theoretic fibre of `forget` over `z`** is the open subscheme
`X_K ∖ {z₀, …, zₙ₋₁}` of `X_K`. -/
noncomputable def fiberIso : pullback (forget X n).left z ≅ (fiberOpens z).toScheme :=
  pullback.congrHom (forget_left X n) rfl ≪≫
    (pullbackRightPullbackFstIso _ z (toProd X n).left).symm ≪≫
    IsOpenImmersion.isoOfRangeEq (pullback.snd (toProd X n).left (fiberBaseι z))
      (fiberOpens z).ι (by
        rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
        rfl)

variable {z} in
/-- If `X_K` is irreducible and infinite, the fibre of `forget` over `z` is irreducible. -/
theorem irreducibleSpace_fiber [IrreducibleSpace (fiberBase z)] [Infinite (fiberBase z)] :
    IrreducibleSpace ↥(pullback (forget X n).left z : Scheme.{u}) := by
  have hne : (fiberOpens z : Set (fiberBase z)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : Finite (Spec (.of K)) := Finite.of_subsingleton
    have hfin : (⋃ i, Set.range (fiberSection z i)).Finite :=
      Set.finite_iUnion fun i ↦ Set.finite_range _
    rw [← compl_fiberOpens, h, Set.compl_empty] at hfin
    exact Set.infinite_univ hfin
  haveI : Nonempty (fiberOpens z).toScheme := ⟨⟨hne.some, hne.some_mem⟩⟩
  haveI : IrreducibleSpace (fiberOpens z).toScheme :=
    (fiberOpens z).ι.isOpenEmbedding.irreducibleSpace
  exact (fiberIso z).hom.homeomorph.irreducibleSpace_iff.mpr this

end Fiber

/-- The hypothesis on `X`: its geometric fibres over `S` are irreducible and infinite (e.g. `X` a
geometrically irreducible curve over a field `S = Spec k`). -/
abbrev GeomIrreducibleInfinite : ObjectProperty Scheme.{u} :=
  fun Y ↦ IrreducibleSpace Y ∧ Infinite Y

variable {X} in
/-- **The fibres of `forget` are geometrically irreducible**: if the geometric fibres of
`X ⟶ S` are irreducible and infinite, then every fibre of `Conf_{n+1}(X) ⟶ Conf_n(X)` over a
field-valued point (an open subscheme `X_K ∖ {z₀, …, zₙ₋₁}`) is irreducible. -/
theorem geometricallyIrreducible_forget
    (hX : geometrically GeomIrreducibleInfinite X.hom) :
    GeometricallyIrreducible (forget X n).left := by
  refine ⟨fun K _ z Z fst snd h ↦ ?_⟩
  obtain ⟨_, _⟩ := hX _ _ _ (isPullback_fiberBase z)
  exact h.isoPullback.hom.homeomorph.irreducibleSpace_iff.mpr (irreducibleSpace_fiber (z := z))

variable {X} in
/-- The fibres of `forget` are geometrically connected. -/
theorem geometricallyConnected_forget (hX : geometrically GeomIrreducibleInfinite X.hom) :
    GeometricallyConnected (forget X n).left := by
  refine ⟨fun K _ z Z fst snd h ↦ ?_⟩
  haveI := (geometricallyIrreducible_forget n hX).geometrically_irreducibleSpace _ _ _ h
  infer_instance

variable {X} in
/-- If `X ⟶ S` is universally open with irreducible infinite geometric fibres and `Conf_n(X)` is
connected, then so is `Conf_{n+1}(X)`. -/
theorem connectedSpace_succ [UniversallyOpen X.hom]
    (hX : geometrically GeomIrreducibleInfinite X.hom) [ConnectedSpace (ConfScheme X n).left] :
    ConnectedSpace (ConfScheme X (n + 1)).left := by
  haveI := geometricallyConnected_forget n hX
  haveI := universallyOpen_forget X n
  exact GeometricallyConnected.connectedSpace (forget X n).left (forget X n).left.isOpenMap

omit [IsSeparated X.hom] in
/-- The empty fibre power `X⁰` is `S`. -/
theorem isIso_power_zero_hom : IsIso (power X 0).hom := by
  let u : Over.mk (𝟙 S) ⟶ power X 0 := Pi.lift fun i ↦ i.elim0
  refine ⟨⟨u.left, ?_, Over.w u⟩⟩
  have : Over.homMk (power X 0).hom ≫ u = 𝟙 _ := Pi.hom_ext _ _ fun i ↦ i.elim0
  exact congrArg CommaMorphism.left this

/-- `Conf_0(X) = S`. -/
theorem isIso_confScheme_zero_hom : IsIso (ConfScheme X 0).hom := by
  haveI := isIso_power_zero_hom X
  haveI : IsIso (opens X 0).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun p ↦ ?_⟩⟩
    have : p ∈ Set.range (opens X 0).ι := by
      rw [Scheme.Opens.range_ι]
      exact fun i ↦ i.elim0
    exact this
  change IsIso ((opens X 0).ι ≫ (power X 0).hom)
  infer_instance

variable {X} in
/-- If `S` is connected, `X ⟶ S` is universally open and its geometric fibres are irreducible and
infinite, then all configuration schemes `Conf_n(X)` are connected. -/
theorem connectedSpace [ConnectedSpace S] [UniversallyOpen X.hom]
    (hX : geometrically GeomIrreducibleInfinite X.hom) :
    ∀ n, ConnectedSpace (ConfScheme X n).left
  | 0 => by
    haveI := isIso_confScheme_zero_hom X
    exact (ConfScheme X 0).hom.homeomorph.connectedSpace_iff.mpr ‹_›
  | n + 1 => by
    haveI := connectedSpace hX n
    exact connectedSpace_succ n hX

/-- Over a field `k`, if the geometric fibre of `X ⟶ Spec k` is irreducible and infinite (e.g. `X`
a geometrically irreducible curve), all configuration schemes `Conf_n(X)` are connected. Universal
openness of `X ⟶ Spec k` is automatic (EGA IV 2.4.10). -/
theorem connectedSpace_of_field {k : Type u} [Field k] {X : Over (Spec (.of k))}
    [IsSeparated X.hom] (hX : geometrically GeomIrreducibleInfinite X.hom) (n : ℕ) :
    ConnectedSpace (ConfScheme X n).left :=
  connectedSpace hX n

variable {X} in
/-- For `S` connected and `X ⟶ S` flat and locally of finite presentation with irreducible
infinite geometric fibres, all configuration schemes `Conf_n(X)` are connected. Universal openness
of `X ⟶ S` is automatic (EGA IV 2.4.6). -/
theorem connectedSpace_of_flat [ConnectedSpace S] [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    (hX : geometrically GeomIrreducibleInfinite X.hom) (n : ℕ) :
    ConnectedSpace (ConfScheme X n).left :=
  connectedSpace hX n

end ConfScheme

end AlgebraicGeometry
