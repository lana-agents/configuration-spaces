/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import ConfigurationSpaces.Topology.Basic

/-!
# Configuration schemes

Let `X` be a separated scheme over `S` (an object of `Over S` with separated structure morphism).

* `AlgebraicGeometry.ConfScheme.power X n`: the `n`-fold fibre power `Xⁿ = X ×_S ⋯ ×_S X`, the
  product in `Over S`, with projections `proj X n i`;
* `partialDiagonal X n i j`: the closed subset `Δᵢⱼ = (prᵢ, prⱼ)⁻¹ (Δ_{X/S})` of `Xⁿ`;
* `opens X n`: the open complement of `⋃_{i ≠ j} Δᵢⱼ`, and the configuration scheme
  `ConfScheme X n` (the corresponding open subscheme), an object of `Over S`, with its open
  immersion `ConfScheme.ι` into `Xⁿ`;
* `ConfScheme.permAut X n : Equiv.Perm (Fin n) →* Aut (ConfScheme X n)`: the action of the
  symmetric group by `S`-automorphisms (`σ` sends `(xᵢ)` to `(x_{σ⁻¹ i})`);
* `ConfScheme.forget X n : ConfScheme X (n + 1) ⟶ ConfScheme X n`: forget the last point,
  equivariant for `Conf.extendPerm` (`ConfScheme.perm_extendPerm_forget`);
* `ConfScheme.toProd`, `ConfScheme.isOpenImmersion_toProd`, `ConfScheme.range_toProd`:
  `Conf_{n+1}(X)` is the open subscheme of `Conf_n(X) ×_S X` complementary to the graphs of the
  `n` tautological sections, and `forget` is the restriction of the first projection;
* `ConfScheme.homEquiv`, `ConfScheme.homEquivSpec`: for an `S`-scheme `T` which is reduced and has
  exactly one point (e.g. the spectrum of a field), `S`-morphisms `T ⟶ Conf_n(X)` are the
  `n`-tuples of pairwise distinct `S`-morphisms `T ⟶ X`;
* `ConfScheme.fiberEquiv`: on such `T`-points, the fibre of `forget` over `z` is
  `X ∖ {z₀, …, zₙ₋₁}`.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace ConfScheme

variable {S : Scheme.{u}} (X : Over S) (n : ℕ)

/-- The `n`-fold fibre power `X ×_S ⋯ ×_S X`, as an object of `Over S`. -/
noncomputable abbrev power : Over S := ∏ᶜ fun _ : Fin n ↦ X

/-- The `i`-th projection `Xⁿ ⟶ X`. -/
noncomputable abbrev proj (i : Fin n) : power X n ⟶ X := Pi.π (fun _ : Fin n ↦ X) i

/-- The pair of projections `(prᵢ, prⱼ) : Xⁿ ⟶ X ×_S X`. -/
noncomputable abbrev pair (i j : Fin n) : power X n ⟶ X ⨯ X := prod.lift (proj X n i) (proj X n j)

/-- The diagonal `X ⟶ X ×_S X` is a closed immersion when `X` is separated over `S`. -/
instance isClosedImmersion_diag_left [IsSeparated X.hom] : IsClosedImmersion (diag X).left := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback X X).hom]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal X.hom))
  ext1
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.diagonal_fst,
      ← Over.comp_left]
    rw [diag, prod.lift_fst, Over.id_left]
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.diagonal_snd,
      ← Over.comp_left]
    rw [diag, prod.lift_snd, Over.id_left]

/-- The partial diagonal `Δᵢⱼ ⊆ Xⁿ`, the preimage of the diagonal under `(prᵢ, prⱼ)`. -/
def partialDiagonal (i j : Fin n) : Set (power X n).left :=
  (pair X n i j).left ⁻¹' Set.range (diag X).left

theorem isClosed_partialDiagonal [IsSeparated X.hom] (i j : Fin n) :
    IsClosed (partialDiagonal X n i j) :=
  ((diag X).left.isClosedEmbedding.isClosed_range).preimage (pair X n i j).left.continuous

variable {X n}

/-- Maps between fibre powers that permute the pairs of projections preserve the partial
diagonals. -/
theorem preimage_partialDiagonal {m : ℕ} (φ : power X m ⟶ power X n) {i j : Fin n}
    {k l : Fin m} (h : φ ≫ pair X n i j = pair X m k l) :
    φ.left ⁻¹' partialDiagonal X n i j = partialDiagonal X m k l := by
  ext p
  simp only [partialDiagonal, Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Over.comp_left, h]

/-- The automorphism of `Xⁿ` permuting the factors: `prᵢ ∘ permHom σ = pr_{σ⁻¹ i}`. -/
noncomputable def permHom (X : Over S) (n : ℕ) (σ : Equiv.Perm (Fin n)) : power X n ⟶ power X n :=
  Pi.lift fun i ↦ proj X n (σ⁻¹ i)

@[reassoc (attr := simp)]
theorem permHom_proj (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permHom X n σ ≫ proj X n i = proj X n (σ⁻¹ i) :=
  Pi.lift_π _ _

theorem permHom_one : permHom X n 1 = 𝟙 _ := Pi.hom_ext _ _ fun i ↦ by simp

theorem permHom_mul (σ τ : Equiv.Perm (Fin n)) :
    permHom X n (σ * τ) = permHom X n τ ≫ permHom X n σ :=
  Pi.hom_ext _ _ fun i ↦ by simp [mul_inv_rev]

theorem permHom_pair (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permHom X n σ ≫ pair X n i j = pair X n (σ⁻¹ i) (σ⁻¹ j) := by
  ext1 <;> simp

/-- The projection `Xⁿ⁺¹ ⟶ Xⁿ` forgetting the last factor. -/
noncomputable def forgetHom (X : Over S) (n : ℕ) : power X (n + 1) ⟶ power X n :=
  Pi.lift fun i ↦ proj X (n + 1) (Fin.castSucc i)

@[reassoc (attr := simp)]
theorem forgetHom_proj (i : Fin n) :
    forgetHom X n ≫ proj X n i = proj X (n + 1) (Fin.castSucc i) :=
  Pi.lift_π _ _

theorem forgetHom_pair (i j : Fin n) :
    forgetHom X n ≫ pair X n i j = pair X (n + 1) (Fin.castSucc i) (Fin.castSucc j) := by
  ext1 <;> simp

theorem permHom_extendPerm_forgetHom (σ : Equiv.Perm (Fin n)) :
    permHom X (n + 1) (Conf.extendPerm σ) ≫ forgetHom X n = forgetHom X n ≫ permHom X n σ :=
  Pi.hom_ext _ _ fun i ↦ by simp [← map_inv]

variable (X n)

/-- The open subset `Xⁿ ∖ ⋃_{i ≠ j} Δᵢⱼ`. -/
def opens [IsSeparated X.hom] : (power X n).left.Opens where
  carrier := {p | ∀ i j, i ≠ j → p ∉ partialDiagonal X n i j}
  is_open' := by
    have : {p | ∀ i j, i ≠ j → p ∉ partialDiagonal X n i j} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), (partialDiagonal X n i j)ᶜ := by
      ext p; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
      isOpen_iInter_of_finite fun _ ↦ (isClosed_partialDiagonal X n i j).isOpen_compl

end ConfScheme

open ConfScheme in
/-- The configuration scheme `Conf_n(X/S)`: the open subscheme of `Xⁿ` complementary to the
partial diagonals, as an `S`-scheme. -/
noncomputable def ConfScheme {S : Scheme.{u}} (X : Over S) [IsSeparated X.hom] (n : ℕ) :
    Over S :=
  Over.mk ((opens X n).ι ≫ (power X n).hom)

namespace ConfScheme

variable {S : Scheme.{u}} (X : Over S) [IsSeparated X.hom] (n : ℕ)

/-- The open immersion `Conf_n(X) ⟶ Xⁿ`, as a morphism over `S`. -/
noncomputable def ι : ConfScheme X n ⟶ power X n := Over.homMk (opens X n).ι

instance : IsOpenImmersion (ι X n).left := by
  change IsOpenImmersion (opens X n).ι; infer_instance

instance : Mono (ι X n) :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono (opens X n).ι))

theorem range_ι : Set.range (ι X n).left = opens X n := Scheme.Opens.range_ι _

variable {X n}

/-! ### The symmetric-group action -/

theorem opens_le_preimage_permHom (σ : Equiv.Perm (Fin n)) :
    opens X n ≤ (permHom X n σ).left ⁻¹ᵁ opens X n := by
  intro p hp i j hij
  change (permHom X n σ).left p ∈ partialDiagonal X n i j → False
  rw [← Set.mem_preimage, preimage_partialDiagonal _ (permHom_pair σ i j)]
  exact hp _ _ fun h ↦ hij (σ⁻¹.injective h)

variable (X n) in
/-- The action of a permutation `σ` on `Conf_n(X)`, an `S`-morphism. -/
noncomputable def perm (σ : Equiv.Perm (Fin n)) : ConfScheme X n ⟶ ConfScheme X n :=
  Over.homMk ((permHom X n σ).left.resLE (opens X n) (opens X n) (opens_le_preimage_permHom σ))
    (by
      change _ ≫ (opens X n).ι ≫ (power X n).hom = (opens X n).ι ≫ (power X n).hom
      rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w])

@[reassoc (attr := simp)]
theorem perm_ι (σ : Equiv.Perm (Fin n)) : perm X n σ ≫ ι X n = ι X n ≫ permHom X n σ := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι _ _

theorem perm_one : perm X n 1 = 𝟙 _ := by
  rw [← cancel_mono (ι X n), perm_ι, permHom_one]; simp

theorem perm_mul (σ τ : Equiv.Perm (Fin n)) :
    perm X n (σ * τ) = perm X n τ ≫ perm X n σ := by
  rw [← cancel_mono (ι X n), perm_ι, permHom_mul]; simp

variable (X n) in
/-- The action of the symmetric group `Sₙ` on `Conf_n(X)` by `S`-automorphisms. -/
noncomputable def permAut : Equiv.Perm (Fin n) →* Aut (ConfScheme X n) where
  toFun σ :=
    { hom := perm X n σ
      inv := perm X n σ⁻¹
      hom_inv_id := by rw [← perm_mul, inv_mul_cancel, perm_one]
      inv_hom_id := by rw [← perm_mul, mul_inv_cancel, perm_one] }
  map_one' := by ext1; exact perm_one
  map_mul' σ τ := by ext1; exact perm_mul σ τ

@[simp] theorem permAut_hom (σ : Equiv.Perm (Fin n)) : (permAut X n σ).hom = perm X n σ := rfl

/-! ### The forgetful morphisms -/

theorem opens_le_preimage_forgetHom :
    opens X (n + 1) ≤ (forgetHom X n).left ⁻¹ᵁ opens X n := by
  intro p hp i j hij
  change (forgetHom X n).left p ∈ partialDiagonal X n i j → False
  rw [← Set.mem_preimage, preimage_partialDiagonal _ (forgetHom_pair i j)]
  exact hp _ _ fun h ↦ hij (Fin.castSucc_injective n h)

variable (X n) in
/-- The forgetful `S`-morphism `Conf_{n+1}(X) ⟶ Conf_n(X)`, forgetting the last point. -/
noncomputable def forget : ConfScheme X (n + 1) ⟶ ConfScheme X n :=
  Over.homMk ((forgetHom X n).left.resLE (opens X n) (opens X (n + 1))
    opens_le_preimage_forgetHom)
    (by
      change _ ≫ (opens X n).ι ≫ (power X n).hom = (opens X (n + 1)).ι ≫ (power X (n + 1)).hom
      rw [Scheme.Hom.resLE_comp_ι_assoc, Over.w])

@[reassoc (attr := simp)]
theorem forget_ι : forget X n ≫ ι X n = ι X (n + 1) ≫ forgetHom X n := by
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι _ _

/-- The forgetful morphism is equivariant for `Conf.extendPerm : Sₙ → Sₙ₊₁`. -/
theorem perm_extendPerm_forget (σ : Equiv.Perm (Fin n)) :
    perm X (n + 1) (Conf.extendPerm σ) ≫ forget X n = forget X n ≫ perm X n σ := by
  rw [← cancel_mono (ι X n)]
  simp only [Category.assoc, forget_ι, perm_ι, perm_ι_assoc, forget_ι_assoc,
    permHom_extendPerm_forgetHom]

/-! ### `Conf_{n+1}(X)` as an open subscheme of `Conf_n(X) ×_S X` -/

omit [IsSeparated X.hom] in
/-- The product (over `S`) of an open immersion with an identity is an open immersion. -/
theorem isOpenImmersion_prodMap_left {A B Y : Over S} (f : A ⟶ B) [IsOpenImmersion f.left] :
    IsOpenImmersion (prod.map f (𝟙 Y)).left := by
  have e : (prod.map f (𝟙 Y)).left = (Over.prodLeftIsoPullback A Y).hom ≫
      pullback.map A.hom Y.hom B.hom Y.hom f.left (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        (Over.prodLeftIsoPullback B Y).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst,
        Over.prodLeftIsoPullback_hom_fst_assoc, ← Over.comp_left, prod.map_fst]
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd,
        ← Over.comp_left, prod.map_snd, Category.comp_id]
  have : IsOpenImmersion (pullback.map A.hom Y.hom B.hom Y.hom f.left (𝟙 _) (𝟙 _)
      (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion _))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w f).symm (Category.id_comp _).symm
  rw [e]
  infer_instance

variable (X n) in
/-- The isomorphism `Xⁿ⁺¹ ≅ Xⁿ ×_S X`. -/
noncomputable def powerSuccIso : power X (n + 1) ≅ power X n ⨯ X where
  hom := prod.lift (forgetHom X n) (proj X (n + 1) (Fin.last n))
  inv := Pi.lift fun i ↦ Fin.lastCases prod.snd (fun j ↦ prod.fst ≫ proj X n j) i
  hom_inv_id := Pi.hom_ext _ _ fun i ↦ by
    rw [Category.assoc, Pi.lift_π, Category.id_comp]
    induction i using Fin.lastCases with
    | last => rw [Fin.lastCases_last, prod.lift_snd]
    | cast j => rw [Fin.lastCases_castSucc, prod.lift_fst_assoc, forgetHom_proj]
  inv_hom_id := by
    ext1
    · rw [Category.assoc, prod.lift_fst, Category.id_comp]
      exact Pi.hom_ext _ _ fun j ↦ by
        rw [Category.assoc, forgetHom_proj, Pi.lift_π, Fin.lastCases_castSucc]
    · rw [Category.assoc, prod.lift_snd, Category.id_comp, Pi.lift_π, Fin.lastCases_last]

variable (X n) in
/-- The `S`-morphism `Conf_{n+1}(X) ⟶ Conf_n(X) ×_S X`, `(x₀, …, xₙ) ↦ ((x₀, …, xₙ₋₁), xₙ)`. -/
noncomputable def toProd : ConfScheme X (n + 1) ⟶ ConfScheme X n ⨯ X :=
  prod.lift (forget X n) (ι X (n + 1) ≫ proj X (n + 1) (Fin.last n))

theorem toProd_prodMap : toProd X n ≫ prod.map (ι X n) (𝟙 X) =
    ι X (n + 1) ≫ (powerSuccIso X n).hom := by
  ext1
  · rw [Category.assoc, prod.map_fst, toProd, prod.lift_fst_assoc, forget_ι, Category.assoc,
      powerSuccIso, prod.lift_fst]
  · rw [Category.assoc, prod.map_snd, Category.comp_id, toProd, prod.lift_snd, Category.assoc,
      powerSuccIso, prod.lift_snd]

/-- **`Conf_{n+1}(X)` is an open subscheme of `Conf_n(X) ×_S X`**: the morphism
`(forget, last) : Conf_{n+1}(X) ⟶ Conf_n(X) ×_S X` is an open immersion. -/
instance isOpenImmersion_toProd : IsOpenImmersion (toProd X n).left := by
  haveI := isOpenImmersion_prodMap_left (Y := X) (ι X n)
  haveI : IsOpenImmersion (toProd X n ≫ prod.map (ι X n) (𝟙 X)).left := by
    rw [toProd_prodMap, Over.comp_left]
    infer_instance
  rw [Over.comp_left] at this
  exact IsOpenImmersion.of_comp _ (prod.map (ι X n) (𝟙 X)).left

/-! ### Points -/

section Points

variable {T : Over S}

/-- Lift a morphism into `Xⁿ` whose image avoids the partial diagonals to `Conf_n(X)`. -/
noncomputable def liftOfRange (g : T ⟶ power X n) (hg : ∀ t, g.left t ∈ opens X n) :
    T ⟶ ConfScheme X n :=
  Over.homMk (IsOpenImmersion.lift (opens X n).ι g.left (by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg t) : T.left ⟶ (opens X n).toScheme)
    (by
      change _ ≫ (opens X n).ι ≫ (power X n).hom = T.hom
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])

@[reassoc (attr := simp)]
theorem liftOfRange_ι (g : T ⟶ power X n) (hg : ∀ t, g.left t ∈ opens X n) :
    liftOfRange g hg ≫ ι X n = g := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (opens X n).ι g.left _

theorem ι_apply_mem_opens (φ : T ⟶ ConfScheme X n) (t : T.left) :
    (φ ≫ ι X n).left t ∈ opens X n := by
  have h := range_ι X n
  rw [Set.ext_iff] at h
  exact (h _).1 ⟨φ.left t, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩

omit [IsSeparated X.hom] in
/-- If two coordinates of `g : T ⟶ Xⁿ` agree, `g` lands in the partial diagonal. -/
theorem mem_partialDiagonal_of_eq (g : T ⟶ power X n) {i j : Fin n}
    (h : g ≫ proj X n i = g ≫ proj X n j) (t : T.left) : g.left t ∈ partialDiagonal X n i j := by
  have e : g ≫ pair X n i j = (g ≫ proj X n i) ≫ diag X := by
    rw [pair, prod.comp_lift, diag, prod.comp_lift, Category.comp_id, h]
  refine ⟨(g ≫ proj X n i).left t, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← e, Over.comp_left, Scheme.Hom.comp_apply]

/-- Conversely, if `T` is reduced with at most one point (e.g. the spectrum of a field) and `g`
meets the partial diagonal `Δᵢⱼ`, then the `i`-th and `j`-th coordinates of `g` agree. -/
theorem eq_of_mem_partialDiagonal [IsReduced T.left] [Subsingleton T.left] (g : T ⟶ power X n)
    {i j : Fin n} {t : T.left} (ht : g.left t ∈ partialDiagonal X n i j) :
    g ≫ proj X n i = g ≫ proj X n j := by
  set h := (g ≫ pair X n i j).left
  have hsurj : Surjective (pullback.fst h (diag X).left) := by
    refine ⟨fun t' ↦ ?_⟩
    have : t' ∈ Set.range (pullback.fst h (diag X).left) := by
      rw [Scheme.Pullback.range_fst, Subsingleton.elim t' t, Set.mem_preimage]
      change (g ≫ pair X n i j).left t ∈ _
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      exact ht
    exact this
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst h (diag X).left)
  have key : h = inv (pullback.fst h (diag X).left) ≫ pullback.snd h (diag X).left ≫
      (diag X).left := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have e1 : (g ≫ proj X n i).left = h ≫ (prod.fst : X ⨯ X ⟶ X).left := by
    simp only [h, ← Over.comp_left, Category.assoc, prod.lift_fst]
  have e2 : (g ≫ proj X n j).left = h ≫ (prod.snd : X ⨯ X ⟶ X).left := by
    simp only [h, ← Over.comp_left, Category.assoc, prod.lift_snd]
  apply Over.OverMorphism.ext
  rw [e1, e2, key]
  simp only [Category.assoc, ← Over.comp_left, diag, prod.lift_fst, prod.lift_snd]

variable [IsReduced T.left] [Nonempty T.left] [Subsingleton T.left]

variable (X n T) in
/-- **Points of configuration schemes.** For an `S`-scheme `T` which is reduced and has exactly one
point (e.g. the spectrum of a field), `S`-morphisms `T ⟶ Conf_n(X)` correspond to `n`-tuples of
pairwise distinct `S`-morphisms `T ⟶ X`. -/
noncomputable def homEquiv :
    (T ⟶ ConfScheme X n) ≃ {x : Fin n → (T ⟶ X) // Function.Injective x} where
  toFun φ := ⟨fun i ↦ φ ≫ ι X n ≫ proj X n i, fun i j hij ↦ by
    by_contra hne
    obtain ⟨t⟩ := ‹Nonempty T.left›
    have hd := mem_partialDiagonal_of_eq (φ ≫ ι X n) (i := i) (j := j)
      (by simpa only [Category.assoc] using hij) t
    exact ι_apply_mem_opens φ t i j hne hd⟩
  invFun x := liftOfRange (Pi.lift x.1) fun t i j hij hd ↦
    hij (x.2 (by
      have := eq_of_mem_partialDiagonal (Pi.lift x.1) hd
      rwa [proj, proj, Pi.lift_π, Pi.lift_π] at this))
  left_inv φ := by
    rw [← cancel_mono (ι X n), liftOfRange_ι]
    exact Pi.hom_ext _ _ fun i ↦ by rw [Pi.lift_π, Category.assoc]
  right_inv x := by
    ext1
    funext i
    change liftOfRange _ _ ≫ ι X n ≫ proj X n i = _
    rw [liftOfRange_ι_assoc]
    exact Pi.lift_π x.1 i

@[simp, nolint unusedArguments]
theorem homEquiv_apply_coe (φ : T ⟶ ConfScheme X n) (i : Fin n) :
    (homEquiv X n T φ : Fin n → (T ⟶ X)) i = φ ≫ ι X n ≫ proj X n i := rfl

theorem homEquiv_forget (w : T ⟶ ConfScheme X (n + 1)) (i : Fin n) :
    (homEquiv X n T (w ≫ forget X n) : Fin n → (T ⟶ X)) i =
      (homEquiv X (n + 1) T w : Fin (n + 1) → (T ⟶ X)) (Fin.castSucc i) := by
  simp [forget_ι_assoc]

/-- **Fibres of the forgetful morphism, on points.** For `T` reduced with exactly one point and
`z : T ⟶ Conf_n(X)` with coordinates `z₀, …, zₙ₋₁`, the lifts of `z` to `Conf_{n+1}(X)` are the
`S`-morphisms `T ⟶ X` different from all `zᵢ`: the fibre of `forget` over `z` is `X ∖ {z₀,…,zₙ₋₁}`
on `T`-points. -/
noncomputable def fiberEquiv (z : T ⟶ ConfScheme X n) :
    {w : T ⟶ ConfScheme X (n + 1) // w ≫ forget X n = z} ≃
      {p : T ⟶ X // p ∉ Set.range (homEquiv X n T z : Fin n → (T ⟶ X))} where
  toFun w := ⟨(homEquiv X (n + 1) T w.1 : Fin (n + 1) → (T ⟶ X)) (Fin.last n), by
    rintro ⟨i, hi⟩
    obtain ⟨w, hw⟩ := w
    subst hw
    rw [homEquiv_forget] at hi
    exact Fin.castSucc_ne_last i ((homEquiv X (n + 1) T w).2 hi)⟩
  invFun p := ⟨(homEquiv X (n + 1) T).symm
      ⟨Fin.snoc (α := fun _ ↦ T ⟶ X) (homEquiv X n T z) p.1,
        Fin.snoc_injective_iff.2 ⟨(homEquiv X n T z).2, p.2⟩⟩, by
    apply (homEquiv X n T).injective
    ext1
    funext i
    rw [homEquiv_forget, Equiv.apply_symm_apply]
    simp⟩
  left_inv w := by
    apply Subtype.ext
    apply (homEquiv X (n + 1) T).injective
    rw [Equiv.apply_symm_apply]
    ext1
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp only [Fin.snoc_castSucc]
      rw [← homEquiv_forget, w.2]
  right_inv p := by
    apply Subtype.ext
    simp

end Points

omit [IsSeparated X.hom] in
theorem mem_partialDiagonal_iff {Y : Over S} (φ : Y ⟶ power X n) (y : Y.left) {i j : Fin n} :
    φ.left y ∈ partialDiagonal X n i j ↔ (φ ≫ pair X n i j).left y ∈ Set.range (diag X).left := by
  rw [partialDiagonal, Set.mem_preimage, Over.comp_left, Scheme.Hom.comp_apply]

omit [IsSeparated X.hom] in
/-- The diagonal of `X ×_S X` is symmetric. -/
theorem mem_range_diag_swap {Y : Over S} (a b : Y ⟶ X) (y : Y.left) :
    (prod.lift a b).left y ∈ Set.range (diag X).left ↔
      (prod.lift b a).left y ∈ Set.range (diag X).left := by
  have hswap : ∀ {Z : Over S} (a b : Z ⟶ X),
      prod.lift a b ≫ prod.lift prod.snd prod.fst = prod.lift b a := fun a b ↦ by
    ext1 <;> rw [Category.assoc] <;> simp only [prod.lift_fst, prod.lift_snd]
  have hdiag : diag X ≫ prod.lift prod.snd prod.fst = diag X := by
    rw [diag, hswap]
  have key : ∀ (a b : Y ⟶ X), (prod.lift a b).left y ∈ Set.range (diag X).left →
      (prod.lift b a).left y ∈ Set.range (diag X).left := by
    rintro a b ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hswap a b, Over.comp_left, Scheme.Hom.comp_apply, ← hx, ← Scheme.Hom.comp_apply,
      ← Over.comp_left, hdiag]
  exact ⟨key a b, key b a⟩

omit [IsSeparated X.hom] in
private theorem powerSuccIso_inv_proj_castSucc (i : Fin n) :
    (powerSuccIso X n).inv ≫ proj X (n + 1) (Fin.castSucc i) = prod.fst ≫ proj X n i := by
  rw [powerSuccIso, Pi.lift_π, Fin.lastCases_castSucc]

omit [IsSeparated X.hom] in
private theorem powerSuccIso_inv_proj_last :
    (powerSuccIso X n).inv ≫ proj X (n + 1) (Fin.last n) = prod.snd := by
  rw [powerSuccIso, Pi.lift_π, Fin.lastCases_last]

/-- The image of `Conf_{n+1}(X)` in `Conf_n(X) ×_S X`: the complement of the graphs of the `n`
tautological sections, i.e. the points `(z, p)` with `p ≠ zᵢ` for all `i`. -/
theorem range_toProd :
    Set.range (toProd X n).left = {q | ∀ i : Fin n,
      (prod.lift (prod.fst ≫ ι X n ≫ proj X n i) prod.snd : ConfScheme X n ⨯ X ⟶ X ⨯ X).left q ∉
        Set.range (diag X).left} := by
  set k := prod.map (ι X n) (𝟙 X)
  set e := powerSuccIso X n
  haveI := isOpenImmersion_prodMap_left (Y := X) (ι X n)
  have hk : Function.Injective k.left := k.left.isOpenEmbedding.injective
  have he : ∀ p, e.inv.left (e.hom.left p) = p := fun p ↦ by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.hom_inv_id, Over.id_left]; rfl
  have he' : ∀ p, e.hom.left (e.inv.left p) = p := fun p ↦ by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e.inv_hom_id, Over.id_left]; rfl
  -- membership in the image, via `Xⁿ⁺¹`
  have step1 : ∀ q, q ∈ Set.range (toProd X n).left ↔ (k ≫ e.inv).left q ∈ opens X (n + 1) := by
    intro q
    constructor
    · rintro ⟨w, rfl⟩
      have : (k ≫ e.inv).left ((toProd X n).left w) = (ι X (n + 1)).left w := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← Category.assoc, toProd_prodMap,
          Category.assoc, e.hom_inv_id, Category.comp_id]
      rw [this]
      exact ι_apply_mem_opens (𝟙 _) w
    · intro h
      have h' : (k ≫ e.inv).left q ∈ Set.range (ι X (n + 1)).left := by rw [range_ι]; exact h
      obtain ⟨w, hw⟩ := h'
      refine ⟨w, hk ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, toProd_prodMap, Over.comp_left,
        Scheme.Hom.comp_apply, hw, Over.comp_left, Scheme.Hom.comp_apply, he']
  have hfst : ∀ i : Fin n, k ≫ e.inv ≫ proj X (n + 1) (Fin.castSucc i) =
      prod.fst ≫ ι X n ≫ proj X n i := fun i ↦ by
    rw [powerSuccIso_inv_proj_castSucc, prod.map_fst_assoc]
  have hlast : k ≫ e.inv ≫ proj X (n + 1) (Fin.last n) = prod.snd := by
    rw [powerSuccIso_inv_proj_last, prod.map_snd, Category.comp_id]
  ext q
  rw [step1]
  simp only [opens, TopologicalSpace.Opens.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h i hi
    refine h (Fin.castSucc i) (Fin.last n) (Fin.castSucc_ne_last i) ?_
    rw [mem_partialDiagonal_iff, pair, prod.comp_lift, Category.assoc, Category.assoc, hfst,
      hlast]
    exact hi
  · intro h a b hab hd
    rw [mem_partialDiagonal_iff, pair, prod.comp_lift, Category.assoc, Category.assoc] at hd
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => exact hab rfl
      | cast j =>
        rw [hfst, hlast, mem_range_diag_swap] at hd
        exact h j hd
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        rw [hfst, hlast] at hd
        exact h i hd
      | cast j =>
        rw [hfst, hfst] at hd
        have hij : i ≠ j := fun e ↦ hab (by rw [e])
        refine ι_apply_mem_opens (prod.fst : ConfScheme X n ⨯ X ⟶ _) q i j hij ?_
        rw [mem_partialDiagonal_iff, pair, prod.comp_lift, Category.assoc, Category.assoc]
        exact hd

/-- **Points with values in a field.** For a field `K` and `f : Spec K ⟶ S`, the `S`-morphisms
`Spec K ⟶ Conf_n(X)` are the `n`-tuples of pairwise distinct `S`-morphisms `Spec K ⟶ X`. -/
noncomputable def homEquivSpec {K : Type u} [Field K] (f : Spec (CommRingCat.of K) ⟶ S) :
    (Over.mk f ⟶ ConfScheme X n) ≃ {x : Fin n → (Over.mk f ⟶ X) // Function.Injective x} :=
  haveI : IsReduced (Over.mk f).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
  haveI : Nonempty (Over.mk f).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))
  haveI : Subsingleton (Over.mk f).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  homEquiv X n (Over.mk f)

end ConfScheme

end AlgebraicGeometry
