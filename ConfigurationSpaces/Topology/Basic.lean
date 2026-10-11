/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Ordered configuration spaces

For a topological space `X` and `n : ℕ`, the ordered configuration space
`Conf n X = Xⁿ ∖ ⋃_{i ≠ j} {xᵢ = xⱼ}` is the space of injective maps `Fin n → X`, with the
subspace topology of `Fin n → X`.

## Main definitions and results

* `Conf n X`: the ordered configuration space; `Conf.isOpen_setOf_injective`: it is open in `Xⁿ`
  if `X` is Hausdorff.
* The free action of `Equiv.Perm (Fin n)` by homeomorphisms, `σ • x = x ∘ σ⁻¹`
  (`Conf.instMulAction`, `Conf.continuous_smul`, `Conf.smul_eq_self_iff`).
* `Conf.forget : C(Conf (n + 1) X, Conf n X)`: forget the last point; it is equivariant
  (`Conf.forget_smul`) for `Conf.extendPerm : Perm (Fin n) →* Perm (Fin (n + 1))`.
* `Conf.snocHomeomorph`: `Conf (n + 1) X ≃ₜ {q : Conf n X × X // q.2 ∉ range q.1}`, over
  `Conf n X`; `Conf.fiberHomeomorph`: the fibre of `forget` over `y` is homeomorphic to the
  punctured space `(range y)ᶜ`.
* Functoriality: `Conf.map` for injective continuous maps, compatible with the action and with
  `forget`; embeddings and homeomorphisms are preserved.
-/

open Function Set Topology

universe u v

/-- The ordered configuration space of `n` points in `X`: injective maps `Fin n → X`. -/
def Conf (n : ℕ) (X : Type u) : Type u := {x : Fin n → X // Injective x}

namespace Conf

variable {n : ℕ} {X : Type u} {Y : Type v}

instance : CoeFun (Conf n X) (fun _ ↦ Fin n → X) := ⟨fun x ↦ x.1⟩

@[ext] theorem ext {x y : Conf n X} (h : ∀ i, x i = y i) : x = y := Subtype.ext (funext h)

theorem injective (x : Conf n X) : Injective x := x.2

/-- Build a configuration from an injective map. -/
def mk (x : Fin n → X) (hx : Injective x) : Conf n X := ⟨x, hx⟩

@[simp] theorem mk_apply (x : Fin n → X) (hx : Injective x) (i : Fin n) : mk x hx i = x i := rfl

@[simp] theorem coe_mk (x : Fin n → X) (hx : Injective x) : ⇑(mk x hx) = x := rfl

theorem apply_ne (x : Conf n X) {i j : Fin n} (h : i ≠ j) : x i ≠ x j :=
  fun e ↦ h (x.injective e)

section Topology

variable [TopologicalSpace X] [TopologicalSpace Y]

instance : TopologicalSpace (Conf n X) :=
  inferInstanceAs (TopologicalSpace {x : Fin n → X // Injective x})

/-- The inclusion `Conf n X → Xⁿ`. -/
def val : C(Conf n X, Fin n → X) := ⟨fun x ↦ x, continuous_subtype_val⟩

@[simp] theorem val_apply (x : Conf n X) : val x = x := rfl

theorem isEmbedding_val : IsEmbedding (fun x : Conf n X ↦ (x : Fin n → X)) :=
  IsEmbedding.subtypeVal

@[fun_prop] theorem continuous_coe : Continuous (fun x : Conf n X ↦ (x : Fin n → X)) :=
  continuous_subtype_val

@[fun_prop] theorem continuous_apply (i : Fin n) : Continuous (fun x : Conf n X ↦ x i) :=
  (_root_.continuous_apply i).comp continuous_coe

theorem continuous_iff {Z : Type*} [TopologicalSpace Z] {f : Z → Conf n X} :
    Continuous f ↔ Continuous (fun z ↦ (f z : Fin n → X)) :=
  isEmbedding_val.continuous_iff

theorem continuousOn_iff {Z : Type*} [TopologicalSpace Z] {f : Z → Conf n X} {s : Set Z} :
    ContinuousOn f s ↔ ContinuousOn (fun z ↦ (f z : Fin n → X)) s :=
  isEmbedding_val.continuousOn_iff

/-- In a Hausdorff space the injective tuples form an open subset of `Xⁿ`. -/
theorem isOpen_setOf_injective [T2Space X] : IsOpen {x : Fin n → X | Injective x} := by
  have : {x : Fin n → X | Injective x} = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | x i ≠ x j} := by
    ext x; simp only [mem_setOf_eq, mem_iInter]
    exact ⟨fun h i j hij e ↦ hij (h e), fun h i j e ↦ by_contra fun hij ↦ h i j hij e⟩
  rw [this]
  refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_iInter_of_finite fun _ ↦ ?_
  exact isOpen_ne_fun (_root_.continuous_apply i) (_root_.continuous_apply j)

theorem isOpenEmbedding_val [T2Space X] :
    IsOpenEmbedding (fun x : Conf n X ↦ (x : Fin n → X)) :=
  isOpen_setOf_injective.isOpenEmbedding_subtypeVal

instance [T2Space X] : T2Space (Conf n X) :=
  inferInstanceAs (T2Space {x : Fin n → X // Injective x})

end Topology

/-! ### The symmetric group action -/

section Action

instance instMulAction : MulAction (Equiv.Perm (Fin n)) (Conf n X) where
  smul σ x := ⟨x ∘ ⇑σ⁻¹, x.injective.comp (Equiv.injective _)⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem smul_def (σ : Equiv.Perm (Fin n)) (x : Conf n X) :
    σ • x = mk (x ∘ ⇑σ⁻¹) (x.injective.comp (Equiv.injective _)) := rfl

@[simp] theorem smul_apply (σ : Equiv.Perm (Fin n)) (x : Conf n X) (i : Fin n) :
    (σ • x) i = x (σ⁻¹ i) := rfl

/-- The action of the symmetric group on `Conf n X` is free. -/
theorem smul_eq_self_iff {σ : Equiv.Perm (Fin n)} {x : Conf n X} : σ • x = x ↔ σ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ one_smul _ x⟩
  refine Equiv.ext fun i ↦ ?_
  have : x (σ⁻¹ (σ i)) = x (σ i) := congrArg (fun y : Conf n X ↦ y (σ i)) h
  simpa using (x.injective this).symm

variable [TopologicalSpace X]

@[fun_prop] theorem continuous_smul (σ : Equiv.Perm (Fin n)) :
    Continuous (fun x : Conf n X ↦ σ • x) :=
  continuous_iff.2 <| continuous_pi fun i ↦ continuous_apply (σ⁻¹ i)

/-- A permutation acts on `Conf n X` by a homeomorphism. -/
def smulHomeomorph (σ : Equiv.Perm (Fin n)) : Conf n X ≃ₜ Conf n X where
  toFun x := σ • x
  invFun x := σ⁻¹ • x
  left_inv x := inv_smul_smul σ x
  right_inv x := smul_inv_smul σ x
  continuous_toFun := continuous_smul σ
  continuous_invFun := continuous_smul σ⁻¹

@[simp] theorem smulHomeomorph_apply (σ : Equiv.Perm (Fin n)) (x : Conf n X) :
    smulHomeomorph σ x = σ • x := rfl

end Action

/-! ### The forgetful maps -/

section Forget

/-- Forget the last point of a configuration of `n + 1` points. -/
def forgetFun (x : Conf (n + 1) X) : Conf n X :=
  mk (fun i ↦ x (Fin.castSucc i)) (x.injective.comp (Fin.castSucc_injective n))

@[simp] theorem forgetFun_apply (x : Conf (n + 1) X) (i : Fin n) :
    forgetFun x i = x (Fin.castSucc i) := rfl

/-- The last point of a configuration of `n + 1` points. -/
def last (x : Conf (n + 1) X) : X := x (Fin.last n)

theorem last_notMem_range (x : Conf (n + 1) X) : x.last ∉ range (forgetFun x) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i (x.injective hi)

/-- Add a new last point to a configuration. -/
def snoc (y : Conf n X) (p : X) (hp : p ∉ range y) : Conf (n + 1) X :=
  mk (Fin.snoc (α := fun _ ↦ X) y p) (Fin.snoc_injective_iff.2 ⟨y.injective, hp⟩)

@[simp] theorem forgetFun_snoc (y : Conf n X) (p : X) (hp : p ∉ range y) :
    forgetFun (snoc y p hp) = y := by
  ext i; simp [snoc]

@[simp] theorem last_snoc (y : Conf n X) (p : X) (hp : p ∉ range y) :
    (snoc y p hp).last = p := by
  simp [snoc, last]

@[simp] theorem snoc_forgetFun_last (x : Conf (n + 1) X) :
    snoc (forgetFun x) x.last (last_notMem_range x) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [snoc, last]

/-- Extend a permutation of `Fin n` to `Fin (n + 1)` by fixing the last element. -/
def extendPerm : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) where
  toFun σ := (finSuccEquivLast.trans (Equiv.optionCongr σ)).trans finSuccEquivLast.symm
  map_one' := by ext i; simp
  map_mul' σ τ := by ext i; simp

@[simp] theorem extendPerm_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm σ (Fin.castSucc i) = Fin.castSucc (σ i) := by
  simp [extendPerm]

@[simp] theorem extendPerm_last (σ : Equiv.Perm (Fin n)) :
    extendPerm σ (Fin.last n) = Fin.last n := by
  simp [extendPerm]

theorem forgetFun_smul (σ : Equiv.Perm (Fin n)) (x : Conf (n + 1) X) :
    forgetFun (extendPerm σ • x) = σ • forgetFun x := by
  ext i
  simp only [forgetFun_apply, smul_apply, ← map_inv]
  rw [extendPerm_castSucc]

@[simp] theorem last_smul (σ : Equiv.Perm (Fin n)) (x : Conf (n + 1) X) :
    (extendPerm σ • x).last = x.last := by
  simp only [last, smul_apply, ← map_inv, extendPerm_last]

variable [TopologicalSpace X]

/-- The forgetful map `Conf (n + 1) X → Conf n X`, forgetting the last point. -/
def forget : C(Conf (n + 1) X, Conf n X) :=
  ⟨forgetFun, continuous_iff.2 <| continuous_pi fun _ ↦ continuous_apply _⟩

@[simp] theorem forget_apply (x : Conf (n + 1) X) : forget x = forgetFun x := rfl

@[fun_prop] theorem continuous_last : Continuous (last : Conf (n + 1) X → X) :=
  continuous_apply _

/-- The forgetful map is equivariant for `extendPerm`. -/
theorem forget_smul (σ : Equiv.Perm (Fin n)) (x : Conf (n + 1) X) :
    forget (extendPerm σ • x) = σ • forget x :=
  forgetFun_smul σ x

/-- The total space of the forgetful map, described as a subspace of `Conf n X × X`. -/
abbrev SnocSpace (n : ℕ) (X : Type u) [TopologicalSpace X] : Type u :=
  {q : Conf n X × X // q.2 ∉ range q.1}

/-- `Conf (n + 1) X` is homeomorphic to the space of pairs `(y, p)` with `p ∉ range y`; under this
homeomorphism `forget` becomes the first projection. -/
def snocHomeomorph : Conf (n + 1) X ≃ₜ SnocSpace n X where
  toFun x := ⟨(forgetFun x, x.last), last_notMem_range x⟩
  invFun q := snoc q.1.1 q.1.2 q.2
  left_inv x := snoc_forgetFun_last x
  right_inv q := by ext <;> simp
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (forget.continuous).prodMk continuous_last
  continuous_invFun := by
    refine continuous_iff.2 ?_
    exact Continuous.finSnoc (A := fun _ ↦ X)
      (f := fun q : SnocSpace n X ↦ (q.1.1 : Fin n → X)) (by fun_prop) (by fun_prop)

@[simp] theorem snocHomeomorph_apply_fst (x : Conf (n + 1) X) :
    (snocHomeomorph x).1.1 = forget x := rfl

@[simp] theorem snocHomeomorph_apply_snd (x : Conf (n + 1) X) :
    (snocHomeomorph x).1.2 = x.last := rfl

@[simp] theorem snocHomeomorph_symm_apply (q : SnocSpace n X) :
    snocHomeomorph.symm q = snoc q.1.1 q.1.2 q.2 := rfl

/-- The fibre of the forgetful map over `y` is homeomorphic to the punctured space
`X ∖ {y₀, …, yₙ₋₁}`. -/
def fiberHomeomorph (y : Conf n X) : (forget ⁻¹' {y} : Set (Conf (n + 1) X)) ≃ₜ
    ((range y)ᶜ : Set X) where
  toFun x := ⟨x.1.last, fun hm ↦ last_notMem_range x.1 (by
    rwa [show forgetFun x.1 = y from x.2])⟩
  invFun p := ⟨snoc y p.1 p.2, by simp⟩
  left_inv x := by
    obtain ⟨x, hx⟩ := x
    have h : forgetFun x = y := hx
    apply Subtype.ext
    ext i
    have h1 := congrArg (fun z : Conf (n + 1) X ↦ z i) (snoc_forgetFun_last x)
    simp only [snoc, mk_apply] at h1 ⊢
    rw [← h]
    exact h1
  right_inv p := by simp
  continuous_toFun := (continuous_last.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_iff.2 ?_) _
    exact Continuous.finSnoc (A := fun _ ↦ X) (f := fun _ : ((range y)ᶜ : Set X) ↦ (y : Fin n → X))
      continuous_const continuous_subtype_val

@[simp] theorem fiberHomeomorph_apply (y : Conf n X) (x : (forget ⁻¹' {y} : Set _)) :
    (fiberHomeomorph y x : X) = x.1.last := rfl

@[simp] theorem fiberHomeomorph_symm_apply (y : Conf n X) (p : ((range y)ᶜ : Set X)) :
    ((fiberHomeomorph y).symm p : Conf (n + 1) X) = snoc y p.1 p.2 := rfl

end Forget

/-! ### Functoriality -/

section Map

/-- An injective map `X → Y` induces a map `Conf n X → Conf n Y`. -/
def mapFun (f : X → Y) (hf : Injective f) (x : Conf n X) : Conf n Y :=
  mk (f ∘ x) (hf.comp x.injective)

@[simp] theorem mapFun_apply (f : X → Y) (hf : Injective f) (x : Conf n X) (i : Fin n) :
    mapFun f hf x i = f (x i) := rfl

theorem mapFun_smul (f : X → Y) (hf : Injective f) (σ : Equiv.Perm (Fin n)) (x : Conf n X) :
    mapFun f hf (σ • x) = σ • mapFun f hf x := rfl

theorem forgetFun_mapFun (f : X → Y) (hf : Injective f) (x : Conf (n + 1) X) :
    forgetFun (mapFun f hf x) = mapFun f hf (forgetFun x) := rfl

theorem mapFun_injective (f : X → Y) (hf : Injective f) :
    Injective (mapFun (n := n) f hf) := fun _ _ h ↦
  ext fun i ↦ hf (congrArg (fun z : Conf n Y ↦ z i) h)

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous injective map `X → Y` induces a continuous map `Conf n X → Conf n Y`. -/
def map (f : C(X, Y)) (hf : Injective f) : C(Conf n X, Conf n Y) :=
  ⟨mapFun f hf, continuous_iff.2 <| continuous_pi fun i ↦ f.continuous.comp (continuous_apply i)⟩

@[simp] theorem map_apply (f : C(X, Y)) (hf : Injective f) (x : Conf n X) (i : Fin n) :
    map f hf x i = f (x i) := rfl

theorem map_smul (f : C(X, Y)) (hf : Injective f) (σ : Equiv.Perm (Fin n)) (x : Conf n X) :
    map f hf (σ • x) = σ • map f hf x := rfl

theorem forget_map (f : C(X, Y)) (hf : Injective f) (x : Conf (n + 1) X) :
    forget (map f hf x) = map f hf (forget x) := rfl

theorem last_map (f : C(X, Y)) (hf : Injective f) (x : Conf (n + 1) X) :
    (map f hf x).last = f x.last := rfl

/-- An embedding `X → Y` induces an embedding `Conf n X → Conf n Y`. -/
theorem isEmbedding_map {f : C(X, Y)} (hf : IsEmbedding f) :
    IsEmbedding (map (n := n) f hf.injective) := by
  refine IsEmbedding.of_comp (map f hf.injective).continuous isEmbedding_val.continuous ?_
  exact (IsEmbedding.piMap fun _ ↦ hf).comp isEmbedding_val

/-- A homeomorphism `X ≃ₜ Y` induces a homeomorphism `Conf n X ≃ₜ Conf n Y`. -/
def mapHomeomorph (e : X ≃ₜ Y) : Conf n X ≃ₜ Conf n Y where
  toFun := mapFun e e.injective
  invFun := mapFun e.symm e.symm.injective
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  continuous_toFun := (map (e : C(X, Y)) e.injective).continuous
  continuous_invFun := (map (e.symm : C(Y, X)) e.symm.injective).continuous

@[simp] theorem mapHomeomorph_apply (e : X ≃ₜ Y) (x : Conf n X) (i : Fin n) :
    mapHomeomorph e x i = e (x i) := rfl

end Map

end Conf
