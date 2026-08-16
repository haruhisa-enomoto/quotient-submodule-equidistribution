import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaLadderRadical
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtNormalForm
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaNakayamaStrictnessBridge
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaRepresentableMesh
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Representable mesh exactness in a finite tau-category

This file supplies the literal categorical version of the representable
mesh calculation used in the manuscript.  The simple quotient is constructed
from the categorical radical, its diagonal/off-diagonal dimensions are
proved, and right tau-sequences give exactness after evaluation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.Iyama

open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh

universe uK v u w

variable {K : Type uK} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

namespace FiniteTauCategoryData

variable (T : FiniteTauCategoryData C Ind)

/-- The chosen categorical radical as a linear subspace of one Hom space. -/
def radicalHomSubmodule (a x : Ind) : Submodule K (T.obj a ⟶ T.obj x) where
  carrier := T.radical.ideal.hom (T.obj a) (T.obj x)
  zero_mem' := (T.radical.ideal.hom (T.obj a) (T.obj x)).zero_mem
  add_mem' := (T.radical.ideal.hom (T.obj a) (T.obj x)).add_mem
  smul_mem' := by
    intro c f hf
    have hcomp := T.radical.ideal.postcomp (c • 𝟙 (T.obj x)) hf
    simpa using hcomp

@[simp]
theorem mem_radicalHomSubmodule_iff (a x : Ind)
    (f : T.obj a ⟶ T.obj x) :
    f ∈ T.radicalHomSubmodule (K := K) a x ↔
      CategoricalRadical.IsRadicalMorphism f :=
  T.radical.mem_ideal_iff f

/-- The radical quotient of a representable Hom space. -/
abbrev RadicalSimpleFiber (a x : Ind) :=
  (T.obj a ⟶ T.obj x) ⧸ T.radicalHomSubmodule (K := K) a x

/-- Distinct chosen indecomposables have only radical morphisms between
them. -/
theorem radicalHomSubmodule_eq_top_of_ne {a x : Ind} (hax : a ≠ x) :
    T.radicalHomSubmodule (K := K) a x = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro f
  rw [mem_radicalHomSubmodule_iff]
  apply (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj f).2
  intro hf
  letI : IsSplitEpi f := hf
  let s : T.obj x ⟶ T.obj a := section_ f
  have hs : IsSplitMono s := inferInstance
  letI : IsSplitMono s := hs
  haveI : IsIso s := T.isIso_of_isSplitMono_obj_obj s
  exact hax (T.obj_skeletal ⟨asIso s⟩).symm

/-- Scalar residue endomorphisms give the expected one-dimensional diagonal
simple and zero off the diagonal. -/
theorem finrank_radicalSimpleFiber
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x)
    (a x : Ind) :
    Module.finrank K (T.RadicalSimpleFiber (K := K) a x) =
      if a = x then 1 else 0 := by
  by_cases hax : a = x
  · subst x
    simp only [if_pos]
    let v : T.RadicalSimpleFiber (K := K) a a :=
      (T.radicalHomSubmodule (K := K) a a).mkQ (𝟙 (T.obj a))
    have hv : v ≠ 0 := by
      intro hv0
      have hidRad :
          (𝟙 (T.obj a) : T.obj a ⟶ T.obj a) ∈
            T.radicalHomSubmodule (K := K) a a := by
        simpa [v] using
          (Submodule.Quotient.mk_eq_zero
            (T.radicalHomSubmodule (K := K) a a)).1 hv0
      have hnot :=
        (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj
          (𝟙 (T.obj a))).1
          ((T.mem_radicalHomSubmodule_iff (K := K) a a
            (𝟙 (T.obj a))).1 hidRad)
      exact hnot inferInstance
    apply finrank_eq_one v hv
    intro q
    obtain ⟨f, rfl⟩ :=
      (T.radicalHomSubmodule (K := K) a a).mkQ_surjective q
    obtain ⟨c, hc⟩ := scalar_mod_radical a f
    refine ⟨c, ?_⟩
    apply (Submodule.Quotient.eq
      (T.radicalHomSubmodule (K := K) a a)).2
    simpa [v] using
      (T.radicalHomSubmodule (K := K) a a).neg_mem hc
  · simp only [if_neg hax]
    letI : Subsingleton (T.RadicalSimpleFiber (K := K) a x) :=
      ⟨fun q r ↦ by
        obtain ⟨f, rfl⟩ :=
          (T.radicalHomSubmodule (K := K) a x).mkQ_surjective q
        obtain ⟨g, rfl⟩ :=
          (T.radicalHomSubmodule (K := K) a x).mkQ_surjective r
        apply (Submodule.Quotient.eq
          (T.radicalHomSubmodule (K := K) a x)).2
        rw [T.radicalHomSubmodule_eq_top_of_ne (K := K) hax]
        exact Submodule.mem_top⟩
    exact Module.finrank_zero_of_subsingleton

/-- A noncanonical identification of the categorical radical quotient with
the standard one-dimensional diagonal fiber used by the numerical mesh
interface. -/
def radicalSimpleFiberLinearEquiv
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x)
    (a x : Ind) :
    T.RadicalSimpleFiber (K := K) a x ≃ₗ[K]
      SimpleRepresentableFiber K a x :=
  LinearEquiv.ofFinrankEq (R := K) _ _
    (by
      rw [T.finrank_radicalSimpleFiber (K := K) scalar_mod_radical]
      exact (finrank_simpleRepresentableFiber (K := K) a x).symm)

/-- The simple quotient map on a chosen representable Hom space. -/
def categoricalSimpleQuotient
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x)
    (a x : Ind) :
    (T.obj a ⟶ T.obj x) →ₗ[K] SimpleRepresentableFiber K a x :=
  (T.radicalSimpleFiberLinearEquiv (K := K) scalar_mod_radical a x).toLinearMap.comp
    (T.radicalHomSubmodule (K := K) a x).mkQ

/-- The second map of the chosen right mesh, transported to its literal
chosen endpoint representative. -/
def representableMeshMu (x : Ind) :
    T.thetaPlus x ⟶ T.obj x :=
  T.muPlus x ≫ (T.rightTermIso (T.obj x)).hom

/-- Evaluating a right tau-sequence is exact at its middle term after the
right endpoint is transported to the chosen representative. -/
theorem exact_at_representableMesh_middle (a x : Ind) :
    Function.Exact
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := T.obj a) (T.nuPlus x))
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := T.obj a) (T.representableMeshMu x)) := by
  intro f
  constructor
  · intro hf
    change f ≫ (T.muPlus x ≫ (T.rightTermIso (T.obj x)).hom) = 0 at hf
    have hfg : f ≫ T.muPlus x = 0 := by
      apply (cancel_mono (T.rightTermIso (T.obj x)).hom).1
      simpa only [Category.assoc, zero_comp] using hf
    exact (T.rightTau (T.obj x)).exact_postcomp (T.obj a) f |>.mp hfg
  · rintro ⟨g, rfl⟩
    change (g ≫ T.nuPlus x) ≫
      (T.muPlus x ≫ (T.rightTermIso (T.obj x)).hom) = 0
    change (g ≫ (T.rightMesh (T.obj x)).f) ≫
      ((T.rightMesh (T.obj x)).g ≫
        (T.rightTermIso (T.obj x)).hom) = 0
    calc
      (g ≫ (T.rightMesh (T.obj x)).f) ≫
          ((T.rightMesh (T.obj x)).g ≫
            (T.rightTermIso (T.obj x)).hom) =
          g ≫ ((T.rightMesh (T.obj x)).f ≫
            (T.rightMesh (T.obj x)).g) ≫
              (T.rightTermIso (T.obj x)).hom := by simp [Category.assoc]
      _ = 0 := by rw [(T.rightMesh (T.obj x)).zero]; simp

/-- The image of the evaluated second mesh map is exactly the categorical
radical. -/
theorem range_representableMeshMu_eq_radical (a x : Ind) :
    LinearMap.range
        (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
          (K := K) (X := T.obj a) (T.representableMeshMu x)) =
      T.radicalHomSubmodule (K := K) a x := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [mem_radicalHomSubmodule_iff]
    change CategoricalRadical.IsRadicalMorphism
      (g ≫ (T.rightMesh (T.obj x)).g ≫
        (T.rightTermIso (T.obj x)).hom)
    simpa only [Category.assoc] using
      (CategoricalRadical.isRadicalMorphism_postcomp
        (T.rightTermIso (T.obj x)).hom
        (CategoricalRadical.isRadicalMorphism_precomp g
          (T.rightTau (T.obj x)).g_radical))
  · intro hf
    have hfRad : CategoricalRadical.IsRadicalMorphism f :=
      (T.mem_radicalHomSubmodule_iff (K := K) a x f).1 hf
    let e := T.rightTermIso (T.obj x)
    have hf'Rad : CategoricalRadical.IsRadicalMorphism (f ≫ e.inv) :=
      CategoricalRadical.isRadicalMorphism_postcomp e.inv hfRad
    obtain ⟨g, hg⟩ :=
      (T.rightTau (T.obj x)).factors_into_right (f ≫ e.inv) hf'Rad
    refine ⟨g, ?_⟩
    change g ≫ T.muPlus x ≫ e.hom = f
    rw [← Category.assoc, hg, Category.assoc, e.inv_hom_id,
      Category.comp_id]

/-- Exactness at the right representable term and its simple quotient. -/
theorem exact_at_representableMesh_right
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x)
    (a x : Ind) :
    Function.Exact
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := T.obj a) (T.representableMeshMu x))
      (T.categoricalSimpleQuotient (K := K) scalar_mod_radical a x) := by
  rw [LinearMap.exact_iff, T.range_representableMeshMu_eq_radical (K := K)]
  apply le_antisymm
  · intro f hf
    change (T.categoricalSimpleQuotient (K := K)
      scalar_mod_radical a x) f = 0 at hf
    change (T.radicalSimpleFiberLinearEquiv (K := K)
      scalar_mod_radical a x)
        ((T.radicalHomSubmodule (K := K) a x).mkQ f) = 0 at hf
    have hmk : (T.radicalHomSubmodule (K := K) a x).mkQ f = 0 := by
      apply (T.radicalSimpleFiberLinearEquiv (K := K)
        scalar_mod_radical a x).injective
      simpa using hf
    exact (Submodule.Quotient.mk_eq_zero _).1 hmk
  · intro f hf
    change (T.radicalSimpleFiberLinearEquiv (K := K)
      scalar_mod_radical a x)
        ((T.radicalHomSubmodule (K := K) a x).mkQ f) = 0
    have hmk : (T.radicalHomSubmodule (K := K) a x).mkQ f = 0 := by
      change Submodule.Quotient.mk f = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hf
    rw [hmk, map_zero]

/-- The simple quotient map is surjective. -/
theorem categoricalSimpleQuotient_surjective
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x)
    (a x : Ind) :
    Function.Surjective
      (T.categoricalSimpleQuotient (K := K) scalar_mod_radical a x) :=
  (T.radicalSimpleFiberLinearEquiv (K := K)
      scalar_mod_radical a x).surjective.comp
    (T.radicalHomSubmodule (K := K) a x).mkQ_surjective

/-- Every finite tau-category with scalar residue endomorphisms supplies the
literal evaluated representable mesh complexes used in the manuscript. -/
def rightRepresentableMeshComplex
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈ T.radicalHomSubmodule (K := K) x x) :
    RightRepresentableMeshComplex (K := K)
      T.obj (fun x ↦ (T.rightMesh (T.obj x)).X₁) T.thetaPlus where
  nu := T.nuPlus
  mu := T.representableMeshMu
  simpleQuotient := T.categoricalSimpleQuotient (K := K) scalar_mod_radical
  exact_at_middle := T.exact_at_representableMesh_middle (K := K)
  exact_at_right := T.exact_at_representableMesh_right
    (K := K) scalar_mod_radical
  simpleQuotient_surjective :=
    T.categoricalSimpleQuotient_surjective (K := K) scalar_mod_radical

end FiniteTauCategoryData

end QuotientSubmoduleEquidistribution.Iyama
