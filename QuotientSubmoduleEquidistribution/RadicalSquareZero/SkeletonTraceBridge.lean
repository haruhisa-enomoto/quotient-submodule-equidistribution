import QuotientSubmoduleEquidistribution.RepresentationTheory.Trace
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedTrace

/-!
# From skeleton trace to separated top coverage

The quotient closure on an indecomposable skeleton uses maps from arbitrary
finite direct sums of selected representatives.  The separated-data trace
comparison is naturally stated for the family of the selected representatives
themselves.  This file proves that the two traces are equal and consequently
expresses actual quotient-closure membership as separated top coverage.
-/

set_option autoImplicit false

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedTrace

open QuotientSubmoduleEquidistribution.ModuleRadicalLayerComparison
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedData
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedCorrespondence
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedModuleFunctor

universe u v w x

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Regard the representatives selected by a set of skeleton labels as a
family of ordinary module-category objects. -/
def skeletonSelectedFamily
    [IsNoetherianRing (TrivSqZeroExt S J)]
    {I : Type x}
    (sigma : IndecomposableSkeleton.{max u v, x, w}
      (TrivSqZeroExt S J) I)
    (T : Set I) :
    {i : I // i ∈ T} → ModuleCat.{w} (TrivSqZeroExt S J) :=
  fun i ↦ (sigma.obj i.1).obj

private theorem fg_hom_sum_apply
    {R : Type*} [Ring R]
    {A : Type*} [Fintype A]
    {X Y : FGModuleCat.{w} R} (f : A → (X ⟶ Y)) (x : X) :
    ((∑ a, f a).hom.hom) x =
      ∑ a, (f a).hom.hom x := by
  have h₁ :
      (∑ a, f a).hom = ∑ a, (f a).hom :=
    map_sum
      (InducedCategory.homAddEquiv :
        (X ⟶ Y) ≃+ (X.obj ⟶ Y.obj))
      f Finset.univ
  rw [h₁, ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ x

/-- Maps from finite direct sums of selected representatives generate the
same trace as the family of all maps from the individual selected
representatives. -/
theorem skeletonTrace_eq_moduleFamilyTrace
    [IsNoetherianRing (TrivSqZeroExt S J)]
    {I : Type x}
    (sigma : IndecomposableSkeleton.{max u v, x, w}
      (TrivSqZeroExt S J) I)
    (T : Set I) (Y : FGModuleCat.{w} (TrivSqZeroExt S J)) :
    sigma.trace T Y =
      moduleFamilyTrace (skeletonSelectedFamily sigma T) Y.obj := by
  apply le_antisymm
  · rw [IndecomposableSkeleton.trace, moduleFamilyTrace]
    apply iSup_le
    intro g
    letI : Fintype g.index := FintypeCat.fintype
    rintro _ ⟨y, rfl⟩
    have hmap :
        g.map =
          ∑ t : g.index,
            biproduct.π
                (fun t : g.index ↦ sigma.obj (g.label t)) t ≫
              (biproduct.ι
                  (fun t : g.index ↦ sigma.obj (g.label t)) t ≫
                g.map) := by
      calc
        g.map = 𝟙 _ ≫ g.map := (Category.id_comp _).symm
        _ =
            (∑ t : g.index,
              biproduct.π
                  (fun t : g.index ↦ sigma.obj (g.label t)) t ≫
                biproduct.ι
                  (fun t : g.index ↦ sigma.obj (g.label t)) t) ≫
              g.map := by rw [biproduct.total]
        _ = _ := by
          rw [Preadditive.sum_comp]
          simp only [Category.assoc]
    rw [hmap, fg_hom_sum_apply]
    apply Submodule.sum_mem
    intro t _
    let ft : sigma.obj (g.label t) ⟶ Y :=
      biproduct.ι
        (fun t : g.index ↦ sigma.obj (g.label t)) t ≫ g.map
    have hmem :
        ft ((biproduct.π
          (fun t : g.index ↦ sigma.obj (g.label t)) t) y) ∈
          LinearMap.range ft.hom.hom :=
      LinearMap.mem_range_self ft.hom.hom _
    have hrange :
        LinearMap.range ft.hom.hom ≤
          moduleTrace (sigma.obj (g.label t)).obj Y.obj :=
      le_iSup
        (fun f : (sigma.obj (g.label t)).obj ⟶ Y.obj ↦
          LinearMap.range f.hom) ft.hom
    have hfamily :
        moduleTrace (sigma.obj (g.label t)).obj Y.obj ≤
          moduleFamilyTrace (skeletonSelectedFamily sigma T) Y.obj :=
      le_iSup
        (fun i : {i : I // i ∈ T} ↦
          moduleTrace (skeletonSelectedFamily sigma T i) Y.obj)
        ⟨g.label t, g.mem t⟩
    exact hfamily (hrange hmem)
  · rw [moduleFamilyTrace]
    apply iSup_le
    intro i
    rw [moduleTrace]
    apply iSup_le
    intro f
    let fFG : sigma.obj i.1 ⟶ Y := ⟨f⟩
    exact IndecomposableSkeleton.range_le_trace_of_mem
      sigma i.2 fFG

/-- Actual quotient-closure membership is exactly separated-data top
coverage by the selected indecomposable family. -/
theorem mem_qClosure_iff_separatedDataFamilyTopTrace_eq_top
    [IsNoetherianRing (TrivSqZeroExt S J)] [IsSemisimpleRing S]
    {I : Type x}
    (sigma : IndecomposableSkeleton.{max u v, x, w}
      (TrivSqZeroExt S J) I)
    (T : Set I) (j : I) :
    j ∈ sigma.qClosure T ↔
      separatedDataFamilyTopTrace
        (fun i : {i : I // i ∈ T} ↦
          moduleSeparatedData (S := S) (J := J)
          ((sigma.obj i.1).obj))
        (moduleSeparatedData (S := S) (J := J)
          ((sigma.obj j).obj)) = ⊤ := by
  rw [IndecomposableSkeleton.mem_qClosure_iff_trace_eq_top]
  rw [skeletonTrace_eq_moduleFamilyTrace]
  exact moduleFamilyTrace_eq_top_iff_separatedDataFamilyTopTrace_eq_top
    (skeletonSelectedFamily sigma T) (sigma.obj j).obj

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedTrace
