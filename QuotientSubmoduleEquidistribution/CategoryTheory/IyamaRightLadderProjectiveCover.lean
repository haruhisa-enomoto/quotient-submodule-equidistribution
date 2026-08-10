import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaKrullSchmidtWeight
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderRadicalResolution

/-!
# Simple-top multiplicities in Iyama right-ladder resolutions

This file turns the retract formulation of the objectwise radical-layer
resolution into the literal multiplicity statement used in the manuscript.
The multiplicity is read from the canonical finite Krull--Schmidt
decomposition; its value is independent of that noncomputable choice.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteRightTauCategoryData

variable (T : FiniteRightTauCategoryData C Ind)

/-- Multiplicity of a chosen indecomposable label in the canonical finite
decomposition of an object. -/
def chosenLabelMultiplicity [DecidableEq Ind] (p : Ind) (X : C) : ℕ :=
  ∑ i, if T.chosenDecompositionLabel X i = p then 1 else 0

/-- A label has positive canonical multiplicity exactly when its chosen
indecomposable is a retract of the object. -/
theorem chosenLabelMultiplicity_pos_iff_retract
    [DecidableEq Ind] (p : Ind) (X : C) :
    0 < T.chosenLabelMultiplicity p X ↔
      Nonempty (Retract (T.obj p) X) := by
  constructor
  · intro hpos
    rw [chosenLabelMultiplicity, Finset.sum_pos_iff] at hpos
    obtain ⟨i, _hi, hterm⟩ := hpos
    have hlabel : T.chosenDecompositionLabel X i = p := by
      by_contra hne
      simp [hne] at hterm
    let ep : T.obj p ≅ T.obj (T.chosenDecompositionLabel X i) :=
      eqToIso (congrArg T.obj hlabel.symm)
    let eX := T.chosenDecompositionIso X
    refine ⟨{
      i := ep.hom ≫
        biproduct.ι (fun j ↦ T.obj (T.chosenDecompositionLabel X j)) i ≫
          eX.inv
      r := eX.hom ≫
        biproduct.π (fun j ↦ T.obj (T.chosenDecompositionLabel X j)) i ≫
          ep.inv
      retract := ?_ }⟩
    simp [Category.assoc]
  · rintro ⟨d⟩
    let eX := T.chosenDecompositionIso X
    let inc : T.obj p ⟶
        ⨁ fun i ↦ T.obj (T.chosenDecompositionLabel X i) :=
      d.i ≫ eX.hom
    let ret : (⨁ fun i ↦ T.obj (T.chosenDecompositionLabel X i)) ⟶
        T.obj p := eX.inv ≫ d.r
    have hret : inc ≫ ret = 𝟙 (T.obj p) := by
      simp [inc, ret, Category.assoc, d.retract]
    obtain ⟨i, hi⟩ :=
      T.exists_isIso_component_of_retraction_finBiproduct p
        (T.chosenDecompositionSize X) (T.chosenDecompositionLabel X)
        inc ret hret
    have hlabel : p = T.chosenDecompositionLabel X i :=
      T.obj_skeletal ⟨asIso
        (inc ≫ biproduct.π
          (fun j ↦ T.obj (T.chosenDecompositionLabel X j)) i)⟩
    rw [chosenLabelMultiplicity, Finset.sum_pos_iff]
    exact ⟨i, Finset.mem_univ i, by simp [hlabel]⟩

/-- The zero-initial right ladder gives the exact simple-top multiplicity
criterion for every radical layer. -/
theorem zeroInitialRightLadder_layerNonzero_iff_multiplicity_pos
    [DecidableEq Ind]
    (T : FiniteRightTauCategoryData C Ind) (X : C) (n : ℕ) (p : Ind) :
    let L := RightLadder.zeroInitialRightLadder T X
    T.radical.LayerNonzero n (T.obj p) X ↔
      0 < T.chosenLabelMultiplicity p (L.Y n) := by
  let L := RightLadder.zeroInitialRightLadder T X
  have hLayer :=
    QuotientSubmoduleEquidistribution.Iyama.RightLadder.FiniteRightTauCategoryData.zeroInitialRightLadder_layerNonzero_iff_retract
      T X n p
  exact hLayer.trans
    (T.chosenLabelMultiplicity_pos_iff_retract p (L.Y n)).symm

end FiniteRightTauCategoryData

end QuotientSubmoduleEquidistribution.Iyama
