import QuotientSubmoduleEquidistribution.RepresentationTheory.IndecomposableBiproduct
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0ModuleExtraction
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0ExhaustivenessReduction
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0FiveObjectAdapter

/-!
# Classification of modules over the dead-path lollipop

Every finite representation of the dead-path lollipop algebra has a
five-block normal form.  Extracting such a representation from an arbitrary
finitely generated module and applying the indecomposable-summand theorem
proves that the five displayed modules exhaust the indecomposables.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.B0Classification

open ModuleExtraction
open ExhaustivenessReduction
open ExhaustivenessReduction.SplittingFlag
open FiveObjectAdapter

universe u

variable (K : Type u) [Field K]

/-- Translation from normal-form block tags to the maintained five-object
table labels. -/
def blockTagLabel : BlockTag → Label
  | .s1 => .s1
  | .s2 => .s2
  | .x => .x
  | .a => .a
  | .p => .p

theorem namedBlockModule_eq_obj
    (D : FiniteB0Rep K) (F : SplittingFlag K D)
    (i : BlockIndex D F) :
    namedBlockModule D F i = obj K (blockTagLabel i.1) := by
  rcases i with ⟨t, j⟩
  cases t <;> rfl

/-- The five displayed modules exhaust all indecomposable finitely generated
modules over the dead-path lollipop algebra. -/
theorem classification : Classification K := by
  refine { exhaustive := ?_ }
  intro M hM
  let D := extractedRep K M
  obtain ⟨F⟩ := exists_splittingFlag K D
  let e : M ≅ biproduct (namedBlockModule D F) :=
    (extractedModuleIso K M).symm ≪≫
      finiteRepNamedBiproductIso D F
  have hblock :
      ∀ i, QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        (B0Model K) (namedBlockModule D F i) := by
    intro i
    rw [namedBlockModule_eq_obj K D F i]
    exact obj_indecomposable K _
  obtain ⟨i, ⟨hi⟩⟩ :=
    QuotientSubmoduleEquidistribution.IndecomposableBiproduct.exists_iso_summand
      M (b0Module_finiteLength K M) hM
      (namedBlockModule D F) hblock e
  refine ⟨blockTagLabel i.1, ⟨hi ≪≫ ?_⟩⟩
  exact eqToIso (namedBlockModule_eq_obj K D F i)

/-- Literal existence-and-uniqueness form of the five-object
classification. -/
theorem indecomposable_iso_exactly_one
    (M : FGModuleCat.{u} (B0Model K))
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B0Model K) M) :
    ∃! i : Label, Nonempty (M ≅ obj K i) := by
  obtain ⟨i, hi⟩ := (classification K).exhaustive M hM
  refine ⟨i, hi, fun j hj ↦ ?_⟩
  exact obj_eq_of_iso K
    ⟨(Classical.choice hj).symm ≪≫ Classical.choice hi⟩

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.B0Classification
