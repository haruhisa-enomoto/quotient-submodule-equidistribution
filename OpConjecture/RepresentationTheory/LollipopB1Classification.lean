import OpConjecture.RepresentationTheory.LollipopB1SevenBlockExpansion
import OpConjecture.RepresentationTheory.LollipopB1NormalModuleIso
import OpConjecture.RepresentationTheory.LollipopB1ClassificationBridge
import OpConjecture.RepresentationTheory.LollipopB1ClassificationAssembly

/-!
# Complete live-path seven-block classification

This file identifies the multiplicity spaces selected by a splitting
flag with the abstract seven-space input of `SevenBlockExpansion`.  It then
joins the normal-form isomorphism, the basis expansion, and the classification
bridge, and instantiates the faithful-core and relation-table assembly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace OpConjecture.LollipopConcrete.B1.ModuleLayer.B1Classification

open ExhaustivenessReduction

universe u

variable (K : Type u) [Field K]

namespace SplittingFlag

variable {K}

/-- The seven multiplicity spaces carried by a splitting flag. -/
def multiplicitySpaces (D : FiniteB1Rep K)
    (F : ExhaustivenessReduction.SplittingFlag K D) :
    SevenBlockExpansion.MultiplicitySpaces K where
  x := FGModuleCat.of K (ExhaustivenessReduction.SplittingFlag.xSpace D)
  u := FGModuleCat.of K (ExhaustivenessReduction.SplittingFlag.uSpace D F)
  w := FGModuleCat.of K (ExhaustivenessReduction.SplittingFlag.wSpace D F)
  p := FGModuleCat.of K (ExhaustivenessReduction.SplittingFlag.pSpace D F)
  s1 := FGModuleCat.of K F.s1Space
  a := FGModuleCat.of K F.aSpace
  s2 := FGModuleCat.of K F.residualTail

/-- With raw `P` target coordinates ordered as `(lower, top)`, the two
normal representations agree literally.  The subsequent block expansion
swaps these raw coordinates when mapping to the displayed `P` module. -/
theorem expansionNormalRep_eq (D : FiniteB1Rep K)
    (F : ExhaustivenessReduction.SplittingFlag K D) :
    SevenBlockExpansion.normalRep K (multiplicitySpaces D F) =
      ExhaustivenessReduction.SplittingFlag.normalRep D F := by
  rfl

/-- Explicit module-level alignment, kept separate so the orientation of the
normal-form isomorphism is visible in the final composition. -/
def expansionNormalModuleIso (D : FiniteB1Rep K)
    (F : ExhaustivenessReduction.SplittingFlag K D) :
    FiniteB1Rep.asFGModule K
        (ExhaustivenessReduction.SplittingFlag.normalRep D F) ≅
      FiniteB1Rep.asFGModule K
        (SevenBlockExpansion.normalRep K (multiplicitySpaces D F)) :=
  eqToIso <| congrArg (FiniteB1Rep.asFGModule K)
    (expansionNormalRep_eq D F).symm

end SplittingFlag

/-- Convert the block-expansion tags to the relation-table labels. -/
def blockLabel : SevenBlockExpansion.BlockTag →
    SevenObjectAdapter.Label
  | .s1 => .s1
  | .s2 => .s2
  | .x => .x
  | .a => .a
  | .u => .u
  | .w => .w
  | .p => .p

theorem namedBlockModule_eq_obj
    (S : SevenBlockExpansion.MultiplicitySpaces K)
    (i : SevenBlockExpansion.BlockIndex K S) :
    SevenBlockExpansion.namedBlockModule K S i =
      SevenObjectAdapter.obj K (blockLabel i.1) := by
  rcases i with ⟨t, j⟩
  cases t <;> rfl

/-- The expansion endpoint with its tags translated to the table labels. -/
def expansionNamedBiproductIso
    (S : SevenBlockExpansion.MultiplicitySpaces K) :
    FiniteB1Rep.asFGModule K (SevenBlockExpansion.normalRep K S) ≅
      biproduct (fun i : SevenBlockExpansion.BlockIndex K S ↦
        SevenObjectAdapter.obj K (blockLabel i.1)) :=
  SevenBlockExpansion.normalNamedBiproductIso K S ≪≫
    biproduct.mapIso (fun i ↦
      eqToIso (namedBlockModule_eq_obj K S i))

/-- A splitting flag gives a genuine-module decomposition of the original
finite representation into copies of the seven displayed modules. -/
def finiteRepNamedBiproductIso (D : FiniteB1Rep K)
    (F : ExhaustivenessReduction.SplittingFlag K D) :
    FiniteB1Rep.asFGModule K D ≅
      biproduct
        (fun i : SevenBlockExpansion.BlockIndex K
            (SplittingFlag.multiplicitySpaces D F) ↦
          SevenObjectAdapter.obj K (blockLabel i.1)) :=
  (ExhaustivenessReduction.SplittingFlag.normalModuleIso D F).symm ≪≫
    SplittingFlag.expansionNormalModuleIso D F ≪≫
      expansionNamedBiproductIso K (SplittingFlag.multiplicitySpaces D F)

/-- Package the selected splitting flag in the deliberately weak interface
consumed by the classification bridge. -/
def sevenBiproductDecomposition (D : FiniteB1Rep K)
    (F : ExhaustivenessReduction.SplittingFlag K D) :
    ClassificationBridge.SevenBiproductDecomposition K D where
  index := SevenBlockExpansion.BlockIndex K
    (SplittingFlag.multiplicitySpaces D F)
  indexFintype := inferInstance
  label i := blockLabel i.1
  iso := by
    exact ⟨finiteRepNamedBiproductIso K D F⟩

/-- Final join: every finite live-path representation has a finite
seven-object biproduct decomposition. -/
theorem finiteRepSevenDecomposition :
    ClassificationBridge.FiniteRepSevenDecomposition K := by
  intro D
  obtain ⟨F⟩ := ExhaustivenessReduction.exists_splittingFlag K D
  exact ⟨sevenBiproductDecomposition K D F⟩

/-! ## Unconditional classification, faithful cores, and table data -/

/-- The complete duplicate-free seven-object live-path classification. -/
theorem classification : SevenObjectAdapter.Classification K :=
  ClassificationBridge.classification K (finiteRepSevenDecomposition K)

theorem indecomposable_iso_exactly_one
    (M : FGModuleCat.{u} (B1Model K))
    (hM : OpConjecture.Foundation.IsIndecomposableModule (B1Model K) M) :
    ∃! i : SevenObjectAdapter.Label,
      Nonempty (M ≅ SevenObjectAdapter.obj K i) :=
  ClassificationBridge.indecomposable_iso_exactly_one K
    (finiteRepSevenDecomposition K) M hM

def indecomposableSkeleton :=
  B1ClassificationAssembly.indecomposableSkeleton K (classification K)

def quotientCoreData :=
  B1ClassificationAssembly.quotientCoreData K (classification K)

def submoduleCoreData :=
  B1ClassificationAssembly.submoduleCoreData K (classification K)

theorem quotientCoreData_core_eq :
    ((quotientCoreData K).core : Set SevenObjectAdapter.Label) =
      SevenObjectAdapter.quotientCore :=
  B1ClassificationAssembly.quotientCoreData_core_eq K (classification K)

theorem submoduleCoreData_core_eq :
    ((submoduleCoreData K).core : Set SevenObjectAdapter.Label) =
      SevenObjectAdapter.submoduleCore :=
  B1ClassificationAssembly.submoduleCoreData_core_eq K (classification K)

/-- All eight live-path rows for the actual faithful cores. -/
def livePathCertificates :=
  B1ClassificationAssembly.livePathCertificates K (classification K)

/-- The unconditional connected-small-core table package. -/
def tableData :=
  B1ClassificationAssembly.tableData K (classification K)

/-- The actual quotient- and submodule-faithful degree-four counts agree. -/
theorem faithfulLevelCount_four_eq :
    BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (indecomposableSkeleton K).qClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (indecomposableSkeleton K).obj) 4 =
      BottomLevels.MinimalFaithfulCore.faithfulLevelCount
        (indecomposableSkeleton K).sClosure
        (AnnihilatorInflation.IsFaithfulSupport
          (indecomposableSkeleton K).obj) 4 :=
  B1ClassificationAssembly.faithfulLevelCount_four_eq K
    (classification K)

end OpConjecture.LollipopConcrete.B1.ModuleLayer.B1Classification
