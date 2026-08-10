import QuotientSubmoduleEquidistribution.RepresentationTheory.LeftCoordinateProjectiveDuality
import QuotientSubmoduleEquidistribution.RepresentationTheory.RejectiveHighestWeight

/-!
# Ordered highest-weight structure from a legal subobject deletion

This file instantiates the abstract coreflector-cokernel construction with
finite-projective Hom duality.  The standard modules are literal left modules
over the original skeleton Auslander algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.CPSLeftStandardLayers.Coordinate

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalSubobjectDeletionChain
open QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent
open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe uR uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Fintype κ]

local notation "Γ" => skeletonAuslanderAlgebra σ

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

local instance highestWeight_rightTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

local instance highestWeight_leftTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (LeftFiniteProjectives Γ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (regularHomDualityEquivalence Γ)

/-- All concrete input for the abstract right-rejective highest-weight
constructor, obtained from a legal subobject-deletion chain by Hom duality. -/
def legalSubobjectCoordinateHighestWeightInput
    (hsource : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (hleft : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (d : LegalSubobjectDeletionChain.Chain σ) :
    Abstract.Input (A := Γ) d.toSaturatedSupport where
  projective := leftCoordinateProjective σ
  simple := leftCoordinateSimple σ
  simple_isSimple := leftCoordinateSimple_isSimple σ hleft
  simple_complete := leftCoordinateSimple_complete σ hleft
  simple_nodup := by
    rintro i j ⟨e⟩
    exact leftCoordinateSimple_eq_of_iso σ hleft e
  hom_projective_simple_eq_zero_of_ne :=
    hom_leftCoordinateSimple_eq_zero_of_ne σ hleft
  cover := leftCoordinateProjectiveCover σ hleft
  coverIso := fun _ ↦ Iso.refl _
  finiteLength := hleft
  term := dualTargetRightRejectiveProperty σ hsource d
  termData := fun i ↦
    (dualTargetRightRejectiveProperty_isRightRejective
      σ hsource d i).some
  coordinate_mem := fun i j hj ↦
    leftCoordinateProjective_mem_dualTarget σ hsource d i j hj
  presentation := by
    intro i X hX
    let P := leftCoordinateAddPresentation_of_mem_dualTarget
      σ hsource d i X hX
    exact {
      index := P.index
      label := P.label
      mem := P.mem
      iso := P.iso }

/-- Every legal subobject-deletion chain supplies the literal ordered
highest-weight structure on left modules over its skeleton Auslander
algebra. -/
def legalSubobjectCoordinateOrderedHighestWeightStructure
    (hsource : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (hleft : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (d : LegalSubobjectDeletionChain.Chain σ) :
    OrderedHighestWeightStructure
      (ModuleCat.{wR} Γ) (Fin (Fintype.card κ)) :=
  (legalSubobjectCoordinateHighestWeightInput σ hsource hleft d).orderedHighestWeightStructure

/-- The same construction is left strongly quasi-hereditary: its standard
kernels are objects of the finite-projective left-module category. -/
def legalSubobjectCoordinateLeftStronglyQuasiHereditaryStructure
    (hsource : ∀ X : FGModuleCat.{wR} R, IsFiniteLength R X)
    (hleft : ∀ i : κ,
      IsFiniteLength Γ (leftCoordinateProjective σ i).obj)
    (d : LegalSubobjectDeletionChain.Chain σ) :
    RightStronglyQuasiHereditaryStructure
      (ModuleCat.{wR} Γ) (Fin (Fintype.card κ)) :=
  (legalSubobjectCoordinateHighestWeightInput
    σ hsource hleft d).rightStronglyQuasiHereditaryStructure

/-- If the source ring and its skeleton Auslander algebra are Artinian, the
two finite-length inputs are automatic. -/
def legalSubobjectCoordinateOrderedHighestWeightStructureOfIsArtinian
    [IsArtinianRing R] [IsArtinianRing Γ]
    (d : LegalSubobjectDeletionChain.Chain σ) :
    OrderedHighestWeightStructure
      (ModuleCat.{wR} Γ) (Fin (Fintype.card κ)) :=
  legalSubobjectCoordinateOrderedHighestWeightStructure σ
    (fun X ↦
      ((IsArtinianRing.tfae R X).out 0 3).mp
        (inferInstance : Module.Finite R X))
    (fun i ↦
      ((IsArtinianRing.tfae Γ
        (leftCoordinateProjective σ i).obj).out 0 3).mp
          (leftCoordinateProjective_isFiniteProjective σ i).1)
    d

/-- Artinianity also gives the paper's left-strongly
quasi-hereditary conclusion without any additional layer hypothesis. -/
def legalSubobjectCoordinateLeftStronglyQuasiHereditaryStructureOfIsArtinian
    [IsArtinianRing R] [IsArtinianRing Γ]
    (d : LegalSubobjectDeletionChain.Chain σ) :
    RightStronglyQuasiHereditaryStructure
      (ModuleCat.{wR} Γ) (Fin (Fintype.card κ)) :=
  legalSubobjectCoordinateLeftStronglyQuasiHereditaryStructure σ
    (fun X ↦
      ((IsArtinianRing.tfae R X).out 0 3).mp
        (inferInstance : Module.Finite R X))
    (fun i ↦
      ((IsArtinianRing.tfae Γ
        (leftCoordinateProjective σ i).obj).out 0 3).mp
          (leftCoordinateProjective_isFiniteProjective σ i).1)
    d

end QuotientSubmoduleEquidistribution.CPSLeftStandardLayers.Coordinate
