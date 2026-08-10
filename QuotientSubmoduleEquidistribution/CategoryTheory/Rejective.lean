import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Rejective full subcategories and equivalence transport

Rejectivity itself is purely categorical.  No zero object, additive
structure, kernels, cokernels, or module structure enters its definition or
its invariance under equivalence.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.CategoricalRejective

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

/-- A full subcategory is right rejective when its inclusion has a right
adjoint with componentwise monic counit. -/
structure RightRejectiveData (P : ObjectProperty C) where
  coreflector : C ⥤ P.FullSubcategory
  adjunction : P.ι ⊣ coreflector
  counit_mono : ∀ X : C, Mono (adjunction.counit.app X)

/-- Propositional form of categorical right rejectivity. -/
def IsRightRejective (P : ObjectProperty C) : Prop :=
  Nonempty (RightRejectiveData P)

/-- A full subcategory is left rejective when its inclusion has a left
adjoint with componentwise epic unit. -/
structure LeftRejectiveData (P : ObjectProperty C) where
  reflector : C ⥤ P.FullSubcategory
  adjunction : reflector ⊣ P.ι
  unit_epi : ∀ X : C, Epi (adjunction.unit.app X)

/-- Propositional form of categorical left rejectivity. -/
def IsLeftRejective (P : ObjectProperty C) : Prop :=
  Nonempty (LeftRejectiveData P)

/-- The replete image predicate on the target of an equivalence, expressed
as pullback along its chosen inverse. -/
def imageProperty (E : C ≌ D) (P : ObjectProperty C) :
    ObjectProperty D :=
  P.inverseImage E.inverse

namespace Equivalence

variable (E : C ≌ D) (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms]

instance : (imageProperty E P).IsClosedUnderIsomorphisms :=
  { of_iso := fun e h ↦
      P.prop_of_iso (E.inverse.mapIso e) h }

/-- Restriction of the inverse equivalence functor to the pulled-back
object property. -/
def inverseLift :
    (imageProperty E P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((imageProperty E P).ι ⋙ E.inverse)
    (fun Y ↦ Y.property)

/-- Restriction of the forward equivalence functor.  Repleteness of `P`
supplies membership after applying the unit isomorphism. -/
def forwardLift :
    P.FullSubcategory ⥤
      (imageProperty E P).FullSubcategory :=
  (imageProperty E P).lift (P.ι ⋙ E.functor)
    (fun X ↦
      P.prop_of_iso (E.unitIso.app X.obj) X.property)

/-- The unit of the ambient equivalence restricted to the full
subcategories. -/
def restrictedUnitIso :
    𝟭 P.FullSubcategory ≅
      forwardLift E P ⋙ inverseLift E P :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk P (E.unitIso.app X.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact E.unitIso.hom.naturality f.hom)

/-- The counit of the ambient equivalence restricted to the full
subcategories. -/
def restrictedCounitIso :
    inverseLift E P ⋙ forwardLift E P ≅
      𝟭 (imageProperty E P).FullSubcategory :=
  NatIso.ofComponents
    (fun Y ↦
      ObjectProperty.isoMk (imageProperty E P)
        (E.counitIso.app Y.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact E.counitIso.hom.naturality f.hom)

/-- The equivalence induced on a replete full subcategory. -/
def restricted :
    P.FullSubcategory ≌
      (imageProperty E P).FullSubcategory where
  functor := forwardLift E P
  inverse := inverseLift E P
  unitIso := restrictedUnitIso E P
  counitIso := restrictedCounitIso E P
  functor_unitIso_comp X := by
    apply ObjectProperty.hom_ext
    change
      E.functor.map (E.unitIso.hom.app X.obj) ≫
          E.counitIso.hom.app (E.functor.obj X.obj) =
        𝟙 (E.functor.obj X.obj)
    exact E.functor_unitIso_comp X.obj

/-- The composite of the transported source inclusion with the ambient
equivalence is canonically the target inclusion. -/
def inverseLiftCompInclusionCompFunctorIso :
    (restricted E P).inverse ⋙ P.ι ⋙ E.functor ≅
      (imageProperty E P).ι :=
  NatIso.ofComponents
    (fun Y ↦ E.counitIso.app Y.obj)
    (fun f ↦ E.counitIso.hom.naturality f.hom)

/-- The transported right adjoint. -/
def transportedCoreflector
    (data : RightRejectiveData P) :
    D ⥤ (imageProperty E P).FullSubcategory :=
  E.inverse ⋙ data.coreflector ⋙ (restricted E P).functor

/-- The composite adjunction, with its left adjoint normalized back to the
literal inclusion of the transported full subcategory. -/
def transportedRightAdjunction
    (data : RightRejectiveData P) :
    (imageProperty E P).ι ⊣
      transportedCoreflector E P data :=
  (((restricted E P).symm.toAdjunction.comp data.adjunction).comp
      E.toAdjunction).ofNatIsoLeft
    (inverseLiftCompInclusionCompFunctorIso E P)

/-- The transported left adjoint. -/
def transportedReflector
    (data : LeftRejectiveData P) :
    D ⥤ (imageProperty E P).FullSubcategory :=
  E.inverse ⋙ data.reflector ⋙ (restricted E P).functor

/-- The composite left-rejective adjunction, with its right adjoint
normalized to the target inclusion. -/
def transportedLeftAdjunction
    (data : LeftRejectiveData P) :
    transportedReflector E P data ⊣
      (imageProperty E P).ι :=
  ((E.symm.toAdjunction.comp data.adjunction).comp
      (restricted E P).toAdjunction).ofNatIsoRight
    (inverseLiftCompInclusionCompFunctorIso E P)

/-- The transported counit is monic.  The proof separates the two
composed adjunctions and the final normalization isomorphism, so typeclass
search only sees composites of mapped monomorphisms and isomorphisms. -/
theorem transportedRightAdjunction_counit_mono
    (data : RightRejectiveData P) (X : D) :
    Mono ((transportedRightAdjunction E P data).counit.app X) := by
  let S := restricted E P
  let adj₁ := S.symm.toAdjunction.comp data.adjunction
  let adj₂ := adj₁.comp E.toAdjunction
  let i := inverseLiftCompInclusionCompFunctorIso E P
  letI h₁ (Z : C) : Mono (adj₁.counit.app Z) := by
    dsimp only [adj₁]
    rw [Adjunction.comp_counit_app]
    haveI restrictedCounitIso : IsIso
        (S.symm.toAdjunction.counit.app
          (data.coreflector.obj Z)) := by
      change IsIso
        ((S.symm.counitIso.app
          (data.coreflector.obj Z)).hom)
      infer_instance
    haveI originalCounitMono : Mono (data.adjunction.counit.app Z) :=
      data.counit_mono Z
    haveI mappedRestrictedCounitIso : IsIso
        (P.ι.map
          (S.symm.toAdjunction.counit.app
            (data.coreflector.obj Z))) :=
      Functor.map_isIso _ _
    apply mono_comp'
    · exact @IsIso.mono_of_iso _ _ _ _ _
        mappedRestrictedCounitIso
    · exact data.counit_mono Z
  haveI equivalencePreservesMonos :
      Functor.PreservesMonomorphisms E.functor :=
    Functor.preservesMonomorphisms_of_adjunction
      E.symm.toAdjunction
  letI h₂ (Y : D) : Mono (adj₂.counit.app Y) := by
    dsimp only [adj₂]
    rw [Adjunction.comp_counit_app]
    haveI equivalenceCounitIso :
        IsIso (E.toAdjunction.counit.app Y) := by
      change IsIso ((E.counitIso.app Y).hom)
      infer_instance
    haveI firstCounitMono :
        Mono (adj₁.counit.app (E.inverse.obj Y)) :=
      h₁ (E.inverse.obj Y)
    apply mono_comp'
    · exact
        @Functor.PreservesMonomorphisms.preserves
          _ _ _ _ E.functor equivalencePreservesMonos _ _ _
          firstCounitMono
    · exact @IsIso.mono_of_iso _ _ _ _ _
        equivalenceCounitIso
  change Mono ((adj₂.ofNatIsoLeft i).counit.app X)
  change Mono
    ((Functor.whiskerLeft _ i.inv ≫ adj₂.counit).app X)
  rw [NatTrans.comp_app]
  let H := E.inverse ⋙ data.coreflector ⋙ S.symm.inverse
  haveI inclusionIsoInv : IsIso (i.inv.app (H.obj X)) := by
    change IsIso ((i.app (H.obj X)).inv)
    infer_instance
  haveI normalizationMono :
      Mono ((Functor.whiskerLeft _ i.inv).app X) := by
    change Mono (i.inv.app (H.obj X))
    infer_instance
  apply mono_comp'
  · exact normalizationMono
  · exact h₂ X

/-- The transported unit is epic, by the dual componentwise argument. -/
theorem transportedLeftAdjunction_unit_epi
    (data : LeftRejectiveData P) (X : D) :
    Epi ((transportedLeftAdjunction E P data).unit.app X) := by
  let S := restricted E P
  let adj₁ := E.symm.toAdjunction.comp data.adjunction
  let adj₂ := adj₁.comp S.toAdjunction
  let i := inverseLiftCompInclusionCompFunctorIso E P
  haveI equivalencePreservesEpis :
      Functor.PreservesEpimorphisms E.symm.inverse :=
    Functor.preservesEpimorphisms_of_adjunction
      E.toAdjunction
  letI h₁ (Y : D) : Epi (adj₁.unit.app Y) := by
    dsimp only [adj₁]
    rw [Adjunction.comp_unit_app]
    haveI equivalenceUnitIso :
        IsIso (E.symm.toAdjunction.unit.app Y) := by
      change IsIso ((E.symm.unitIso.app Y).hom)
      infer_instance
    haveI originalUnitEpi : Epi
        (data.adjunction.unit.app (E.symm.functor.obj Y)) :=
      data.unit_epi _
    apply epi_comp'
    · exact @IsIso.epi_of_iso _ _ _ _ _
        equivalenceUnitIso
    · exact
        @Functor.PreservesEpimorphisms.preserves
          _ _ _ _ E.symm.inverse equivalencePreservesEpis _ _ _
          originalUnitEpi
  letI h₂ (Y : D) : Epi (adj₂.unit.app Y) := by
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    haveI restrictedUnitIso : IsIso
        (S.toAdjunction.unit.app
          ((E.symm.functor ⋙ data.reflector).obj Y)) := by
      change IsIso
        ((S.unitIso.app
          ((E.symm.functor ⋙ data.reflector).obj Y)).hom)
      infer_instance
    haveI mappedRestrictedUnitIso : IsIso
        ((P.ι ⋙ E.symm.inverse).map
          (S.toAdjunction.unit.app
            ((E.symm.functor ⋙ data.reflector).obj Y))) :=
      Functor.map_isIso _ _
    apply epi_comp'
    · exact h₁ Y
    · exact @IsIso.epi_of_iso _ _ _ _ _
        mappedRestrictedUnitIso
  change Epi ((adj₂.ofNatIsoRight i).unit.app X)
  change Epi
    ((adj₂.unit ≫ Functor.whiskerLeft _ i.hom).app X)
  rw [NatTrans.comp_app]
  let H := (E.symm.functor ⋙ data.reflector) ⋙ S.functor
  haveI inclusionIsoHom : IsIso (i.hom.app (H.obj X)) := by
    change IsIso ((i.app (H.obj X)).hom)
    infer_instance
  haveI normalizationEpi :
      Epi ((Functor.whiskerLeft _ i.hom).app X) := by
    change Epi (i.hom.app (H.obj X))
    infer_instance
  apply epi_comp'
  · exact h₂ X
  · exact normalizationEpi

/-- Right rejective data transports along a categorical equivalence. -/
def transportRightRejectiveData
    (data : RightRejectiveData P) :
    RightRejectiveData (imageProperty E P) where
  coreflector := transportedCoreflector E P data
  adjunction := transportedRightAdjunction E P data
  counit_mono :=
    transportedRightAdjunction_counit_mono E P data

/-- Left rejective data transports along a categorical equivalence. -/
def transportLeftRejectiveData
    (data : LeftRejectiveData P) :
    LeftRejectiveData (imageProperty E P) where
  reflector := transportedReflector E P data
  adjunction := transportedLeftAdjunction E P data
  unit_epi :=
    transportedLeftAdjunction_unit_epi E P data

/-- Right rejectivity transports in the forward direction. -/
theorem isRightRejective_image
    (h : IsRightRejective P) :
    IsRightRejective (imageProperty E P) :=
  h.map (transportRightRejectiveData E P)

/-- Left rejectivity transports in the forward direction. -/
theorem isLeftRejective_image
    (h : IsLeftRejective P) :
    IsLeftRejective (imageProperty E P) :=
  h.map (transportLeftRejectiveData E P)

/-- Pulling the image predicate back through the inverse equivalence
recovers the original predicate.  Repleteness is the only input. -/
theorem imageProperty_symm_imageProperty_eq :
    imageProperty E.symm (imageProperty E P) = P := by
  funext X
  apply propext
  change
    P (E.inverse.obj (E.functor.obj X)) ↔ P X
  constructor
  · intro h
    exact P.prop_of_iso (E.unitIso.app X).symm h
  · intro h
    exact P.prop_of_iso (E.unitIso.app X) h

/-- Right rejectivity is invariant under categorical equivalence. -/
theorem isRightRejective_iff_image :
    IsRightRejective P ↔
      IsRightRejective (imageProperty E P) := by
  constructor
  · exact isRightRejective_image E P
  · intro h
    have h' :=
      isRightRejective_image E.symm
        (imageProperty E P) h
    simpa only [imageProperty_symm_imageProperty_eq E P]
      using h'

/-- Left rejectivity is invariant under categorical equivalence. -/
theorem isLeftRejective_iff_image :
    IsLeftRejective P ↔
      IsLeftRejective (imageProperty E P) := by
  constructor
  · exact isLeftRejective_image E P
  · intro h
    have h' :=
      isLeftRejective_image E.symm
        (imageProperty E P) h
    simpa only [imageProperty_symm_imageProperty_eq E P]
      using h'

end Equivalence

end QuotientSubmoduleEquidistribution.CategoricalRejective


