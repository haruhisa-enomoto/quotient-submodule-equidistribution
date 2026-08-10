import OpConjecture.CategoryTheory.Rejective
import OpConjecture.RepresentationTheory.LiteralTraceRejective

/-!
# Rejectivity transport for module subcategories

This file identifies the module-specific rejective packages with the generic
categorical definitions and transports them through arbitrary equivalences.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u w vD uD

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- The existing module-specific right-rejective package is literally an
instance of the generic categorical package. -/
def rightRejectiveDataToCategorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R))
    (data : RightRejectiveData C) :
    CategoricalRejective.RightRejectiveData C.carrier where
  coreflector := data.coreflector
  adjunction := data.adjunction
  counit_mono := data.counit_mono

/-- Conversely, the generic package on the carrier of a literal additive
subcategory is exactly the existing module-specific package. -/
def rightRejectiveDataOfCategorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R))
    (data : CategoricalRejective.RightRejectiveData C.carrier) :
    RightRejectiveData C where
  coreflector := data.coreflector
  adjunction := data.adjunction
  counit_mono := data.counit_mono

omit [IsNoetherianRing R] in
/-- The specialized and generic propositions for right rejectivity agree. -/
theorem isRightRejective_iff_categorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    IsRightRejective C ↔
      CategoricalRejective.IsRightRejective C.carrier :=
  ⟨Nonempty.map (rightRejectiveDataToCategorical C),
    Nonempty.map (rightRejectiveDataOfCategorical C)⟩

/-- The existing module-specific left-rejective package is literally an
instance of the generic categorical package. -/
def leftRejectiveDataToCategorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R))
    (data : LeftRejectiveData C) :
    CategoricalRejective.LeftRejectiveData C.carrier where
  reflector := data.reflector
  adjunction := data.adjunction
  unit_epi := data.unit_epi

/-- Conversely, generic left-rejective data on the carrier recovers the
existing package. -/
def leftRejectiveDataOfCategorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R))
    (data : CategoricalRejective.LeftRejectiveData C.carrier) :
    LeftRejectiveData C where
  reflector := data.reflector
  adjunction := data.adjunction
  unit_epi := data.unit_epi

omit [IsNoetherianRing R] in
/-- The specialized and generic propositions for left rejectivity agree. -/
theorem isLeftRejective_iff_categorical
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    IsLeftRejective C ↔
      CategoricalRejective.IsLeftRejective C.carrier :=
  ⟨Nonempty.map (leftRejectiveDataToCategorical C),
    Nonempty.map (leftRejectiveDataOfCategorical C)⟩

/-- Retract closure supplies the repleteness instance required by generic
equivalence transport. -/
instance carrier_isClosedUnderIsomorphisms
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    C.carrier.IsClosedUnderIsomorphisms where
  of_iso := fun e h ↦ C.iso_mem e h

variable {D : Type uD} [Category.{vD} D]

omit [IsNoetherianRing R] in
/-- Right rejectivity of the literal module subcategory is equivalent to
generic right rejectivity of its image under any categorical equivalence. -/
theorem isRightRejective_iff_categorical_image
    (E : FGModuleCat.{w} R ≌ D)
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    IsRightRejective C ↔
      CategoricalRejective.IsRightRejective
        (CategoricalRejective.imageProperty E C.carrier) :=
  (isRightRejective_iff_categorical C).trans
    (CategoricalRejective.Equivalence.isRightRejective_iff_image
      E C.carrier)

omit [IsNoetherianRing R] in
/-- Left rejectivity has the same equivalence-invariance bridge. -/
theorem isLeftRejective_iff_categorical_image
    (E : FGModuleCat.{w} R ≌ D)
    (C : AdditiveRepleteSummandSubcategory.{u, w} (R := R)) :
    IsLeftRejective C ↔
      CategoricalRejective.IsLeftRejective
        (CategoricalRejective.imageProperty E C.carrier) :=
  (isLeftRejective_iff_categorical C).trans
    (CategoricalRejective.Equivalence.isLeftRejective_iff_image
      E C.carrier)

end OpConjecture.IndecomposableSkeleton


