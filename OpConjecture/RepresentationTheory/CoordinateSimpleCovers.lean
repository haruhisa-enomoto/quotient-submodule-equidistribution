import OpConjecture.RepresentationTheory.ProjectiveSimpleTop
import OpConjecture.RepresentationTheory.CoordinateProjectives

/-!
# Coordinate simple tops and projective covers

The simple labels attached to singleton coordinate projectives over the
skeleton Auslander algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.AuslanderEquivalence.CoordinateIdempotent

open OpConjecture.IndecomposableSkeleton
open OpConjecture.ProjectiveSimpleTop
open OpConjecture.Tsukamoto.StandardSemantics

universe uR uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Finite κ]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

local instance coordinateTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- The simple top attached to a singleton coordinate projective. -/
abbrev coordinateSimple (i : κ) :
    ModuleCat.{wR} (skeletonAuslanderAlgebra σ)ᵐᵒᵖ :=
  ModuleCat.of
    (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
    ((coordinateProjective σ i).obj ⧸
      Module.jacobson
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (coordinateProjective σ i).obj)

/-- The canonical radical-quotient cover of a coordinate simple. -/
def coordinateProjectiveCover
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj)
    (i : κ) :
    ProjectiveCover (coordinateSimple σ i) := by
  let hP :=
    coordinateProjective_isFiniteProjective σ i
  letI : Module.Finite
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    hP.1
  letI : CategoryTheory.Projective
      (coordinateProjective σ i).obj :=
    hP.2
  letI : Module.Projective
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (coordinateProjective σ i).obj).mpr hP.2
  exact
    jacobsonProjectiveCoverOfIndecomposable
      (hfinite i)
      (coordinateProjective_indecomposable σ i)

/-- Each coordinate radical quotient is categorically simple. -/
theorem coordinateSimple_isSimple
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj)
    (i : κ) :
    Simple (coordinateSimple σ i) := by
  let hP :=
    coordinateProjective_isFiniteProjective σ i
  letI : Module.Finite
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    hP.1
  letI : CategoryTheory.Projective
      (coordinateProjective σ i).obj :=
    hP.2
  letI : Module.Projective
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (coordinateProjective σ i).obj).mpr hP.2
  rw [simple_iff_isSimpleModule]
  exact
    simple_top_of_indec_projective
      (hfinite i)
      (coordinateProjective_indecomposable σ i)

/-- Distinct skeleton labels have nonisomorphic coordinate simple tops. -/
theorem coordinateSimple_eq_of_iso
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj)
    {i j : κ}
    (e : coordinateSimple σ i ≅ coordinateSimple σ j) :
    i = j := by
  let pIso :
      (coordinateProjectiveCover σ hfinite i).object ≅
        (coordinateProjectiveCover σ hfinite j).object :=
    ProjectiveCover.objectIsoOfTargetIso
      (coordinateProjectiveCover σ hfinite i)
      (coordinateProjectiveCover σ hfinite j)
      e
  let pIsoBase :
      (coordinateProjective σ i).obj ≅
        (coordinateProjective σ j).obj :=
    pIso
  exact
    coordinateProjective_eq_of_iso σ
      ((AuslanderEquivalence.finiteProjectiveModules
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ).isoMk pIsoBase)

/-- The biproduct of all projective images of the skeleton representatives
is the regular module over the opposite Auslander algebra. -/
def auslanderImageBiproductIsoRegular :
    (⨁ fun i : κ ↦
        ((skeletonAuslanderEquivalence σ).functor.obj
          (σ.obj i)).obj) ≅
      ModuleCat.of
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ := by
  classical
  let E := skeletonAuslanderEquivalence σ
  let P :=
    AuslanderEquivalence.finiteProjectiveModules
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
  let I := P.ι
  let F : κ → skeletonProjectiveTarget σ :=
    fun i ↦ E.functor.obj (σ.obj i)
  letI : PreservesBiproduct σ.obj E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  letI : PreservesBiproduct F I :=
    preservesBiproduct_of_preservesProduct I
  exact
    (I.mapBiproduct F).symm ≪≫
      I.mapIso (E.functor.mapBiproduct σ.obj).symm ≪≫
      (AuslanderEquivalence.regularLinearEquiv
        (skeletonGenerator σ)).toModuleIso.symm

/-- A nonzero map from a singleton coordinate projective to a simple
module identifies that module with the coordinate top. -/
def simpleIsoCoordinateSimpleOfNonzero
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj)
    (i : κ)
    (S : ModuleCat.{wR} (skeletonAuslanderAlgebra σ)ᵐᵒᵖ)
    (hS : Simple S)
    (f : (coordinateProjective σ i).obj ⟶ S)
    (hf : f ≠ 0) :
    S ≅ coordinateSimple σ i := by
  letI : Simple S := hS
  letI : IsSimpleModule
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ S :=
    isSimpleModule_of_simple S
  let hindec :=
    coordinateProjective_indecomposable σ i
  let hP :=
    coordinateProjective_isFiniteProjective σ i
  letI : Nontrivial (coordinateProjective σ i).obj :=
    hindec.nontrivial
  letI : Module.Finite
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    hP.1
  letI : CategoryTheory.Projective
      (coordinateProjective σ i).obj :=
    hP.2
  letI : Module.Projective
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj :=
    (IsProjective.iff_projective
      (coordinateProjective σ i).obj).mpr hP.2
  letI : IsLocalRing
      (Module.End
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
        (coordinateProjective σ i).obj) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable
      (hfinite i) hindec
  letI : Epi f :=
    epi_of_nonzero_to_simple hf
  exact
    (topLinearEquivOfSurjectiveToSimple
      f.hom
      ((ModuleCat.epi_iff_surjective f).mp inferInstance)).toModuleIso.symm

/-- The coordinate radical quotients form a complete family of simple
modules once the coordinate projectives are known to have finite length. -/
theorem coordinateSimple_complete
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj)
    (S : ModuleCat.{wR} (skeletonAuslanderAlgebra σ)ᵐᵒᵖ)
    (hS : Simple S) :
    ∃ i : κ, Nonempty (S ≅ coordinateSimple σ i) := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : Simple S := hS
  letI : IsSimpleModule
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ S :=
    isSimpleModule_of_simple S
  letI : Nontrivial S :=
    IsSimpleModule.nontrivial
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let q :
      ModuleCat.of
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ ⟶
        S :=
    ModuleCat.ofHom
      (LinearMap.toSpanSingleton
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ S s)
  haveI : Epi q := by
    rw [ModuleCat.epi_iff_surjective]
    exact
      IsSimpleModule.toSpanSingleton_surjective
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ hs
  let F : κ →
      ModuleCat.{wR} (skeletonAuslanderAlgebra σ)ᵐᵒᵖ :=
    fun i ↦
      ((skeletonAuslanderEquivalence σ).functor.obj
        (σ.obj i)).obj
  let t : (⨁ F) ⟶ S :=
    (auslanderImageBiproductIsoRegular σ).hom ≫ q
  haveI : Epi t := by
    dsimp [t]
    infer_instance
  have ht : t ≠ 0 := by
    intro ht
    exact
      Simple.not_isZero S
        (IsZero.of_epi_eq_zero t ht)
  have hcomponent :
      ∃ i : κ, biproduct.ι F i ≫ t ≠ 0 := by
    by_contra h
    push Not at h
    apply ht
    apply biproduct.hom_ext'
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hcomponent
  let I :=
    AuslanderEquivalence.finiteProjectiveModules
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
  let e :
      F i ≅ (coordinateProjective σ i).obj :=
    I.ι.mapIso (auslanderImageIsoCoordinateProjective σ i)
  let f : (coordinateProjective σ i).obj ⟶ S :=
    e.inv ≫ biproduct.ι F i ≫ t
  have hef :
      e.hom ≫ f = biproduct.ι F i ≫ t := by
    simp [f]
  have hf : f ≠ 0 := by
    intro hf
    apply hi
    rw [← hef, hf, comp_zero]
  exact
    ⟨i, ⟨simpleIsoCoordinateSimpleOfNonzero
      σ hfinite i S hS f hf⟩⟩

/-- The exact simple-label and projective-cover package needed before
constructing standard modules. -/
structure CoordinateSimpleCoverClassification where
  simple_isSimple :
    ∀ i : κ, Simple (coordinateSimple σ i)
  simple_complete :
    ∀ (S : ModuleCat.{wR}
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ),
      Simple S →
        ∃ i : κ, Nonempty (S ≅ coordinateSimple σ i)
  simple_nodup :
    ∀ {i j : κ},
      Nonempty (coordinateSimple σ i ≅ coordinateSimple σ j) →
        i = j
  cover :
    ∀ i : κ, ProjectiveCover (coordinateSimple σ i)

/-- Finite length of the coordinate projectives supplies the complete,
duplicate-free simple family and its canonical projective covers. -/
def coordinateSimpleCoverClassification
    (hfinite :
      ∀ i : κ,
        IsFiniteLength
          (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
          (coordinateProjective σ i).obj) :
    CoordinateSimpleCoverClassification σ where
  simple_isSimple :=
    coordinateSimple_isSimple σ hfinite
  simple_complete :=
    coordinateSimple_complete σ hfinite
  simple_nodup := by
    rintro i j ⟨e⟩
    exact coordinateSimple_eq_of_iso σ hfinite e
  cover :=
    coordinateProjectiveCover σ hfinite

section ArtinianAuslanderOpposite

variable [IsArtinianRing (skeletonAuslanderAlgebra σ)ᵐᵒᵖ]

/-- Over a right-Artinian Auslander algebra, singleton coordinate
projectives automatically have finite length. -/
theorem coordinateProjective_isFiniteLength (i : κ) :
    IsFiniteLength
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj := by
  let hP :=
    coordinateProjective_isFiniteProjective σ i
  exact
    ((IsArtinianRing.tfae
      (skeletonAuslanderAlgebra σ)ᵐᵒᵖ
      (coordinateProjective σ i).obj).out 0 3).mp hP.1

/-- The canonical coordinate projective cover with finite length
discharged by right Artinianity. -/
abbrev coordinateProjectiveCoverOfIsArtinian (i : κ) :
    ProjectiveCover (coordinateSimple σ i) :=
  coordinateProjectiveCover σ
    (coordinateProjective_isFiniteLength σ) i

/-- Coordinate tops are simple under right Artinianity. -/
theorem coordinateSimple_isSimple_of_isArtinian (i : κ) :
    Simple (coordinateSimple σ i) :=
  coordinateSimple_isSimple σ
    (coordinateProjective_isFiniteLength σ) i

/-- Coordinate tops have no isomorphic duplicates under right
Artinianity. -/
theorem coordinateSimple_eq_of_iso_of_isArtinian
    {i j : κ} (e : coordinateSimple σ i ≅ coordinateSimple σ j) :
    i = j :=
  coordinateSimple_eq_of_iso σ
    (coordinateProjective_isFiniteLength σ) e

/-- Under right Artinianity, the coordinate simple labels are complete. -/
theorem coordinateSimple_complete_of_isArtinian
    (S : ModuleCat.{wR} (skeletonAuslanderAlgebra σ)ᵐᵒᵖ)
    (hS : Simple S) :
    ∃ i : κ, Nonempty (S ≅ coordinateSimple σ i) :=
  coordinateSimple_complete σ
    (coordinateProjective_isFiniteLength σ) S hS

/-- Under right Artinianity, the entire simple-cover classification is
automatic. -/
abbrev coordinateSimpleCoverClassificationOfIsArtinian :
    CoordinateSimpleCoverClassification σ :=
  coordinateSimpleCoverClassification σ
    (coordinateProjective_isFiniteLength σ)

end ArtinianAuslanderOpposite

end OpConjecture.AuslanderEquivalence.CoordinateIdempotent
