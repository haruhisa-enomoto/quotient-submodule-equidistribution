import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateIdempotent
import QuotientSubmoduleEquidistribution.RepresentationTheory.IdealQuotientTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoRejectiveBridge

/-!
# A maximal quotient-closed flag on both sides of the Auslander equivalence

This file combines the target total right-rejective chain with its coordinate
idempotent-ideal chain.  The required literal identification with
`add(eᵢ Γ)` is proved term by term.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution
namespace IndecomposableSkeleton
namespace LegalQuotientDeletionChain

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent

universe uR uι wR uK

section EquivalenceFiniteAdd

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

private def FiniteAddPresentation.replaceObject
    {G X Y : C} (e : X ≅ Y)
    (P : FiniteAddPresentation G X) :
    FiniteAddPresentation G Y where
  n := P.n
  retract := (Retract.ofIso e.symm).trans P.retract

private def FiniteAddPresentation.mapEquivalence
    (E : C ≌ D) {G X : C}
    (P : FiniteAddPresentation G X) :
    FiniteAddPresentation (E.functor.obj G) (E.functor.obj X) := by
  letI : PreservesBiproduct
      (fun _ : Fin P.n ↦ G) E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  exact
    { n := P.n
      retract :=
        (P.retract.map E.functor).trans
          (Retract.ofIso
            (E.functor.mapBiproduct
              (fun _ : Fin P.n ↦ G))) }

/-- Equivalences preserve and reflect the additive retract closure of one
object, with the target object left arbitrary rather than normalized to an
object in the strict image. -/
theorem finiteAddClosure_inverse_iff
    (E : C ≌ D) (G : C) (X : D) :
    finiteAddClosure G (E.inverse.obj X) ↔
      finiteAddClosure (E.functor.obj G) X := by
  constructor
  · rintro ⟨P⟩
    exact
      ⟨FiniteAddPresentation.replaceObject
        (E.counitIso.app X)
        (FiniteAddPresentation.mapEquivalence E P)⟩
  · rintro ⟨P⟩
    have hMapped :
        finiteAddClosure
          (E.inverse.obj (E.functor.obj G))
          (E.inverse.obj X) :=
      ⟨FiniteAddPresentation.mapEquivalence E.symm P⟩
    exact
      (finiteAddClosure_iff_of_iso
        (E.unitIso.app G)).mpr hMapped

end EquivalenceFiniteAdd

section FullSubcategoryFiniteAdd

universe vC uC

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- If the literal inclusion of a full subcategory preserves finite
biproducts, its internal and ambient finite additive closures agree. -/
theorem finiteAddClosure_fullSubcategory_iff
    (Q : ObjectProperty C)
    [HasFiniteBiproducts Q.FullSubcategory]
    [PreservesFiniteBiproducts Q.ι]
    (G X : Q.FullSubcategory) :
    finiteAddClosure G X ↔
      finiteAddClosure G.obj X.obj := by
  constructor
  · rintro ⟨P⟩
    letI : PreservesBiproduct
        (fun _ : Fin P.n ↦ G) Q.ι :=
      inferInstance
    exact
      ⟨{
        n := P.n
        retract :=
          (P.retract.map Q.ι).trans
            (Retract.ofIso
              (Q.ι.mapBiproduct
                (fun _ : Fin P.n ↦ G))) }⟩
  · rintro ⟨P⟩
    letI : PreservesBiproduct
        (fun _ : Fin P.n ↦ G) Q.ι :=
      inferInstance
    let rAmbient :
        Retract X.obj
          (Q.ι.obj
            (⨁ fun _ : Fin P.n ↦ G)) :=
      P.retract.trans
        (Retract.ofIso
          (Q.ι.mapBiproduct
            (fun _ : Fin P.n ↦ G)).symm)
    exact
      ⟨{
        n := P.n
        retract :=
          { i := ObjectProperty.homMk rAmbient.i
            r := ObjectProperty.homMk rAmbient.r
            retract := by
              apply ObjectProperty.hom_ext
              exact rAmbient.retract } }⟩

end FullSubcategoryFiniteAdd

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R ι)
  [Fintype ι]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

local instance flagSkeletonProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- On a finite indecomposable skeleton, the explicit additive closure of a
support is the retract closure of its selected partial generator. -/
theorem inAdd_iff_finiteAddClosure_partialGenerator
    (p : ι → Prop) (X : FGModuleCat.{wR} R) :
    σ.InAdd {i | p i} X ↔
      finiteAddClosure (partialGenerator σ.obj p) X := by
  classical
  constructor
  · rintro ⟨Q⟩
    let ε : Q.index ≃ Fin (Fintype.card Q.index) :=
      Fintype.equivFin Q.index
    let a : Fin (Fintype.card Q.index) → ι :=
      fun t ↦ Q.label (ε.symm t)
    let reindex :
        σ.sumOver Q.index Q.label ≅
          ⨁ fun t : Fin (Fintype.card Q.index) ↦ σ.obj (a t) :=
      biproduct.whiskerEquiv ε
        (fun t ↦ eqToIso (by
          simp only [a, Equiv.symm_apply_apply]))
    let summandRetract
        (t : Fin (Fintype.card Q.index)) :
        Retract (σ.obj (a t)) (partialGenerator σ.obj p) :=
      let ht : p (a t) := Q.mem (ε.symm t)
      let eCoord :
          σ.obj (a t) ≅
            Subtype.restrict p σ.obj ⟨a t, ht⟩ :=
        eqToIso
          (Subtype.restrict_apply σ.obj p ⟨a t, ht⟩).symm
      { i := eCoord.hom ≫
          biproduct.ι (Subtype.restrict p σ.obj) ⟨a t, ht⟩
        r := biproduct.π
            (Subtype.restrict p σ.obj) ⟨a t, ht⟩ ≫
          eCoord.inv
        retract := by simp }
    let sumRetract :
        Retract
          (⨁ fun t : Fin (Fintype.card Q.index) ↦ σ.obj (a t))
          (⨁ fun _ : Fin (Fintype.card Q.index) ↦
            partialGenerator σ.obj p) :=
      { i := biproduct.map fun t ↦ (summandRetract t).i
        r := biproduct.map fun t ↦ (summandRetract t).r
        retract := by
          apply biproduct.hom_ext'
          intro t
          simp [summandRetract] }
    exact
      ⟨{
        n := Fintype.card Q.index
        retract :=
          (Retract.ofIso Q.iso).trans
            ((Retract.ofIso reindex).trans sumRetract) }⟩
  · rintro ⟨P⟩
    apply inAdd_of_retract σ P.retract
    exact
      inAdd_biproduct σ (FintypeCat.of (Fin P.n))
        (fun _ : Fin P.n ↦ partialGenerator σ.obj p)
        (fun _ ↦ partialGenerator_inAdd σ p)

/-- Under the finite-type Auslander equivalence, the transported additive
subcategory generated by a support is literally `add(eₚ Γ)` on underlying
right modules. -/
theorem transportedGenerated_carrier_iff_addPrincipal
    (p : ι → Prop) (X : skeletonProjectiveTarget σ) :
    (σ.transportedGeneratedSubcategory
        (skeletonAuslanderEquivalence σ) {i | p i}).carrier X ↔
      Tsukamoto.addPrincipalRightModule
        (skeletonCoordinateProjector σ p) X.obj := by
  change
    σ.InAdd {i | p i}
        ((skeletonAuslanderEquivalence σ).inverse.obj X) ↔
      finiteAddClosure
        (Tsukamoto.principalRightModule
          (skeletonCoordinateProjector σ p)) X.obj
  rw [inAdd_iff_finiteAddClosure_partialGenerator σ p]
  rw [finiteAddClosure_inverse_iff
    (skeletonAuslanderEquivalence σ)
    (partialGenerator σ.obj p) X]
  rw [finiteAddClosure_iff_of_iso
    (auslanderImagePartialGeneratorIsoPrincipal σ p)]
  exact
    finiteAddClosure_fullSubcategory_iff
      (AuslanderEquivalence.finiteProjectiveModules
        (skeletonAuslanderAlgebra σ)ᵐᵒᵖ)
      (principalProjectiveObject σ p) X

abbrev FlagSourceChain
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :=
  ofClosedFlag (K := K) σ s

/-- The saturated total right-rejective chain in the finite-projective
Auslander target associated to a maximal quotient-closed flag. -/
abbrev flagTargetChain
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    SaturatedTotalTargetRightRejectiveChain σ
      (skeletonAuslanderEquivalence σ) :=
  saturatedTotalTargetRightRejectiveChainOfClosedFlag
    (K := K) σ (skeletonAuslanderEquivalence σ) s

/-- The coordinate principal-ideal chain attached to the same support
deletion chain. -/
abbrev flagIdealChain
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) (Fintype.card ι) :=
  idempotentIdealChainOfSaturatedSupportDeletion σ
    (FlagSourceChain (K := K) σ s).toSaturatedSupport

/-- Explicit coordinate idempotents presenting every term of the ideal
chain attached to the flag. -/
def flagIdempotentPresentation
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    (flagIdealChain (K := K) σ s).IdempotentPresentation :=
  idempotentPresentationOfSupportChain σ
    (FlagSourceChain (K := K) σ s).support
    (saturatedSupportDeletionChain_strictAnti
      (FlagSourceChain (K := K) σ s).toSaturatedSupport)
    (FlagSourceChain (K := K) σ s).top
    (FlagSourceChain (K := K) σ s).bottom

/-- The exact object-property compatibility required to identify a term of
the transported target chain with `add(eᵢ Γ)` in the literal ambient
finite-projective category. -/
def FlagTermPrincipalAlignment
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) : Prop :=
  ∀ i : Fin (Fintype.card ι + 1),
    (targetRightRejectiveTerm σ
        (skeletonAuslanderEquivalence σ)
        (FlagSourceChain (K := K) σ s) i).1.carrier =
      (fun X : skeletonProjectiveTarget σ ↦
        Tsukamoto.addPrincipalRightModule
          (skeletonCoordinateProjector σ
            ((FlagSourceChain (K := K) σ s).support i))
          X.obj)

/-- The compatibility is automatic for the finite-type Auslander
equivalence: it is preservation/reflection of finite additive closure,
followed by the coordinate projector's principal-module isomorphism. -/
theorem flagTermPrincipalAlignment
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    FlagTermPrincipalAlignment (K := K) σ s := by
  intro i
  funext X
  apply propext
  rw [targetRightRejectiveTerm_subcategory]
  exact
    transportedGenerated_carrier_iff_addPrincipal σ
      ((FlagSourceChain (K := K) σ s).support i) X

/-- Once the literal carrier alignment is supplied, every nonfinal
coordinate ideal is right projective by the source-faithful direction of
Tsukamoto Proposition 3.16. -/
theorem flagIdealChain_rightProjective_of_alignment
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure)
    (halign : FlagTermPrincipalAlignment (K := K) σ s) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsRightProjectiveIdeal
        ((flagIdealChain (K := K) σ s).ideal i.castSucc) := by
  intro i
  let d := FlagSourceChain (K := K) σ s
  let e :=
    skeletonCoordinateProjector σ (d.support i.castSucc)
  have hrr :
      CategoricalRejective.IsRightRejective
        (fun X : skeletonProjectiveTarget σ ↦
          Tsukamoto.addPrincipalRightModule e X.obj) := by
    rw [← halign i.castSucc]
    exact
      (targetRightRejectiveTerm σ
        (skeletonAuslanderEquivalence σ) d i.castSucc).2
  exact
    Tsukamoto.principalTwoSidedIdeal_rightProjective_of_literal_rightRejective
      (coordinateProjector_isIdempotent σ.obj
        (d.support i.castSucc))
      hrr

/-- Every nonfinal ideal in the coordinate chain of a maximal
quotient-closed flag is right projective. -/
theorem flagIdealChain_rightProjective
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsRightProjectiveIdeal
        ((flagIdealChain (K := K) σ s).ideal i.castSucc) :=
  flagIdealChain_rightProjective_of_alignment
    (K := K) σ s (flagTermPrincipalAlignment (K := K) σ s)

/-- Compact combined package.  It retains both the arbitrary target chain
and the coordinate ideal chain, together with the literal coordinate
presentation and right projectivity of all nonfinal ideals. -/
structure MaximalFlagAuslanderPackage
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) where
  targetChain :
    SaturatedTotalTargetRightRejectiveChain σ
      (skeletonAuslanderEquivalence σ)
  idealChain :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) (Fintype.card ι)
  presentation : idealChain.IdempotentPresentation
  ideal_rightProjective :
    ∀ i : Fin (Fintype.card ι),
      Tsukamoto.IsRightProjectiveIdeal
        (idealChain.ideal i.castSucc)

/-- The combined package constructed from a flag and the one required
carrier-identification theorem. -/
def maximalFlagAuslanderPackageOfAlignment
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure)
    (halign : FlagTermPrincipalAlignment (K := K) σ s) :
    MaximalFlagAuslanderPackage σ s where
  targetChain := flagTargetChain (K := K) σ s
  idealChain := flagIdealChain (K := K) σ s
  presentation := flagIdempotentPresentation (K := K) σ s
  ideal_rightProjective :=
    flagIdealChain_rightProjective_of_alignment
      (K := K) σ s halign

/-- A maximal quotient-closed flag canonically yields the combined target
rejective chain and coordinate ideal chain, including explicit generators
and right projectivity of every nonfinal ideal. -/
def maximalFlagAuslanderPackage
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    MaximalFlagAuslanderPackage σ s :=
  maximalFlagAuslanderPackageOfAlignment
    (K := K) σ s (flagTermPrincipalAlignment (K := K) σ s)

end LegalQuotientDeletionChain
end IndecomposableSkeleton
end QuotientSubmoduleEquidistribution
