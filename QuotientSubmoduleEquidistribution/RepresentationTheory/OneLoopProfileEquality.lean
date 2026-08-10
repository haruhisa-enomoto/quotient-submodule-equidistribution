import QuotientSubmoduleEquidistribution.RepresentationTheory.OneLoopIdealClassification
import QuotientSubmoduleEquidistribution.RepresentationTheory.OppositeDuality
import QuotientSubmoduleEquidistribution.RepresentationTheory.SkeletonAlignment
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrence

/-!
# Full closure-profile equality from a one-loop presentation

The module classification of a truncated polynomial algebra is not needed
for the connected small-core recurrence.  An algebra equivalence with a
commutative algebra makes the source algebra isomorphic to its opposite.
The maintained opposite-duality theorem then identifies its quotient and
submodule level polynomials.

The final theorem is stated for an arbitrary finite complete
indecomposable skeleton, matching the `AlgebraNode` interface.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LocalNakayamaBranch

universe u v

/-- An algebra which is algebra-isomorphic to a commutative algebra is
algebra-isomorphic to its opposite. -/
def algEquivOppositeOfAlgEquivComm
    {K B C : Type u}
    [CommSemiring K]
    [Ring B] [Algebra K B]
    [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C) :
    B ≃ₐ[K] Bᵐᵒᵖ :=
  e.trans <|
    (AlgEquiv.toOpposite K C).trans (AlgEquiv.op e.symm)

/-- The canonical right-module closure profile agrees for any
finite-dimensional algebra which is algebra-isomorphic to a commutative
algebra. -/
theorem rightEquidistribution_of_algEquivComm
    {K B C : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C)
    (hB : IsRightRepresentationFinite.{u, u, u} K B) :
    RightQuotientSubmoduleEquidistribution K B hB := by
  exact
    QuotientSubmoduleEquidistribution.rightEquidistribution_of_moritaEquivalence_op K B
      (MoritaEquivalence.ofAlgEquiv
        (algEquivOppositeOfAlgEquivComm e))
      hB

/-- The same profile equality on any finite complete duplicate-free
indecomposable skeleton of right modules. -/
theorem rightSkeletonEquidistribution_of_algEquivComm
    {K B C : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C) :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  intro iota _ sigma
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B
  let E :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence sigma tau :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.Equivalence.alignedEquivalence
      sigma tau CategoryTheory.Equivalence.refl
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) :=
    E.labelEquiv.finite_iff.mp inferInstance
  have hB : IsRightRepresentationFinite.{u, u, u} K B :=
    (inferInstance :
      Finite
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ))
  have hcanonical :
      tau.qClosure.levelPolynomial =
        tau.sClosure.levelPolynomial := by
    exact rightEquidistribution_of_algEquivComm e hB
  have hq :
      sigma.qClosure.levelPolynomial =
        tau.qClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      sigma tau E
  have hs :
      sigma.sClosure.levelPolynomial =
        tau.sClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      sigma tau E
  exact hq.trans (hcanonical.trans hs.symm)

/-- Profile equality on an arbitrary finite indecomposable skeleton of the
algebra itself.  This is the convention used by `AlgebraNode`.

Contragredient duality identifies quotient closure on `B` with submodule
closure on `Bᵐᵒᵖ`; the algebra equivalence `B ≃ Bᵐᵒᵖ` identifies that
target submodule closure with the original one. -/
theorem skeletonEquidistribution_of_algEquivComm
    {K B C : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    [CommRing C] [Algebra K C]
    (e : B ≃ₐ[K] C) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsNoetherianRing B := inferInstance
  letI : IsArtinianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K B
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K B
  intro iota _ sigma
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B
  let morita : MoritaEquivalence K B Bᵐᵒᵖ :=
    MoritaEquivalence.ofAlgEquiv
      (algEquivOppositeOfAlgEquivComm e)
  let E :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence sigma tau :=
    MoritaEquivalence.alignedFgEquivalence morita sigma tau
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Bᵐᵒᵖ) :=
    E.labelEquiv.finite_iff.mp inferInstance
  let D :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality K B sigma tau
  have hdual :
      sigma.qClosure.levelPolynomial =
        tau.sClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleLevelPolynomial_eq
      sigma tau D
  have hs :
      sigma.sClosure.levelPolynomial =
        tau.sClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      sigma tau E
  exact hdual.trans hs.symm

/-- On a finite complete indecomposable skeleton, a surjective algebra map
from a commutative algebra is already enough for profile equality.  Indeed,
the first isomorphism theorem identifies the target with a quotient of the
commutative source.  This is strictly weaker than specifying a
truncated-polynomial presentation. -/
theorem skeletonEquidistribution_of_surjective_from_commutative
    {K A B : Type u}
    [Field K]
    [CommRing A] [Algebra K A]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsNoetherianRing B := inferInstance
  intro iota _ sigma
  let e : B ≃ₐ[K] (A ⧸ (RingHom.ker f)) :=
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm
  exact skeletonEquidistribution_of_algEquivComm e sigma

/-- Polynomial specialization of
`skeletonEquidistribution_of_surjective_from_commutative`.  Thus the
representation-theoretic input needed for the profile endpoint can be
reduced to monogenicity of the algebra. -/
theorem skeletonEquidistribution_of_surjective_polynomial
    {K B : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    (f : Polynomial K →ₐ[K] B) (hf : Function.Surjective f) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  exact skeletonEquidistribution_of_surjective_from_commutative f hf

/-- Equivalent generator formulation: if one element generates the algebra,
evaluation at that element is a surjective polynomial-algebra map. -/
theorem skeletonEquidistribution_of_singleton_adjoin
    {K B : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    (x : B) (hx : Algebra.adjoin K {x} = ⊤) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsNoetherianRing B := inferInstance
  intro iota _ sigma
  let f : Polynomial K →ₐ[K] B := Polynomial.aeval x
  have hf : Function.Surjective f := by
    apply (AlgHom.range_eq_top f).mp
    simpa [f] using
      (Algebra.adjoin_singleton_eq_range_aeval K x).symm.trans hx
  exact skeletonEquidistribution_of_surjective_polynomial f hf sigma

/-- A surjection from the one-loop path algebra also suffices: compose it
with the maintained algebra equivalence from `K[X]` to the one-loop path
algebra.  No admissibility or relation-ideal classification is needed for
this profile-only conclusion. -/
theorem skeletonEquidistribution_of_surjective_oneLoop
    {K B : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    (f : QuotientSubmoduleEquidistribution.Foundation.pathAlgebra K QuotientSubmoduleEquidistribution.Foundation.Quiver.OneLoop →ₐ[K] B)
    (hf : Function.Surjective f) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsNoetherianRing B := inferInstance
  intro iota _ sigma
  let g : Polynomial K →ₐ[K] B :=
    f.comp (oneLoopPolynomialAlgEquiv K).symm.toAlgHom
  have hg : Function.Surjective g :=
    hf.comp (oneLoopPolynomialAlgEquiv K).symm.surjective
  exact skeletonEquidistribution_of_surjective_polynomial g hg sigma

/-- A one-loop Gabriel presentation already gives the complete
quotient/submodule profile equality on any finite indecomposable skeleton.
No classification of individual truncated-polynomial modules is needed for
this endpoint. -/
theorem skeletonEquidistribution_of_oneLoopPresentation
    {K B : Type u}
    [Field K]
    [Ring B] [Algebra K B] [FiniteDimensional K B]
    (P : OneLoopPresentation K B) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite K B
    letI : IsNoetherianRing B := inferInstance
    ∀ {iota : Type v} [Finite iota]
      (sigma :
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} B iota),
      sigma.qClosure.levelPolynomial =
        sigma.sClosure.levelPolynomial := by
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI : IsNoetherianRing B := inferInstance
  intro iota _ sigma
  obtain ⟨L, _hL, ⟨e⟩⟩ :=
    algEquiv_truncatedPolynomial_of_oneLoopPresentation P
  exact skeletonEquidistribution_of_algEquivComm e sigma

/-- Exact `AlgebraNode` form of the one-loop profile endpoint used by the
connected small-core adapter. -/
theorem algebraNodeEquidistribution_of_oneLoopPresentation
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (P : OneLoopPresentation K B.Carrier) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  exact skeletonEquidistribution_of_oneLoopPresentation P B.skeleton

/-- Exact `AlgebraNode` endpoint under the weakest structural input isolated
above: the carrier is an algebra quotient of some commutative algebra. -/
theorem algebraNodeEquidistribution_of_surjective_from_commutative
    {K A : Type u} [Field K]
    [CommRing A] [Algebra K A]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (f : A →ₐ[K] B.Carrier) (hf : Function.Surjective f) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  exact
    skeletonEquidistribution_of_surjective_from_commutative f hf B.skeleton

/-- Full profile equality transports between finite complete skeletons along
a Morita equivalence.  This is the reusable node-level transport behind the
basicization forms below. -/
theorem algebraNodeEquidistribution_of_morita
    {K : Type u} [Field K]
    (B D :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (M : MoritaEquivalence K B.Carrier D.Carrier)
    (hD :
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
          K D).levelPolynomial =
        (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
          K D).levelPolynomial) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing D.Carrier :=
    IsArtinianRing.of_finite K D.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    M B.skeleton D.skeleton
  have hq :
      B.skeleton.qClosure.levelPolynomial =
        D.skeleton.qClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      B.skeleton D.skeleton E
  have hs :
      B.skeleton.sClosure.levelPolynomial =
        D.skeleton.sClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      B.skeleton D.skeleton E
  exact hq.trans (hD.trans hs.symm)

/-- Morita-invariant form suited to basicization: it is enough that the
source node be Morita equivalent to a node whose carrier is a quotient of a
commutative algebra. -/
theorem algebraNodeEquidistribution_of_morita_surjective_from_commutative
    {K A : Type u} [Field K]
    [CommRing A] [Algebra K A]
    (B D :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (M : MoritaEquivalence K B.Carrier D.Carrier)
    (f : A →ₐ[K] D.Carrier) (hf : Function.Surjective f) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  apply algebraNodeEquidistribution_of_morita B D M
  exact skeletonEquidistribution_of_surjective_from_commutative
    f hf D.skeleton

/-- In particular, a single algebra generator is sufficient in the exact
`AlgebraNode` shape consumed by the connected small-core recurrence. -/
theorem algebraNodeEquidistribution_of_singleton_adjoin
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (x : B.Carrier) (hx : Algebra.adjoin K {x} = ⊤) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  exact skeletonEquidistribution_of_singleton_adjoin x hx B.skeleton

/-- Most direct basicization interface for the one-simple branch: a
Morita-equivalent one-generated model already forces the source node's full
quotient/submodule profile equality. -/
theorem algebraNodeEquidistribution_of_morita_singleton_adjoin
    {K : Type u} [Field K]
    (B D :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (M : MoritaEquivalence K B.Carrier D.Carrier)
    (x : D.Carrier) (hx : Algebra.adjoin K {x} = ⊤) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  let f : Polynomial K →ₐ[K] D.Carrier := Polynomial.aeval x
  have hf : Function.Surjective f := by
    apply (AlgHom.range_eq_top f).mp
    simpa [f] using
      (Algebra.adjoin_singleton_eq_range_aeval K x).symm.trans hx
  exact
    algebraNodeEquidistribution_of_morita_surjective_from_commutative
      B D M f hf

/-- Structural one-simple endpoint: the source node is Morita equivalent to
a finite complete node whose algebra has one generator. -/
def HasMoritaMonogenicModel
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K) :
    Prop :=
  ∃ D :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K,
    Nonempty (MoritaEquivalence K B.Carrier D.Carrier) ∧
      ∃ x : D.Carrier, Algebra.adjoin K {x} = ⊤

/-- A Morita-equivalent monogenic model supplies the full profile equality
needed by the connected recurrence. -/
theorem algebraNodeEquidistribution_of_hasMoritaMonogenicModel
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (hB : HasMoritaMonogenicModel B) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  rcases hB with ⟨D, ⟨M⟩, x, hx⟩
  exact algebraNodeEquidistribution_of_morita_singleton_adjoin B D M x hx

/-- A presentation-level variant matching the classical one-vertex Gabriel
route: the source node is Morita equivalent to a node with a one-loop
presentation. -/
def HasMoritaOneLoopPresentation
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K) :
    Prop :=
  ∃ D :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K,
    Nonempty (MoritaEquivalence K B.Carrier D.Carrier) ∧
      Nonempty (OneLoopPresentation K D.Carrier)

/-- A Morita-equivalent one-loop presentation supplies the full profile
equality without classifying the individual truncated-polynomial modules. -/
theorem algebraNodeEquidistribution_of_hasMoritaOneLoopPresentation
    {K : Type u} [Field K]
    (B :
      QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode K)
    (hB : HasMoritaOneLoopPresentation B) :
    (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.qClosure
        K B).levelPolynomial =
      (QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode.sClosure
        K B).levelPolynomial := by
  rcases hB with ⟨D, ⟨M⟩, ⟨P⟩⟩
  exact algebraNodeEquidistribution_of_morita B D M
    (algebraNodeEquidistribution_of_oneLoopPresentation D P)

end QuotientSubmoduleEquidistribution.LocalNakayamaBranch
