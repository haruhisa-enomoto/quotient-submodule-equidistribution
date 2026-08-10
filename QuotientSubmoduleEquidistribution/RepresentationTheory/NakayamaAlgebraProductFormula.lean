import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaProductFormula
import QuotientSubmoduleEquidistribution.RepresentationTheory.SerialBoundaryTheorem

/-!
# The paper-facing Nakayama algebra theorem

The manuscript uses the conventional two-sided definition: every
indecomposable projective and every indecomposable injective right module is
uniserial.  The abstract serial-boundary theorem upgrades this condition to
uniseriality of every indecomposable, without assuming representation-finite.
The maintained Nakayama classification-free finiteness bridge and product
formula then give the literal standalone theorem from the paper.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula

universe u

/-- The manuscript's conventional right-module definition of a
finite-dimensional Nakayama algebra, expressed on the canonical complete
indecomposable skeleton.  No representation-finiteness is assumed. -/
def IsRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  let σA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
  QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σA ∧
    QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton σA

/-- The conventional projective-and-injective boundary definition forces
every indecomposable right module to be uniserial, with no prior finiteness
assumption on the set of indecomposables. -/
theorem allIndecomposablesUniserial_of_isRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    let σA :=
      QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton σA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : IsArtinianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
  let σA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
  exact
    QuotientSubmoduleEquidistribution.SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) σA hNakayama.1 hNakayama.2

/-- A finite-dimensional Nakayama algebra in the conventional sense is
automatically right representation-finite. -/
theorem rightRepresentationFinite_of_isRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A := by
  apply
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A
  exact
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama

/-- Literal polynomial conclusion of the standalone Nakayama theorem.  The
factor indexed by a simple module is the geometric chain polynomial whose
capacity is the composition length of its chosen indecomposable projective
cover. -/
theorem exists_rightLevelPolynomials_eq_projectiveCoverLengthProduct
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
      σA.qClosure.levelPolynomial =
          QuotientSubmoduleEquidistribution.NakayamaProductFormula.fixedTopChainPolynomial σA ∧
        σA.sClosure.levelPolynomial =
          QuotientSubmoduleEquidistribution.NakayamaProductFormula.fixedTopChainPolynomial σA := by
  apply
    QuotientSubmoduleEquidistribution.NakayamaProductFormula.exists_rightLevelPolynomials_eq_fixedTopChainPolynomial
      K A
  exact
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama

/-- Direct main-theorem form of the Nakayama case.  The supplied
representation-finiteness witness is used for the canonical finite skeleton;
the conventional projective-and-injective uniserial boundary hypothesis gives
the common projective-cover-length product on both sides. -/
theorem rightQuotientSubmoduleEquidistribution
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A)
    (hNakayama : IsRightNakayamaAlgebra K A) :
    QuotientSubmoduleEquidistribution.RightQuotientSubmoduleEquidistribution K A hA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  let hAll :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton
        (QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  have hPolynomial :=
    QuotientSubmoduleEquidistribution.NakayamaProductFormula.rightLevelPolynomials_eq_fixedTopChainPolynomial
      K A hA hAll
  exact hPolynomial.1.trans hPolynomial.2.symm

/-- The conventional Nakayama condition also supplies the graded lattice
isomorphism obtained by matching the equal projective- and injective-chain
capacity multisets. -/
theorem exists_rightQuotientSubmoduleClosedsOrderIso
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
      Nonempty (σA.qClosure.Closeds ≃o σA.sClosure.Closeds) := by
  apply
    QuotientSubmoduleEquidistribution.NakayamaProductFormula.exists_rightQuotientSubmoduleClosedsOrderIso
      K A
  exact
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama

/-- Both closed-set lattices are products of chains.  The quotient-side
capacities are the projective-cover lengths; the submodule-side capacities
are the opposite-side projective-cover lengths, equivalently the injective
envelope lengths on the original side.  Their multisets agree. -/
theorem exists_rightProductOfChainsData
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ (hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A)
        (hAop : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ),
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
      letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
        QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
      letI : Finite
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      letI : Finite
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
            (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
      let σA :=
        QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
      let τA :=
        QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
      letI : Finite σA.SimpleIndex :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Finite τA.SimpleIndex :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Fintype σA.SimpleIndex := Fintype.ofFinite σA.SimpleIndex
      letI : Fintype τA.SimpleIndex := Fintype.ofFinite τA.SimpleIndex
      Nonempty
          (QuotientSubmoduleEquidistribution.NakayamaCombinatorics.CapacityVector
              (QuotientSubmoduleEquidistribution.NakayamaFixedTopChains.fixedTopCapacity σA) ≃o
            σA.qClosure.Closeds) ∧
        Nonempty
          (QuotientSubmoduleEquidistribution.NakayamaCombinatorics.CapacityVector
              (QuotientSubmoduleEquidistribution.NakayamaFixedTopChains.fixedTopCapacity τA) ≃o
            σA.sClosure.Closeds) ∧
        QuotientSubmoduleEquidistribution.NakayamaCombinatorics.capacityMultiset
            (QuotientSubmoduleEquidistribution.NakayamaFixedTopChains.fixedTopCapacity σA) =
          QuotientSubmoduleEquidistribution.NakayamaCombinatorics.capacityMultiset
            (QuotientSubmoduleEquidistribution.NakayamaFixedTopChains.fixedTopCapacity τA) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hAll :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton
        (QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  let hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A :=
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hAll
  have hAop : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (QuotientSubmoduleEquidistribution.rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
  let τA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  letI : Finite σA.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τA.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σA.SimpleIndex := Fintype.ofFinite σA.SimpleIndex
  letI : Fintype τA.SimpleIndex := Fintype.ofFinite τA.SimpleIndex
  refine ⟨hA, hAop, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · exact
      QuotientSubmoduleEquidistribution.NakayamaProductFormula.quotientClosedsOrderIso
        σA hAll
  · exact
      QuotientSubmoduleEquidistribution.NakayamaProductFormula.submoduleClosedsOrderIsoOfAlignedBiduality
        σA τA (QuotientSubmoduleEquidistribution.rightOppositeAlignedBiduality K A) hAll
  · exact
      QuotientSubmoduleEquidistribution.NakayamaProductFormula.fixedTopCapacityMultiset_eq_of_alignedBiduality
        σA τA (QuotientSubmoduleEquidistribution.rightOppositeAlignedBiduality K A) hAll

/-- The lattice isomorphism can be chosen to preserve closed-set
cardinality, so it is a graded lattice isomorphism in the manuscript's
sense. -/
theorem exists_rightQuotientSubmoduleClosedsGradedOrderIso
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
      ∃ e : σA.qClosure.Closeds ≃o σA.sClosure.Closeds,
        ∀ C : σA.qClosure.Closeds,
          ((e C : σA.sClosure.Closeds) : Set
              (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ)).ncard =
            ((C : σA.qClosure.Closeds) : Set
              (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ)).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hAll :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton
        (QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  let hA : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K A :=
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hAll
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  have hAop : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (QuotientSubmoduleEquidistribution.rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K A
  let τA :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  let e : σA.qClosure.Closeds ≃o σA.sClosure.Closeds :=
    QuotientSubmoduleEquidistribution.NakayamaProductFormula.quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σA τA (QuotientSubmoduleEquidistribution.rightOppositeAlignedBiduality K A) hAll
  refine ⟨hA, e, ?_⟩
  intro C
  exact
    QuotientSubmoduleEquidistribution.NakayamaProductFormula.ncard_quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σA τA (QuotientSubmoduleEquidistribution.rightOppositeAlignedBiduality K A) hAll C

end QuotientSubmoduleEquidistribution.NakayamaAlgebraProductFormula
