import OpConjecture.RepresentationTheory.NakayamaProductFormula
import OpConjecture.RepresentationTheory.SerialBoundaryTheorem

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

namespace OpConjecture.NakayamaAlgebraProductFormula

universe u

/-- The manuscript's conventional right-module definition of a
finite-dimensional Nakayama algebra, expressed on the canonical complete
indecomposable skeleton.  No representation-finiteness is assumed. -/
def IsRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A] : Prop :=
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  let σA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σA ∧
    OpConjecture.SerialRingBridge.IsInjectiveNakayamaSkeleton σA

/-- The conventional projective-and-injective boundary definition forces
every indecomposable right module to be uniserial, with no prior finiteness
assumption on the set of indecomposables. -/
theorem allIndecomposablesUniserial_of_isRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    let σA :=
      OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : IsArtinianRing Aᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K A
  let σA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  exact
    OpConjecture.SerialEndpointReduction.isNakayamaSkeleton_of_projective_and_injective_boundaries
      (K := K) σA hNakayama.1 hNakayama.2

/-- A finite-dimensional Nakayama algebra in the conventional sense is
automatically right representation-finite. -/
theorem rightRepresentationFinite_of_isRightNakayamaAlgebra
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    OpConjecture.IsRightRepresentationFinite.{u, u, u} K A := by
  apply
    OpConjecture.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
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
    ∃ hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
      σA.qClosure.levelPolynomial =
          OpConjecture.NakayamaProductFormula.fixedTopChainPolynomial σA ∧
        σA.sClosure.levelPolynomial =
          OpConjecture.NakayamaProductFormula.fixedTopChainPolynomial σA := by
  apply
    OpConjecture.NakayamaProductFormula.exists_rightLevelPolynomials_eq_fixedTopChainPolynomial
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
    (hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A)
    (hNakayama : IsRightNakayamaAlgebra K A) :
    OpConjecture.RightQuotientSubmoduleEquidistribution K A hA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  let hAll :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton
        (OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  have hPolynomial :=
    OpConjecture.NakayamaProductFormula.rightLevelPolynomials_eq_fixedTopChainPolynomial
      K A hA hAll
  exact hPolynomial.1.trans hPolynomial.2.symm

/-- The conventional Nakayama condition also supplies the graded lattice
isomorphism obtained by matching the equal projective- and injective-chain
capacity multisets. -/
theorem exists_rightQuotientSubmoduleClosedsOrderIso
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
      Nonempty (σA.qClosure.Closeds ≃o σA.sClosure.Closeds) := by
  apply
    OpConjecture.NakayamaProductFormula.exists_rightQuotientSubmoduleClosedsOrderIso
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
    ∃ (hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A)
        (hAop : OpConjecture.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ),
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u}
            (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
      let τA :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
      letI : Finite σA.SimpleIndex :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Finite τA.SimpleIndex :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Fintype σA.SimpleIndex := Fintype.ofFinite σA.SimpleIndex
      letI : Fintype τA.SimpleIndex := Fintype.ofFinite τA.SimpleIndex
      Nonempty
          (OpConjecture.NakayamaCombinatorics.CapacityVector
              (OpConjecture.NakayamaFixedTopChains.fixedTopCapacity σA) ≃o
            σA.qClosure.Closeds) ∧
        Nonempty
          (OpConjecture.NakayamaCombinatorics.CapacityVector
              (OpConjecture.NakayamaFixedTopChains.fixedTopCapacity τA) ≃o
            σA.sClosure.Closeds) ∧
        OpConjecture.NakayamaCombinatorics.capacityMultiset
            (OpConjecture.NakayamaFixedTopChains.fixedTopCapacity σA) =
          OpConjecture.NakayamaCombinatorics.capacityMultiset
            (OpConjecture.NakayamaFixedTopChains.fixedTopCapacity τA) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hAll :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton
        (OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  let hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A :=
    OpConjecture.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hAll
  have hAop : OpConjecture.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (OpConjecture.rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u}
        (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  let τA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  letI : Finite σA.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τA.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σA.SimpleIndex := Fintype.ofFinite σA.SimpleIndex
  letI : Fintype τA.SimpleIndex := Fintype.ofFinite τA.SimpleIndex
  refine ⟨hA, hAop, ⟨?_⟩, ⟨?_⟩, ?_⟩
  · exact
      OpConjecture.NakayamaProductFormula.quotientClosedsOrderIso
        σA hAll
  · exact
      OpConjecture.NakayamaProductFormula.submoduleClosedsOrderIsoOfAlignedBiduality
        σA τA (OpConjecture.rightOppositeAlignedBiduality K A) hAll
  · exact
      OpConjecture.NakayamaProductFormula.fixedTopCapacityMultiset_eq_of_alignedBiduality
        σA τA (OpConjecture.rightOppositeAlignedBiduality K A) hAll

/-- The lattice isomorphism can be chosen to preserve closed-set
cardinality, so it is a graded lattice isomorphism in the manuscript's
sense. -/
theorem exists_rightQuotientSubmoduleClosedsGradedOrderIso
    (K A : Type u)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama : IsRightNakayamaAlgebra K A) :
    ∃ hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
      ∃ e : σA.qClosure.Closeds ≃o σA.sClosure.Closeds,
        ∀ C : σA.qClosure.Closeds,
          ((e C : σA.sClosure.Closeds) : Set
              (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ)).ncard =
            ((C : σA.qClosure.Closeds) : Set
              (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ)).ncard := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  let hAll :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton
        (OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A) :=
    allIndecomposablesUniserial_of_isRightNakayamaAlgebra
      K A hNakayama
  let hA : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A :=
    OpConjecture.NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hAll
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ) := hA
  have hAop : OpConjecture.IsRightRepresentationFinite.{u, u, u} K Aᵐᵒᵖ :=
    (OpConjecture.rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u}
        (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  let τA :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K Aᵐᵒᵖ
  let e : σA.qClosure.Closeds ≃o σA.sClosure.Closeds :=
    OpConjecture.NakayamaProductFormula.quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σA τA (OpConjecture.rightOppositeAlignedBiduality K A) hAll
  refine ⟨hA, e, ?_⟩
  intro C
  exact
    OpConjecture.NakayamaProductFormula.ncard_quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σA τA (OpConjecture.rightOppositeAlignedBiduality K A) hAll C

end OpConjecture.NakayamaAlgebraProductFormula
