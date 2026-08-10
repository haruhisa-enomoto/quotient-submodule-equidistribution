import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrence
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProductModules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LevelTwoUnconditional
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaConsequences

/-!
# Binary block decomposition from a central idempotent

Maintained development for the disconnected branch of the repaired bottom-level
recurrence.  The component rings are kept as quotient algebras so that the
maintained canonical factor-skeleton and finrank-drop APIs apply literally.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.BlockDecomposition

universe u

variable {R : Type u} [Ring R]

/-- The two-sided component ideal cut out by a central element `e`: its
elements are exactly those fixed by left multiplication by `e`. -/
def componentIdeal (e : R) (hc : IsMulCentral e) : TwoSidedIdeal R :=
  TwoSidedIdeal.mk' {r | e * r = r}
    (by simp)
    (by
      intro x y hx hy
      change e * (x + y) = x + y
      rw [mul_add, hx, hy])
    (by
      intro x hx
      change e * (-x) = -x
      rw [mul_neg, hx])
    (by
      intro x y hy
      change e * (x * y) = x * y
      rw [hc.left_comm, hy])
    (by
      intro x y hx
      change e * (x * y) = x * y
      rw [← mul_assoc, hx])

@[simp]
theorem mem_componentIdeal_iff (e : R) (hc : IsMulCentral e) (r : R) :
    r ∈ componentIdeal e hc ↔ e * r = r := by
  simp [componentIdeal]

/-- The complement of a central element is central. -/
theorem one_sub_isMulCentral (e : R) (hc : IsMulCentral e) :
    IsMulCentral (1 - e) where
  comm r := by
    rw [commute_iff_eq, sub_mul, one_mul, mul_sub, mul_one,
      (hc.comm r).eq]
  left_assoc := fun _ _ ↦ (mul_assoc _ _ _).symm
  right_assoc := fun _ _ ↦ mul_assoc _ _ _

section Idempotent

variable (e : R) (hc : IsMulCentral e)

/-- The first central component ideal. -/
abbrev leftIdeal : TwoSidedIdeal R := componentIdeal e hc

/-- The complementary central component ideal. -/
abbrev rightIdeal : TwoSidedIdeal R :=
  componentIdeal (1 - e) (one_sub_isMulCentral e hc)

@[simp]
theorem e_mem_leftIdeal (he : IsIdempotentElem e) :
    e ∈ leftIdeal e hc := by
  exact (mem_componentIdeal_iff e hc e).mpr he

@[simp]
theorem one_sub_mem_rightIdeal (he : IsIdempotentElem e) :
    1 - e ∈ rightIdeal e hc := by
  exact
    (mem_componentIdeal_iff (1 - e)
      (one_sub_isMulCentral e hc) (1 - e)).mpr he.one_sub

/-- The diagonal quotient map into the two complementary factor rings. -/
def quotientPairAlgHom {K : Type u} [CommSemiring K] [Algebra K R] :
    R →ₐ[K]
      (AnnihilatorInflation.Quotient.Factor (leftIdeal e hc) ×
        AnnihilatorInflation.Quotient.Factor (rightIdeal e hc)) :=
  (Ideal.Quotient.mkₐ K (leftIdeal e hc).asIdeal).prod
    (Ideal.Quotient.mkₐ K (rightIdeal e hc).asIdeal)

theorem quotientPairAlgHom_injective {K : Type u} [CommSemiring K]
    [Algebra K R] : Function.Injective (quotientPairAlgHom e hc :
      R →ₐ[K]
        (AnnihilatorInflation.Quotient.Factor (leftIdeal e hc) ×
          AnnihilatorInflation.Quotient.Factor (rightIdeal e hc))) := by
  intro x y hxy
  have hleft :
      Ideal.Quotient.mk (leftIdeal e hc).asIdeal x =
        Ideal.Quotient.mk (leftIdeal e hc).asIdeal y :=
    congrArg Prod.fst hxy
  have hright :
      Ideal.Quotient.mk (rightIdeal e hc).asIdeal x =
        Ideal.Quotient.mk (rightIdeal e hc).asIdeal y :=
    congrArg Prod.snd hxy
  have hxleft : e * (x - y) = x - y :=
    (mem_componentIdeal_iff e hc (x - y)).mp
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := (leftIdeal e hc).asIdeal) x y).mp hleft)
  have hxright : (1 - e) * (x - y) = x - y :=
    (mem_componentIdeal_iff (1 - e) (one_sub_isMulCentral e hc)
      (x - y)).mp
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem
        (I := (rightIdeal e hc).asIdeal) x y).mp hright)
  have hdouble : x - y = (x - y) + (x - y) := by
    calc
      x - y = (e + (1 - e)) * (x - y) := by simp
      _ = e * (x - y) + (1 - e) * (x - y) := add_mul _ _ _
      _ = (x - y) + (x - y) := by rw [hxleft, hxright]
  have hzero : x - y = 0 := by
    have hz : 0 = x - y := by
      simpa [add_assoc] using
        congrArg (fun z ↦ z + -(x - y)) hdouble
    exact hz.symm
  exact sub_eq_zero.mp hzero

theorem quotientPairAlgHom_surjective {K : Type u} [CommSemiring K]
    [Algebra K R] (he : IsIdempotentElem e) :
    Function.Surjective (quotientPairAlgHom e hc :
      R →ₐ[K]
        (AnnihilatorInflation.Quotient.Factor (leftIdeal e hc) ×
          AnnihilatorInflation.Quotient.Factor (rightIdeal e hc))) := by
  rintro ⟨a, b⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(1 - e) * x + e * y, ?_⟩
  apply Prod.ext
  · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (leftIdeal e hc).asIdeal) _ _).mpr
    apply (mem_componentIdeal_iff e hc _).mpr
    noncomm_ring
    have heq : e * e = e := he
    simp only [← mul_assoc, heq]
  · apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := (rightIdeal e hc).asIdeal) _ _).mpr
    apply (mem_componentIdeal_iff (1 - e)
      (one_sub_isMulCentral e hc) _).mpr
    noncomm_ring
    have heq : e * e = e := he
    simp only [← mul_assoc, heq]
    abel

/-- A noncommutative algebra splits as the product of the quotient algebras
cut out by a central idempotent and its complement. -/
def algEquivQuotientProduct {K : Type u} [CommSemiring K] [Algebra K R]
    (he : IsIdempotentElem e) :
    R ≃ₐ[K]
      (AnnihilatorInflation.Quotient.Factor (leftIdeal e hc) ×
        AnnihilatorInflation.Quotient.Factor (rightIdeal e hc)) :=
  AlgEquiv.ofBijective (quotientPairAlgHom e hc)
    ⟨quotientPairAlgHom_injective e hc,
      quotientPairAlgHom_surjective e hc he⟩

end Idempotent

namespace Node

open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment
open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode

variable (K : Type u) [Field K]

/-- Every finitely generated module over a finite-dimensional algebra has
finite length.  This left-module form is convenient for the node API. -/
theorem finiteLength_of_finiteDimensional
    (R : Type u) [Ring R] [Algebra K R] [FiniteDimensional K R]
    (X : FGModuleCat.{u} R) : IsFiniteLength R X := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact
    ((IsArtinianRing.tfae R X).out 0 3).mp
      (inferInstance : Module.Finite R X)

/-- The canonical complete indecomposable skeleton for left modules over a
finite-dimensional algebra. -/
noncomputable def canonicalLeftSkeleton
    (R : Type u) [Ring R] [Algebra K R] [FiniteDimensional K R]
    [IsNoetherianRing R] :
    IndecomposableSkeleton.{u, u + 1, u} R
      (CanonicalIndecomposableIndex.{u, u} R) :=
  indecomposableSkeletonOfFiniteLength
    (finiteLength_of_finiteDimensional K R)

/-- The standard ring-theoretic connectedness predicate: a block-connected
algebra has no central idempotents other than zero and one. -/
def IsBlockConnected (B : AlgebraNode K) : Prop :=
  ∀ e : B.Carrier, IsIdempotentElem e → IsMulCentral e →
    e = 0 ∨ e = 1

/-- Failure of block connectedness produces a nontrivial central
idempotent. -/
theorem exists_nontrivial_central_idempotent (B : AlgebraNode K)
    (hB : ¬ IsBlockConnected K B) :
    ∃ e : B.Carrier, IsIdempotentElem e ∧ IsMulCentral e ∧
      e ≠ 0 ∧ e ≠ 1 := by
  classical
  simp only [IsBlockConnected] at hB
  push Not at hB
  obtain ⟨e, he, hc, hnontrivial⟩ := hB
  exact ⟨e, he, hc, hnontrivial⟩

/-- The canonical finite quotient node attached to an arbitrary two-sided
ideal of a node.  Unlike `AlgebraNode.factor`, this does not require the
ideal to occur as a realized annihilator. -/
noncomputable def quotientNode (B : AlgebraNode K)
    (I : TwoSidedIdeal B.Carrier) : AlgebraNode K := by
  letI factorNoeth : IsNoetherianRing (Quotient.Factor I) :=
    factorNoetherian K B.Carrier I
  letI factorArtinianOpposite :
      IsArtinianRing (Quotient.Factor I)ᵐᵒᵖ :=
    IsArtinianRing.of_finite K _
  letI factorNoethOpposite :
      IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ := inferInstance
  let tau := canonicalFactorSkeleton K B.Carrier I
  let finiteTau := alignedFiniteFactorSkeleton B.skeleton I tau
  exact
    { Carrier := Quotient.Factor I
      ring := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      noetherian := factorNoeth
      noetherianOpposite := factorNoethOpposite
      Index := FactorIndex B.Carrier I
      finiteIndex := finiteTau.finite_ι
      skeleton := tau }

/-- Any nonzero quotient ideal gives a strict recurrence-measure drop. -/
theorem quotientNode_measure_lt (B : AlgebraNode K)
    (I : TwoSidedIdeal B.Carrier) (hI : I ≠ ⊥) :
    measure K (quotientNode K B I) < measure K B := by
  exact factor_finrank_lt K B.Carrier I hI

/-- Level two agrees for every finite algebra node over an algebraically
closed field.  The maintained right-module theorem is applied to the double
opposite algebra and transported back along `AlgEquiv.opOp`. -/
theorem levelCount_two_eq [IsAlgClosed K] (B : AlgebraNode K) :
    (qClosure K B).levelCount 2 = (sClosure K B).levelCount 2 := by
  let R := B.Carrier
  let S := (Rᵐᵒᵖ)ᵐᵒᵖ
  letI artinianR : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI artinianS : IsArtinianRing S := IsArtinianRing.of_finite K S
  letI noetherianS : IsNoetherianRing S := inferInstance
  let tau := canonicalLeftSkeleton K S
  let morita : MoritaEquivalence K R S :=
    MoritaEquivalence.ofAlgEquiv (AlgEquiv.opOp K R)
  let E : IndecomposableSkeleton.AlignedEquivalence B.skeleton tau :=
    MoritaEquivalence.alignedFgEquivalence morita B.skeleton tau
  letI finiteTau : Finite (CanonicalIndecomposableIndex.{u, u} S) :=
    E.labelEquiv.finite_iff.mp B.finiteIndex
  letI : Fintype B.Index := Fintype.ofFinite B.Index
  let SmallIndex := ULift.{u} (Fin (Fintype.card B.Index))
  let smallToB : SmallIndex ≃ B.Index :=
    Equiv.ulift.trans (Fintype.equivFin B.Index).symm
  let smallToTau : SmallIndex ≃ CanonicalIndecomposableIndex.{u, u} S :=
    smallToB.trans E.labelEquiv
  let tauSmall :
      IndecomposableSkeleton.{u, u, u} S SmallIndex :=
    LevelTwoUnconditional.relabelIndecomposableSkeleton tau smallToTau
  let ESmall :
      IndecomposableSkeleton.AlignedEquivalence tau tauSmall :=
    LevelTwoUnconditional.relabelAlignedEquivalence tau smallToTau
  have hsmall :
      tauSmall.qClosure.levelCount 2 =
        tauSmall.sClosure.levelCount 2 :=
    LevelTwoUnconditional.qLevelCount_two_eq_sLevelCount_two_of_finiteDimensional_of_finiteSkeleton
      K Rᵐᵒᵖ tauSmall
  have hq : B.skeleton.qClosure.levelCount 2 =
      tau.qClosure.levelCount 2 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.qClosureRelabeling
        B.skeleton tau E) 2
  have hs : B.skeleton.sClosure.levelCount 2 =
      tau.sClosure.levelCount 2 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.sClosureRelabeling
        B.skeleton tau E) 2
  have hqSmall : tau.qClosure.levelCount 2 =
      tauSmall.qClosure.levelCount 2 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.qClosureRelabeling
        tau tauSmall ESmall) 2
  have hsSmall : tau.sClosure.levelCount 2 =
      tauSmall.sClosure.levelCount 2 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.sClosureRelabeling
        tau tauSmall ESmall) 2
  exact hq.trans (hqSmall.trans (hsmall.trans (hsSmall.symm.trans hs.symm)))

variable {K}

theorem leftIdeal_ne_bot {R : Type u} [Ring R]
    (e : R) (he : IsIdempotentElem e) (hc : IsMulCentral e)
    (he0 : e ≠ 0) : leftIdeal e hc ≠ ⊥ := by
  intro hbot
  apply he0
  have hmem : e ∈ (⊥ : TwoSidedIdeal R) := by
    rw [← hbot]
    exact e_mem_leftIdeal e hc he
  simpa using hmem

theorem rightIdeal_ne_bot {R : Type u} [Ring R]
    (e : R) (he : IsIdempotentElem e) (hc : IsMulCentral e)
    (he1 : e ≠ 1) : rightIdeal e hc ≠ ⊥ := by
  intro hbot
  apply he1
  have hmem : 1 - e ∈ (⊥ : TwoSidedIdeal R) := by
    rw [← hbot]
    exact one_sub_mem_rightIdeal e hc he
  have hzero : 1 - e = 0 := by simpa using hmem
  exact (sub_eq_zero.mp hzero).symm

/-- The complete disconnected branch required by
`FiniteDimensionalRecurrence.RemainingData`: a nontrivial central
idempotent gives two strictly smaller quotient nodes, product convolution
handles their level counts, and Morita transport along the algebra
isomorphism returns the result to the original chosen skeleton. -/
theorem disconnected_levelCount_three_and_four_eq
    (K : Type u) [Field K] [IsAlgClosed K]
    (B : AlgebraNode K) (hNotB : ¬ IsBlockConnected K B)
    (ih : ∀ B' : AlgebraNode K, measure K B' < measure K B →
      (qClosure K B').levelCount 3 =
          (sClosure K B').levelCount 3 ∧
        (qClosure K B').levelCount 4 =
          (sClosure K B').levelCount 4) :
    (qClosure K B).levelCount 3 =
        (sClosure K B).levelCount 3 ∧
      (qClosure K B).levelCount 4 =
        (sClosure K B).levelCount 4 := by
  obtain ⟨e, he, hc, he0, he1⟩ :=
    exists_nontrivial_central_idempotent K B hNotB
  let I : TwoSidedIdeal B.Carrier := leftIdeal e hc
  let J : TwoSidedIdeal B.Carrier := rightIdeal e hc
  have hI : I ≠ ⊥ := leftIdeal_ne_bot e he hc he0
  have hJ : J ≠ ⊥ := rightIdeal_ne_bot e he hc he1
  let leftNode : AlgebraNode K := quotientNode K B I
  let rightNode : AlgebraNode K := quotientNode K B J
  have hleftMeasure : measure K leftNode < measure K B :=
    quotientNode_measure_lt K B I hI
  have hrightMeasure : measure K rightNode < measure K B :=
    quotientNode_measure_lt K B J hJ
  have hleftIH := ih leftNode hleftMeasure
  have hrightIH := ih rightNode hrightMeasure
  have hleft : ∀ n ≤ 4,
      leftNode.skeleton.qClosure.levelCount n =
        leftNode.skeleton.sClosure.levelCount n := by
    intro n hn
    have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl | rfl
    · exact
        IndecomposableSkeleton.qLevelCount_zero_eq_sLevelCount_zero
          leftNode.skeleton
    · exact
        IndecomposableSkeleton.qLevelCount_one_eq_sLevelCount_one
          leftNode.skeleton
    · exact levelCount_two_eq K leftNode
    · exact hleftIH.1
    · exact hleftIH.2
  have hright : ∀ n ≤ 4,
      rightNode.skeleton.qClosure.levelCount n =
        rightNode.skeleton.sClosure.levelCount n := by
    intro n hn
    have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
      omega
    rcases hnCases with rfl | rfl | rfl | rfl | rfl
    · exact
        IndecomposableSkeleton.qLevelCount_zero_eq_sLevelCount_zero
          rightNode.skeleton
    · exact
        IndecomposableSkeleton.qLevelCount_one_eq_sLevelCount_one
          rightNode.skeleton
    · exact levelCount_two_eq K rightNode
    · exact hrightIH.1
    · exact hrightIH.2
  let P :=
    AnnihilatorInflation.Quotient.Factor I ×
      AnnihilatorInflation.Quotient.Factor J
  letI artinianB : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  letI artinianP : IsArtinianRing P := IsArtinianRing.of_finite K P
  letI noetherianP : IsNoetherianRing P := inferInstance
  let rho := canonicalLeftSkeleton K P
  let splitEquiv : B.Carrier ≃ₐ[K] P :=
    algEquivQuotientProduct e hc he
  let morita : MoritaEquivalence K B.Carrier P :=
    MoritaEquivalence.ofAlgEquiv splitEquiv
  let E : IndecomposableSkeleton.AlignedEquivalence B.skeleton rho :=
    MoritaEquivalence.alignedFgEquivalence morita B.skeleton rho
  letI finiteRho : Finite (CanonicalIndecomposableIndex.{u, u} P) :=
    E.labelEquiv.finite_iff.mp B.finiteIndex
  have hproduct :
      rho.qClosure.levelCount 3 = rho.sClosure.levelCount 3 ∧
        rho.qClosure.levelCount 4 = rho.sClosure.levelCount 4 := by
    exact
      ProductModules.productRing_levelCount_three_and_four_eq
        leftNode.skeleton rightNode.skeleton rho hleft hright
  have hq3 : B.skeleton.qClosure.levelCount 3 =
      rho.qClosure.levelCount 3 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.qClosureRelabeling
        B.skeleton rho E) 3
  have hs3 : B.skeleton.sClosure.levelCount 3 =
      rho.sClosure.levelCount 3 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.sClosureRelabeling
        B.skeleton rho E) 3
  have hq4 : B.skeleton.qClosure.levelCount 4 =
      rho.qClosure.levelCount 4 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.qClosureRelabeling
        B.skeleton rho E) 4
  have hs4 : B.skeleton.sClosure.levelCount 4 =
      rho.sClosure.levelCount 4 :=
    SetClosure.ComponentwiseProduct.levelCount_eq_of_relabeling
      (IndecomposableSkeleton.AlignedEquivalence.sClosureRelabeling
        B.skeleton rho E) 4
  exact
    ⟨hq3.trans (hproduct.1.trans hs3.symm),
      hq4.trans (hproduct.2.trans hs4.symm)⟩

/-- With the disconnected branch now canonical, the repaired recurrence
data need only Ringel core cardinality and the connected small-core input. -/
theorem remainingData_of_ringel_and_smallCore
    (K : Type u) [Field K] [IsAlgClosed K]
    (ringel : ∀ B : AlgebraNode K,
      IndecomposableSkeleton.FaithfulCore.RingelCoreCardinality B.skeleton)
    (smallCore :
      ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
        IsBlockConnected K B →
        (((quotientCoreData K B).core : Set B.Index).ncard < n) →
        (faithfulQCount K B n = faithfulSCount K B n) ∨
          (qClosure K B).levelCount n =
            (sClosure K B).levelCount n) :
    RemainingData K (IsBlockConnected K) where
  ringel := ringel
  smallCore := smallCore
  disconnected := disconnected_levelCount_three_and_four_eq K

end Node

end QuotientSubmoduleEquidistribution.BlockDecomposition
