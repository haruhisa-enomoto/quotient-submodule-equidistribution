import OpConjecture.RepresentationTheory.MoritaA2Boundary

/-!
# The classification-free cardinality boundary at level three

The direct bottom-three split leaves faithful triples over factors whose
Ringel core has size two.  The existing one-simple and two-simple boundary
theorems imply that every such factor has at most three indecomposable
modules.  Consequently its faithful level-three fiber is a subsingleton,
inhabited exactly when the complete factor skeleton has three labels.

This file assembles that observation globally.  It proves the bottom-three
quotient--submodule equivalence and the common two-summand cardinality formula
with the second summand expressed intrinsically as the core-two factors having
three indecomposable isomorphism classes.  No concrete algebra model or module
classification is used.
-/

noncomputable section

open Set

namespace OpConjecture.ArtinBottomThree.CardinalityBoundary

universe u

open OpConjecture.AnnihilatorInflation
open OpConjecture.IndecomposableSkeleton
open OpConjecture.IndecomposableSkeleton.FaithfulCore

variable (K : Type u) [Field K]
  {R : Type u} [Ring R] [Algebra K R]
  [IsArtinianRing R] [IsNoetherianRing Rᵐᵒᵖ]

variable {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)
  (duality : ∀ I : TwoSidedIdeal R,
    ArtinDuality.Data (Quotient.Factor I))

open MoritaA2Boundary

/-- Core-two factor ideals whose complete canonical skeleton has exactly
three labels.  This is the intrinsic residual parameter at level three. -/
abbrev CardThreeCoreTwoFactorIdeal :=
  {I : CoreTwoFactorIdeal (R := R) //
    factorIndecomposableCount (R := R) I.1 = 3}

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Every core-two factor has at most three indecomposable isomorphism
classes.  The proof splits only by the number of simple modules and uses the
already established abstract one-simple and two-simple boundary theorems. -/
theorem factorIndecomposableCount_le_three
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R)) :
    factorIndecomposableCount (R := R) I.1 ≤ 3 := by
  rcases factorSimpleCount_eq_one_or_two K sigma I with hOne | hTwo
  · rw [factorIndecomposableCount_eq_two_of_oneSimple K sigma I hOne]
    omega
  · exact factorIndecomposableCount_le_three_of_twoSimple
      K sigma I hTwo

include sigma duality in
/-- A quotient-side residual fiber over a core-two factor is equivalent to
the proposition that the factor has exactly three indecomposables. -/
def qFiberEquivCardThree
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R)) :
    QFiber (R := R) I ≃
      PLift (factorIndecomposableCount (R := R) I.1 = 3) := by
  let tau := ArtinBottomThree.factorSkeleton (R := R) I.1
  letI factorOppositeNoetherian :
      IsNoetherianRing (Quotient.Factor I.1)ᵐᵒᵖ :=
    ArtinBottomTwo.factorOppositeNoetherian_of_oppositeNoetherian R I.1
  letI finiteFactorIndex : Finite
      (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I.1)) :=
    (factorNode K sigma I.1).finiteIndex
  let normal := ArtinDuality.faithfulNormalForm (duality I.1) tau
  have hle : factorIndecomposableCount (R := R) I.1 ≤ 3 :=
    factorIndecomposableCount_le_three K sigma I
  letI : Subsingleton (QFiber (R := R) I) := by
    simpa only [QFiber, tau,
      Skeleton.InflationData.FaithfulQLevel,
      SkeletonFaithfulQTriple] using
      faithfulQLevel_three_subsingleton_of_natCard_le tau hle
  apply equivPLiftOfSubsingletonIff
  simpa only [QFiber, tau,
    Skeleton.InflationData.FaithfulQLevel,
    SkeletonFaithfulQTriple,
    factorIndecomposableCount] using
    nonempty_faithfulQLevel_three_iff_natCard_eq tau normal hle

include sigma duality in
/-- The identical intrinsic description of the submodule-side residual
fiber. -/
def sFiberEquivCardThree
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R)) :
    SFiber (R := R) I ≃
      PLift (factorIndecomposableCount (R := R) I.1 = 3) := by
  let tau := ArtinBottomThree.factorSkeleton (R := R) I.1
  letI factorOppositeNoetherian :
      IsNoetherianRing (Quotient.Factor I.1)ᵐᵒᵖ :=
    ArtinBottomTwo.factorOppositeNoetherian_of_oppositeNoetherian R I.1
  letI finiteFactorIndex : Finite
      (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I.1)) :=
    (factorNode K sigma I.1).finiteIndex
  let normal := ArtinDuality.faithfulNormalForm (duality I.1) tau
  have hle : factorIndecomposableCount (R := R) I.1 ≤ 3 :=
    factorIndecomposableCount_le_three K sigma I
  letI : Subsingleton (SFiber (R := R) I) := by
    simpa only [SFiber, tau,
      Skeleton.InflationData.FaithfulSLevel,
      SkeletonFaithfulSTriple] using
      faithfulSLevel_three_subsingleton_of_natCard_le tau hle
  apply equivPLiftOfSubsingletonIff
  simpa only [SFiber, tau,
    Skeleton.InflationData.FaithfulSLevel,
    SkeletonFaithfulSTriple,
    factorIndecomposableCount] using
    nonempty_faithfulSLevel_three_iff_natCard_eq tau normal hle

/-- Forget the lifted equality proof in the sigma family of core-two
factors with three indecomposables. -/
def sigmaCardThreeEquiv :
    (Σ I : CoreTwoFactorIdeal (R := R),
      PLift (factorIndecomposableCount (R := R) I.1 = 3)) ≃
        CardThreeCoreTwoFactorIdeal (R := R) where
  toFun X := ⟨X.1, X.2.down⟩
  invFun I := ⟨I.1, PLift.up I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The quotient residual family is intrinsically parametrized by core-two
factors having three indecomposables. -/
def qResidualEquiv
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    ArtinBottomThree.CoreTwoFaithfulQTripleFiber (R := R) ≃
      CardThreeCoreTwoFactorIdeal (R := R) :=
  (Equiv.sigmaCongrRight (qFiberEquivCardThree K sigma duality)).trans
    (sigmaCardThreeEquiv (R := R))

/-- The submodule residual family has the same intrinsic parameter type. -/
def sResidualEquiv
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    ArtinBottomThree.CoreTwoFaithfulSTripleFiber (R := R) ≃
      CardThreeCoreTwoFactorIdeal (R := R) :=
  (Equiv.sigmaCongrRight (sFiberEquivCardThree K sigma duality)).trans
    (sigmaCardThreeEquiv (R := R))

/-- Classification-free bottom-three quotient parametrization. -/
def quotientTripleIdealEquiv
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    ArtinQTriple sigma ≃
      ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        CardThreeCoreTwoFactorIdeal (R := R) :=
  ArtinBottomThree.quotientTripleIdealEquiv sigma duality
    (qResidualEquiv K sigma duality)

/-- Classification-free bottom-three submodule parametrization. -/
def submoduleTripleIdealEquiv
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    ArtinSTriple sigma ≃
      ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        CardThreeCoreTwoFactorIdeal (R := R) :=
  ArtinBottomThree.submoduleTripleIdealEquiv sigma duality
    (sResidualEquiv K sigma duality)

/-- The unconditional level-three quotient--submodule equivalence, with no
concrete algebra recognition premise. -/
def tripleEquiv
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    ArtinQTriple sigma ≃ ArtinSTriple sigma :=
  ArtinBottomThree.tripleEquiv sigma duality
    (qResidualEquiv K sigma duality)
    (sResidualEquiv K sigma duality)

include duality in
/-- Exact quotient-side cardinality formula with the intrinsic residual
factor condition. -/
theorem quotientTriple_natCard_formula
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinQTriple sigma) =
      Nat.card (ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card (CardThreeCoreTwoFactorIdeal (R := R)) :=
  ArtinBottomThree.quotientTriple_natCard_formula sigma duality
    (qResidualEquiv K sigma duality)

include duality in
/-- The identical submodule-side cardinality formula. -/
theorem submoduleTriple_natCard_formula
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinSTriple sigma) =
      Nat.card (ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card (CardThreeCoreTwoFactorIdeal (R := R)) :=
  ArtinBottomThree.submoduleTriple_natCard_formula sigma duality
    (sResidualEquiv K sigma duality)

include duality in
/-- Direct numerical equality at level three. -/
theorem triple_natCard_eq
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota] :
    Nat.card (ArtinQTriple sigma) = Nat.card (ArtinSTriple sigma) :=
  Nat.card_congr (tripleEquiv K sigma duality)

end OpConjecture.ArtinBottomThree.CardinalityBoundary
