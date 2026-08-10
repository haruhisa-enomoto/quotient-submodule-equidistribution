import QuotientSubmoduleEquidistribution.RepresentationTheory.FullIdempotentMorita
import QuotientSubmoduleEquidistribution.RepresentationTheory.OneSimpleBasicizationInterface
import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateSimpleAlignment
import QuotientSubmoduleEquidistribution.RepresentationTheory.ContragredientDuality

/-!
# Ordinary Morita basicization in the one-simple branch

This file records the strongest general adapter available without a Gabriel
presentation or a module classification.  Ordinary basicization supplies the
basic carrier, Morita equivalence, and scalar residue; the only remaining
datum is a generator for the Jacobson cotangent space.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LocalNakayamaBranch

universe u

open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.MoritaBasicizationInterface

variable {K : Type u} [Field K] [IsAlgClosed K]

namespace MoritaBasicizationAdapter

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

/-- The exact datum not supplied by ordinary Morita basicization in the
one-simple profile argument: one radical element spans the Jacobson
cotangent space as a left module. -/
structure CyclicCotangentGenerator
    {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
    (P : MoritaBasicModel (K := K) (A := A)) where
  generator : P.Carrier
  generator_mem_jacobson : generator ∈ Ring.jacobson P.Carrier
  cyclicCotangent :
    (Ring.jacobson P.Carrier : Submodule P.Carrier P.Carrier) ≤
      P.Carrier ∙ generator ⊔
        (Ring.jacobson P.Carrier : Submodule P.Carrier P.Carrier) •
          (Ring.jacobson P.Carrier : Submodule P.Carrier P.Carrier)

namespace CyclicCotangentGenerator

variable {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
  {P : MoritaBasicModel (K := K) (A := A)}

end CyclicCotangentGenerator

omit [IsAlgClosed K] in
/-- Morita transport sends the one-simple condition on the source skeleton
to the canonical skeleton of an ordinary basic model. -/
theorem target_oneSimple_of_projectiveRank_eq_one
    (B : AlgebraNode K)
    (P : MoritaBasicModel (K := K) (A := B.Carrier))
    (hB : projectiveRank B.skeleton = 1) :
    OneSimple (algebraNodeMoritaTarget B P.morita).skeleton := by
  let D := algebraNodeMoritaTarget B P.morita
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing P.Carrier := IsArtinianRing.of_finite K P.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    P.morita B.skeleton D.skeleton
  have hpoly :
      B.skeleton.qClosure.levelPolynomial =
        D.skeleton.qClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      B.skeleton D.skeleton E
  have hcount :
      B.skeleton.qClosure.levelCount 1 =
        D.skeleton.qClosure.levelCount 1 := by
    rw [← QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff,
      hpoly, QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff]
  have hs : OneSimple B.skeleton :=
    (oneSimple_iff_projectiveRank_eq_one B.skeleton).2 hB
  rw [B.skeleton.qLevelCount_one_eq_natCard_simpleIndex,
    D.skeleton.qLevelCount_one_eq_natCard_simpleIndex] at hcount
  change Nat.card D.skeleton.SimpleIndex = 1
  change Nat.card B.skeleton.SimpleIndex = 1 at hs
  exact hcount.symm.trans hs

/-- Basicness over an algebraically closed field supplies scalar residue in
the one-simple branch.  No Gabriel presentation is used: quotient coordinates
are aligned with the target skeleton and hence have exactly one coordinate. -/
theorem splitResidue_of_projectiveRank_eq_one
    (B : AlgebraNode K)
    (P : MoritaBasicModel (K := K) (A := B.Carrier))
    (hB : projectiveRank B.skeleton = 1) :
    ∀ d : P.Carrier, ∃ k : K,
      d - algebraMap K P.Carrier k ∈ Ring.jacobson P.Carrier := by
  letI : Ring P.Carrier := P.ring
  letI : Algebra K P.Carrier := P.algebra
  letI : FiniteDimensional K P.Carrier := P.finiteDimensional
  letI : IsNoetherianRing P.Carrier :=
    IsNoetherianRing.of_finite K P.Carrier
  letI : IsArtinianRing P.Carrier :=
    IsArtinianRing.of_finite K P.Carrier
  letI : IsNoetherianRing P.Carrierᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K P.Carrier
  obtain ⟨n, ⟨Q⟩⟩ :=
    QuotientSubmoduleEquidistribution.MoritaBasicizationInterface.MoritaBasicModel.exists_target_quotientCoordinateData
      P
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  let sigma :=
    QuotientSubmoduleEquidistribution.BlockDecomposition.Node.canonicalLeftSkeleton K P.Carrier
  let E :=
    MoritaEquivalence.alignedFgEquivalence P.morita B.skeleton sigma
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        P.Carrier) :=
    E.labelEquiv.finite_iff.mp inferInstance
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K P.Carrier
  let dual :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K P.Carrier sigma tau
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        P.Carrierᵐᵒᵖ) :=
    dual.forward.labelEquiv.finite_iff.mp inferInstance
  have hone : OneSimple sigma := by
    have hpoly :
        B.skeleton.qClosure.levelPolynomial =
          sigma.qClosure.levelPolynomial :=
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
        B.skeleton sigma E
    have hcount :
        B.skeleton.qClosure.levelCount 1 =
          sigma.qClosure.levelCount 1 := by
      rw [← QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff,
        hpoly, QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff]
    rw [B.skeleton.qLevelCount_one_eq_natCard_simpleIndex,
      sigma.qLevelCount_one_eq_natCard_simpleIndex] at hcount
    have hsource : OneSimple B.skeleton :=
      (oneSimple_iff_projectiveRank_eq_one B.skeleton).2 hB
    change Nat.card B.skeleton.SimpleIndex = 1 at hsource
    change Nat.card sigma.SimpleIndex = 1
    exact hcount.symm.trans hsource
  have htau : OneSimple tau := by
    have hpoly :
        sigma.qClosure.levelPolynomial =
          tau.sClosure.levelPolynomial :=
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.quotientToSubmoduleLevelPolynomial_eq
        sigma tau dual
    have hcount :
        sigma.qClosure.levelCount 1 =
          tau.sClosure.levelCount 1 := by
      rw [← QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff,
        hpoly, QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff]
    rw [sigma.qLevelCount_one_eq_natCard_simpleIndex,
      tau.sLevelCount_one_eq_natCard_simpleIndex] at hcount
    change Nat.card sigma.SimpleIndex = 1 at hone
    change Nat.card tau.SimpleIndex = 1
    exact hcount.symm.trans hone
  have hcard : n = 1 := by
    have heq : Nat.card (Fin n) = Nat.card tau.SimpleIndex :=
      Nat.card_congr
        (QuotientSubmoduleEquidistribution.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
          Q tau)
    change Nat.card tau.SimpleIndex = 1 at htau
    simpa using heq.trans htau
  subst n
  intro d
  let k : K :=
    Q.quotientEquiv
      (Ideal.Quotient.mk (Ring.jacobson P.Carrier) d) 0
  refine ⟨k, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply Q.quotientEquiv.injective
  ext i
  fin_cases i
  simp [k]

/-- An ordinary basic model needs no extra residue or presentation field in
the one-simple branch.  A cyclic cotangent generator is the sole additional
datum required by the maintained monogenicity bridge. -/
noncomputable def toMoritaSplitCyclicCotangentModel
    (B : AlgebraNode K)
    (P : MoritaBasicModel (K := K) (A := B.Carrier))
    (hB : projectiveRank B.skeleton = 1)
    (C : CyclicCotangentGenerator P) :
    MoritaSplitCyclicCotangentModel K B where
  Carrier := P.Carrier
  ring := P.ring
  algebra := P.algebra
  finiteDimensional := P.finiteDimensional
  morita := P.morita
  generator := C.generator
  generator_mem_jacobson := C.generator_mem_jacobson
  splitResidue := splitResidue_of_projectiveRank_eq_one B P hB
  cyclicCotangent := C.cyclicCotangent

/-- Direct profile endpoint: ordinary Morita basicization together with the
single residual cotangent generator proves the full OP profile equality. -/
theorem levelPolynomial_eq_of_basicModelCyclicCotangent
    (B : AlgebraNode K)
    (P : MoritaBasicModel (K := K) (A := B.Carrier))
    (hB : projectiveRank B.skeleton = 1)
    (C : CyclicCotangentGenerator P) :
    (AlgebraNode.qClosure K B).levelPolynomial =
      (AlgebraNode.sClosure K B).levelPolynomial :=
  (toMoritaSplitCyclicCotangentModel B P hB C).levelPolynomial_eq

/-- The exact residual theorem after ordinary basicization: every basic
model of a projective-rank-one node has a cyclic Jacobson cotangent
generator.  It contains no Morita-equivalence, basicness, residue-splitting,
or presentation field. -/
def ProjectiveRankOneBasicCyclicCotangentUpgrade : Prop :=
  ∀ (B : AlgebraNode K)
    (P : MoritaBasicModel (K := K) (A := B.Carrier)),
    projectiveRank B.skeleton = 1 →
      Nonempty (CyclicCotangentGenerator P)

/-- Unconditional full-idempotent basicization discharges all model fields;
the cyclic-cotangent upgrade alone implies the maintained one-simple
classification interface. -/
theorem projectiveRankOneMoritaSplitCyclicCotangentClassification_of_upgrade
    (hupgrade : ProjectiveRankOneBasicCyclicCotangentUpgrade (K := K)) :
    ProjectiveRankOneMoritaSplitCyclicCotangentClassification K := by
  intro B hB
  let P : MoritaBasicModel (K := K) (A := B.Carrier) :=
    (QuotientSubmoduleEquidistribution.FullIdempotentMorita.finiteDimensionalMoritaBasicization
      K B.Carrier).some
  obtain ⟨C⟩ := hupgrade B P hB
  exact ⟨toMoritaSplitCyclicCotangentModel B P hB C⟩

/-- Consequently the same sole cotangent upgrade proves the full profile in
the projective-rank-one branch. -/
theorem levelPolynomial_eq_of_projectiveRank_eq_one_of_basicCyclicCotangentUpgrade
    (hupgrade : ProjectiveRankOneBasicCyclicCotangentUpgrade (K := K))
    (B : AlgebraNode K)
    (hB : projectiveRank B.skeleton = 1) :
    (AlgebraNode.qClosure K B).levelPolynomial =
      (AlgebraNode.sClosure K B).levelPolynomial :=
  levelPolynomial_eq_of_projectiveRank_eq_one_of_splitCyclicCotangent
    (projectiveRankOneMoritaSplitCyclicCotangentClassification_of_upgrade
      hupgrade)
    B hB

end MoritaBasicizationAdapter

end QuotientSubmoduleEquidistribution.LocalNakayamaBranch
