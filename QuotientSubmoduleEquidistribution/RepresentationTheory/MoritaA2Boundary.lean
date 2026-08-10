import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinBottomThree
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreAssembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.HereditaryTwoSimpleBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaConventionBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.OneSimpleCoreSaturation

/-!
# The residual Morita-`kA₂` boundary at level three

The classification-free bottom-three theorem splits both level-three types
into core-size-three factor ideals and faithful triples over core-size-two
factors.  This file gives the exact, paper-shaped interface for the sole
remaining local input: over a core-size-two factor, a faithful triple exists
uniquely precisely when the factor is Morita equivalent to a fixed `kA₂`
model.

No quiver presentation or concrete module classification is performed here.
The interface records the local theorem fiberwise and assembles it into the
literal ideal subtype and cardinality formula occurring in the manuscript.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary

universe u

open QuotientSubmoduleEquidistribution.AnnihilatorInflation
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence

variable (K : Type u) [Field K]
  {R : Type u} [Ring R] [Algebra K R]
  [IsArtinianRing R] [IsNoetherianRing Rᵐᵒᵖ]

/- Abstractly fixed finite-dimensional representation-finite node which is
to be instantiated by the path algebra `kA₂`. -/
variable (A₂ : AlgebraNode K)

/-- A factor belongs to the manuscript's second summand when it is Morita
equivalent to the fixed `kA₂` node. -/
def IsMoritaA2Factor (I : TwoSidedIdeal R) : Prop :=
  Nonempty (MoritaEquivalence K (Quotient.Factor I) A₂.Carrier)

/-- The literal ideal subtype in the displayed bottom-three formula. -/
abbrev MoritaA2FactorIdeal :=
  {I : TwoSidedIdeal R // IsMoritaA2Factor K A₂ I}

/-- The already-classified core-size-two factor-ideal subtype. -/
abbrev CoreTwoFactorIdeal :=
  ArtinBottomTwo.CoreTwoIdeal (R := R)

/-- The quotient residual fiber over one fixed core-size-two factor. -/
abbrev QFiber (I : CoreTwoFactorIdeal (R := R)) :=
  Skeleton.InflationData.FaithfulQLevel I.1
    (ArtinBottomThree.factorSkeleton (R := R) I.1) 3

/-- The submodule residual fiber over one fixed core-size-two factor. -/
abbrev SFiber (I : CoreTwoFactorIdeal (R := R)) :=
  Skeleton.InflationData.FaithfulSLevel I.1
    (ArtinBottomThree.factorSkeleton (R := R) I.1) 3

/-- Exact production input for the local classification.  The two fiber
equivalences assert existence and uniqueness precisely in the Morita-`kA₂`
case.  The final field removes the redundant core-size-two proof when the
fibers are assembled over all ideals. -/
structure ClassificationData where
  qFiberEquiv : ∀ I : CoreTwoFactorIdeal (R := R),
    QFiber (R := R) I ≃ PLift (IsMoritaA2Factor K A₂ I.1)
  sFiberEquiv : ∀ I : CoreTwoFactorIdeal (R := R),
    SFiber (R := R) I ≃ PLift (IsMoritaA2Factor K A₂ I.1)
  coreTwo_of_morita : ∀ I : TwoSidedIdeal R,
    IsMoritaA2Factor K A₂ I →
      (quotientCore (ArtinBottomThree.factorSkeleton (R := R) I) :
        Set (CanonicalIndecomposableIndex.{u, u}
          (Quotient.Factor I))).ncard = 2

/-- The theorem shape naturally produced by either small-rank branch:
each fiber is a proposition up to equivalence, and its inhabitation is
exactly the Morita-`kA₂` condition. -/
structure FiberData (I : CoreTwoFactorIdeal (R := R)) where
  qSubsingleton : Subsingleton (QFiber (R := R) I)
  sSubsingleton : Subsingleton (SFiber (R := R) I)
  qNonempty_iff :
    Nonempty (QFiber (R := R) I) ↔ IsMoritaA2Factor K A₂ I.1
  sNonempty_iff :
    Nonempty (SFiber (R := R) I) ↔ IsMoritaA2Factor K A₂ I.1

/-- A subsingleton type inhabited exactly when `P` holds is equivalent to
the proposition-valued type `PLift P`. -/
def equivPLiftOfSubsingletonIff
    {X : Type*} {P : Prop} [Subsingleton X]
    (h : Nonempty X ↔ P) : X ≃ PLift P where
  toFun x := PLift.up (h.mp ⟨x⟩)
  invFun p := Classical.choice (h.mpr p.down)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- An empty pair of residual fibers, together with exclusion of the
Morita-`kA₂` case, gives the required fiber classification data. -/
theorem FiberData.ofIsEmpty
    (I : CoreTwoFactorIdeal (R := R))
    (hq : IsEmpty (QFiber (R := R) I))
    (hs : IsEmpty (SFiber (R := R) I))
    (hnot : ¬ IsMoritaA2Factor K A₂ I.1) :
    FiberData K A₂ I where
  qSubsingleton :=
    ⟨fun x _ ↦ isEmptyElim x⟩
  sSubsingleton :=
    ⟨fun x _ ↦ isEmptyElim x⟩
  qNonempty_iff := by
    constructor
    · rintro ⟨x⟩
      exact isEmptyElim x
    · intro h
      exact False.elim (hnot h)
  sNonempty_iff := by
    constructor
    · rintro ⟨x⟩
      exact isEmptyElim x
    · intro h
      exact False.elim (hnot h)

/-- Fiberwise existence and uniqueness construct the exact global
classification package. -/
def ClassificationData.ofFiberData
    (fiber : ∀ I : CoreTwoFactorIdeal (R := R),
      FiberData K A₂ I)
    (coreTwo : ∀ I : TwoSidedIdeal R,
      IsMoritaA2Factor K A₂ I →
        (quotientCore (ArtinBottomThree.factorSkeleton (R := R) I) :
          Set (CanonicalIndecomposableIndex.{u, u}
            (Quotient.Factor I))).ncard = 2) :
    ClassificationData K A₂ (R := R) where
  qFiberEquiv I := by
    letI := (fiber I).qSubsingleton
    exact equivPLiftOfSubsingletonIff (fiber I).qNonempty_iff
  sFiberEquiv I := by
    letI := (fiber I).sSubsingleton
    exact equivPLiftOfSubsingletonIff (fiber I).sNonempty_iff
  coreTwo_of_morita := coreTwo

/-- Forget the core-size-two proof in a sigma family whose proposition
itself forces core size two. -/
def sigmaMoritaEquiv (D : ClassificationData K A₂ (R := R)) :
    (Σ I : CoreTwoFactorIdeal (R := R),
      PLift (IsMoritaA2Factor K A₂ I.1)) ≃
        MoritaA2FactorIdeal K A₂ (R := R) where
  toFun X := ⟨X.1.1, X.2.down⟩
  invFun I :=
    ⟨⟨I.1, D.coreTwo_of_morita I.1 I.2⟩, PLift.up I.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Assemble the quotient residual fibers into the exact Morita-`kA₂`
ideal subtype. -/
def qResidualEquiv (D : ClassificationData K A₂ (R := R)) :
    ArtinBottomThree.CoreTwoFaithfulQTripleFiber (R := R) ≃
      MoritaA2FactorIdeal K A₂ (R := R) :=
  (Equiv.sigmaCongrRight D.qFiberEquiv).trans
    (sigmaMoritaEquiv K A₂ D)

/-- Assemble the submodule residual fibers into the same ideal subtype. -/
def sResidualEquiv (D : ClassificationData K A₂ (R := R)) :
    ArtinBottomThree.CoreTwoFaithfulSTripleFiber (R := R) ≃
      MoritaA2FactorIdeal K A₂ (R := R) :=
  (Equiv.sigmaCongrRight D.sFiberEquiv).trans
    (sigmaMoritaEquiv K A₂ D)

variable {iota : Type (u + 1)}
  (sigma : IndecomposableSkeleton.{u, u + 1, u} R iota)
  (duality : ∀ I : TwoSidedIdeal R,
    ArtinDuality.Data (Quotient.Factor I))

/-- Package a canonical factor at the existing finite-dimensional node
interface.  Finiteness of its index follows from inflation into the finite
ambient skeleton. -/
def factorNode [FiniteDimensional K R] [Finite iota]
    (I : TwoSidedIdeal R) : AlgebraNode K := by
  letI factorNoetherian : IsNoetherianRing (Quotient.Factor I) :=
    IsNoetherianRing.of_finite K (Quotient.Factor I)
  letI factorOppositeNoetherian :
      IsNoetherianRing (Quotient.Factor I)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional
      K (Quotient.Factor I)
  let inflation :=
    QuotientSubmoduleEquidistribution.QuotientSkeletonAlignment.artinInflationData sigma I
  exact
    { Carrier := Quotient.Factor I
      ring := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      noetherian := inferInstance
      noetherianOpposite := inferInstance
      Index := CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I)
      finiteIndex :=
        Finite.of_injective inflation.label inflation.label.injective
      skeleton := ArtinBottomThree.factorSkeleton (R := R) I }

/-- The number of simple modules of the canonical factor node. -/
abbrev factorSimpleCount [FiniteDimensional K R] [Finite iota]
    (I : TwoSidedIdeal R) : ℕ :=
  Nat.card (factorNode K sigma I).skeleton.SimpleIndex

/-- The number of indecomposable modules in the canonical complete factor
skeleton.  This is the only module-counting datum needed to manufacture the
residual level-three fibers. -/
abbrev factorIndecomposableCount
    (I : TwoSidedIdeal R) : ℕ :=
  Nat.card
    (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I))

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Ordinary Morita equivalence preserves the total number of
indecomposable isomorphism classes in the canonical complete skeleton. -/
theorem factorIndecomposableCount_eq_model_of_morita
    [FiniteDimensional K R] [Finite iota]
    (I : TwoSidedIdeal R)
    (hI : IsMoritaA2Factor K A₂ I) :
    factorIndecomposableCount (R := R) I = Nat.card A₂.Index := by
  obtain ⟨e⟩ := hI
  let B := factorNode K sigma I
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing A₂.Carrier :=
    IsArtinianRing.of_finite K A₂.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    e B.skeleton A₂.skeleton
  change Nat.card B.Index = Nat.card A₂.Index
  exact Nat.card_congr E.labelEquiv

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- Ordinary Morita equivalence also preserves the number of simple
isomorphism classes. -/
theorem factorSimpleCount_eq_model_of_morita
    [FiniteDimensional K R] [Finite iota]
    (I : TwoSidedIdeal R)
    (hI : IsMoritaA2Factor K A₂ I) :
    factorSimpleCount K sigma I =
      Nat.card A₂.skeleton.SimpleIndex := by
  obtain ⟨e⟩ := hI
  let B := factorNode K sigma I
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K B.Carrier
  letI : IsArtinianRing A₂.Carrier :=
    IsArtinianRing.of_finite K A₂.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence
    e B.skeleton A₂.skeleton
  change Nat.card B.skeleton.SimpleIndex =
    Nat.card A₂.skeleton.SimpleIndex
  exact Nat.card_congr
    (QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.simpleIndexEquiv
      B.skeleton A₂.skeleton E)

include sigma duality in
/-- If a core-two factor has at most three indecomposables, and it has
exactly three precisely in the Morita-`kA₂` case, then both residual
level-three fibers have the required existence-and-uniqueness
classification.  Thus the local representation-theoretic seam can be
supplied purely as a total-skeleton cardinality theorem. -/
theorem FiberData.ofIndecomposableCardinality
    [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R))
    (hcard_le : factorIndecomposableCount (R := R) I.1 ≤ 3)
    (hcard_iff :
      factorIndecomposableCount (R := R) I.1 = 3 ↔
        IsMoritaA2Factor K A₂ I.1) :
    FiberData K A₂ I := by
  let τ := ArtinBottomThree.factorSkeleton (R := R) I.1
  letI factorOppositeNoetherian :
      IsNoetherianRing (Quotient.Factor I.1)ᵐᵒᵖ :=
    ArtinBottomTwo.factorOppositeNoetherian_of_oppositeNoetherian R I.1
  letI finiteFactorIndex : Finite
      (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I.1)) :=
    (factorNode K sigma I.1).finiteIndex
  let normal := ArtinDuality.faithfulNormalForm (duality I.1) τ
  refine
    { qSubsingleton := ?_
      sSubsingleton := ?_
      qNonempty_iff := ?_
      sNonempty_iff := ?_ }
  · simpa only [QFiber, τ,
      Skeleton.InflationData.FaithfulQLevel,
      SkeletonFaithfulQTriple] using
      faithfulQLevel_three_subsingleton_of_natCard_le τ hcard_le
  · simpa only [SFiber, τ,
      Skeleton.InflationData.FaithfulSLevel,
      SkeletonFaithfulSTriple] using
      faithfulSLevel_three_subsingleton_of_natCard_le τ hcard_le
  · simpa only [QFiber, τ,
      Skeleton.InflationData.FaithfulQLevel,
      SkeletonFaithfulQTriple,
      factorIndecomposableCount] using
      (nonempty_faithfulQLevel_three_iff_natCard_eq
        τ normal hcard_le).trans hcard_iff
  · simpa only [SFiber, τ,
      Skeleton.InflationData.FaithfulSLevel,
      SkeletonFaithfulSTriple,
      factorIndecomposableCount] using
      (nonempty_faithfulSLevel_three_iff_natCard_eq
        τ normal hcard_le).trans hcard_iff

include sigma duality in
/-- It is enough to prove only the classification direction
"three indecomposables imply Morita-`kA₂`".  The reverse direction follows
formally from Morita invariance once the fixed model is known to have three
indecomposables. -/
theorem FiberData.ofBoundAndCardThreeMorita
    [FiniteDimensional K R] [Finite iota]
    (hA₂card : Nat.card A₂.Index = 3)
    (I : CoreTwoFactorIdeal (R := R))
    (hcard_le : factorIndecomposableCount (R := R) I.1 ≤ 3)
    (hmorita : factorIndecomposableCount (R := R) I.1 = 3 →
      IsMoritaA2Factor K A₂ I.1) :
    FiberData K A₂ I := by
  apply FiberData.ofIndecomposableCardinality K A₂ sigma duality I
    hcard_le
  constructor
  · exact hmorita
  · intro hI
    exact (factorIndecomposableCount_eq_model_of_morita
      K A₂ sigma I.1 hI).trans hA₂card

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- The projective--simple bijection identifies the connected-small-core
projective count with the literal simple count of a canonical factor. -/
theorem projectiveCount_factorNode_eq_factorSimpleCount
    [FiniteDimensional K R] [Finite iota]
    (I : TwoSidedIdeal R) :
    projectiveCount K (factorNode K sigma I) =
      factorSimpleCount K sigma I :=
  ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
    (factorNode K sigma I).skeleton

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- A core-size-two factor with two simple modules has at most three
indecomposable modules.  This is the classification-free categorical part
of the two-simple boundary. -/
theorem factorIndecomposableCount_le_three_of_twoSimple
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R))
    (hTwo : factorSimpleCount K sigma I.1 = 2) :
    factorIndecomposableCount (R := R) I.1 ≤ 3 := by
  let B := factorNode K sigma I.1
  have hTwoB : Nat.card B.skeleton.SimpleIndex = 2 := by
    simpa [B] using hTwo
  have hcore : coreSize K B = 2 := by
    simpa [B, factorNode, coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using I.2
  have hvd : projectiveCount K B = coreSize K B := by
    calc
      projectiveCount K B = Nat.card B.skeleton.SimpleIndex :=
        ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex
          B.skeleton
      _ = 2 := hTwoB
      _ = coreSize K B := hcore.symm
  have hbound : Nat.card B.Index ≤ 3 :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.AlgebraNode.indexCard_le_three_of_twoSimples_of_projectiveCount_eq_coreSize
      K B hTwoB hvd
  simpa [factorIndecomposableCount, B, factorNode] using hbound

include sigma duality in
/-- Consequently, the only remaining two-simple input needed for the
level-three fiber is the forward classification statement that cardinality
three implies Morita equivalence to the fixed `kA₂` model. -/
theorem FiberData.ofCardThreeMorita
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (hA₂card : Nat.card A₂.Index = 3)
    (I : CoreTwoFactorIdeal (R := R))
    (hTwo : factorSimpleCount K sigma I.1 = 2)
    (hmorita : factorIndecomposableCount (R := R) I.1 = 3 →
      IsMoritaA2Factor K A₂ I.1) :
    FiberData K A₂ I := by
  exact FiberData.ofBoundAndCardThreeMorita
    K A₂ sigma duality hA₂card I
      (factorIndecomposableCount_le_three_of_twoSimple
        K sigma I hTwo)
      hmorita

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- In the one-simple/core-two branch the complete factor skeleton has
exactly two labels.  This is the node-level assembly of the existing
classification-free one-simple saturation theorem. -/
theorem factorIndecomposableCount_eq_two_of_oneSimple
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R))
    (hOne : factorSimpleCount K sigma I.1 = 1) :
    factorIndecomposableCount (R := R) I.1 = 2 := by
  let B := factorNode K sigma I.1
  letI : IsArtinianRing B.Carrier :=
    IsArtinianRing.of_finite K B.Carrier
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let D :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} B.Carrierᵐᵒᵖ) :=
    D.forward.labelEquiv.finite_iff.mp inferInstance
  have hOneB :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.OneSimple B.skeleton := by
    simpa [QuotientSubmoduleEquidistribution.LocalNakayamaBranch.OneSimple, B] using hOne
  have hNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) B.skeleton :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.noParallelExtSupport_of_finiteDimensional
      B.skeleton
  have hDualNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) tau :=
    QuotientSubmoduleEquidistribution.HereditaryTwoSimpleBoundary.noParallelExtSupport_of_finiteDimensional
      tau
  have hSaturation :
      (submoduleCore B.skeleton : Set B.Index) = Set.univ :=
    QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation.submoduleCore_eq_univ_of_oneSimple_of_noParallel
      B.skeleton tau D hOneB hNoParallel hDualNoParallel
  have hRingel : RingelCoreCardinality B.skeleton :=
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      B.skeleton K
  have hcoreSize : coreSize K B = 2 := by
    simpa [B, factorNode, coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using I.2
  have hcore :
      (quotientCore B.skeleton : Set B.Index).ncard = 2 := by
    simpa [coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using hcoreSize
  have hcard : Nat.card B.Index = 2 :=
    QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation.natCard_eq_two_of_coreTwo_of_submoduleCore_eq_univ
      B.skeleton hRingel hcore hSaturation
  simpa [factorIndecomposableCount, B, factorNode] using hcard

include sigma in
omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- If the fixed `kA₂` model has two simple modules, the one-simple branch
has empty level-three fibers and cannot be Morita equivalent to that model. -/
theorem FiberData.ofOneSimple
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (hA₂simple : Nat.card A₂.skeleton.SimpleIndex = 2)
    (I : CoreTwoFactorIdeal (R := R))
    (hOne : factorSimpleCount K sigma I.1 = 1) :
    FiberData K A₂ I := by
  let tau := ArtinBottomThree.factorSkeleton (R := R) I.1
  letI : Finite
      (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I.1)) :=
    (factorNode K sigma I.1).finiteIndex
  have hcard : Nat.card
      (CanonicalIndecomposableIndex.{u, u} (Quotient.Factor I.1)) = 2 :=
    factorIndecomposableCount_eq_two_of_oneSimple K sigma I hOne
  have hqLevel : IsEmpty (ArtinQLevel tau 3) :=
    QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation.isEmpty_qLevel_three_of_natCard_eq_two
      tau hcard
  have hsLevel : IsEmpty (ArtinSLevel tau 3) :=
    QuotientSubmoduleEquidistribution.OneSimpleCoreSaturation.isEmpty_sLevel_three_of_natCard_eq_two
      tau hcard
  have hq : IsEmpty (QFiber (R := R) I) := by
    constructor
    intro C
    exact isEmptyElim (α := ArtinQLevel tau 3)
      ⟨C.1, C.2.2⟩
  have hs : IsEmpty (SFiber (R := R) I) := by
    constructor
    intro C
    exact isEmptyElim (α := ArtinSLevel tau 3)
      ⟨C.1, C.2.2⟩
  have hnot : ¬ IsMoritaA2Factor K A₂ I.1 := by
    intro hI
    have hsimple := factorSimpleCount_eq_model_of_morita
      K A₂ sigma I.1 hI
    rw [hOne, hA₂simple] at hsimple
    omega
  exact FiberData.ofIsEmpty K A₂ I hq hs hnot

omit [IsNoetherianRing Rᵐᵒᵖ] in
/-- A core-size-two nonzero factor has either one or two simple modules.
This is the complete rank dichotomy used to split the local classification. -/
theorem factorSimpleCount_eq_one_or_two
    [FiniteDimensional K R] [Finite iota]
    (I : CoreTwoFactorIdeal (R := R)) :
    factorSimpleCount K sigma I.1 = 1 ∨
      factorSimpleCount K sigma I.1 = 2 := by
  let B := factorNode K sigma I.1
  have hcore : coreSize K B = 2 := by
    simpa [B, factorNode, coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using I.2
  have hcoreCard :
      (((AlgebraNode.quotientCoreData K B).core : Set B.Index)).ncard = 2 :=
    hcore
  have hcoreNonempty :
      (((AlgebraNode.quotientCoreData K B).core : Set B.Index)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hcoreCard]; omega)
  obtain ⟨j, _hj⟩ := hcoreNonempty
  letI : Nontrivial (B.skeleton.obj j) :=
    (B.skeleton.indecomposable j).nontrivial
  letI : Nontrivial B.Carrier :=
    Module.nontrivial B.Carrier (B.skeleton.obj j)
  have hpos : 0 < projectiveCount K B :=
    AlgebraNode.projectiveCount_pos K B
  have hle : projectiveCount K B ≤ 2 := by
    simpa [hcore] using projectiveCount_le_coreSize K B
  rw [show projectiveCount K B = factorSimpleCount K sigma I.1 by
    simpa [B] using
      projectiveCount_factorNode_eq_factorSimpleCount K sigma I.1] at hpos hle
  omega

/-- The one-simple and two-simple local theorems assemble solely by the
simple/projective count of the canonical factor. -/
def ClassificationData.ofRankBranches
    [FiniteDimensional K R] [Finite iota]
    (oneSimple : ∀ I : CoreTwoFactorIdeal (R := R),
      factorSimpleCount K sigma I.1 = 1 →
        FiberData K A₂ I)
    (twoSimple : ∀ I : CoreTwoFactorIdeal (R := R),
      factorSimpleCount K sigma I.1 = 2 →
        FiberData K A₂ I)
    (coreTwo : ∀ I : TwoSidedIdeal R,
      IsMoritaA2Factor K A₂ I →
        (quotientCore (ArtinBottomThree.factorSkeleton (R := R) I) :
          Set (CanonicalIndecomposableIndex.{u, u}
            (Quotient.Factor I))).ncard = 2) :
    ClassificationData K A₂ (R := R) :=
  ClassificationData.ofFiberData K A₂
    (fun I ↦ (factorSimpleCount_eq_one_or_two K sigma I).elim
      (oneSimple I) (twoSimple I)) coreTwo

/-- Complete classification-data assembly after the categorical work in
both rank branches.  The only factor-dependent premise left is the narrow
forward implication that a two-simple core-two factor with exactly three
indecomposables is Morita equivalent to the fixed `kA₂` model. -/
def ClassificationData.ofCardThreeMorita
    [IsAlgClosed K] [FiniteDimensional K R] [Finite iota]
    (hA₂card : Nat.card A₂.Index = 3)
    (hA₂simple : Nat.card A₂.skeleton.SimpleIndex = 2)
    (hmorita : ∀ I : CoreTwoFactorIdeal (R := R),
      factorSimpleCount K sigma I.1 = 2 →
        factorIndecomposableCount (R := R) I.1 = 3 →
          IsMoritaA2Factor K A₂ I.1)
    (coreTwo : ∀ I : TwoSidedIdeal R,
      IsMoritaA2Factor K A₂ I →
        (quotientCore (ArtinBottomThree.factorSkeleton (R := R) I) :
          Set (CanonicalIndecomposableIndex.{u, u}
            (Quotient.Factor I))).ncard = 2) :
    ClassificationData K A₂ (R := R) :=
  ClassificationData.ofRankBranches K A₂ sigma
    (fun I hOne ↦ FiberData.ofOneSimple
      K A₂ sigma hA₂simple I hOne)
    (fun I hTwo ↦ FiberData.ofCardThreeMorita
      K A₂ sigma duality hA₂card I hTwo (hmorita I hTwo))
    coreTwo

/-- Paper-shaped quotient parametrization. -/
def quotientTripleIdealEquiv
    (D : ClassificationData K A₂ (R := R)) :
    ArtinQTriple sigma ≃
      ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        MoritaA2FactorIdeal K A₂ (R := R) :=
  ArtinBottomThree.quotientTripleIdealEquiv sigma duality
    (qResidualEquiv K A₂ D)

/-- Paper-shaped submodule parametrization. -/
def submoduleTripleIdealEquiv
    (D : ClassificationData K A₂ (R := R)) :
    ArtinSTriple sigma ≃
      ArtinBottomThree.CoreThreeFactorIdeal (R := R) ⊕
        MoritaA2FactorIdeal K A₂ (R := R) :=
  ArtinBottomThree.submoduleTripleIdealEquiv sigma duality
    (sResidualEquiv K A₂ D)

/-- Direct bottom-three quotient--submodule equivalence after the narrow
local classification input. -/
def tripleEquiv (D : ClassificationData K A₂ (R := R)) :
    ArtinQTriple sigma ≃ ArtinSTriple sigma :=
  ArtinBottomThree.tripleEquiv sigma duality
    (qResidualEquiv K A₂ D)
    (sResidualEquiv K A₂ D)

include duality in
/-- Exact quotient-side cardinality formula in the manuscript's two
ideal-summand form. -/
theorem quotientTriple_natCard_formula [Finite iota]
    (D : ClassificationData K A₂ (R := R)) :
    Nat.card (ArtinQTriple sigma) =
      Nat.card (ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card (MoritaA2FactorIdeal K A₂ (R := R)) :=
  ArtinBottomThree.quotientTriple_natCard_formula sigma duality
    (qResidualEquiv K A₂ D)

include duality in
/-- The identical submodule-side cardinality formula. -/
theorem submoduleTriple_natCard_formula [Finite iota]
    (D : ClassificationData K A₂ (R := R)) :
    Nat.card (ArtinSTriple sigma) =
      Nat.card (ArtinBottomThree.CoreThreeFactorIdeal (R := R)) +
        Nat.card (MoritaA2FactorIdeal K A₂ (R := R)) :=
  ArtinBottomThree.submoduleTriple_natCard_formula sigma duality
    (sResidualEquiv K A₂ D)

include duality in
/-- Direct numerical equality at level three. -/
theorem triple_natCard_eq (D : ClassificationData K A₂ (R := R)) :
    Nat.card (ArtinQTriple sigma) = Nat.card (ArtinSTriple sigma) :=
  Nat.card_congr (tripleEquiv K A₂ sigma duality D)

end QuotientSubmoduleEquidistribution.ArtinBottomThree.MoritaA2Boundary
