import OpConjecture.RepresentationTheory.ConnectedSmallCoreHereditary
import OpConjecture.RepresentationTheory.FiniteDimensionalNoParallelExt
import OpConjecture.RepresentationTheory.FiniteDimensionalRecurrence
import OpConjecture.RepresentationTheory.BlockDecomposition
import OpConjecture.RepresentationTheory.RingelEtaCoreCardinality
import OpConjecture.RepresentationTheory.MoritaConsequences
import OpConjecture.RepresentationTheory.OppositeDuality
import OpConjecture.RepresentationTheory.ProjectiveSimpleRank
import OpConjecture.RepresentationTheory.NakayamaChainClosureAdapter
import OpConjecture.RepresentationTheory.OneLoopProfileEquality
import OpConjecture.RepresentationTheory.OneSimpleBasicizationInterface
import OpConjecture.RepresentationTheory.OneSimpleCoreSaturation
import OpConjecture.Combinatorics.ConnectedSmallCore
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Connected small-core assembly at the finite-dimensional node interface

This file makes the current hereditary/Dynkin gap precise without
postulating it as a fact about the ambient algebra.

The maintained Ringel theorem and the collapse theorem already prove that
`projectiveRank = coreSize` makes every left ideal projective.  A future
Gabriel theorem may replace the algebra by a Morita-equivalent Dynkin model;
the existing skeleton-alignment machinery then transports the Dynkin profile
back to the original node.
-/

noncomputable section

open Set

namespace OpConjecture.BottomLevels.FiniteDimensionalRecurrence

open OpConjecture.IndecomposableSkeleton.FaithfulCore
open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

variable (K : Type u) [Field K]

/-- The profile equality required from a Dynkin model. -/
abbrev FullProfileEquality (B : AlgebraNode K) : Prop :=
  (AlgebraNode.qClosure K B).levelPolynomial =
    (AlgebraNode.sClosure K B).levelPolynomial

/-- Two quotient-polynomial computations, on a node and on an opposite-side
skeleton, with the same explicitly recorded target polynomial.  The fields
are the exact output shape needed from the two orientations of the
ORT/Poincaré calculation; no Dynkin or ORT assertion is stored here. -/
structure CommonOppositeQuotientPolynomial
    (B : AlgebraNode K)
    {kappa : Type v} [Finite kappa]
    (tau :
      OpConjecture.IndecomposableSkeleton.{u, v, u}
        B.Carrierᵐᵒᵖ kappa) where
  target : Polynomial ℕ
  node_quotient_eq :
    (AlgebraNode.qClosure K B).levelPolynomial = target
  opposite_quotient_eq :
    tau.qClosure.levelPolynomial = target

/-- A common quotient-polynomial formula on a node and an opposite-side
skeleton gives the node's exact quotient/submodule profile equality.
Contragredient duality supplies the last step in
`q(B) = target = q(Bᵐᵒᵖ-side) = s(B)`. -/
theorem fullProfileEquality_of_commonOppositeQuotientPolynomial
    {kappa : Type v} [Finite kappa]
    (B : AlgebraNode K)
    (tau :
      OpConjecture.IndecomposableSkeleton.{u, v, u}
        B.Carrierᵐᵒᵖ kappa)
    (F : CommonOppositeQuotientPolynomial K B tau) :
    FullProfileEquality K B := by
  let D :=
    OpConjecture.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  have hdual :
      B.skeleton.sClosure.levelPolynomial =
        tau.qClosure.levelPolynomial :=
    OpConjecture.IndecomposableSkeleton.AlignedBiduality.submoduleToQuotientLevelPolynomial_eq
      B.skeleton tau D
  change
    B.skeleton.qClosure.levelPolynomial =
      B.skeleton.sClosure.levelPolynomial
  calc
    B.skeleton.qClosure.levelPolynomial = F.target :=
      F.node_quotient_eq
    _ = tau.qClosure.levelPolynomial :=
      F.opposite_quotient_eq.symm
    _ = B.skeleton.sClosure.levelPolynomial :=
      hdual.symm

namespace CommonOppositeQuotientPolynomial

variable
    {K : Type u} [Field K]
    {B : AlgebraNode K}
    {kappa : Type v} [Finite kappa]
    {tau :
      OpConjecture.IndecomposableSkeleton.{u, v, u}
        B.Carrierᵐᵒᵖ kappa}

/-- Method form of the connected Dynkin-profile adapter. -/
theorem fullProfileEquality
    (F : CommonOppositeQuotientPolynomial K B tau) :
    FullProfileEquality K B :=
  fullProfileEquality_of_commonOppositeQuotientPolynomial K B tau F

end CommonOppositeQuotientPolynomial

/-- The actual projective count used as the simple count in the connected
classification interface. -/
abbrev projectiveCount (B : AlgebraNode K) : ℕ :=
  projectiveRank B.skeleton

/-- The actual quotient faithful-core size used by the recurrence. -/
abbrev coreSize (B : AlgebraNode K) : ℕ :=
  (((AlgebraNode.quotientCoreData K B).core : Set B.Index).ncard)

/-- A node has a verified Nakayama profile when its actual skeleton has
the fixed-top and fixed-socle chain classification used by the paper. -/
abbrev NakayamaChainModel (B : AlgebraNode K) : Prop :=
  Nonempty
    (OpConjecture.NakayamaModuleChains.FixedTopSocleChainClassification
      B.skeleton)

/-- The profile-only connected branch can be discharged by a
Morita-equivalent monogenic model, by the classical one-loop-presentation
route, or by the full fixed-top/fixed-socle chain classification (needed for
the general Nakayama theorem and available for the two-simple Nakayama
branch). -/
abbrev NakayamaProfileModel (B : AlgebraNode K) : Prop :=
  OpConjecture.LocalNakayamaBranch.HasMoritaMonogenicModel B ∨
    OpConjecture.LocalNakayamaBranch.HasMoritaOneLoopPresentation B ∨
      NakayamaChainModel K B

/-- The maintained chain adapter turns a verified Nakayama model into the
full profile equality required by the connected recurrence. -/
theorem fullProfileEquality_of_nakayamaChainModel
    (B : AlgebraNode K) (hB : NakayamaChainModel K B) :
    FullProfileEquality K B := by
  obtain ⟨D⟩ := hB
  exact D.levelPolynomial_eq

/-- Either verified Nakayama-profile input supplies the same full profile
equality. -/
theorem fullProfileEquality_of_nakayamaProfileModel
    (B : AlgebraNode K) (hB : NakayamaProfileModel K B) :
    FullProfileEquality K B := by
  rcases hB with hmonogenic | hpresentation | hchains
  · exact
      OpConjecture.LocalNakayamaBranch.algebraNodeEquidistribution_of_hasMoritaMonogenicModel
        B hmonogenic
  · exact
      OpConjecture.LocalNakayamaBranch.algebraNodeEquidistribution_of_hasMoritaOneLoopPresentation
        B hpresentation
  · exact fullProfileEquality_of_nakayamaChainModel K B hchains

/-- A Morita basicization with split residue and cyclic Jacobson cotangent
space feeds the preferred one-simple profile branch after the compiled
noncommutative Nakayama and monogenicity argument. -/
theorem nakayamaProfileModel_of_splitCyclicCotangent
    (B : AlgebraNode K)
    (P :
      OpConjecture.LocalNakayamaBranch.MoritaSplitCyclicCotangentModel
        K B) :
    NakayamaProfileModel K B :=
  Or.inl P.toPolynomialQuotientModel.toHasMoritaMonogenicModel

namespace AlgebraNode

/-- A node over the zero ring has no indecomposable labels. -/
theorem index_isEmpty_of_subsingleton
    (B : AlgebraNode K) [Subsingleton B.Carrier] :
    IsEmpty B.Index := by
  constructor
  intro i
  letI : Nontrivial (B.skeleton.obj i) :=
    (B.skeleton.indecomposable i).nontrivial
  exact
    not_subsingleton (B.skeleton.obj i)
      (Module.subsingleton B.Carrier (B.skeleton.obj i))

/-- Hence all positive levels agree for a node over the zero ring. -/
theorem levelCount_eq_of_subsingleton
    (B : AlgebraNode K) [Subsingleton B.Carrier]
    (n : ℕ) (hn : 0 < n) :
    (qClosure K B).levelCount n =
      (sClosure K B).levelCount n := by
  letI : IsEmpty B.Index := index_isEmpty_of_subsingleton K B
  letI : Fintype B.Index := Fintype.ofFinite B.Index
  have hcard : Nat.card B.Index = 0 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    infer_instance
  have hlt : Nat.card B.Index < n := by omega
  rw [OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
      (qClosure K B) hlt,
    OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
      (sClosure K B) hlt]

/-- Every nonzero node has a simple chosen skeleton label. -/
theorem simpleIndex_nonempty
    (B : AlgebraNode K) [Nontrivial B.Carrier] :
    Nonempty B.skeleton.SimpleIndex := by
  obtain ⟨N, hNcoatom, -⟩ :=
    (eq_top_or_exists_le_coatom
      (⊥ : Submodule B.Carrier B.Carrier)).resolve_left bot_ne_top
  let X : FGModuleCat.{u} B.Carrier :=
    FGModuleCat.of B.Carrier (B.Carrier ⧸ N)
  have hsimpleModule : IsSimpleModule B.Carrier X := by
    change IsSimpleModule B.Carrier (B.Carrier ⧸ N)
    exact isSimpleModule_iff_isCoatom.mpr hNcoatom
  have hindec :
      OpConjecture.Foundation.IsIndecomposableModule B.Carrier X :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨i, ⟨e⟩⟩ := B.skeleton.complete X hindec
  refine ⟨⟨i, ?_⟩⟩
  have hsimple : CategoryTheory.Simple X :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      X).2 hsimpleModule
  exact (CategoryTheory.Simple.iff_of_iso e).mp hsimple

/-- The projective count is positive for every nonzero node. -/
theorem projectiveCount_pos
    (B : AlgebraNode K) [Nontrivial B.Carrier] :
    0 < projectiveCount K B := by
  obtain ⟨s⟩ := simpleIndex_nonempty K B
  let e :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      B.skeleton
  let p := e.symm s
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨p.1, p.2⟩

end AlgebraNode

/-- Ringel's compiled stable equivalence supplies `v ≤ d` at every node. -/
theorem projectiveCount_le_coreSize (B : AlgebraNode K) :
    projectiveCount K B ≤ coreSize K B := by
  apply projectiveRank_le_quotientCore_of_ringel B.skeleton
  exact
    OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      B.skeleton K

/-- In the one-simple branch, no presentation theorem is needed: aligned
duality and the no-parallel theorem saturate the submodule Ringel core, so
Ringel cardinality identifies the whole indecomposable skeleton with the
quotient core. -/
theorem indexCard_eq_coreSize_of_projectiveCount_eq_one
    [IsAlgClosed K]
    (B : AlgebraNode K)
    (hOneCount : projectiveCount K B = 1) :
    Nat.card B.Index = coreSize K B := by
  let tau :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let D :=
    OpConjecture.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  letI : Finite
      (OpConjecture.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) :=
    D.forward.labelEquiv.finite_iff.mp inferInstance
  have hOne :
      OpConjecture.LocalNakayamaBranch.OneSimple B.skeleton :=
    (OpConjecture.LocalNakayamaBranch.oneSimple_iff_projectiveRank_eq_one
      B.skeleton).2 hOneCount
  have hNoParallel :
      OpConjecture.GabrielArrowBridge.NoParallelExtSupport
        (K := K) B.skeleton :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport
      B.skeleton
  have hDualNoParallel :
      OpConjecture.GabrielArrowBridge.NoParallelExtSupport
        (K := K) tau :=
    OpConjecture.FiniteDimensionalNoParallelExt.noParallelExtSupport
      tau
  have hSaturation :
      (submoduleCore B.skeleton : Set B.Index) = Set.univ :=
    OpConjecture.OneSimpleCoreSaturation.submoduleCore_eq_univ_of_oneSimple_of_noParallel
      B.skeleton tau D hOne hNoParallel hDualNoParallel
  have hRingel : RingelCoreCardinality B.skeleton :=
    OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      B.skeleton K
  have hCardCore :
      Nat.card B.Index =
        (quotientCore B.skeleton : Set B.Index).ncard :=
    OpConjecture.OneSimpleCoreSaturation.natCard_eq_quotientCore_ncard_of_submoduleCore_eq_univ
      B.skeleton hRingel hSaturation
  simpa [coreSize, AlgebraNode.quotientCoreData,
    concreteQuotientCoreData] using hCardCore

/-- Consequently every level strictly above the one-simple faithful-core
size is empty on both sides.  This is the exact degreewise input needed by
the repaired small-core recurrence. -/
theorem levelCount_eq_of_projectiveCount_eq_one_of_coreSize_lt
    [IsAlgClosed K]
    (B : AlgebraNode K)
    (hOneCount : projectiveCount K B = 1)
    {n : ℕ} (hsmall : coreSize K B < n) :
    (AlgebraNode.qClosure K B).levelCount n =
      (AlgebraNode.sClosure K B).levelCount n := by
  have hCard : Nat.card B.Index = coreSize K B :=
    indexCard_eq_coreSize_of_projectiveCount_eq_one
      K B hOneCount
  have hlt : Nat.card B.Index < n := hCard.trans_lt hsmall
  rw [OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
      (AlgebraNode.qClosure K B) hlt,
    OpConjecture.SetClosure.levelCount_eq_zero_of_card_lt
      (AlgebraNode.sClosure K B) hlt]

/-- The equality branch of the connected classification is already a
literal left-hereditary statement: every left ideal is projective. -/
theorem everyLeftIdealProjective_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hvd : projectiveCount K B = coreSize K B) :
    EveryLeftIdealProjective B.Carrier := by
  apply everyLeftIdealProjective_of_projectiveRank_eq_core B.skeleton
  · exact
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        B.skeleton K
  · simpa [coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using hvd

/-- The equality branch also retains the stronger finite-module form of
left heredity used by the categorical two-simple argument: every submodule
of a finitely generated projective is projective. -/
theorem finitelyGeneratedLeftHereditary_of_projectiveCount_eq_coreSize
    (B : AlgebraNode K)
    (hvd : projectiveCount K B = coreSize K B) :
    FinitelyGeneratedLeftHereditary B.Carrier := by
  apply finitelyGeneratedLeftHereditary_of_projectiveRank_eq_core B.skeleton
  · exact
      OpConjecture.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        B.skeleton K
  · simpa [coreSize, AlgebraNode.quotientCoreData,
      concreteQuotientCoreData] using hvd

/-- A source algebra has a Dynkin model when it is Morita equivalent to a
node carrying the chosen `DynkinModel` predicate.  This formulation does not
require the source node itself to be basic. -/
def HasMoritaDynkinModel
    (DynkinModel : AlgebraNode K → Prop)
    (B : AlgebraNode K) : Prop :=
  ∃ D : AlgebraNode K, DynkinModel D ∧
    Nonempty (MoritaEquivalence K B.Carrier D.Carrier)

/-- Existing Morita/skeleton alignment transports full profile equality
from a Dynkin model to the original node. -/
theorem fullProfileEquality_of_hasMoritaDynkinModel
    (DynkinModel : AlgebraNode K → Prop)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    {B : AlgebraNode K}
    (hB : HasMoritaDynkinModel K DynkinModel B) :
    FullProfileEquality K B := by
  rcases hB with ⟨D, hD, ⟨e⟩⟩
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K _
  letI : IsArtinianRing D.Carrier := IsArtinianRing.of_finite K _
  let E := MoritaEquivalence.alignedFgEquivalence
    e B.skeleton D.skeleton
  have hq :
      B.skeleton.qClosure.levelPolynomial =
        D.skeleton.qClosure.levelPolynomial :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      B.skeleton D.skeleton E
  have hs :
      B.skeleton.sClosure.levelPolynomial =
        D.skeleton.sClosure.levelPolynomial :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      B.skeleton D.skeleton E
  exact hq.trans ((hDynkin D hD).trans hs.symm)

/-- Exact Gabriel-classification seam: connected finite-dimensional,
representation-finite, left-hereditary nodes admit Morita-equivalent Dynkin
models.  Finite-dimensionality and representation-finiteness are already
carried by `AlgebraNode`; the latter is witnessed by its finite complete
skeleton.  In the paper this input is applied over an algebraically closed
field to the opposite carrier modeling right modules; the abstract signature
leaves that splitness and side convention inside the supplied theorem. -/
def HereditaryGabrielDynkinClassification
    (DynkinModel : AlgebraNode K → Prop) : Prop :=
  ∀ B : AlgebraNode K,
    OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
    Nontrivial B.Carrier →
    EveryLeftIdealProjective B.Carrier →
    HasMoritaDynkinModel K DynkinModel B

/-- The maintained equality branch followed by the two missing classical
inputs gives the full profile equality needed by `smallCore`. -/
theorem fullProfileEquality_of_projectiveCount_eq_coreSize
    (DynkinModel : AlgebraNode K → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (B : AlgebraNode K)
    (hConnected :
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B)
    (hNonzero : Nontrivial B.Carrier)
    (hvd : projectiveCount K B = coreSize K B) :
    FullProfileEquality K B := by
  apply fullProfileEquality_of_hasMoritaDynkinModel K DynkinModel hDynkin
  exact hGabriel B hConnected hNonzero
    (everyLeftIdealProjective_of_projectiveCount_eq_coreSize K B hvd)

/-- Degreewise form used in the simultaneous degree-three/degree-four
recurrence.  No full-profile hypothesis is imposed on the source algebra;
it is transported from the classified Dynkin model. -/
theorem levelCount_eq_of_projectiveCount_eq_coreSize
    (DynkinModel : AlgebraNode K → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (B : AlgebraNode K)
    (hConnected :
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B)
    (hNonzero : Nontrivial B.Carrier)
    (hvd : projectiveCount K B = coreSize K B)
    (n : ℕ) :
    (AlgebraNode.qClosure K B).levelCount n =
      (AlgebraNode.sClosure K B).levelCount n := by
  exact
    (OpConjecture.SetClosure.levelPolynomial_eq_iff
      (AlgebraNode.qClosure K B) (AlgebraNode.sClosure K B)).1
      (fullProfileEquality_of_projectiveCount_eq_coreSize
        K DynkinModel hGabriel hDynkin B hConnected hNonzero hvd) n

/-!
## Direct connection to `ConnectedSmallCore.ClassificationData`

The generic classification interface does not require its predicate named
`HereditaryDynkin` to be a ring-theoretic primitive.  We take it to mean
"has a Morita-equivalent Dynkin model."  Consequently its equality field is
exactly the compiled core-collapse theorem followed by the isolated Gabriel
seam above.
-/

open OpConjecture.BottomLevels.ConnectedSmallCore

/-- The nonzero connected predicate used inside the arithmetic
classification.  The zero ring is handled directly at the outer
`smallCore` interface. -/
def NonzeroBlockConnected (B : AlgebraNode K) : Prop :=
  OpConjecture.BlockDecomposition.Node.IsBlockConnected K B ∧
    Nontrivial B.Carrier

/-- Construct the actual connected-classification package once the three
genuinely local inputs are supplied.  Ringel supplies `v ≤ d`, and the
entire `v = d` field is compiled here. -/
theorem classificationData_of_local_inputs
    (DynkinModel Nakayama : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hOneSimple :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 1 → Nakayama B)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        Nakayama B ∨ ∃ kind, IsLollipop B kind) :
    ClassificationData
      (coreSize K) (projectiveCount K)
      (NonzeroBlockConnected K)
      (HasMoritaDynkinModel K DynkinModel) Nakayama IsLollipop where
  simpleCount_pos := fun B hB ↦ by
    letI : Nontrivial B.Carrier := hB.2
    exact AlgebraNode.projectiveCount_pos K B
  simpleCount_le_coreSize := fun B _ ↦ projectiveCount_le_coreSize K B
  hereditaryDynkin_of_eq := fun B hB hvd ↦
    hGabriel B hB.1 hB.2
      (everyLeftIdealProjective_of_projectiveCount_eq_coreSize K B hvd)
  nakayama_of_simpleCount_eq_one := hOneSimple
  twoSimple_coreThree := hTwoSimpleCoreThree

/-- The complete connected `smallCore` field, with the hereditary branch
reduced to the two named classical seams.  The remaining hypotheses are the
separate one-simple/two-simple classification and maintained table inputs;
the zero ring and positivity are discharged internally. -/
theorem smallCore_of_local_inputs
    (DynkinModel Nakayama : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hOneSimple :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 1 → Nakayama B)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        Nakayama B ∨ ∃ kind, IsLollipop B kind)
    (hNakayama : ∀ B, Nakayama B → FullProfileEquality K B)
    (hTables :
      ∀ B kind, IsLollipop B kind →
        LollipopTableData
          (fun C : AlgebraNode K ↦ C.Index)
          (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.quotientCoreData K)
          (AlgebraNode.submoduleCoreData K) B) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
        (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n := by
  intro B n hn hConnected hsmall
  rcases subsingleton_or_nontrivial B.Carrier with hzero | hnonzero
  · letI : Subsingleton B.Carrier := hzero
    exact Or.inr
      (AlgebraNode.levelCount_eq_of_subsingleton K B n (by omega))
  · letI : Nontrivial B.Carrier := hnonzero
    let hAdapter :=
      smallCore_of_classification_and_lollipopTables
        (fun C : AlgebraNode K ↦ C.Index)
        (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
        (AlgebraNode.IsFaithfulSupport K)
        (AlgebraNode.IsFaithfulSupport K)
        (AlgebraNode.quotientCoreData K)
        (AlgebraNode.submoduleCoreData K)
        (projectiveCount K)
        (NonzeroBlockConnected K)
        (HasMoritaDynkinModel K DynkinModel) Nakayama IsLollipop
        (classificationData_of_local_inputs K DynkinModel Nakayama
          IsLollipop hGabriel hOneSimple hTwoSimpleCoreThree)
        (fun C hC ↦
          fullProfileEquality_of_hasMoritaDynkinModel
            K DynkinModel hDynkin hC)
        hNakayama hTables
    exact hAdapter B n hn ⟨hConnected, inferInstance⟩ hsmall

/-- Preferred connected adapter: a one-simple branch may use a
Morita-equivalent monogenic model or a one-loop presentation, while a genuine
Nakayama branch may use the actual fixed-top/fixed-socle classification
package.  In every case the full-profile field is a theorem rather than a
separate hypothesis. -/
theorem smallCore_of_profile_classifications
    (DynkinModel : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hOneSimple :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 1 → NakayamaProfileModel K B)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        NakayamaProfileModel K B ∨
          ∃ kind, IsLollipop B kind)
    (hTables :
      ∀ B kind, IsLollipop B kind →
        LollipopTableData
          (fun C : AlgebraNode K ↦ C.Index)
          (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.quotientCoreData K)
          (AlgebraNode.submoduleCoreData K) B) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
      (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n :=
  smallCore_of_local_inputs K DynkinModel (NakayamaProfileModel K)
    IsLollipop hGabriel hDynkin hOneSimple hTwoSimpleCoreThree
    (fullProfileEquality_of_nakayamaProfileModel K) hTables

/-- Preferred classification-free one-simple adapter with the lollipop
endpoint stated only as the faithful degree-four equality actually consumed
by the recurrence.  This form permits the equality to be transported from a
Morita or opposite-Morita model without reconstructing a named table on the
target skeleton. -/
theorem smallCore_of_twoSimple_profile_classification_with_lollipopEquality
    [IsAlgClosed K]
    (DynkinModel : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        NakayamaProfileModel K B ∨
          ∃ kind, IsLollipop B kind)
    (hLollipop :
      ∀ B kind, IsLollipop B kind →
        AlgebraNode.faithfulQCount K B 4 =
          AlgebraNode.faithfulSCount K B 4) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
        (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n := by
  intro B n hn hConnected hsmall
  rcases subsingleton_or_nontrivial B.Carrier with hzero | hnonzero
  · letI : Subsingleton B.Carrier := hzero
    exact Or.inr
      (AlgebraNode.levelCount_eq_of_subsingleton K B n (by omega))
  · letI : Nontrivial B.Carrier := hnonzero
    have hPositive : 0 < projectiveCount K B :=
      AlgebraNode.projectiveCount_pos K B
    have hBound : projectiveCount K B ≤ coreSize K B :=
      projectiveCount_le_coreSize K B
    by_cases hOne : projectiveCount K B = 1
    · exact Or.inr
        (levelCount_eq_of_projectiveCount_eq_one_of_coreSize_lt
          K B hOne hsmall)
    by_cases hEqual : projectiveCount K B = coreSize K B
    · exact Or.inr
        (levelCount_eq_of_projectiveCount_eq_coreSize
          K DynkinModel hGabriel hDynkin B hConnected inferInstance
          hEqual n)
    rcases hn with rfl | rfl
    · omega
    · have hTwo : projectiveCount K B = 2 := by omega
      have hCoreThree : coreSize K B = 3 := by omega
      rcases hTwoSimpleCoreThree B ⟨hConnected, inferInstance⟩
          hTwo hCoreThree with hNakayama | ⟨kind, hLollipopModel⟩
      · exact Or.inr
          ((OpConjecture.SetClosure.levelPolynomial_eq_iff
            (AlgebraNode.qClosure K B)
            (AlgebraNode.sClosure K B)).1
              (fullProfileEquality_of_nakayamaProfileModel
                K B hNakayama) 4)
      · exact Or.inl (hLollipop B kind hLollipopModel)

/-- Table-valued specialization retained for callers that have literal
one-point extension tables on the target skeleton. -/
theorem smallCore_of_twoSimple_profile_classification
    [IsAlgClosed K]
    (DynkinModel : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        NakayamaProfileModel K B ∨
          ∃ kind, IsLollipop B kind)
    (hTables :
      ∀ B kind, IsLollipop B kind →
        LollipopTableData
          (fun C : AlgebraNode K ↦ C.Index)
          (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.quotientCoreData K)
          (AlgebraNode.submoduleCoreData K) B) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
        (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n := by
  apply smallCore_of_twoSimple_profile_classification_with_lollipopEquality
    K DynkinModel IsLollipop hGabriel hDynkin hTwoSimpleCoreThree
  intro B kind hB
  exact (hTables B kind hB).faithful_four_eq

/-- Fixed-chain specialization of the preferred adapter.  It requires no
one-simple presentation or cotangent generator; only the two-simple,
core-three Nakayama/lollipop split remains. -/
theorem smallCore_of_twoSimple_chain_classification
    [IsAlgClosed K]
    (DynkinModel : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        NakayamaChainModel K B ∨
          ∃ kind, IsLollipop B kind)
    (hTables :
      ∀ B kind, IsLollipop B kind →
        LollipopTableData
          (fun C : AlgebraNode K ↦ C.Index)
          (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.quotientCoreData K)
          (AlgebraNode.submoduleCoreData K) B) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
        (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n := by
  apply smallCore_of_twoSimple_profile_classification
    K DynkinModel IsLollipop hGabriel hDynkin
  · intro B hB hTwo hCoreThree
    rcases hTwoSimpleCoreThree B hB hTwo hCoreThree with
      hChains | hLollipop
    · exact Or.inl (Or.inr (Or.inr hChains))
    · exact Or.inr hLollipop
  · exact hTables

/-- Legacy structural specialization exposing the former local seams:
the one-simple branch supplies a Morita basicization with split residue and
cyclic Jacobson cotangent space, while the two-simple/core-three Nakayama
branch supplies actual fixed-chain data. -/
theorem smallCore_of_splitCyclicCotangent_and_chain_classifications
    (DynkinModel : AlgebraNode K → Prop)
    (IsLollipop : AlgebraNode K → LollipopKind → Prop)
    (hGabriel : HereditaryGabrielDynkinClassification K DynkinModel)
    (hDynkin : ∀ D, DynkinModel D → FullProfileEquality K D)
    (hOneSimple :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 1 →
          Nonempty
            (OpConjecture.LocalNakayamaBranch.MoritaSplitCyclicCotangentModel
              K B))
    (hTwoSimpleCoreThree :
      ∀ B : AlgebraNode K,
        NonzeroBlockConnected K B →
        projectiveCount K B = 2 → coreSize K B = 3 →
        NakayamaChainModel K B ∨
          ∃ kind, IsLollipop B kind)
    (hTables :
      ∀ B kind, IsLollipop B kind →
        LollipopTableData
          (fun C : AlgebraNode K ↦ C.Index)
          (AlgebraNode.qClosure K) (AlgebraNode.sClosure K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.IsFaithfulSupport K)
          (AlgebraNode.quotientCoreData K)
          (AlgebraNode.submoduleCoreData K) B) :
    ∀ (B : AlgebraNode K) (n : ℕ), n = 3 ∨ n = 4 →
      OpConjecture.BlockDecomposition.Node.IsBlockConnected K B →
      coreSize K B < n →
      (AlgebraNode.faithfulQCount K B n =
          AlgebraNode.faithfulSCount K B n) ∨
        (AlgebraNode.qClosure K B).levelCount n =
          (AlgebraNode.sClosure K B).levelCount n := by
  apply smallCore_of_profile_classifications K DynkinModel IsLollipop
    hGabriel hDynkin
  · intro B hB hcount
    obtain ⟨P⟩ := hOneSimple B hB hcount
    exact nakayamaProfileModel_of_splitCyclicCotangent K B P
  · intro B hB hcount hcore
    rcases hTwoSimpleCoreThree B hB hcount hcore with hchains | hlollipop
    · exact Or.inl (Or.inr (Or.inr hchains))
    · exact Or.inr hlollipop
  · exact hTables

end OpConjecture.BottomLevels.FiniteDimensionalRecurrence
