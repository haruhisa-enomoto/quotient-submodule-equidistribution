import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulLevelDualityTransport
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalRecurrence
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Assembly
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Classification
import QuotientSubmoduleEquidistribution.RepresentationTheory.SkeletonAlignment
import QuotientSubmoduleEquidistribution.Combinatorics.ConnectedSmallCore

/-!
# Transporting the two lollipop computations to algebra nodes

The concrete dead- and live-path classifications prove their faithful
degree-four equalities using convenient custom skeletons.  This file
transports those equalities to an arbitrary finite complete skeleton whenever
its carrier is Morita equivalent to the corresponding model algebra.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModelTransport

open QuotientSubmoduleEquidistribution.BottomLevels
open QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

universe u v

variable {K : Type u} [Field K]

/-- Node-level meaning of the four lollipop kinds.  The relation field
selects the dead- or live-path model, and the orientation records whether
that model is Morita equivalent to the carrier or to its opposite. -/
def IsMoritaLollipop
    (B : AlgebraNode K)
    (kind : QuotientSubmoduleEquidistribution.BottomLevels.ConnectedSmallCore.LollipopKind) : Prop :=
  match kind.relation, kind.orientation with
  | .deadPath, .forward =>
      Nonempty (MoritaEquivalence K (B0Model K) B.Carrier)
  | .deadPath, .opposite =>
      Nonempty (MoritaEquivalence K (B0Model K) B.Carrierᵐᵒᵖ)
  | .livePath, .forward =>
      Nonempty (MoritaEquivalence K (B1.B1Model K) B.Carrier)
  | .livePath, .opposite =>
      Nonempty (MoritaEquivalence K (B1.B1Model K) B.Carrierᵐᵒᵖ)

/-- A faithful level equality for a finite-dimensional model algebra
transports to a node whose opposite carrier is Morita equivalent to the
model.  Contragredient duality performs the two side exchanges, while the
Morita equivalence only relabels the model skeleton. -/
theorem faithfulLevelCount_eq_of_oppositeMorita
    {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
    [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {iota : Type v} [Finite iota]
    (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} A iota)
    (B : AlgebraNode K)
    (morita : MoritaEquivalence K A B.Carrierᵐᵒᵖ)
    (n : ℕ)
    (hModel :
      MinimalFaithfulCore.faithfulLevelCount sigma.qClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) n =
        MinimalFaithfulCore.faithfulLevelCount sigma.sClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) n) :
    AlgebraNode.faithfulQCount K B n =
      AlgebraNode.faithfulSCount K B n := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI : IsArtinianRing B.Carrierᵐᵒᵖ :=
    IsArtinianRing.of_finite K B.Carrierᵐᵒᵖ
  letI : IsNoetherianRing (B.Carrierᵐᵒᵖ)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional
      K B.Carrierᵐᵒᵖ
  let tau :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{u, u, u} K B.Carrier
  let E := MoritaEquivalence.alignedFgEquivalence morita sigma tau
  letI : Finite
      (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{u, u}
        B.Carrierᵐᵒᵖ) :=
    E.labelEquiv.finite_iff.mp inferInstance
  let D :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K B.Carrier B.skeleton tau
  have hModelQ :
      MinimalFaithfulCore.faithfulLevelCount sigma.qClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) n =
        MinimalFaithfulCore.faithfulLevelCount tau.qClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) n :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) n
  have hModelS :
      MinimalFaithfulCore.faithfulLevelCount sigma.sClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) n =
        MinimalFaithfulCore.faithfulLevelCount tau.sClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) n :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) n
  have hDualQ :
      MinimalFaithfulCore.faithfulLevelCount B.skeleton.qClosure
          (AnnihilatorInflation.IsFaithfulSupport B.skeleton.obj) n =
        MinimalFaithfulCore.faithfulLevelCount tau.sClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) n :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.quotientFaithfulLevelCount_eq_submodule
      B.skeleton tau
      (closedFaithfulNormalForm (K := K) B.skeleton)
      (closedFaithfulNormalForm (K := K) tau) D
      (AnnihilatorInflation.isFaithfulSupport_monotone B.skeleton.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) n
  have hDualS :
      MinimalFaithfulCore.faithfulLevelCount B.skeleton.sClosure
          (AnnihilatorInflation.IsFaithfulSupport B.skeleton.obj) n =
        MinimalFaithfulCore.faithfulLevelCount tau.qClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) n :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedBiduality.submoduleFaithfulLevelCount_eq_quotient
      B.skeleton tau
      (closedFaithfulNormalForm (K := K) B.skeleton)
      (closedFaithfulNormalForm (K := K) tau) D
      (AnnihilatorInflation.isFaithfulSupport_monotone B.skeleton.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) n
  exact hDualQ.trans <|
    hModelS.symm.trans <| hModel.symm.trans <|
      hModelQ.trans hDualS.symm

/-- Morita equivalence with the dead-path model transports its faithful
degree-four equality to any algebra node. -/
theorem faithfulLevelCount_four_eq_of_b0Morita
    (B : AlgebraNode K)
    (morita : MoritaEquivalence K (B0Model K) B.Carrier) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 := by
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K _
  letI : IsNoetherianRing (B0Model K)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite K _
  let sigma := ModuleLayer.B0Assembly.indecomposableSkeleton K
  let tau := B.skeleton
  let E := MoritaEquivalence.alignedFgEquivalence morita sigma tau
  have hq :
      MinimalFaithfulCore.faithfulLevelCount sigma.qClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) 4 =
        MinimalFaithfulCore.faithfulLevelCount tau.qClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) 4 :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) 4
  have hs :
      MinimalFaithfulCore.faithfulLevelCount sigma.sClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) 4 =
        MinimalFaithfulCore.faithfulLevelCount tau.sClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) 4 :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) 4
  exact hq.symm.trans
    (ModuleLayer.B0Assembly.faithfulLevelCount_four_eq K |>.trans hs)

/-- An algebra equivalence with the dead-path model is the principal
specialization used by the lollipop recognition theorem. -/
theorem faithfulLevelCount_four_eq_of_b0AlgEquiv
    (B : AlgebraNode K)
    (e : B0Model K ≃ₐ[K] B.Carrier) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 :=
  faithfulLevelCount_four_eq_of_b0Morita B
    (MoritaEquivalence.ofAlgEquiv e)

/-- If the dead-path model is Morita equivalent to the opposite carrier,
duality transports the same degree-four equality back to the node. -/
theorem faithfulLevelCount_four_eq_of_b0OppositeMorita
    (B : AlgebraNode K)
    (morita : MoritaEquivalence K (B0Model K) B.Carrierᵐᵒᵖ) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 := by
  letI : IsNoetherianRing (B0Model K)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite K _
  exact faithfulLevelCount_eq_of_oppositeMorita
    (ModuleLayer.B0Assembly.indecomposableSkeleton K) B morita 4
    (ModuleLayer.B0Assembly.faithfulLevelCount_four_eq K)

/-- Algebra-equivalence specialization of the opposite dead-path
transport. -/
theorem faithfulLevelCount_four_eq_of_b0OppositeAlgEquiv
    (B : AlgebraNode K)
    (e : B0Model K ≃ₐ[K] B.Carrierᵐᵒᵖ) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 :=
  faithfulLevelCount_four_eq_of_b0OppositeMorita B
    (MoritaEquivalence.ofAlgEquiv e)

/-- Morita equivalence with the live-path model transports its faithful
degree-four equality to any algebra node. -/
theorem faithfulLevelCount_four_eq_of_b1Morita
    (B : AlgebraNode K)
    (morita : MoritaEquivalence K (B1.B1Model K) B.Carrier) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 := by
  letI : IsArtinianRing B.Carrier := IsArtinianRing.of_finite K _
  letI : IsNoetherianRing (B1.B1Model K)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite K _
  let sigma := B1.ModuleLayer.B1Classification.indecomposableSkeleton K
  let tau := B.skeleton
  let E := MoritaEquivalence.alignedFgEquivalence morita sigma tau
  have hq :
      MinimalFaithfulCore.faithfulLevelCount sigma.qClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) 4 =
        MinimalFaithfulCore.faithfulLevelCount tau.qClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) 4 :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) 4
  have hs :
      MinimalFaithfulCore.faithfulLevelCount sigma.sClosure
          (AnnihilatorInflation.IsFaithfulSupport sigma.obj) 4 =
        MinimalFaithfulCore.faithfulLevelCount tau.sClosure
          (AnnihilatorInflation.IsFaithfulSupport tau.obj) 4 :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleFaithfulLevelCount_eq
      sigma tau E
      (closedFaithfulNormalForm (K := K) sigma)
      (closedFaithfulNormalForm (K := K) tau)
      (AnnihilatorInflation.isFaithfulSupport_monotone sigma.obj)
      (AnnihilatorInflation.isFaithfulSupport_monotone tau.obj) 4
  exact hq.symm.trans
    (B1.ModuleLayer.B1Classification.faithfulLevelCount_four_eq K |>.trans hs)

/-- An algebra equivalence with the live-path model is the principal
specialization used by the lollipop recognition theorem. -/
theorem faithfulLevelCount_four_eq_of_b1AlgEquiv
    (B : AlgebraNode K)
    (e : B1.B1Model K ≃ₐ[K] B.Carrier) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 :=
  faithfulLevelCount_four_eq_of_b1Morita B
    (MoritaEquivalence.ofAlgEquiv e)

/-- If the live-path model is Morita equivalent to the opposite carrier,
duality transports the same degree-four equality back to the node. -/
theorem faithfulLevelCount_four_eq_of_b1OppositeMorita
    (B : AlgebraNode K)
    (morita : MoritaEquivalence K (B1.B1Model K) B.Carrierᵐᵒᵖ) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 := by
  letI : IsNoetherianRing (B1.B1Model K)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite K _
  exact faithfulLevelCount_eq_of_oppositeMorita
    (B1.ModuleLayer.B1Classification.indecomposableSkeleton K)
    B morita 4
    (B1.ModuleLayer.B1Classification.faithfulLevelCount_four_eq K)

/-- Algebra-equivalence specialization of the opposite live-path
transport. -/
theorem faithfulLevelCount_four_eq_of_b1OppositeAlgEquiv
    (B : AlgebraNode K)
    (e : B1.B1Model K ≃ₐ[K] B.Carrierᵐᵒᵖ) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 :=
  faithfulLevelCount_four_eq_of_b1OppositeMorita B
    (MoritaEquivalence.ofAlgEquiv e)

/-- Every one of the four node-level lollipop kinds has equal faithful
degree-four quotient and submodule counts. -/
theorem faithfulLevelCount_four_eq_of_isMoritaLollipop
    (B : AlgebraNode K)
    (kind : QuotientSubmoduleEquidistribution.BottomLevels.ConnectedSmallCore.LollipopKind)
    (h : IsMoritaLollipop B kind) :
    AlgebraNode.faithfulQCount K B 4 =
      AlgebraNode.faithfulSCount K B 4 := by
  rcases kind with ⟨relation, orientation⟩
  cases relation <;> cases orientation
  · exact faithfulLevelCount_four_eq_of_b0Morita B h.some
  · exact faithfulLevelCount_four_eq_of_b0OppositeMorita B h.some
  · exact faithfulLevelCount_four_eq_of_b1Morita B h.some
  · exact faithfulLevelCount_four_eq_of_b1OppositeMorita B h.some

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModelTransport
