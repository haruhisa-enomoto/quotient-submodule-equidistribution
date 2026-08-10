import QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteRootedDigraph
import QuotientSubmoduleEquidistribution.RepresentationTheory.ARMeshRootedBalance
import QuotientSubmoduleEquidistribution.RepresentationTheory.ReverseFactorLadderRooted

/-!
# Cofinite factor-ladder endpoint

This file assembles the quotient and reverse-submodule factor-ladder closure
characterizations with grouped rooted-set matching.  The remaining input for
a fixed colevel is exactly equality of the two bad rooted families.
-/

set_option autoImplicit false
noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- Grouped rooted-set matching and equality of the two bad rooted families
give the complete rooted/bad-rooted cofinite input. -/
def rootedBadCofiniteInput_of_factorLadders
    (D : AlignedBiduality σ τ)
    (M : QuotientSubmoduleEquidistribution.RootedDigraph.GroupedTopPartMatching
      σ.irreducibleEdge (fun x y ↦ σ.irreducibleEdge y x)
        σ.projectiveLabelFinset σ.injectiveLabelFinset)
    (j : ℕ)
    (bad_rooted_card_eq :
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset)
        (QuotientFactorLadderBad (k := k) (R := R) σ) j).card =
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
          σ.irreducibleEdge σ.injectiveLabelFinset)
        (SubmoduleFactorLadderBad
          (k := k) (S := S) σ τ D) j).card) :
    QuotientSubmoduleEquidistribution.SetClosure.RootedBadCofiniteInput
      σ.qClosure σ.sClosure j :=
  QuotientSubmoduleEquidistribution.SetClosure.rootedBadCofiniteInput_of_groupedTopPartMatching
    σ.qClosure σ.sClosure σ.irreducibleEdge σ.irreducibleEdge
      σ.projectiveLabelFinset σ.injectiveLabelFinset M j
      (QuotientFactorLadderBad (k := k) (R := R) σ)
      (SubmoduleFactorLadderBad (k := k) (S := S) σ τ D)
      (fun _ ↦
        qClosure_isClosed_compl_iff_projectivelyRooted_and_not_factorLadderBad
          (k := k) (R := R) σ _)
      (fun _ ↦
        sClosure_isClosed_compl_iff_injectivelyCorooted_and_not_factorLadderBad
          (k := k) (S := S) σ τ D _)
      bad_rooted_card_eq

/-- Paper-facing colevel equality after all factor-ladder closure and rooted
count obligations have been eliminated.  Only grouped AR matching and bad
rooted balance remain. -/
theorem levelCount_card_sub_eq_of_factorLadders
    (D : AlignedBiduality σ τ)
    (M : QuotientSubmoduleEquidistribution.RootedDigraph.GroupedTopPartMatching
      σ.irreducibleEdge (fun x y ↦ σ.irreducibleEdge y x)
        σ.projectiveLabelFinset σ.injectiveLabelFinset)
    (j : ℕ) (hj : j ≤ Nat.card ι)
    (bad_rooted_card_eq :
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset)
        (QuotientFactorLadderBad (k := k) (R := R) σ) j).card =
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
          σ.irreducibleEdge σ.injectiveLabelFinset)
        (SubmoduleFactorLadderBad
          (k := k) (S := S) σ τ D) j).card) :
    σ.qClosure.levelCount (Nat.card ι - j) =
      σ.sClosure.levelCount (Nat.card ι - j) := by
  exact
    QuotientSubmoduleEquidistribution.SetClosure.levelCount_card_sub_eq_of_rootedBadCofiniteInput
      σ.qClosure σ.sClosure j hj <|
        rootedBadCofiniteInput_of_factorLadders
          (k := k) (R := R) (S := S) σ τ D M j bad_rooted_card_eq

/-- With the actual finite AR translation, rooted balance is automatic.
Thus the sole residual input at a fixed colevel is equality of the two bad
rooted factor-ladder families. -/
theorem levelCount_card_sub_eq_of_badRootedFactorLadderBalance
    (D : AlignedBiduality σ τ)
    (j : ℕ) (hj : j ≤ Nat.card ι)
    (bad_rooted_card_eq :
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset)
        (QuotientFactorLadderBad (k := k) (R := R) σ) j).card =
      (QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
        (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
          σ.irreducibleEdge σ.injectiveLabelFinset)
        (SubmoduleFactorLadderBad
          (k := k) (S := S) σ τ D) j).card) :
    σ.qClosure.levelCount (Nat.card ι - j) =
      σ.sClosure.levelCount (Nat.card ι - j) := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional k R
  exact levelCount_card_sub_eq_of_factorLadders
    (k := k) (R := R) (S := S) σ τ D
      ((σ.finiteDimensionalARMeshRotationData
        (K := k)).groupedTopPartMatching σ)
      j hj bad_rooted_card_eq

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
