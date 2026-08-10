import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderRooted
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveMiddleARBridge

/-!
# Reverse factor ladders imply injective corootedness

The reverse ladder is the forward ladder on an aligned dual category.  A
positive reverse coefficient therefore propagates along reversed
irreducible arrows.  Reaching a deleted injective gives a path inside the
deleted set from that injective boundary vertex to the starting vertex in
the reversed AR digraph.
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

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

omit [Algebra k R] [FiniteDimensional k R] [Fintype ι]
  [DecidableEq ι] in
/-- A positive coefficient in the reverse factor ladder lies on a path of
reversed irreducible arrows from that coefficient's label to the starting
label. -/
theorem reverseFactorLadderData_ladder_pos_reflTransGen_irreducible
    (K : Set ι) (x p : DeletedLabel K) (n : ℕ)
    (hpos : 0 <
      (D.finiteDimensionalReverseFactorLadderData
        (k := k) (S := S) σ τ K).ladder x n p) :
    Relation.ReflTransGen
      (fun y z : DeletedLabel K ↦
        HasIrreducibleMorphism (σ.obj z.1) (σ.obj y.1))
      p x := by
  let eDeleted := D.forward.deletedLabelEquiv σ τ K
  let A := D.finiteDimensionalReverseFactorLadderData
    (k := k) (S := S) σ τ K
  let B := τ.finiteDimensionalFactorLadderData k S
    (D.forward.labelEquiv '' K)
  have hrel : FactorLadder.Data.Relabeling A B eDeleted :=
    D.finiteDimensionalReverseFactorLadderData_relabeling
      (k := k) (S := S) σ τ K
  have hl : A.ladder x n p =
      B.ladder (eDeleted x) n (eDeleted p) := by
    simpa using congrFun (hrel.reindex_ladder x n) (eDeleted p)
  have hposDual : 0 < B.ladder (eDeleted x) n (eDeleted p) := by
    simpa [← hl] using hpos
  have hpathDual :=
    FiniteARTranslationData.factorLadderData_ladder_pos_reflTransGen_irreducible
      (σ := τ) (D := τ.finiteDimensionalARTranslationData k S)
      (D.forward.labelEquiv '' K) (eDeleted x) (eDeleted p) n
        hposDual
  have pullPath :
      ∀ {a b : DeletedLabel (D.forward.labelEquiv '' K)},
        Relation.ReflTransGen
            (fun y z : DeletedLabel (D.forward.labelEquiv '' K) ↦
              HasIrreducibleMorphism (τ.obj y.1) (τ.obj z.1))
            a b →
          Relation.ReflTransGen
            (fun y z : DeletedLabel K ↦
              HasIrreducibleMorphism (σ.obj z.1) (σ.obj y.1))
            (eDeleted.symm a) (eDeleted.symm b) := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
        apply Relation.ReflTransGen.tail ih
        apply (D.hasIrreducibleMorphism_image_iff σ τ).1
        simpa [eDeleted, AlignedAntiEquivalence.deletedLabelEquiv] using hbc
  simpa [eDeleted] using pullPath hpathDual

omit [Algebra k R] [FiniteDimensional k R] in
/-- Reaching the injective reverse-ladder boundary gives literal reachability
from the injective boundary in the reversed irreducible AR digraph. -/
theorem reverseFactorLadder_reachesBoundary_implies_reachedFromBoundary
    (Deleted : Finset ι)
    (x : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hreach :
      (D.finiteDimensionalReverseFactorLadderData
        (k := k) (S := S) σ τ ((Deleted : Set ι)ᶜ)).ReachesBoundary
          (deletedInjectiveSet σ ((Deleted : Set ι)ᶜ)) x) :
    QuotientSubmoduleEquidistribution.RootedDigraph.ReachedFromBoundary
      (fun y z ↦ σ.irreducibleEdge z y)
      σ.injectiveLabelFinset Deleted x.1 := by
  rcases hreach with ⟨n, i, hi, hpos⟩
  refine ⟨i.1, ?_, ?_, ?_⟩
  · simpa [deletedInjectiveSet] using hi
  · simpa using i.2
  · have hpath :=
      D.reverseFactorLadderData_ladder_pos_reflTransGen_irreducible
        (k := k) (S := S) σ τ ((Deleted : Set ι)ᶜ) x i n hpos
    have liftPath :
        ∀ {y z : DeletedLabel ((Deleted : Set ι)ᶜ)},
          Relation.ReflTransGen
              (fun a b : DeletedLabel ((Deleted : Set ι)ᶜ) ↦
                HasIrreducibleMorphism (σ.obj b.1) (σ.obj a.1))
              y z →
            Relation.ReflTransGen
              (QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
                (fun a b ↦ σ.irreducibleEdge b a) Deleted) y.1 z.1 := by
      intro y z hyz
      induction hyz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
          exact Relation.ReflTransGen.tail ih
            ⟨by simpa using b.2, by simpa using c.2,
              by simpa [irreducibleEdge] using hbc⟩
    exact liftPath hpath

omit [Algebra k R] [FiniteDimensional k R] in
/-- If every deleted label reaches the injective reverse-ladder boundary,
then the deleted finset is injectively corooted. -/
theorem isInjectivelyCorooted_of_reverseFactorLadder_reachesBoundary
    (Deleted : Finset ι)
    (hall : ∀ x : DeletedLabel ((Deleted : Set ι)ᶜ),
      (D.finiteDimensionalReverseFactorLadderData
        (k := k) (S := S) σ τ ((Deleted : Set ι)ᶜ)).ReachesBoundary
          (deletedInjectiveSet σ ((Deleted : Set ι)ᶜ)) x) :
    QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
      σ.irreducibleEdge σ.injectiveLabelFinset Deleted := by
  intro x hx
  let xd : DeletedLabel ((Deleted : Set ι)ᶜ) :=
    ⟨x, by simpa using hx⟩
  exact D.reverseFactorLadder_reachesBoundary_implies_reachedFromBoundary
    (k := k) (S := S) σ τ Deleted xd (hall xd)

end AlignedBiduality

/-- The bad event for a deleted finset on the submodule side: some reverse
factor ladder fails to reach a deleted injective. -/
def SubmoduleFactorLadderBad
    (D : AlignedBiduality σ τ) (Deleted : Finset ι) : Prop :=
  ∃ x : DeletedLabel ((Deleted : Set ι)ᶜ),
    ¬ (D.finiteDimensionalReverseFactorLadderData
      (k := k) (S := S) σ τ ((Deleted : Set ι)ᶜ)).ReachesBoundary
        (deletedInjectiveSet σ ((Deleted : Set ι)ᶜ)) x

omit [Algebra k R] [FiniteDimensional k R] in
/-- Submodule closure of a cofinite support is exactly injective corootedness
of its deleted vertices together with absence of the reverse factor-ladder
bad event. -/
theorem sClosure_isClosed_compl_iff_injectivelyCorooted_and_not_factorLadderBad
    (D : AlignedBiduality σ τ) (Deleted : Finset ι) :
    σ.sClosure.IsClosed ((Deleted : Set ι)ᶜ) ↔
      QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
          σ.irreducibleEdge σ.injectiveLabelFinset Deleted ∧
        ¬ SubmoduleFactorLadderBad
          (k := k) (S := S) σ τ D Deleted := by
  constructor
  · intro hclosed
    have hall : ∀ x : DeletedLabel ((Deleted : Set ι)ᶜ),
        (D.finiteDimensionalReverseFactorLadderData
          (k := k) (S := S) σ τ
            ((Deleted : Set ι)ᶜ)).ReachesBoundary
              (deletedInjectiveSet σ ((Deleted : Set ι)ᶜ)) x :=
      (sClosed_iff_generated_isClosedUnderSubobjects
        σ ((Deleted : Set ι)ᶜ)).1 hclosed |>
          (D.generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
            (k := k) (R := R) (S := S) σ τ
              ((Deleted : Set ι)ᶜ)).1
    refine ⟨?_, ?_⟩
    · exact D.isInjectivelyCorooted_of_reverseFactorLadder_reachesBoundary
        (k := k) (S := S) σ τ Deleted hall
    · rintro ⟨x, hx⟩
      exact hx (hall x)
  · rintro ⟨_, hgood⟩
    apply (sClosed_iff_generated_isClosedUnderSubobjects
      σ ((Deleted : Set ι)ᶜ)).2
    apply
      (D.generated_isClosedUnderSubobjects_iff_reverseFactorLadder_reaches_injective
        (k := k) (R := R) (S := S) σ τ
          ((Deleted : Set ι)ᶜ)).2
    intro x
    by_contra hx
    exact hgood ⟨x, hx⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
