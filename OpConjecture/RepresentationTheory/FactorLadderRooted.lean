import OpConjecture.ConvexGeometry.CofiniteRootedDigraph
import OpConjecture.RepresentationTheory.ARQuiverDetermination

/-!
# Factor ladders imply projective rootedness

Positive coefficients in a forward AR factor ladder propagate only along
irreducible predecessors.  Consequently, reaching a deleted projective
forces an irreducible path inside the deleted set from a projective vertex to
the starting vertex.  This removes projective rootedness as an independent
hypothesis in the quotient-side cofinite closure characterization.
-/

set_option autoImplicit false
noncomputable section

open Set CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The underlying directed AR edge relation, with valuations forgotten. -/
def irreducibleEdge (x y : ι) : Prop :=
  HasIrreducibleMorphism (σ.obj x) (σ.obj y)

/-- The finite projective boundary of the chosen skeleton. -/
def projectiveLabelFinset : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun p ↦ Projective (σ.obj p)

/-- The finite injective boundary of the chosen skeleton. -/
def injectiveLabelFinset : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun i ↦ Injective (σ.obj i)

omit [DecidableEq ι] in
@[simp]
theorem mem_projectiveLabelFinset {p : ι} :
    p ∈ σ.projectiveLabelFinset ↔ Projective (σ.obj p) := by
  classical
  simp [projectiveLabelFinset]

omit [DecidableEq ι] in
@[simp]
theorem mem_injectiveLabelFinset {i : ι} :
    i ∈ σ.injectiveLabelFinset ↔ Injective (σ.obj i) := by
  classical
  simp [injectiveLabelFinset]

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- Reaching the projective factor-ladder boundary gives literal directed
reachability from the projective boundary inside the deleted finset. -/
theorem factorLadder_reachesBoundary_implies_reachedFromBoundary
    (Deleted : Finset ι)
    (x : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hreach :
      (factorLadderData (σ := σ) (D := D)
        ((Deleted : Set ι)ᶜ)).ReachesBoundary
          (deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)) x) :
    OpConjecture.RootedDigraph.ReachedFromBoundary
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted x.1 := by
  rcases hreach with ⟨n, p, hp, hpos⟩
  refine ⟨p.1, ?_, ?_, ?_⟩
  · simpa [deletedProjectiveSet] using hp
  · simpa using p.2
  · have hpath :=
      factorLadderData_ladder_pos_reflTransGen_irreducible
        (σ := σ) D ((Deleted : Set ι)ᶜ) x p n hpos
    have liftPath :
        ∀ {y z : DeletedLabel ((Deleted : Set ι)ᶜ)},
          Relation.ReflTransGen
              (fun a b : DeletedLabel ((Deleted : Set ι)ᶜ) ↦
                HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1))
              y z →
            Relation.ReflTransGen
              (OpConjecture.RootedDigraph.InsideEdge
                σ.irreducibleEdge Deleted) y.1 z.1 := by
      intro y z hyz
      induction hyz with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c hab hbc ih =>
          exact Relation.ReflTransGen.tail ih
            ⟨by simpa using b.2, by simpa using c.2,
              by simpa [irreducibleEdge] using hbc⟩
    exact liftPath hpath

/-- If every deleted label reaches the projective factor-ladder boundary,
then the deleted finset is projectively rooted in the irreducible AR
digraph. -/
theorem isProjectivelyRooted_of_factorLadder_reachesBoundary
    (Deleted : Finset ι)
    (hall : ∀ x : DeletedLabel ((Deleted : Set ι)ᶜ),
      (factorLadderData (σ := σ) (D := D)
        ((Deleted : Set ι)ᶜ)).ReachesBoundary
          (deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)) x) :
    OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted := by
  intro x hx
  let xd : DeletedLabel ((Deleted : Set ι)ᶜ) :=
    ⟨x, by simpa using hx⟩
  exact D.factorLadder_reachesBoundary_implies_reachedFromBoundary
    σ Deleted xd (hall xd)

end FiniteARTranslationData

section FiniteDimensional

variable (k : Type u) [Field k] [Algebra k R]
  [FiniteDimensional k R]

/-- The bad event for a deleted finset: some forward factor ladder fails to
reach a deleted projective. -/
def QuotientFactorLadderBad (Deleted : Finset ι) : Prop :=
  ∃ x : DeletedLabel ((Deleted : Set ι)ᶜ),
    ¬ (finiteDimensionalFactorLadderData k R σ
      ((Deleted : Set ι)ᶜ)).ReachesBoundary
        (deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)) x

/-- Quotient closure of a cofinite support is exactly projective rootedness
of its deleted vertices together with absence of the factor-ladder bad
event.  Projective rootedness is a consequence of the latter condition in
the forward direction, but is retained explicitly for the counting split. -/
theorem qClosure_isClosed_compl_iff_projectivelyRooted_and_not_factorLadderBad
    (Deleted : Finset ι) :
    σ.qClosure.IsClosed ((Deleted : Set ι)ᶜ) ↔
      OpConjecture.RootedDigraph.IsProjectivelyRooted
          σ.irreducibleEdge σ.projectiveLabelFinset Deleted ∧
        ¬ QuotientFactorLadderBad (k := k) (R := R) σ Deleted := by
  let D := σ.finiteDimensionalARTranslationData k R
  constructor
  · intro hclosed
    have hall : ∀ x : DeletedLabel ((Deleted : Set ι)ᶜ),
        (finiteDimensionalFactorLadderData k R σ
          ((Deleted : Set ι)ᶜ)).ReachesBoundary
            (deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)) x :=
      (qClosure_isClosed_iff_quotientARClosedSupport
        (k := k) (R := R) σ ((Deleted : Set ι)ᶜ)).1 hclosed
    refine ⟨?_, ?_⟩
    · exact D.isProjectivelyRooted_of_factorLadder_reachesBoundary
        σ Deleted hall
    · rintro ⟨x, hx⟩
      exact hx (hall x)
  · rintro ⟨_, hgood⟩
    apply (qClosure_isClosed_iff_quotientARClosedSupport
      (k := k) (R := R) σ ((Deleted : Set ι)ᶜ)).2
    intro x
    by_contra hx
    exact hgood ⟨x, hx⟩

end FiniteDimensional

end OpConjecture.IndecomposableSkeleton
