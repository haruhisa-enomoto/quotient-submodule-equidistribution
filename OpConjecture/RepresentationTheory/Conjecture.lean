import OpConjecture.ConvexGeometry.LevelPolynomial
import OpConjecture.RepresentationTheory.FacSub

/-!
# The quotient--submodule equidistribution statements

This file states the strong and weak conjectures from the manuscript on a
finite chosen indecomposable skeleton.  It deliberately proves only the
formal implication from the levelwise statement to the total-count
statement; the universal equidistribution assertion remains a conjecture.
-/

noncomputable section

namespace OpConjecture.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Strong quotient--submodule equidistribution: the two cardinality
generating polynomials agree. -/
def QuotientSubmoduleEquidistribution : Prop :=
  σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial

/-- Weak quotient--submodule equidistribution: the two closed-set lattices
have the same total cardinality. -/
def WeakQuotientSubmoduleEquidistribution : Prop :=
  Nat.card σ.qClosure.Closeds = Nat.card σ.sClosure.Closeds

/-- Polynomial equidistribution is equivalent to equality at every
cardinality level. -/
theorem quotientSubmoduleEquidistribution_iff_levelCounts :
    σ.QuotientSubmoduleEquidistribution ↔
      ∀ n : ℕ,
        σ.qClosure.levelCount n = σ.sClosure.levelCount n := by
  exact
    OpConjecture.SetClosure.levelPolynomial_eq_iff
      σ.qClosure σ.sClosure

/-- The strong conjecture formally implies its specialization at `q = 1`. -/
theorem quotientSubmoduleEquidistribution_implies_weak :
    σ.QuotientSubmoduleEquidistribution →
      σ.WeakQuotientSubmoduleEquidistribution := by
  intro h
  unfold WeakQuotientSubmoduleEquidistribution
  rw [← OpConjecture.SetClosure.levelPolynomial_eval_one σ.qClosure,
    ← OpConjecture.SetClosure.levelPolynomial_eval_one σ.sClosure,
    h]

/-- The finite aggregation used in the first case of the main theorem:
agreement through the bottom and top four levels gives full
equidistribution when there are at most nine indecomposable labels. -/
theorem quotientSubmoduleEquidistribution_of_bottom_top_four
    (hcard : Nat.card ι ≤ 9)
    (hbottom : ∀ i ≤ 4,
      σ.qClosure.levelCount i = σ.sClosure.levelCount i)
    (htop : ∀ i ≤ 4,
      σ.qClosure.levelCount (Nat.card ι - i) =
        σ.sClosure.levelCount (Nat.card ι - i)) :
    σ.QuotientSubmoduleEquidistribution :=
  OpConjecture.SetClosure.levelPolynomial_eq_of_bottom_top_four
    σ.qClosure σ.sClosure hcard hbottom htop

end OpConjecture.IndecomposableSkeleton
