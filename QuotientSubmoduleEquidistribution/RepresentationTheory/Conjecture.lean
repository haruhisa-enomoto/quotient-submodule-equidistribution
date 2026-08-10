import QuotientSubmoduleEquidistribution.ConvexGeometry.LevelPolynomial
import QuotientSubmoduleEquidistribution.RepresentationTheory.FacSub

/-!
# The quotient--submodule equidistribution statements

This file states the strong and weak conjectures from the manuscript on a
finite chosen indecomposable skeleton.  It deliberately proves only the
formal implication from the levelwise statement to the total-count
statement; the universal equidistribution assertion remains a conjecture.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Strong quotient--submodule equidistribution: the two cardinality
generating polynomials agree. -/
def HasQuotientSubmoduleEquidistribution : Prop :=
  σ.qClosure.levelPolynomial = σ.sClosure.levelPolynomial

/-- Weak quotient--submodule equidistribution: the two closed-set lattices
have the same total cardinality. -/
def WeakQuotientSubmoduleEquidistribution : Prop :=
  Nat.card σ.qClosure.Closeds = Nat.card σ.sClosure.Closeds

/-- Polynomial equidistribution is equivalent to equality at every
cardinality level. -/
theorem quotientSubmoduleEquidistribution_iff_levelCounts :
    σ.HasQuotientSubmoduleEquidistribution ↔
      ∀ n : ℕ,
        σ.qClosure.levelCount n = σ.sClosure.levelCount n := by
  exact
    QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_iff
      σ.qClosure σ.sClosure

/-- The strong conjecture formally implies its specialization at `q = 1`. -/
theorem quotientSubmoduleEquidistribution_implies_weak :
    σ.HasQuotientSubmoduleEquidistribution →
      σ.WeakQuotientSubmoduleEquidistribution := by
  intro h
  unfold WeakQuotientSubmoduleEquidistribution
  rw [← QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eval_one σ.qClosure,
    ← QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eval_one σ.sClosure,
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
    σ.HasQuotientSubmoduleEquidistribution :=
  QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_eq_of_bottom_top_four
    σ.qClosure σ.sClosure hcard hbottom htop

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
