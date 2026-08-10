import OpConjecture.RepresentationTheory.AnnihilatorInflation

noncomputable section

open Set

namespace OpConjecture.AnnihilatorInflation.Skeleton

universe u v w vq

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {K : Type v} [Finite K]
  (sigma : IndecomposableSkeleton.{u, v, w} R K)

variable [∀ I : ProperRealizedAnnihilator sigma,
  IsNoetherianRing (Quotient.Factor I.1.1)]

/-- A simultaneously chosen quotient skeleton and inflation alignment for
every proper annihilator realized by either finite closed-set lattice. -/
structure FactorFamilyData where
  Index : ProperRealizedAnnihilator sigma → Type vq
  finiteIndex : ∀ I : ProperRealizedAnnihilator sigma, Finite (Index I)
  skeleton : ∀ I : ProperRealizedAnnihilator sigma,
    IndecomposableSkeleton.{u, vq, w}
      (Quotient.Factor I.1.1) (Index I)
  inflation : ∀ I : ProperRealizedAnnihilator sigma,
    @InflationData (R := R) (K := K) (L := Index I) _ _ sigma I.1.1
      (inferInstance : IsNoetherianRing (Quotient.Factor I.1.1))
      (skeleton I)

namespace FactorFamilyData

variable (D : FactorFamilyData sigma)

local instance factorIndexFinite
    (I : ProperRealizedAnnihilator sigma) : Finite (D.Index I) :=
  D.finiteIndex I

/-- Exact quotient-side annihilator recurrence rewritten as faithful
level counts of the simultaneously chosen proper factors. -/
theorem qLevelCount_eq_faithful_add_sum_factorFaithful (n : ℕ) :
    sigma.qClosure.levelCount n =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.qClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            (D.skeleton I).qClosure
            (IsFaithfulSupport (D.skeleton I).obj) n := by
  rw [qLevelCount_eq_faithful_add_sum_annihilatorFibers sigma n]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  exact qAnnihilatorFiberCard_eq_factorFaithfulLevelCount
    sigma I (D.skeleton I) (D.inflation I) n

/-- Exact submodule-side annihilator recurrence rewritten over the same
finite family of proper factors. -/
theorem sLevelCount_eq_faithful_add_sum_factorFaithful (n : ℕ) :
    sigma.sClosure.levelCount n =
      OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
          sigma.sClosure (IsFaithfulSupport sigma.obj) n +
        ∑ I : ProperRealizedAnnihilator sigma,
          OpConjecture.BottomLevels.MinimalFaithfulCore.faithfulLevelCount
            (D.skeleton I).sClosure
            (IsFaithfulSupport (D.skeleton I).obj) n := by
  rw [sLevelCount_eq_faithful_add_sum_annihilatorFibers sigma n]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  exact sAnnihilatorFiberCard_eq_factorFaithfulLevelCount
    sigma I (D.skeleton I) (D.inflation I) n

end FactorFamilyData

end OpConjecture.AnnihilatorInflation.Skeleton
