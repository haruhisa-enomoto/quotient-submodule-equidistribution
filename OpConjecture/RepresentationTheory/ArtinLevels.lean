import OpConjecture.RepresentationTheory.AnnihilatorInflation

/-!
# Exact-annihilator decomposition at arbitrary levels

Every fixed-cardinality quotient- or submodule-closed support has a unique
common annihilator.  This partitions the level as a dependent sum of exact
annihilator fibers.  Given compatible skeletons for all factor rings,
inflation identifies those fibers with faithful supports over the factors.

The construction is valid at every level and does not require Artinianity,
finiteness of the ambient skeleton or ideal type, or any duality.
-/

noncomputable section

open Set

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore

universe u v vq

open OpConjecture.AnnihilatorInflation
open OpConjecture.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- Quotient-closed supports at level `n`. -/
abbrev ArtinQLevel (n : ℕ) :=
  {C : σ.qClosure.Closeds // (C : Set ι).ncard = n}

/-- Submodule-closed supports at level `n`. -/
abbrev ArtinSLevel (n : ℕ) :=
  {C : σ.sClosure.Closeds // (C : Set ι).ncard = n}

/-- Partition quotient-closed level `n` by its exact common annihilator. -/
def qLevelSigmaAnnihilatorEquiv (n : ℕ) :
    ArtinQLevel σ n ≃
      Σ I : TwoSidedIdeal R,
        Skeleton.InflationData.QAnnihilatorLevel σ I n where
  toFun C :=
    ⟨supportAnnihilator σ.obj (C.1 : Set ι),
      ⟨C.1, rfl, C.2⟩⟩
  invFun C := ⟨C.2.1, C.2.2.2⟩
  left_inv _ := rfl
  right_inv C := by
    rcases C with ⟨I, ⟨C, hAnn, hCard⟩⟩
    subst I
    rfl

/-- Partition submodule-closed level `n` by its exact common annihilator. -/
def sLevelSigmaAnnihilatorEquiv (n : ℕ) :
    ArtinSLevel σ n ≃
      Σ I : TwoSidedIdeal R,
        Skeleton.InflationData.SAnnihilatorLevel σ I n where
  toFun C :=
    ⟨supportAnnihilator σ.obj (C.1 : Set ι),
      ⟨C.1, rfl, C.2⟩⟩
  invFun C := ⟨C.2.1, C.2.2.2⟩
  left_inv _ := rfl
  right_inv C := by
    rcases C with ⟨I, ⟨C, hAnn, hCard⟩⟩
    subst I
    rfl

@[simp]
theorem qLevelSigmaAnnihilatorEquiv_ideal
    (n : ℕ) (C : ArtinQLevel σ n) :
    (qLevelSigmaAnnihilatorEquiv σ n C).1 =
      supportAnnihilator σ.obj (C.1 : Set ι) :=
  rfl

@[simp]
theorem sLevelSigmaAnnihilatorEquiv_ideal
    (n : ℕ) (C : ArtinSLevel σ n) :
    (sLevelSigmaAnnihilatorEquiv σ n C).1 =
      supportAnnihilator σ.obj (C.1 : Set ι) :=
  rfl

section Factorwise

variable {L : TwoSidedIdeal R → Type vq}
  [factorNoetherian : ∀ I : TwoSidedIdeal R,
    IsNoetherianRing (Quotient.Factor I)]
  (τ : ∀ I : TwoSidedIdeal R,
    IndecomposableSkeleton.{u, vq, u} (Quotient.Factor I) (L I))
  (D : ∀ I : TwoSidedIdeal R,
    Skeleton.InflationData σ I (τ I))

/-- Refine the annihilator partition of quotient-closed level `n` by
identifying each exact fiber with faithful quotient-closed supports over its
factor ring. -/
def qLevelFactorFaithfulEquiv (n : ℕ) :
    ArtinQLevel σ n ≃
      Σ I : TwoSidedIdeal R,
        Skeleton.InflationData.FaithfulQLevel I (τ I) n :=
  (qLevelSigmaAnnihilatorEquiv σ n).trans
    (Equiv.sigmaCongrRight fun I ↦
      (Skeleton.InflationData.faithfulQLevelEquiv
        σ I (τ I) (D I) n).symm)

/-- Refine the annihilator partition of submodule-closed level `n` by
identifying each exact fiber with faithful submodule-closed supports over its
factor ring. -/
def sLevelFactorFaithfulEquiv (n : ℕ) :
    ArtinSLevel σ n ≃
      Σ I : TwoSidedIdeal R,
        Skeleton.InflationData.FaithfulSLevel I (τ I) n :=
  (sLevelSigmaAnnihilatorEquiv σ n).trans
    (Equiv.sigmaCongrRight fun I ↦
      (Skeleton.InflationData.faithfulSLevelEquiv
        σ I (τ I) (D I) n).symm)

@[simp]
theorem qLevelFactorFaithfulEquiv_ideal
    (n : ℕ) (C : ArtinQLevel σ n) :
    (qLevelFactorFaithfulEquiv σ τ D n C).1 =
      supportAnnihilator σ.obj (C.1 : Set ι) :=
  rfl

@[simp]
theorem sLevelFactorFaithfulEquiv_ideal
    (n : ℕ) (C : ArtinSLevel σ n) :
    (sLevelFactorFaithfulEquiv σ τ D n C).1 =
      supportAnnihilator σ.obj (C.1 : Set ι) :=
  rfl

end Factorwise

end OpConjecture.IndecomposableSkeleton.FaithfulCore
