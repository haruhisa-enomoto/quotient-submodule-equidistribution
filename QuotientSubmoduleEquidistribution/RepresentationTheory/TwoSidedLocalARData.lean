import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteARTranslationData

/-!
# Two-sided local almost-split data on an arbitrary skeleton

The mixed cofinite-two boundary is local: identifying it with irreducible
boundary pairs needs a minimal right almost-split decomposition at each
nonprojective endpoint and a minimal left almost-split decomposition at each
noninjective endpoint, but it does not need a finite ambient skeleton.

This file packages those two families together with the projective--injective
boundary equivalence used by the finite AR-translation construction.  It then
identifies the quotient and submodule mixed-boundary types with their
categorical irreducible-boundary types.  No cardinality or ambient finiteness
statement is made here.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- Two-sided local Auslander--Reiten input on an arbitrary complete
indecomposable skeleton.  The structure itself imposes no finiteness
condition on the label type. -/
structure TwoSidedLocalARData where
  rightAR_nonempty : ∀ z : σ.NonprojectiveLabel,
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1)
  leftAR_nonempty : ∀ z : σ.NoninjectiveLabel,
    Nonempty (σ.MinimalLeftAlmostSplitDecomposition z.1)
  boundary :
    {i : ι // Projective (σ.obj i)} ≃
      {i : ι // Injective (σ.obj i)}

namespace TwoSidedLocalARData

variable (D : σ.TwoSidedLocalARData)

/-- Forget the separately supplied left almost-split decompositions.  The
remaining right family and boundary equivalence are exactly the existing
`FiniteARTranslationData` interface. -/
def toFiniteARTranslationData : σ.FiniteARTranslationData where
  rightAR_nonempty := D.rightAR_nonempty
  boundary := D.boundary

/-- Choose the supplied minimal right almost-split decomposition at a
nonprojective label. -/
def chosenRightAR (z : σ.NonprojectiveLabel) :
    σ.MinimalRightAlmostSplitDecomposition z.1 :=
  Classical.choice (D.rightAR_nonempty z)

/-- Choose the supplied minimal left almost-split decomposition at a
noninjective label. -/
def chosenLeftAR (z : σ.NoninjectiveLabel) :
    σ.MinimalLeftAlmostSplitDecomposition z.1 :=
  Classical.choice (D.leftAR_nonempty z)

section ArtinianEnds

variable [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

private theorem qIsTopExtreme_iff_projective (p : ι) :
    σ.qClosure.IsTopExtreme p ↔ Projective (σ.obj p) := by
  calc
    σ.qClosure.IsTopExtreme p ↔
        σ.IsRelativeSplitProjective Set.univ p := by
      change
        p ∈ σ.qClosure.extremePoints Set.univ ↔
          σ.IsRelativeSplitProjective Set.univ p
      rw [qExtremePoints_eq_relativeSplitProjectives σ]
      simp
    _ ↔ Projective (σ.obj p) :=
      (σ.projective_iff_isRelativeSplitProjective_univ).symm

private theorem sIsTopExtreme_iff_injective (i : ι) :
    σ.sClosure.IsTopExtreme i ↔ Injective (σ.obj i) := by
  calc
    σ.sClosure.IsTopExtreme i ↔
        σ.IsRelativeSplitInjective Set.univ i := by
      change
        i ∈ σ.sClosure.extremePoints Set.univ ↔
          σ.IsRelativeSplitInjective Set.univ i
      rw [sExtremePoints_eq_relativeSplitInjectives σ]
      simp
    _ ↔ Injective (σ.obj i) :=
      (σ.injective_iff_isRelativeSplitInjective_univ).symm

/-- Orienting a quotient mixed-boundary deletion yields precisely a
projective-to-nonprojective irreducible boundary pair.  This equivalence is
valid on an arbitrary label type. -/
def qMixedBoundaryPairEquivQIrreducibleBoundaryPair :
    σ.qClosure.MixedBoundaryPair ≃ σ.QIrreducibleBoundaryPair where
  toFun p := by
    have hp : Projective (σ.obj p.1.1) :=
      (qIsTopExtreme_iff_projective σ p.1.1).1 p.2.1
    have hz : ¬ Projective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((qIsTopExtreme_iff_projective σ p.1.2).2 hz)
    have hp' : σ.IsRelativeSplitProjective Set.univ p.1.1 :=
      (σ.projective_iff_isRelativeSplitProjective_univ).1 hp
    have hz' : ¬ σ.IsRelativeSplitProjective Set.univ p.1.2 := by
      intro hz'
      exact hz ((σ.projective_iff_isRelativeSplitProjective_univ).2 hz')
    exact
      ⟨p.1, hp, hz,
        (σ.qClosed_compl_pair_iff_hasIrreducible_of_rightAR
          p.ne hp' hz' (chosenRightAR σ D ⟨p.1.2, hz⟩)).1
            p.2.2.2⟩
  invFun p := by
    have hp : σ.qClosure.IsTopExtreme p.1.1 :=
      (qIsTopExtreme_iff_projective σ p.1.1).2 p.2.1
    have hz : ¬ σ.qClosure.IsTopExtreme p.1.2 := by
      intro hz
      exact p.2.2.1
        ((qIsTopExtreme_iff_projective σ p.1.2).1 hz)
    have hne : p.1.1 ≠ p.1.2 := by
      intro h
      exact p.2.2.1 (h ▸ p.2.1)
    have hp' : σ.IsRelativeSplitProjective Set.univ p.1.1 :=
      (σ.projective_iff_isRelativeSplitProjective_univ).1 p.2.1
    have hz' : ¬ σ.IsRelativeSplitProjective Set.univ p.1.2 := by
      intro hz'
      exact p.2.2.1
        ((σ.projective_iff_isRelativeSplitProjective_univ).2 hz')
    exact
      ⟨p.1, hp, hz,
        (σ.qClosed_compl_pair_iff_hasIrreducible_of_rightAR
          hne hp' hz' (chosenRightAR σ D ⟨p.1.2, p.2.2.1⟩)).2
            p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Reversing the closure-theoretic submodule orientation yields precisely a
noninjective-to-injective irreducible boundary pair.  This equivalence is
valid on an arbitrary label type. -/
def sMixedBoundaryPairEquivSIrreducibleBoundaryPair :
    σ.sClosure.MixedBoundaryPair ≃ σ.SIrreducibleBoundaryPair where
  toFun p := by
    have hi : Injective (σ.obj p.1.1) :=
      (sIsTopExtreme_iff_injective σ p.1.1).1 p.2.1
    have hz : ¬ Injective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((sIsTopExtreme_iff_injective σ p.1.2).2 hz)
    have hi' : σ.IsRelativeSplitInjective Set.univ p.1.1 :=
      (σ.injective_iff_isRelativeSplitInjective_univ).1 hi
    have hz' : ¬ σ.IsRelativeSplitInjective Set.univ p.1.2 := by
      intro hz'
      exact hz ((σ.injective_iff_isRelativeSplitInjective_univ).2 hz')
    have hclosed :
        σ.sClosure.IsClosed ({p.1.2, p.1.1} : Set ι)ᶜ := by
      simpa [Set.pair_comm] using p.2.2.2
    exact
      ⟨(p.1.2, p.1.1), hz, hi,
        (σ.sClosed_compl_pair_iff_hasIrreducible_of_leftAR
          p.ne.symm hz' hi' (chosenLeftAR σ D ⟨p.1.2, hz⟩)).1
            hclosed⟩
  invFun p := by
    have hi : σ.sClosure.IsTopExtreme p.1.2 :=
      (sIsTopExtreme_iff_injective σ p.1.2).2 p.2.2.1
    have hz : ¬ σ.sClosure.IsTopExtreme p.1.1 := by
      intro hz
      exact p.2.1
        ((sIsTopExtreme_iff_injective σ p.1.1).1 hz)
    have hne : p.1.1 ≠ p.1.2 := by
      intro h
      exact p.2.1 (h ▸ p.2.2.1)
    have hi' : σ.IsRelativeSplitInjective Set.univ p.1.2 :=
      (σ.injective_iff_isRelativeSplitInjective_univ).1 p.2.2.1
    have hz' : ¬ σ.IsRelativeSplitInjective Set.univ p.1.1 := by
      intro hz'
      exact p.2.1
        ((σ.injective_iff_isRelativeSplitInjective_univ).2 hz')
    have hclosed :
        σ.sClosure.IsClosed ({p.1.2, p.1.1} : Set ι)ᶜ := by
      simpa [Set.pair_comm] using
        ((σ.sClosed_compl_pair_iff_hasIrreducible_of_leftAR
          hne hz' hi' (chosenLeftAR σ D ⟨p.1.1, p.2.1⟩)).2
            p.2.2.2)
    exact ⟨(p.1.2, p.1.1), hi, hz, hclosed⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

end ArtinianEnds

end TwoSidedLocalARData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
