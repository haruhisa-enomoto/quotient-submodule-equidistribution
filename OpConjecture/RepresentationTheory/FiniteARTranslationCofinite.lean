import OpConjecture.RepresentationTheory.FiniteARTranslationData

/-!
# Field-free finite AR translation and colevel two

This file removes the field from the finite-skeleton colevel-two deduction.
Pointwise Artinianness of indecomposable endomorphism rings supplies the
anti-exchange descriptions of the quotient and submodule closures.  A
`FiniteARTranslationData` supplies both the right and transported left
almost-split decompositions used to identify the mixed boundary with
irreducible morphisms.

Consequently the two literal `rad / rad²` boundary counts and the two
literal `N - 2` levels agree, with the manuscript's simple-rank formula.
-/

noncomputable section

open Set CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

open OpConjecture.IndecomposableSkeleton.FaithfulCore

universe uR uι

section ArtinianEnds

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)
  [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]

/-- With Artinian indecomposable endomorphism rings, a quotient-side top
extreme is exactly a categorical projective. -/
theorem qIsTopExtreme_iff_projective_of_artinianEnd (p : ι) :
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

/-- With Artinian indecomposable endomorphism rings, a submodule-side top
extreme is exactly a categorical injective. -/
theorem sIsTopExtreme_iff_injective_of_artinianEnd (i : ι) :
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

end ArtinianEnds

namespace FiniteARTranslationData

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{uR, uι, uR} R ι)
  [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))]
  (D : σ.FiniteARTranslationData)

omit [DecidableEq ι] in
/-- The quotient top-extreme finset is the projective boundary. -/
theorem qTopExtremeFinset_eq_topSplitProjectiveIndices_of_artinianEnd :
    σ.qClosure.topExtremeFinset =
      σ.topSplitProjectiveIndices := by
  classical
  ext x
  rw [OpConjecture.SetClosure.mem_topExtremeFinset,
    mem_topSplitProjectiveIndices]
  calc
    σ.qClosure.IsTopExtreme x ↔ Projective (σ.obj x) :=
      σ.qIsTopExtreme_iff_projective_of_artinianEnd x
    _ ↔ σ.IsRelativeSplitProjective Set.univ x :=
      σ.projective_iff_isRelativeSplitProjective_univ

omit [DecidableEq ι] in
/-- The submodule top-extreme finset is the injective boundary. -/
theorem sTopExtremeFinset_eq_topSplitInjectiveIndices_of_artinianEnd :
    σ.sClosure.topExtremeFinset =
      σ.topSplitInjectiveIndices := by
  classical
  ext x
  rw [OpConjecture.SetClosure.mem_topExtremeFinset,
    mem_topSplitInjectiveIndices]
  calc
    σ.sClosure.IsTopExtreme x ↔ Injective (σ.obj x) :=
      σ.sIsTopExtreme_iff_injective_of_artinianEnd x
    _ ↔ σ.IsRelativeSplitInjective Set.univ x :=
      σ.injective_iff_isRelativeSplitInjective_univ

/-- Quotient cofinite-two count split into its projective and mixed
boundaries, without a field hypothesis. -/
theorem qCofiniteTwoCount_eq_choose_add_mixedBoundaryCount_of_artinianEnd :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        σ.qClosure.mixedBoundaryCount := by
  rw [← qTopExtremeFinset_eq_topSplitProjectiveIndices_of_artinianEnd σ]
  exact
    OpConjecture.SetClosure.cofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      σ.qClosure (qClosure_isAntiExchange σ)

/-- Submodule cofinite-two count split into its injective and mixed
boundaries, without a field hypothesis. -/
theorem sCofiniteTwoCount_eq_choose_add_mixedBoundaryCount_of_artinianEnd :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        σ.sClosure.mixedBoundaryCount := by
  rw [← sTopExtremeFinset_eq_topSplitInjectiveIndices_of_artinianEnd σ]
  exact
    OpConjecture.SetClosure.cofiniteTwoCount_eq_choose_add_mixedBoundaryCount
      σ.sClosure (sClosure_isAntiExchange σ)

/-- Orienting a quotient mixed boundary pair gives its unique
projective-to-nonprojective irreducible pair. -/
def qMixedBoundaryPairEquivQIrreducibleBoundaryPair_of_finiteAR :
    σ.qClosure.MixedBoundaryPair ≃ σ.QIrreducibleBoundaryPair where
  toFun p := by
    have hp : Projective (σ.obj p.1.1) :=
      (σ.qIsTopExtreme_iff_projective_of_artinianEnd p.1.1).1 p.2.1
    have hz : ¬ Projective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((σ.qIsTopExtreme_iff_projective_of_artinianEnd p.1.2).2 hz)
    have hp' : σ.IsRelativeSplitProjective Set.univ p.1.1 :=
      (σ.projective_iff_isRelativeSplitProjective_univ).1 hp
    have hz' : ¬ σ.IsRelativeSplitProjective Set.univ p.1.2 := by
      intro hz'
      exact hz ((σ.projective_iff_isRelativeSplitProjective_univ).2 hz')
    exact
      ⟨p.1, hp, hz,
        (σ.qClosed_compl_pair_iff_hasIrreducible_of_rightAR
          p.ne hp' hz'
          (chosenRightAR σ D ⟨p.1.2, hz⟩)).1 p.2.2.2⟩
  invFun p := by
    have hp : σ.qClosure.IsTopExtreme p.1.1 :=
      (σ.qIsTopExtreme_iff_projective_of_artinianEnd p.1.1).2 p.2.1
    have hz : ¬ σ.qClosure.IsTopExtreme p.1.2 := by
      intro hz
      exact p.2.2.1
        ((σ.qIsTopExtreme_iff_projective_of_artinianEnd p.1.2).1 hz)
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

/-- Reversing the closure-theoretic submodule orientation gives the unique
noninjective-to-injective irreducible pair. -/
def sMixedBoundaryPairEquivSIrreducibleBoundaryPair_of_finiteAR :
    σ.sClosure.MixedBoundaryPair ≃ σ.SIrreducibleBoundaryPair where
  toFun p := by
    have hi : Injective (σ.obj p.1.1) :=
      (σ.sIsTopExtreme_iff_injective_of_artinianEnd p.1.1).1 p.2.1
    have hz : ¬ Injective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((σ.sIsTopExtreme_iff_injective_of_artinianEnd p.1.2).2 hz)
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
      (σ.sIsTopExtreme_iff_injective_of_artinianEnd p.1.2).2 p.2.2.1
    have hz : ¬ σ.sClosure.IsTopExtreme p.1.1 := by
      intro hz
      exact p.2.1
        ((σ.sIsTopExtreme_iff_injective_of_artinianEnd p.1.1).1 hz)
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

include D in
/-- The quotient mixed boundary has cardinality `beta_q`. -/
theorem qMixedBoundaryCount_eq_natCard_QIrreducibleBoundaryPair_of_finiteAR :
    σ.qClosure.mixedBoundaryCount =
      Nat.card σ.QIrreducibleBoundaryPair := by
  rw [OpConjecture.SetClosure.mixedBoundaryCount_eq_natCard_mixedBoundaryPair]
  exact Nat.card_congr
    (qMixedBoundaryPairEquivQIrreducibleBoundaryPair_of_finiteAR σ D)

include D in
/-- The submodule mixed boundary has cardinality `beta_s`. -/
theorem sMixedBoundaryCount_eq_natCard_SIrreducibleBoundaryPair_of_finiteAR :
    σ.sClosure.mixedBoundaryCount =
      Nat.card σ.SIrreducibleBoundaryPair := by
  rw [OpConjecture.SetClosure.mixedBoundaryCount_eq_natCard_mixedBoundaryPair]
  exact Nat.card_congr
    (sMixedBoundaryPairEquivSIrreducibleBoundaryPair_of_finiteAR σ D)

include D in
/-- Field-free quotient cofinite-two formula with categorical boundary. -/
theorem qCofiniteTwoCount_eq_choose_add_irreducibleBoundary_of_finiteAR :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [qCofiniteTwoCount_eq_choose_add_mixedBoundaryCount_of_artinianEnd σ,
    qMixedBoundaryCount_eq_natCard_QIrreducibleBoundaryPair_of_finiteAR σ D]

include D in
/-- Field-free submodule cofinite-two formula with categorical boundary. -/
theorem sCofiniteTwoCount_eq_choose_add_irreducibleBoundary_of_finiteAR :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [sCofiniteTwoCount_eq_choose_add_mixedBoundaryCount_of_artinianEnd σ,
    sMixedBoundaryCount_eq_natCard_SIrreducibleBoundaryPair_of_finiteAR σ D]

omit [DecidableEq ι]
  [∀ i : ι, IsArtinianRing (Module.End R (σ.obj i))] in
include D in
/-- The injective top boundary has one label for every simple module, using
only the supplied projective--injective boundary equivalence. -/
theorem topSplitInjectiveIndices_card_eq_natCard_simpleIndex_of_finiteAR :
    σ.topSplitInjectiveIndices.card = Nat.card σ.SimpleIndex := by
  calc
    σ.topSplitInjectiveIndices.card =
        ((↑σ.topSplitInjectiveIndices : Set ι)).ncard :=
      (Set.ncard_coe_finset _).symm
    _ = (OpConjecture.RingelStable.injectiveSet σ).ncard := by
      congr 1
      ext i
      simp [OpConjecture.RingelStable.injectiveSet,
        σ.injective_iff_isRelativeSplitInjective_univ]
    _ = (OpConjecture.RingelStable.projectiveSet σ).ncard := by
      change Nat.card {i : ι // Injective (σ.obj i)} =
        Nat.card {i : ι // Projective (σ.obj i)}
      exact (Nat.card_congr D.boundary).symm
    _ = (projectiveLabels σ).ncard := rfl
    _ = Nat.card σ.SimpleIndex :=
      ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex σ

include D in
/-- Field-free quotient cofinite-two formula in simple-rank form. -/
theorem qCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [qCofiniteTwoCount_eq_choose_add_irreducibleBoundary_of_finiteAR σ D,
    σ.topSplitProjectiveIndices_card_eq_natCard_simpleIndex]

include D in
/-- Field-free submodule cofinite-two formula in simple-rank form. -/
theorem sCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [sCofiniteTwoCount_eq_choose_add_irreducibleBoundary_of_finiteAR σ D,
    topSplitInjectiveIndices_card_eq_natCard_simpleIndex_of_finiteAR σ D]

include D in
/-- The quotient-side literal `N - 2` level has the categorical
simple-rank-plus-boundary formula. -/
theorem
    literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.literalQuotientLevelCount_eq_levelCount,
    ← σ.qCofiniteTwoCount_eq_levelCount_card_sub_two hcard]
  exact
    qCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
      σ D

include D in
/-- The submodule-side literal `N - 2` level has the categorical
simple-rank-plus-boundary formula. -/
theorem
    literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.literalSubobjectLevelCount_eq_levelCount,
    ← σ.sCofiniteTwoCount_eq_levelCount_card_sub_two hcard]
  exact
    sCofiniteTwoCount_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
      σ D

include D in
/-- The quotient-side literal formula in the manuscript's `rad / rad²`
notation. -/
theorem
    literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary_of_finiteAR
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.QRadicalQuotientBoundaryPair := by
  rw [literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
      σ D hcard,
    σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair]

include D in
/-- The submodule-side literal formula in the manuscript's `rad / rad²`
notation. -/
theorem
    literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary_of_finiteAR
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose (Nat.card σ.SimpleIndex) 2 +
        Nat.card σ.SRadicalQuotientBoundaryPair := by
  rw [literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_irreducibleBoundary_of_finiteAR
      σ D hcard,
    σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair]

include D in
/-- Field-free finite-skeleton form of the manuscript's colevel-two
corollary: `beta_q = beta_s`, the two literal levels agree, and their common
value is the simple-rank plus literal radical-quotient boundary count. -/
theorem literalRadicalQuotientCofiniteTwo_formula_of_finiteAR
    (hcard : 2 ≤ Nat.card ι) :
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.SRadicalQuotientBoundaryPair ∧
      σ.literalQuotientLevelCount (Nat.card ι - 2) =
          σ.literalSubobjectLevelCount (Nat.card ι - 2) ∧
        σ.literalQuotientLevelCount (Nat.card ι - 2) =
          Nat.choose (Nat.card σ.SimpleIndex) 2 +
            Nat.card σ.QRadicalQuotientBoundaryPair := by
  have hbeta :
      Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.SRadicalQuotientBoundaryPair :=
    natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair
      σ D
  have hq :=
    literalQuotientLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary_of_finiteAR
      σ D hcard
  have hs :=
    literalSubobjectLevelCount_card_sub_two_eq_choose_simpleIndex_add_radicalQuotientBoundary_of_finiteAR
      σ D hcard
  refine ⟨hbeta, ?_, hq⟩
  calc
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.QRadicalQuotientBoundaryPair := hq
    _ = Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.SRadicalQuotientBoundaryPair := by rw [hbeta]
    _ = σ.literalSubobjectLevelCount (Nat.card ι - 2) := hs.symm

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
