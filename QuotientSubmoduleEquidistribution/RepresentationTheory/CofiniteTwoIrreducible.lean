import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleRadicalQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.LiteralLevelCount

/-!
# Cofinite-two counts by irreducible boundary pairs

For a finite complete indecomposable skeleton over a field, this file
identifies the mixed two-point boundary of the quotient and submodule closure
systems with ordered pairs carrying an irreducible morphism.  It then rewrites
the local cofinite-two formulas, both on the skeleton and for literal additive
subcategories, using those categorical pair counts.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe uK uR v w

variable {K : Type uK} [Field K]
  {R : Type uR} [Ring R] [Algebra K R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{uR, v, w} R ι)
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]
  [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
include K in
/-- A quotient-side top extreme label is exactly a categorical projective
indecomposable. -/
theorem qIsTopExtreme_iff_projective (p : ι) :
    σ.qClosure.IsTopExtreme p ↔ Projective (σ.obj p) := by
  calc
    σ.qClosure.IsTopExtreme p ↔
        σ.IsRelativeSplitProjective Set.univ p :=
      σ.qIsTopExtreme_iff_isRelativeSplitProjective (K := K) p
    _ ↔ Projective (σ.obj p) :=
      (σ.projective_iff_isRelativeSplitProjective_univ).symm

omit [Fintype ι] [DecidableEq ι] in
include K in
/-- A submodule-side top extreme label is exactly a categorical injective
indecomposable. -/
theorem sIsTopExtreme_iff_injective (i : ι) :
    σ.sClosure.IsTopExtreme i ↔ Injective (σ.obj i) := by
  calc
    σ.sClosure.IsTopExtreme i ↔
        σ.IsRelativeSplitInjective Set.univ i :=
      σ.sIsTopExtreme_iff_isRelativeSplitInjective (K := K) i
    _ ↔ Injective (σ.obj i) :=
      (σ.injective_iff_isRelativeSplitInjective_univ).symm

/-- Ordered projective-to-nonprojective pairs supporting an irreducible
morphism.  Its natural cardinality is the finite-skeleton version of the
paper's quotient-side boundary term `beta_q`. -/
def QIrreducibleBoundaryPair :=
  {p : ι × ι //
    Projective (σ.obj p.1) ∧
      ¬ Projective (σ.obj p.2) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- Ordered noninjective-to-injective pairs supporting an irreducible
morphism.  Its natural cardinality is the finite-skeleton version of the
paper's submodule-side boundary term `beta_s`. -/
def SIrreducibleBoundaryPair :=
  {p : ι × ι //
    ¬ Injective (σ.obj p.1) ∧
      Injective (σ.obj p.2) ∧
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj p.2)}

/-- The manuscript's literal quotient-side boundary type: ordered
projective-to-nonprojective pairs for which `rad / rad²` is nonzero. -/
def QRadicalQuotientBoundaryPair :=
  {p : ι × ι //
    Projective (σ.obj p.1) ∧
      ¬ Projective (σ.obj p.2) ∧
      Nontrivial (σ.irreducibleHomQuotient p.1 p.2)}

/-- The manuscript's literal submodule-side boundary type: ordered
noninjective-to-injective pairs for which `rad / rad²` is nonzero. -/
def SRadicalQuotientBoundaryPair :=
  {p : ι × ι //
    ¬ Injective (σ.obj p.1) ∧
      Injective (σ.obj p.2) ∧
      Nontrivial (σ.irreducibleHomQuotient p.1 p.2)}

/-- Replacing `rad / rad² ≠ 0` by existence of an irreducible morphism
does not change the quotient-side boundary pair. -/
noncomputable def
    qRadicalQuotientBoundaryPairEquivQIrreducibleBoundaryPair :
    σ.QRadicalQuotientBoundaryPair ≃ σ.QIrreducibleBoundaryPair where
  toFun p :=
    ⟨p.1, p.2.1, p.2.2.1,
      (σ.nontrivial_irreducibleHomQuotient_iff_hasIrreducibleMorphism
        p.1.1 p.1.2).1 p.2.2.2⟩
  invFun p :=
    ⟨p.1, p.2.1, p.2.2.1,
      (σ.hasIrreducibleMorphism_iff_nontrivial_irreducibleHomQuotient
        p.1.1 p.1.2).1 p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Replacing `rad / rad² ≠ 0` by existence of an irreducible morphism
does not change the submodule-side boundary pair. -/
noncomputable def
    sRadicalQuotientBoundaryPairEquivSIrreducibleBoundaryPair :
    σ.SRadicalQuotientBoundaryPair ≃ σ.SIrreducibleBoundaryPair where
  toFun p :=
    ⟨p.1, p.2.1, p.2.2.1,
      (σ.nontrivial_irreducibleHomQuotient_iff_hasIrreducibleMorphism
        p.1.1 p.1.2).1 p.2.2.2⟩
  invFun p :=
    ⟨p.1, p.2.1, p.2.2.1,
      (σ.hasIrreducibleMorphism_iff_nontrivial_irreducibleHomQuotient
        p.1.1 p.1.2).1 p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The literal and categorical quotient-side boundary types have the same
cardinality. -/
theorem
    natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair :
    Nat.card σ.QRadicalQuotientBoundaryPair =
      Nat.card σ.QIrreducibleBoundaryPair :=
  Nat.card_congr σ.qRadicalQuotientBoundaryPairEquivQIrreducibleBoundaryPair

omit [Fintype ι] [DecidableEq ι] in
/-- The literal and categorical submodule-side boundary types have the same
cardinality. -/
theorem
    natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair :
    Nat.card σ.SRadicalQuotientBoundaryPair =
      Nat.card σ.SIrreducibleBoundaryPair :=
  Nat.card_congr σ.sRadicalQuotientBoundaryPairEquivSIrreducibleBoundaryPair

include K in
/-- Orienting a quotient mixed boundary pair identifies it with its unique
projective-to-nonprojective irreducible pair. -/
noncomputable def qMixedBoundaryPairEquivQIrreducibleBoundaryPair :
    σ.qClosure.MixedBoundaryPair ≃ σ.QIrreducibleBoundaryPair where
  toFun p := by
    have hp : Projective (σ.obj p.1.1) :=
      (σ.qIsTopExtreme_iff_projective (K := K) p.1.1).1 p.2.1
    have hz : ¬ Projective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((σ.qIsTopExtreme_iff_projective (K := K) p.1.2).2 hz)
    have hp' : σ.IsRelativeSplitProjective Set.univ p.1.1 :=
      (σ.projective_iff_isRelativeSplitProjective_univ).1 hp
    have hz' : ¬ σ.IsRelativeSplitProjective Set.univ p.1.2 := by
      intro hz'
      exact hz ((σ.projective_iff_isRelativeSplitProjective_univ).2 hz')
    exact
      ⟨p.1, hp, hz,
        (σ.qClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
          (K := K) p.ne hp' hz').1 p.2.2.2⟩
  invFun p := by
    have hp : σ.qClosure.IsTopExtreme p.1.1 :=
      (σ.qIsTopExtreme_iff_projective (K := K) p.1.1).2 p.2.1
    have hz : ¬ σ.qClosure.IsTopExtreme p.1.2 := by
      intro hz
      exact p.2.2.1
        ((σ.qIsTopExtreme_iff_projective (K := K) p.1.2).1 hz)
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
        (σ.qClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
          (K := K) hne hp' hz').2 p.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

include K in
/-- The quotient mixed-boundary count is the cardinality of the categorical
`beta_q` pair type in the finite-skeleton setting. -/
theorem qMixedBoundaryCount_eq_natCard_QIrreducibleBoundaryPair :
    σ.qClosure.mixedBoundaryCount =
      Nat.card σ.QIrreducibleBoundaryPair := by
  rw [QuotientSubmoduleEquidistribution.SetClosure.mixedBoundaryCount_eq_natCard_mixedBoundaryPair]
  exact Nat.card_congr
    (σ.qMixedBoundaryPairEquivQIrreducibleBoundaryPair (K := K))

include K in
/-- Quotient cofinite-two count in terms of projective boundary points and
categorical irreducible boundary pairs. -/
theorem qCofiniteTwoCount_eq_choose_add_natCard_QIrreducibleBoundaryPair :
    σ.qClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.qCofiniteTwoCount_eq_choose_add_mixedBoundaryCount (K := K),
    σ.qMixedBoundaryCount_eq_natCard_QIrreducibleBoundaryPair (K := K)]

include K in
/-- On the submodule side, reverse the closure-theoretic orientation so that
the noninjective source precedes the injective target. -/
noncomputable def sMixedBoundaryPairEquivSIrreducibleBoundaryPair :
    σ.sClosure.MixedBoundaryPair ≃ σ.SIrreducibleBoundaryPair where
  toFun p := by
    have hi : Injective (σ.obj p.1.1) :=
      (σ.sIsTopExtreme_iff_injective (K := K) p.1.1).1 p.2.1
    have hz : ¬ Injective (σ.obj p.1.2) := by
      intro hz
      exact p.2.2.1
        ((σ.sIsTopExtreme_iff_injective (K := K) p.1.2).2 hz)
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
        (σ.sClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
          (K := K) p.ne.symm hz' hi').1 hclosed⟩
  invFun p := by
    have hi : σ.sClosure.IsTopExtreme p.1.2 :=
      (σ.sIsTopExtreme_iff_injective (K := K) p.1.2).2 p.2.2.1
    have hz : ¬ σ.sClosure.IsTopExtreme p.1.1 := by
      intro hz
      exact p.2.1
        ((σ.sIsTopExtreme_iff_injective (K := K) p.1.1).1 hz)
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
        ((σ.sClosed_compl_pair_iff_hasIrreducible_of_finiteSkeleton
          (K := K) hne hz' hi').2 p.2.2.2)
    exact ⟨(p.1.2, p.1.1), hi, hz, hclosed⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

include K in
/-- The submodule mixed-boundary count is the cardinality of the categorical
`beta_s` pair type in the finite-skeleton setting. -/
theorem sMixedBoundaryCount_eq_natCard_SIrreducibleBoundaryPair :
    σ.sClosure.mixedBoundaryCount =
      Nat.card σ.SIrreducibleBoundaryPair := by
  rw [QuotientSubmoduleEquidistribution.SetClosure.mixedBoundaryCount_eq_natCard_mixedBoundaryPair]
  exact Nat.card_congr
    (σ.sMixedBoundaryPairEquivSIrreducibleBoundaryPair (K := K))

include K in
/-- Submodule cofinite-two count in terms of injective boundary points and
categorical irreducible boundary pairs. -/
theorem sCofiniteTwoCount_eq_choose_add_natCard_SIrreducibleBoundaryPair :
    σ.sClosure.cofiniteTwoCount =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.sCofiniteTwoCount_eq_choose_add_mixedBoundaryCount (K := K),
    σ.sMixedBoundaryCount_eq_natCard_SIrreducibleBoundaryPair (K := K)]

include K in
/-- Quotient-side categorical boundary formula on the chosen skeleton's
`(Nat.card ι - 2)` level. -/
theorem qLevelCount_card_sub_two_eq_choose_add_natCard_QIrreducibleBoundaryPair
    (hcard : 2 ≤ Nat.card ι) :
    σ.qClosure.levelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [← σ.qCofiniteTwoCount_eq_levelCount_card_sub_two hcard]
  exact
    σ.qCofiniteTwoCount_eq_choose_add_natCard_QIrreducibleBoundaryPair
      (K := K)

include K in
/-- Submodule-side categorical boundary formula on the chosen skeleton's
`(Nat.card ι - 2)` level. -/
theorem sLevelCount_card_sub_two_eq_choose_add_natCard_SIrreducibleBoundaryPair
    (hcard : 2 ≤ Nat.card ι) :
    σ.sClosure.levelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [← σ.sCofiniteTwoCount_eq_levelCount_card_sub_two hcard]
  exact
    σ.sCofiniteTwoCount_eq_choose_add_natCard_SIrreducibleBoundaryPair
      (K := K)

include K in
/-- The quotient-side categorical boundary formula for literal
quotient-closed additive subcategories. -/
theorem
    literalQuotientLevelCount_card_sub_two_eq_choose_add_natCard_QIrreducibleBoundaryPair
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalQuotientLevelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitProjectiveIndices.card 2 +
        Nat.card σ.QIrreducibleBoundaryPair := by
  rw [σ.literalQuotientLevelCount_eq_levelCount]
  exact
    σ.qLevelCount_card_sub_two_eq_choose_add_natCard_QIrreducibleBoundaryPair
      (K := K) hcard

include K in
/-- The submodule-side categorical boundary formula for literal
subobject-closed additive subcategories. -/
theorem
    literalSubobjectLevelCount_card_sub_two_eq_choose_add_natCard_SIrreducibleBoundaryPair
    (hcard : 2 ≤ Nat.card ι) :
    σ.literalSubobjectLevelCount (Nat.card ι - 2) =
      Nat.choose σ.topSplitInjectiveIndices.card 2 +
        Nat.card σ.SIrreducibleBoundaryPair := by
  rw [σ.literalSubobjectLevelCount_eq_levelCount]
  exact
    σ.sLevelCount_card_sub_two_eq_choose_add_natCard_SIrreducibleBoundaryPair
      (K := K) hcard

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
