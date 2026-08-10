import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreRank
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleRank

/-!
# The exceptional rank-two, core-three reduction

For an arbitrary finite indecomposable skeleton, Ringel core-cardinality,
projective rank two, and quotient-core cardinality three force the actual
torsionless core to consist of the two projective labels and one uniquely
determined nonprojective label.  This is the general counting reduction used
in the exceptional branch of the bottom-level argument.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The labels of indecomposable torsionless modules which are not
projective. -/
def nonprojectiveTorsionlessLabels : Set ι :=
  (submoduleCore σ : Set ι) \ projectiveLabels σ

omit [Finite ι] in
/-- Ringel's equality transports quotient-core cardinality three to the
actual torsionless core. -/
theorem submoduleCore_ncard_eq_three
    (hRingel : RingelCoreCardinality σ)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    (submoduleCore σ : Set ι).ncard = 3 := by
  calc
    (submoduleCore σ : Set ι).ncard =
        (quotientCore σ : Set ι).ncard := by
      simpa [RingelCoreCardinality] using hRingel.symm
    _ = 3 := hCore

omit [Finite ι] in
/-- Projective rank two means that the chosen simple labels have cardinality
two. -/
theorem natCard_simpleIndex_eq_two
    (hRank : projectiveRank σ = 2) :
    Nat.card σ.SimpleIndex = 2 := by
  calc
    Nat.card σ.SimpleIndex = (projectiveLabels σ).ncard :=
      (ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex σ).symm
    _ = projectiveRank σ := rfl
    _ = 2 := hRank

/-- Projective rank two identifies the chosen simple labels with `Fin 2`. -/
noncomputable def simpleIndexEquivFinTwo
    (hRank : projectiveRank σ = 2) :
    σ.SimpleIndex ≃ Fin 2 := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Finite.equivFinOfCardEq (natCard_simpleIndex_eq_two σ hRank)

/-- Exactly one label in the actual torsionless core is not projective. -/
theorem ncard_nonprojectiveTorsionlessLabels_eq_one
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    (nonprojectiveTorsionlessLabels σ).ncard = 1 := by
  have hSubset := projectiveLabels_subset_submoduleCore σ
  have hSum := Set.ncard_sdiff_add_ncard_of_subset hSubset
  have hProjective : (projectiveLabels σ).ncard = 2 := by
    simpa [projectiveRank] using hRank
  have hSubmodule : (submoduleCore σ : Set ι).ncard = 3 :=
    submoduleCore_ncard_eq_three σ hRingel hCore
  change
    ((submoduleCore σ : Set ι) \ projectiveLabels σ).ncard = 1
  omega

/-- There is a unique nonprojective label in the actual torsionless core. -/
theorem existsUnique_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    ∃! T : ι,
      T ∈ (submoduleCore σ : Set ι) ∧
        ¬ CategoryTheory.Projective (σ.obj T) := by
  have hCard :=
    ncard_nonprojectiveTorsionlessLabels_eq_one σ hRingel hRank hCore
  obtain ⟨T, hSingleton⟩ := Set.ncard_eq_one.mp hCard
  have hT : T ∈ (submoduleCore σ : Set ι) \ projectiveLabels σ := by
    rw [← nonprojectiveTorsionlessLabels, hSingleton]
    exact Set.mem_singleton T
  refine ⟨T, ⟨hT.1, ?_⟩, ?_⟩
  · simpa [projectiveLabels] using hT.2
  · intro U hU
    have hUDiff :
        U ∈ (submoduleCore σ : Set ι) \ projectiveLabels σ :=
      ⟨hU.1, by simpa [projectiveLabels] using hU.2⟩
    rw [← nonprojectiveTorsionlessLabels, hSingleton] at hUDiff
    exact Set.mem_singleton_iff.mp hUDiff

/-- Source-language form of the exceptional-label theorem: there is a
unique chosen indecomposable which embeds into a finite power of the basic
projective generator but is not projective. -/
theorem existsUnique_nonprojective_torsionlessLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    ∃! T : ι,
      IndecomposableSkeleton.InSubOfModule
          (projectiveGenerator σ) (σ.obj T) ∧
        ¬ CategoryTheory.Projective (σ.obj T) := by
  simpa only [mem_submoduleCore_iff_inSubOfModule] using
    existsUnique_exceptionalLabel σ hRingel hRank hCore

/-- The unique nonprojective torsionless-core label in the exceptional
rank-two, core-three branch. -/
noncomputable def exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) : ι :=
  Classical.choose (existsUnique_exceptionalLabel σ hRingel hRank hCore).exists

/-- The exceptional label belongs to the actual torsionless core. -/
theorem exceptionalLabel_mem_submoduleCore
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    exceptionalLabel σ hRingel hRank hCore ∈
      (submoduleCore σ : Set ι) :=
  (Classical.choose_spec
    (existsUnique_exceptionalLabel σ hRingel hRank hCore).exists).1

/-- The exceptional label is not projective. -/
theorem exceptionalLabel_nonprojective
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    ¬ CategoryTheory.Projective
      (σ.obj (exceptionalLabel σ hRingel hRank hCore)) :=
  (Classical.choose_spec
    (existsUnique_exceptionalLabel σ hRingel hRank hCore).exists).2

/-- Membership normal form for the exceptional torsionless core: a label is
in the core exactly when it is projective or it is the exceptional label. -/
theorem mem_submoduleCore_iff_projective_or_eq_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (i : ι) :
    i ∈ (submoduleCore σ : Set ι) ↔
      CategoryTheory.Projective (σ.obj i) ∨
        i = exceptionalLabel σ hRingel hRank hCore := by
  constructor
  · intro hi
    by_cases hProjective : CategoryTheory.Projective (σ.obj i)
    · exact Or.inl hProjective
    · exact Or.inr <|
        (existsUnique_exceptionalLabel σ hRingel hRank hCore).unique
          ⟨hi, hProjective⟩
          ⟨exceptionalLabel_mem_submoduleCore σ hRingel hRank hCore,
            exceptionalLabel_nonprojective σ hRingel hRank hCore⟩
  · rintro (hProjective | rfl)
    · exact projectiveLabels_subset_submoduleCore σ hProjective
    · exact exceptionalLabel_mem_submoduleCore σ hRingel hRank hCore

/-- Source-language exhaustive form: an indecomposable embeds into a finite
power of the basic projective generator exactly when it is projective or is
the exceptional label. -/
theorem inSubOfProjectiveGenerator_iff_projective_or_eq_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (i : ι) :
    IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator σ) (σ.obj i) ↔
      CategoryTheory.Projective (σ.obj i) ∨
        i = exceptionalLabel σ hRingel hRank hCore :=
  (mem_submoduleCore_iff_inSubOfModule σ i).symm.trans
    (mem_submoduleCore_iff_projective_or_eq_exceptionalLabel
      σ hRingel hRank hCore i)

/-- The complete general output of the rank-two, core-three counting
reduction, packaged for the subsequent structural classification. -/
structure TwoSimpleCoreThreeReduction where
  simpleEquiv : σ.SimpleIndex ≃ Fin 2
  exceptional : ι
  exceptional_torsionless :
    exceptional ∈ (submoduleCore σ : Set ι)
  exceptional_not_projective :
    ¬ CategoryTheory.Projective (σ.obj exceptional)
  core_exhaustive (i : ι) :
    i ∈ (submoduleCore σ : Set ι) ↔
      CategoryTheory.Projective (σ.obj i) ∨ i = exceptional

/-- Assemble the complete rank-two, core-three reduction. -/
noncomputable def twoSimpleCoreThreeReduction
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3) :
    TwoSimpleCoreThreeReduction σ where
  simpleEquiv := simpleIndexEquivFinTwo σ hRank
  exceptional := exceptionalLabel σ hRingel hRank hCore
  exceptional_torsionless :=
    exceptionalLabel_mem_submoduleCore σ hRingel hRank hCore
  exceptional_not_projective :=
    exceptionalLabel_nonprojective σ hRingel hRank hCore
  core_exhaustive :=
    mem_submoduleCore_iff_projective_or_eq_exceptionalLabel
      σ hRingel hRank hCore

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
