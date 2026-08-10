import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreExceptionalObjects
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreAssembly

/-!
# Algebra-node interface for the exceptional small-core reduction

This downstream wrapper supplies Ringel core-cardinality from the maintained
`RingelEta` equivalence.  Its only numerical inputs are the general
connected-small-core hypotheses `projectiveCount K B = 2` and
`coreSize K B = 3`.
-/

noncomputable section

open Set CategoryTheory

namespace QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode

universe u

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

variable {K : Type u} [Field K]

/-- The general rank-two, core-three reduction at a finite-dimensional
algebra node. -/
noncomputable def twoSimpleCoreThreeReduction
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    TwoSimpleCoreThreeReduction B.skeleton :=
  ConnectedSmallCore.twoSimpleCoreThreeReduction B.skeleton
    (QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
      B.skeleton K)
    hProjective
    (by
      simpa [coreSize, quotientCoreData, concreteQuotientCoreData] using hCore)

/-- At a finite-dimensional algebra node in the exceptional numerical
branch, there is a unique nonprojective label in the actual torsionless
core. -/
theorem existsUnique_exceptionalCoreLabel
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    ∃! T : B.Index,
      T ∈ (submoduleCore B.skeleton : Set B.Index) ∧
        ¬ CategoryTheory.Projective (B.skeleton.obj T) := by
  apply existsUnique_exceptionalLabel B.skeleton
  · exact
      QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        B.skeleton K
  · exact hProjective
  · simpa [coreSize, quotientCoreData, concreteQuotientCoreData] using hCore

/-- Source-language node form: there is a unique chosen indecomposable which
embeds into a finite power of the basic projective generator and is not
projective. -/
theorem existsUnique_nonprojectiveTorsionlessLabel
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    ∃! T : B.Index,
      IndecomposableSkeleton.InSubOfModule
          (projectiveGenerator B.skeleton) (B.skeleton.obj T) ∧
        ¬ CategoryTheory.Projective (B.skeleton.obj T) := by
  apply existsUnique_nonprojective_torsionlessLabel B.skeleton
  · exact
      QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.ringelCoreCardinality_of_ringelEtaStableEquivalence
        B.skeleton K
  · exact hProjective
  · simpa [coreSize, quotientCoreData, concreteQuotientCoreData] using hCore

/-- The node-level exceptional label, with Ringel's theorem compiled into
the definition. -/
noncomputable def exceptionalCoreLabel
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) : B.Index :=
  (twoSimpleCoreThreeReduction B hProjective hCore).exceptional

/-- The node-level exceptional label lies in the actual torsionless core
and is not projective. -/
theorem exceptionalCoreLabel_spec
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3) :
    exceptionalCoreLabel B hProjective hCore ∈
        (submoduleCore B.skeleton : Set B.Index) ∧
      ¬ CategoryTheory.Projective
        (B.skeleton.obj (exceptionalCoreLabel B hProjective hCore)) :=
  ⟨(twoSimpleCoreThreeReduction B hProjective hCore).exceptional_torsionless,
    (twoSimpleCoreThreeReduction B hProjective hCore).exceptional_not_projective⟩

/-- Node-level membership normal form for the actual torsionless core. -/
theorem mem_submoduleCore_iff_projective_or_eq_exceptionalCoreLabel
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3)
    (i : B.Index) :
    i ∈ (submoduleCore B.skeleton : Set B.Index) ↔
      CategoryTheory.Projective (B.skeleton.obj i) ∨
        i = exceptionalCoreLabel B hProjective hCore :=
  (twoSimpleCoreThreeReduction B hProjective hCore).core_exhaustive i

/-- Source-language node-level membership normal form. -/
theorem inSubOfProjectiveGenerator_iff_projective_or_eq_exceptionalCoreLabel
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3)
    (i : B.Index) :
    IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator B.skeleton) (B.skeleton.obj i) ↔
      CategoryTheory.Projective (B.skeleton.obj i) ∨
        i = exceptionalCoreLabel B hProjective hCore :=
  (mem_submoduleCore_iff_inSubOfModule B.skeleton i).symm.trans
    (mem_submoduleCore_iff_projective_or_eq_exceptionalCoreLabel
      B hProjective hCore i)

/-- Every indecomposable finitely generated module in the node's torsionless
class is projective or isomorphic to its unique exceptional representative. -/
theorem projective_or_nonempty_iso_exceptionalCoreLabel_of_inSubOfProjectiveGenerator
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2)
    (hCore : coreSize K B = 3)
    (X : FGModuleCat.{u} B.Carrier)
    (hIndecomposable : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule B.Carrier X)
    (hX : IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator B.skeleton) X) :
    CategoryTheory.Projective X ∨
      Nonempty (X ≅ B.skeleton.obj
        (exceptionalCoreLabel B hProjective hCore)) := by
  obtain ⟨i, ⟨e⟩⟩ := B.skeleton.complete X hIndecomposable
  have hiSub :
      IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator B.skeleton) (B.skeleton.obj i) := by
    obtain ⟨J, p, hp⟩ := hX
    letI : Mono p := hp
    exact ⟨J, e.inv ≫ p, inferInstance⟩
  rcases
      (inSubOfProjectiveGenerator_iff_projective_or_eq_exceptionalCoreLabel
        B hProjective hCore i).1 hiSub with
    hiProjective | hiExceptional
  · exact Or.inl (CategoryTheory.Projective.of_iso e.symm hiProjective)
  · exact Or.inr
      ⟨e ≪≫ eqToIso (congrArg B.skeleton.obj hiExceptional)⟩

/-- The node's chosen simple labels are exactly a two-element type in the
exceptional numerical branch. -/
noncomputable def simpleIndexEquivFinTwo
    (B : AlgebraNode K)
    (hProjective : projectiveCount K B = 2) :
    B.skeleton.SimpleIndex ≃ Fin 2 :=
  ConnectedSmallCore.simpleIndexEquivFinTwo B.skeleton hProjective

end QuotientSubmoduleEquidistribution.BottomLevels.FiniteDimensionalRecurrence.AlgebraNode
