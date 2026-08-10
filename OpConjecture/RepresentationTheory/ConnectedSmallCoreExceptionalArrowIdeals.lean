import OpConjecture.RepresentationTheory.BottomTwoModules
import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalObjects
import OpConjecture.RepresentationTheory.ConnectedSmallCoreHereditary
import OpConjecture.RepresentationTheory.CyclicRightIdeal
import OpConjecture.RepresentationTheory.FamilyFourControl
import OpConjecture.RepresentationTheory.ProjectiveSimpleRecognition

/-!
# Exceptional cyclic-arrow-ideal reduction

This file isolates the exact use interface required from a future
split-basic Gabriel-presentation theorem.  Given arrow ideals with their
source-projective embeddings and target simple tops, the exceptional
rank-two/core-three reduction proves that every arrow ideal is the target
projective or the unique exceptional torsionless module.  It also proves
that a loop ideal is exceptional and that loops cannot occur at two distinct
simple vertices.

No claim that abstract Ext-Gabriel arrows have already been realized by
algebra elements is made here.
-/

noncomputable section

open Set CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v w

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace CyclicRightIdeal

variable {A : Type u} [Ring A] [IsNoetherianRing Aᵐᵒᵖ]
  {κ : Type v} [Finite κ]
  (τ : IndecomposableSkeleton.{u, v, u} Aᵐᵒᵖ κ)

omit [Finite κ] in
/-- A cyclic right ideal with simple top is indecomposable.  This is the
object-level step needed before applying skeleton completeness. -/
theorem indecomposable_of_top_iso
    (a : A) (j : τ.SimpleIndex)
    (eTop :
      FGModuleCat.of Aᵐᵒᵖ
          (OpConjecture.Tsukamoto.cyclicRightIdealFG a ⧸
            Module.jacobson Aᵐᵒᵖ
              (OpConjecture.Tsukamoto.cyclicRightIdealFG a)) ≅
        τ.obj j.1) :
    OpConjecture.Foundation.IsIndecomposableModule Aᵐᵒᵖ
      (OpConjecture.Tsukamoto.cyclicRightIdealFG a) := by
  have hTarget : IsSimpleModule Aᵐᵒᵖ (τ.obj j.1) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp j.2
  have hTop :
      IsSimpleModule Aᵐᵒᵖ
        (OpConjecture.Tsukamoto.cyclicRightIdealFG a ⧸
          Module.jacobson Aᵐᵒᵖ
            (OpConjecture.Tsukamoto.cyclicRightIdealFG a)) :=
    (FGModuleCat.isoToLinearEquiv eTop).isSimpleModule_iff.mpr hTarget
  exact OpConjecture.FamilyFourControl.isIndecomposableModule_of_simple_top
    hTop

/-- A concrete cyclic right ideal lies in `Sub(projectives)` of every finite
complete skeleton, since it embeds in the regular projective module. -/
theorem inSubOfProjectiveGenerator (a : A) :
    IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator τ)
      (OpConjecture.Tsukamoto.cyclicRightIdealFG a) :=
  (torsionless_iff_inSubOfModule_projectiveGenerator τ
    (OpConjecture.Tsukamoto.cyclicRightIdealFG a)).1
      (OpConjecture.Tsukamoto.cyclicRightIdeal_torsionless a)

/-- Concrete arrow-ideal conclusion, conditional only on the missing
Gabriel endpoint/top theorem: if the cyclic ideal `aA` has chosen simple top
`j`, then it is the target projective `P_j` or the unique exceptional
torsionless module. -/
theorem iso_targetProjective_or_exceptional_of_top_iso
    (hRingel : RingelCoreCardinality τ)
    (hRank : projectiveRank τ = 2)
    (hCore : (quotientCore τ : Set κ).ncard = 3)
    (a : A) (j : τ.SimpleIndex)
    (eTop :
      FGModuleCat.of Aᵐᵒᵖ
          (OpConjecture.Tsukamoto.cyclicRightIdealFG a ⧸
            Module.jacobson Aᵐᵒᵖ
              (OpConjecture.Tsukamoto.cyclicRightIdealFG a)) ≅
        τ.obj j.1) :
    Nonempty
        (OpConjecture.Tsukamoto.cyclicRightIdealFG a ≅
          τ.obj (projectiveLabelOfSimple τ j)) ∨
      Nonempty
        (OpConjecture.Tsukamoto.cyclicRightIdealFG a ≅
          τ.obj (exceptionalLabel τ hRingel hRank hCore)) := by
  have hIndecomposable := indecomposable_of_top_iso τ a j eTop
  rcases
      projective_or_nonempty_iso_exceptionalLabel_of_inSubOfProjectiveGenerator
        τ hRingel hRank hCore
        (OpConjecture.Tsukamoto.cyclicRightIdealFG a)
        hIndecomposable (inSubOfProjectiveGenerator τ a) with
    hProjective | hExceptional
  · exact Or.inl <|
      projective_iso_of_indec_of_top_iso τ
        (OpConjecture.Tsukamoto.cyclicRightIdealFG a)
        hProjective hIndecomposable j eTop
  · exact Or.inr hExceptional

end CyclicRightIdeal

/-- The exact module-theoretic data used from a realization of Gabriel
arrows as cyclic ideals.  Each ideal is already represented by a skeleton
label; a future constructor must obtain that label by proving that the
concrete cyclic ideal has simple top and hence is indecomposable. -/
structure ExceptionalArrowIdealData
    {Arrow : Type w}
    (source target : Arrow → σ.SimpleIndex) where
  idealLabel : Arrow → ι
  topIso : ∀ a,
    Nonempty
      (FGModuleCat.of R (σ.moduleTop (idealLabel a)) ≅
        σ.obj (target a).1)
  inclusion : ∀ a,
    σ.obj (idealLabel a) ⟶
      σ.obj (projectiveLabelOfSimple σ (source a))
  inclusion_mono : ∀ a, Mono (inclusion a)
  /-- Every concrete Gabriel-arrow ideal is a proper submodule of its source
  projective.  A future realization theorem obtains this from the fact that
  an arrow representative lies in the Jacobson radical. -/
  inclusion_not_epi : ∀ a, ¬ Epi (inclusion a)

namespace ExceptionalArrowIdealData

variable {Arrow : Type w}
  {source target : Arrow → σ.SimpleIndex}
  (D : ExceptionalArrowIdealData σ source target)

/-- Every represented cyclic arrow ideal embeds into a finite power of the
basic projective generator. -/
theorem idealLabel_inSubOfProjectiveGenerator (a : Arrow) :
    IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator σ) (σ.obj (D.idealLabel a)) := by
  have hProjective :
      CategoryTheory.Projective
        (σ.obj (projectiveLabelOfSimple σ (source a))) :=
    projective_projectiveLabelOfSimple σ (source a)
  obtain ⟨J, p, hp⟩ :=
    inSubOfModule_projectiveGenerator_of_projective σ
      (σ.obj (projectiveLabelOfSimple σ (source a))) hProjective
  letI : Mono p := hp
  letI : Mono (D.inclusion a) := D.inclusion_mono a
  exact ⟨J, D.inclusion a ≫ p, inferInstance⟩

/-- Therefore every represented arrow ideal lies in the actual torsionless
core. -/
theorem idealLabel_mem_submoduleCore (a : Arrow) :
    D.idealLabel a ∈ (submoduleCore σ : Set ι) :=
  (mem_submoduleCore_iff_inSubOfModule σ (D.idealLabel a)).2
    (idealLabel_inSubOfProjectiveGenerator σ D a)

/-- The first exceptional dichotomy: an arrow ideal is projective or its
label is the unique nonprojective torsionless label. -/
theorem projective_or_idealLabel_eq_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (a : Arrow) :
    CategoryTheory.Projective (σ.obj (D.idealLabel a)) ∨
      D.idealLabel a = exceptionalLabel σ hRingel hRank hCore :=
      (mem_submoduleCore_iff_projective_or_eq_exceptionalLabel
    σ hRingel hRank hCore (D.idealLabel a)).1
      (idealLabel_mem_submoduleCore σ D a)

/-- Exact form of the manuscript's arrow-ideal dichotomy: the cyclic ideal
of an arrow with target `j` is the chosen projective `P_j` or the unique
exceptional torsionless module. -/
theorem idealLabel_eq_targetProjective_or_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (a : Arrow) :
    D.idealLabel a = projectiveLabelOfSimple σ (target a) ∨
      D.idealLabel a = exceptionalLabel σ hRingel hRank hCore := by
  rcases
      projective_or_idealLabel_eq_exceptionalLabel σ D
        hRingel hRank hCore a with
    hProjective | hExceptional
  · left
    obtain ⟨eTop⟩ := D.topIso a
    exact σ.eq_of_iso <|
      projective_iso_of_indec_of_top_iso σ
        (σ.obj (D.idealLabel a)) hProjective
        (σ.indecomposable (D.idealLabel a)) (target a) eTop
  · exact Or.inr hExceptional

/-- Object-isomorphism form of the arrow-ideal dichotomy. -/
theorem idealModule_iso_targetProjective_or_exceptional
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (a : Arrow) :
    Nonempty
        (σ.obj (D.idealLabel a) ≅
          σ.obj (projectiveLabelOfSimple σ (target a))) ∨
      Nonempty
        (σ.obj (D.idealLabel a) ≅
          σ.obj (exceptionalLabel σ hRingel hRank hCore)) := by
  rcases
      idealLabel_eq_targetProjective_or_exceptionalLabel σ D
        hRingel hRank hCore a with
    hProjective | hExceptional
  · exact Or.inl ⟨eqToIso (congrArg σ.obj hProjective)⟩
  · exact Or.inr ⟨eqToIso (congrArg σ.obj hExceptional)⟩

/-- A loop ideal cannot be projective: otherwise its simple top identifies
it with the source projective, and its monic inclusion between equal-length
representatives would be an isomorphism and hence epic. -/
theorem loop_idealLabel_eq_exceptionalLabel
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (a : Arrow) (hLoop : source a = target a) :
    D.idealLabel a = exceptionalLabel σ hRingel hRank hCore := by
  rcases
      projective_or_idealLabel_eq_exceptionalLabel σ D
        hRingel hRank hCore a with
    hProjective | hExceptional
  · exfalso
    obtain ⟨eTop⟩ := D.topIso a
    have hTarget :
        D.idealLabel a = projectiveLabelOfSimple σ (target a) :=
      σ.eq_of_iso <|
        projective_iso_of_indec_of_top_iso σ
          (σ.obj (D.idealLabel a)) hProjective
          (σ.indecomposable (D.idealLabel a)) (target a) eTop
    have hSource :
        D.idealLabel a = projectiveLabelOfSimple σ (source a) :=
      hTarget.trans
        (congrArg (projectiveLabelOfSimple σ) hLoop.symm)
    letI : Mono (D.inclusion a) := D.inclusion_mono a
    letI : IsIso (D.inclusion a) :=
      σ.isIso_of_mono_of_compositionLength_eq (D.inclusion a)
        (congrArg σ.compositionLength hSource)
    exact (D.inclusion_not_epi a) inferInstance
  · exact hExceptional

/-- Object-isomorphism form: every loop ideal is the exceptional module. -/
theorem loop_idealModule_iso_exceptional
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (a : Arrow) (hLoop : source a = target a) :
    Nonempty
      (σ.obj (D.idealLabel a) ≅
        σ.obj (exceptionalLabel σ hRingel hRank hCore)) :=
  ⟨eqToIso <| congrArg σ.obj <|
    loop_idealLabel_eq_exceptionalLabel σ D
      hRingel hRank hCore a hLoop⟩

include D in
/-- Loops cannot occur at two distinct simple vertices: both loop ideals are
the same exceptional representative, and their simple tops identify their
vertices. -/
theorem loop_vertices_eq
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    {a b : Arrow}
    (ha : source a = target a)
    (hb : source b = target b) :
    source a = source b := by
  have hIa :=
    loop_idealLabel_eq_exceptionalLabel σ D
      hRingel hRank hCore a ha
  have hIb :=
    loop_idealLabel_eq_exceptionalLabel σ D
      hRingel hRank hCore b hb
  obtain ⟨eA⟩ := D.topIso a
  obtain ⟨eB⟩ := D.topIso b
  have hTop : target a = target b := by
    apply Subtype.ext
    apply σ.eq_of_iso
    exact ⟨eA.symm ≪≫
      eqToIso (congrArg
        (fun i : ι ↦ FGModuleCat.of R (σ.moduleTop i))
        (hIa.trans hIb.symm)) ≪≫ eB⟩
  exact ha.trans (hTop.trans hb.symm)

end ExceptionalArrowIdealData

end OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
