import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreRank
import QuotientSubmoduleEquidistribution.RepresentationTheory.GabrielArrowBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserial
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveBoundary
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleRank

/-!
# The one-simple connected branch

This file isolates everything in the local Nakayama branch which is
already forced by the maintained finite-skeleton development.

For a finite-dimensional algebra over an algebraically closed field, a finite
complete indecomposable skeleton has no parallel `Ext¹` arrows.  If there is
only one simple object, this implies:

* the simple-label type is unique;
* the indecomposable-projective label type is unique;
* the indecomposable-injective label type is unique; and
* there is at most one indecomposable of composition length two, equivalently
  the Ext-Gabriel quiver has at most one loop.

The former one-sided route from this data to a Nakayama algebra passed through
a basic one-loop presentation.  That presentation is not needed for the
bottom-three theorem: `OneSimpleCoreSaturation` uses the no-parallel bounds on
both sides of the aligned biduality, the abstract serial-boundary theorem, and
fixed-socle chains to prove the required core saturation directly.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LocalNakayamaBranch

universe u v

section SimpleAndProjective

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι)

/-- The literal finite-skeleton formulation of “there is one simple
module”. -/
def OneSimple : Prop :=
  Nat.card σ.SimpleIndex = 1

/-- A module-category formulation of the Nakayama property: every chosen
indecomposable representative is uniserial.  Completeness and
duplicate-freeness make this independent of the chosen skeleton. -/
def IsNakayamaSkeleton : Prop :=
  ∀ i : ι, IsUniserialModule R (σ.obj i)

/-- The weaker projective-boundary formulation of the Nakayama property. -/
def IsProjectiveNakayamaSkeleton : Prop :=
  ∀ i : ι, CategoryTheory.Projective (σ.obj i) →
    IsUniserialModule R (σ.obj i)

/-- The all-indecomposable formulation implies the usual projective
formulation immediately. -/
theorem isProjectiveNakayamaSkeleton_of_isNakayamaSkeleton
    (h : IsNakayamaSkeleton σ) :
    IsProjectiveNakayamaSkeleton σ := by
  intro i _
  exact h i

/-- One simple label gives a genuine `Unique` instance, not only a numerical
cardinality equality. -/
@[reducible]
def simpleIndexUnique (h₁ : OneSimple σ) : Unique σ.SimpleIndex := by
  have h := Nat.card_eq_one_iff_unique.mp h₁
  letI : Subsingleton σ.SimpleIndex := h.1
  exact uniqueOfSubsingleton h.2.some

variable [Finite ι]

/-- The projective-top equivalence turns one simple into one
indecomposable projective. -/
@[reducible]
def projectiveIndexUnique (h₁ : OneSimple σ) :
    Unique
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex
        σ) := by
  letI : Unique σ.SimpleIndex := simpleIndexUnique σ h₁
  let e :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveIndexEquivSimpleIndex
      σ
  let defaultProjective := e.symm (default : σ.SimpleIndex)
  exact
    { default := defaultProjective
      uniq := fun p ↦ e.injective
        (Subsingleton.elim (e p) (e defaultProjective)) }

omit [Finite ι] in
/-- The actual projective rank used by the connected-core adapter equals one
exactly when the simple-label cardinality equals one. -/
theorem oneSimple_iff_projectiveRank_eq_one :
    OneSimple σ ↔
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
        σ = 1 := by
  rw [OneSimple,
    ← QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ncard_projectiveLabels_eq_natCard_simpleIndex]
  rfl

end SimpleAndProjective

section InjectiveBoundary

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v} [Finite ι]
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι)

/-- The maintained Nakayama boundary equivalence gives one indecomposable
injective whenever there is one simple. -/
@[reducible]
def injectiveIndexUnique (h₁ : OneSimple σ) :
    Unique {i : ι // CategoryTheory.Injective (σ.obj i)} := by
  letI : Unique
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex
        σ) := projectiveIndexUnique σ h₁
  letI : Unique
      {i : ι // i ∈ QuotientSubmoduleEquidistribution.RingelStable.projectiveSet σ} := by
    change Unique
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex
        σ)
    infer_instance
  let e :=
    QuotientSubmoduleEquidistribution.RingelStable.projectiveInjectiveLabelEquiv
      (R := R) K σ
  let p₀ : {i : ι // i ∈ QuotientSubmoduleEquidistribution.RingelStable.projectiveSet σ} :=
    default
  let i₀ := e p₀
  exact
    { default := i₀
      uniq := fun i ↦ e.symm.injective
        (Subsingleton.elim (e.symm i) (e.symm i₀)) }

end InjectiveBoundary

section OneArrow

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι)

/-- Under one simple and the no-parallel bound, the multiplicity-bearing
Ext-Gabriel arrow type is a subsingleton.  Thus the unique vertex carries at
most one loop. -/
theorem extGabrielArrowIndex_subsingleton
    (h₁ : OneSimple σ)
    (hnoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport (K := K) σ) :
    Subsingleton
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex (K := K) σ) := by
  letI : Unique σ.SimpleIndex := simpleIndexUnique σ h₁
  constructor
  rintro ⟨s, t, a⟩ ⟨s', t', b⟩
  have hs : s = s' := Subsingleton.elim s s'
  subst s'
  have ht : t = t' := Subsingleton.elim t t'
  subst t'
  congr 1
  congr 1
  apply Fin.ext
  have ha := a.2
  have hb := b.2
  have hdim := (hnoParallel s t).2
  omega

variable [IsArtinianRing R]

/-- Consequently there is at most one length-two indecomposable.  The proof
uses the maintained exact equivalence between length-two representatives and
the multiplicity-bearing Ext-Gabriel arrows. -/
theorem lengthTwoIndex_subsingleton_of_noParallel
    (h₁ : OneSimple σ)
    (hnoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport (K := K) σ) :
    Subsingleton σ.LengthTwoIndex := by
  exact
    (Equiv.subsingleton_congr
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.LengthTwo.lengthTwoEquivExtGabrielArrow
        σ hnoParallel)).mpr
      (extGabrielArrowIndex_subsingleton σ h₁ hnoParallel)

variable [Finite ι]

/-- Numerical form of the one-loop conclusion. -/
theorem natCard_lengthTwoIndex_le_one_of_noParallel
    (h₁ : OneSimple σ)
    (hnoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport (K := K) σ) :
    Nat.card σ.LengthTwoIndex ≤ 1 := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Finite σ.LengthTwoIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.LengthTwoIndex := Fintype.ofFinite σ.LengthTwoIndex
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_one_iff_subsingleton.mpr
    (lengthTwoIndex_subsingleton_of_noParallel σ h₁ hnoParallel)

/-- The former one-sided classification formulation.  It remains a useful
standalone statement, but the bottom-three proof no longer depends on it: the
aligned two-sided argument in `OneSimpleCoreSaturation` proves the required
Nakayama conclusion without a quiver presentation. -/
def OneVertexAtMostOneLoopNakayamaClassification : Prop :=
  OneSimple σ →
    Subsingleton
      (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex (K := K) σ) →
    IsNakayamaSkeleton σ

omit [IsArtinianRing R] [Finite ι] in
/-- The no-parallel theorem supplies every hypothesis of the residual
classification seam. -/
theorem isNakayamaSkeleton_of_oneSimple_of_classification
    (hclassification :
      OneVertexAtMostOneLoopNakayamaClassification (K := K) σ)
    (h₁ : OneSimple σ)
    (hnoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport (K := K) σ) :
    IsNakayamaSkeleton σ := by
  exact hclassification h₁
    (extGabrielArrowIndex_subsingleton σ h₁ hnoParallel)

end OneArrow

section RightFiniteDimensional

variable (K A : Type u)
  [Field K] [IsAlgClosed K]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- Paper-scope endpoint: a one-simple finite complete right-module skeleton
has at most one length-two indecomposable. -/
theorem right_natCard_lengthTwoIndex_le_one :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    letI : IsArtinianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Aᵐᵒᵖ ι),
      OneSimple σ → Nat.card σ.LengthTwoIndex ≤ 1 := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsArtinianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
  intro ι _ σ h₁
  exact natCard_lengthTwoIndex_le_one_of_noParallel σ h₁
    (QuotientSubmoduleEquidistribution.GabrielArrowBridge.RightModules.noParallelExtSupport_of_finiteDimensional_of_finiteSkeleton
      K A σ)

/-- The same endpoint in the projective-rank language used by
`ConnectedSmallCore.ClassificationData`. -/
theorem right_natCard_lengthTwoIndex_le_one_of_projectiveRank_eq_one :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    letI : IsArtinianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
    ∀ {ι : Type u} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, u, u} Aᵐᵒᵖ ι),
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.projectiveRank
          σ = 1 →
        Nat.card σ.LengthTwoIndex ≤ 1 := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsArtinianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
  intro ι _ σ hproj
  apply right_natCard_lengthTwoIndex_le_one K A σ
  exact (oneSimple_iff_projectiveRank_eq_one σ).2 hproj

end RightFiniteDimensional

end QuotientSubmoduleEquidistribution.LocalNakayamaBranch
