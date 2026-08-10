import OpConjecture.RepresentationTheory.AlmostSplitDuality
import OpConjecture.RepresentationTheory.ContragredientDuality
import OpConjecture.RepresentationTheory.FiniteDimensionalAlmostSplit
import OpConjecture.RepresentationTheory.LocalARCofiniteTwoFormula

/-!
# Two-sided almost-split data over finite-dimensional algebras

Contragredient duality transports the right almost-split construction over
the opposite algebra to a left almost-split construction.  Combining both
sides supplies the local Auslander--Reiten data needed by the cofinite-two
formulas on an arbitrary complete indecomposable skeleton.

No finite-skeleton, representation-finiteness, concrete algebra, or module
classification hypothesis is used.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u uIota

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

include K in
/-- Every noninjective chosen indecomposable over a finite-dimensional
algebra admits a left almost-split morphism. -/
theorem exists_leftAlmostSplit_of_finiteDimensional
    (x : Iota) (hx : ¬ Injective (sigma.obj x)) :
    ∃ (E : FGModuleCat.{u} R) (f : sigma.obj x ⟶ E),
      IsLeftAlmostSplit f := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  let tau := indecomposableSkeletonOfFiniteLength
    (R := Rᵐᵒᵖ)
    (fgModule_isFiniteLength_of_finiteDimensional K Rᵐᵒᵖ)
  let y := OpConjecture.Contragredient.dualMapLabel
    K R sigma tau x
  have hy : ¬ Projective (tau.obj y) := by
    intro hprojective
    apply hx
    have hdual : Projective
        ((OpConjecture.Contragredient.dualFunctor K R).obj
          (Opposite.op (sigma.obj x))) :=
      Projective.of_iso
        (OpConjecture.Contragredient.dualMapObjIso
          K R sigma tau x).symm hprojective
    have hop : Projective (Opposite.op (sigma.obj x)) :=
      ((OpConjecture.Contragredient.dualityEquivalence K R).map_projective_iff
        (Opposite.op (sigma.obj x))).mp hdual
    exact Injective.injective_iff_projective_op.mpr hop
  obtain ⟨E, q, hq⟩ :=
    tau.exists_rightAlmostSplit_of_finiteDimensional K Rᵐᵒᵖ y hy
  let D := OpConjecture.Contragredient.reverseDualityEquivalence K R
  have hdual : IsLeftAlmostSplit (D.functor.map q.op) :=
    hq.map_op_equivalence D
  have hyx :
      OpConjecture.Contragredient.reverseMapLabel
          K R sigma tau y = x := by
    exact OpConjecture.Contragredient.reverseMapLabel_dualMapLabel
      K R sigma tau x
  let sourceIso : sigma.obj x ≅
      D.functor.obj (Opposite.op (tau.obj y)) :=
    eqToIso (congrArg sigma.obj hyx.symm) ≪≫
      (OpConjecture.Contragredient.reverseMapObjIso
        K R sigma tau y).symm
  exact ⟨D.functor.obj (Opposite.op E),
    sourceIso.hom ≫ D.functor.map q.op,
    hdual.precomp_iso sourceIso⟩

include K in
/-- The duality construction has a finite-length middle term. -/
theorem exists_finiteLength_leftAlmostSplit_of_finiteDimensional_of_not_injective
    (x : Iota) (hx : ¬ Injective (sigma.obj x)) :
    ∃ (E : FGModuleCat.{u} R) (f : sigma.obj x ⟶ E),
      IsFiniteLength R E ∧ IsLeftAlmostSplit f := by
  obtain ⟨E, f, hf⟩ :=
    sigma.exists_leftAlmostSplit_of_finiteDimensional K R x hx
  exact ⟨E, f, fgModule_isFiniteLength_of_finiteDimensional K R E, hf⟩

include K in
/-- Every noninjective chosen indecomposable has a minimal left
almost-split decomposition, without a finite-skeleton hypothesis. -/
theorem minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_injective
    (x : Iota) (hx : ¬ Injective (sigma.obj x)) :
    Nonempty (sigma.MinimalLeftAlmostSplitDecomposition x) := by
  obtain ⟨E, f, hE, hf⟩ :=
    sigma.exists_finiteLength_leftAlmostSplit_of_finiteDimensional_of_not_injective
      K R x hx
  exact
    MinimalLeftAlmostSplitDecomposition.exists_of_leftAlmostSplit_of_finiteLength
      sigma f hf hE

include K in
/-- The finite-dimensional field hypotheses supply both local minimal
almost-split families and the projective--injective boundary equivalence. -/
def finiteDimensionalTwoSidedLocalARData :
    sigma.TwoSidedLocalARData := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  exact TwoSidedLocalARData.ofArtinDuality sigma
    (OpConjecture.ArtinDuality.ofFiniteDimensional K)
    (fun z ↦
      sigma.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_projective
        K R z.1 z.2)
    (fun z ↦
      sigma.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_injective
        K R z.1 z.2)

include K in
/-- The two cofinite-two deletion sets are finite over every
finite-dimensional field algebra, without representation-finiteness. -/
theorem finiteDimensional_cofiniteTwoDeletionSets_finite :
    sigma.qClosure.cofiniteTwoDeletionSet.Finite ∧
      sigma.sClosure.cofiniteTwoDeletionSet.Finite := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  exact sigma.moduleFiniteArtin_cofiniteTwoDeletionSets_finite
    (k := K) (OpConjecture.ArtinDuality.ofFiniteDimensional K)
    (fun z ↦
      sigma.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_projective
        K R z.1 z.2)
    (fun z ↦
      sigma.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_injective
        K R z.1 z.2)

include K in
/-- Finite-dimensional-field specialization of the manuscript's two exact
cofinite-two formulas on a possibly infinite indecomposable skeleton. -/
theorem finiteDimensional_literalRadicalQuotientCofiniteTwo_formulas :
    sigma.qClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card sigma.SimpleIndex) 2 +
          Nat.card sigma.QRadicalQuotientBoundaryPair ∧
      sigma.sClosure.cofiniteTwoDeletionSet.ncard =
        Nat.choose (Nat.card sigma.SimpleIndex) 2 +
          Nat.card sigma.SRadicalQuotientBoundaryPair := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  exact sigma.moduleFiniteArtin_literalRadicalQuotientCofiniteTwo_formulas
    (k := K) (OpConjecture.ArtinDuality.ofFiniteDimensional K)
    (fun z ↦
      sigma.minimalRightAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_projective
        K R z.1 z.2)
    (fun z ↦
      sigma.minimalLeftAlmostSplitDecomposition_nonempty_of_finiteDimensional_of_not_injective
        K R z.1 z.2)

end OpConjecture.IndecomposableSkeleton
