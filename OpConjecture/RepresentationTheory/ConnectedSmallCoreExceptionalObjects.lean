import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalReduction

/-!
# Object-level exceptional torsionless classification

This upgrades the chosen-label rank-two/core-three reduction to an arbitrary
indecomposable finitely generated module by skeleton completeness and
transport across an isomorphism.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- Every indecomposable finitely generated module in `Sub(projectives)` is
either projective or isomorphic to the unique exceptional representative in
the rank-two, core-three branch. -/
theorem projective_or_nonempty_iso_exceptionalLabel_of_inSubOfProjectiveGenerator
    (hRingel : RingelCoreCardinality σ)
    (hRank : projectiveRank σ = 2)
    (hCore : (quotientCore σ : Set ι).ncard = 3)
    (X : FGModuleCat.{u} R)
    (hIndecomposable : OpConjecture.Foundation.IsIndecomposableModule R X)
    (hX : IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator σ) X) :
    CategoryTheory.Projective X ∨
      Nonempty
        (X ≅ σ.obj (exceptionalLabel σ hRingel hRank hCore)) := by
  obtain ⟨i, ⟨e⟩⟩ := σ.complete X hIndecomposable
  have hiSub :
      IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator σ) (σ.obj i) := by
    obtain ⟨J, p, hp⟩ := hX
    letI : Mono p := hp
    exact ⟨J, e.inv ≫ p, inferInstance⟩
  rcases
      (inSubOfProjectiveGenerator_iff_projective_or_eq_exceptionalLabel
        σ hRingel hRank hCore i).1 hiSub with
    hiProjective | hiExceptional
  · exact Or.inl (CategoryTheory.Projective.of_iso e.symm hiProjective)
  · exact Or.inr
      ⟨e ≪≫ eqToIso (congrArg σ.obj hiExceptional)⟩

end OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
