import OpConjecture.RepresentationTheory.LoopTwoCycleFamily
import OpConjecture.RepresentationTheory.ContragredientDuality

/-!
# Contragredient alignment of an infinite left-module family

This file transports the already constructed quotient family from left
modules to the paper's right-module convention.  It uses only the
maintained finite-dimensional contragredient equivalence and does not rebuild
the opposite multiplication table.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.RepresentationInfiniteCertificate

universe u v z

namespace InfiniteIndecomposableFamily

/-- Contragredient duality turns an infinite family of left `B`-modules into
an infinite family of right `B`-modules, preserving both indecomposability
and parameter separation. -/
def contragredient
    {K B : Type u} [Field K] [Ring B] [Algebra K B]
    [FiniteDimensional K B]
    {Parameter : Type z}
    (F : InfiniteIndecomposableFamily (R := B) Parameter) :
    InfiniteIndecomposableFamily (R := Bᵐᵒᵖ) Parameter where
  obj t :=
    (OpConjecture.Contragredient.dualFunctor K B).obj
      (Opposite.op (F.obj t))
  indecomposable t :=
    OpConjecture.Contragredient.dualFunctor_indec K B
      (F.indecomposable t)
  eq_of_iso {a b} e := by
    apply F.eq_of_iso
    let E := OpConjecture.Contragredient.dualityEquivalence K B
    let eop : Opposite.op (F.obj a) ≅ Opposite.op (F.obj b) :=
      E.functor.preimageIso e.some
    exact ⟨(Iso.unop eop).symm⟩

end InfiniteIndecomposableFamily

end OpConjecture.RepresentationInfiniteCertificate

namespace OpConjecture.LoopTwoCycleFamily.SixDimensionalQuotientData

universe u v

variable {K B S : Type u}
  [Field K]
  [Ring B] [Algebra K B] [FiniteDimensional K B]
  [Ring S] [Algebra K S]

/-- Paper-facing endpoint: a six-coordinate quotient family contradicts a
finite complete skeleton of right `B`-modules.  The only extra hypothesis
needed by the maintained duality is finite-dimensionality of `B` over `K`. -/
theorem false_of_right_finite_skeleton
    [Infinite K]
    (q : B →+* S) (hq : Function.Surjective q)
    (D : OpConjecture.LoopTwoCycleFamily.SixDimensionalQuotientData K S) :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      IsNoetherianRing.of_finite K Bᵐᵒᵖ
    ∀ {ι : Type v} [Finite ι],
      OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ ι → False := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Bᵐᵒᵖ
  intro ι _ σ
  let FleftS := infiniteIndecomposableFamily D
  let FleftB := FleftS.restrictScalars q hq
  let Fright :=
    OpConjecture.RepresentationInfiniteCertificate.InfiniteIndecomposableFamily.contragredient
      (K := K) (B := B) FleftB
  exact Fright.false_of_finite_skeleton σ

end OpConjecture.LoopTwoCycleFamily.SixDimensionalQuotientData
