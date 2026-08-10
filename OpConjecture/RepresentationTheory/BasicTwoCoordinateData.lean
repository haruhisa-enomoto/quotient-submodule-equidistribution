import OpConjecture.RepresentationTheory.BasicnessWrapper
import OpConjecture.RepresentationTheory.CoordinateSimpleAlignment
import OpConjecture.RepresentationTheory.ConnectedSmallCoreExceptionalReduction

/-!
# Two split coordinates from basicness and projective rank two

An intrinsic basic semisimple quotient first gives an unspecified finite set
of split coordinates.  Coordinate-simple exhaustion identifies that set with
the simple labels of any complete skeleton.  Thus projective rank two lets us
reindex the quotient presentation canonically up to a chosen equivalence with
`Fin 2`.
-/

noncomputable section

namespace OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData

universe u v w

variable {K B : Type u} {I : Type v} {J : Type w}
  [Field K] [Ring B] [Algebra K B]

/-- Reindex a split quotient-coordinate presentation along an equivalence. -/
def reindex
    (D : OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
      (K := K) (B := B) (I := I))
    (e : I ≃ J) :
    OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
      (K := K) (B := B) (I := J) where
  quotientEquiv :=
    D.quotientEquiv.trans
      (AlgEquiv.piCongrLeft K (fun _ : J ↦ K) e)

end OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData

namespace OpConjecture.BasicTwoCoordinateData

open OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

variable {K B : Type u} {kappa : Type v}
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B] [FiniteDimensional K B]
  [IsNoetherianRing Bᵐᵒᵖ] [Finite kappa]
  (tau : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ kappa)

/-- A basic algebra whose complete right-module skeleton has projective rank
two has a split semisimple quotient with coordinates indexed by `Fin 2`. -/
theorem exists_twoCoordinateData_of_isBasicAlgebra
    (hBasic : OpConjecture.BasicnessWrapper.IsBasicAlgebra K B)
    (hRank : projectiveRank tau = 2) :
    Nonempty
      (OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
        (K := K) (B := B) (I := Fin 2)) := by
  obtain ⟨n, ⟨D⟩⟩ :=
    OpConjecture.BasicnessWrapper.exists_quotientCoordinateData_of_isBasicAlgebra
      K B hBasic
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  let e : Fin n ≃ Fin 2 :=
    (OpConjecture.CotangentExtBridge.CoordinateData.coordinateSimpleIndexEquiv
      D tau).trans
      (simpleIndexEquivFinTwo tau hRank)
  exact
    ⟨OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData.reindex
      D e⟩

/-- A chosen two-coordinate presentation supplied by basicness and projective
rank two. -/
noncomputable def twoCoordinateDataOfIsBasicAlgebra
    (hBasic : OpConjecture.BasicnessWrapper.IsBasicAlgebra K B)
    (hRank : projectiveRank tau = 2) :
    OpConjecture.SplitBasicCoordinateSystem.QuotientCoordinateData
      (K := K) (B := B) (I := Fin 2) :=
  (exists_twoCoordinateData_of_isBasicAlgebra tau hBasic hRank).some

end OpConjecture.BasicTwoCoordinateData
