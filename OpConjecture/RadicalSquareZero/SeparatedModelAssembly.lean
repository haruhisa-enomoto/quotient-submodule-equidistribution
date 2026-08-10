import OpConjecture.RadicalSquareZero.SeparatedFreeSimple
import OpConjecture.RadicalSquareZero.SeparatedQuiverEndpoint

/-!
# Assemble the radical-square-zero separated quotient model

Once the original and triangular separated skeletons carry their literal
nonsimple/simple labels and objectwise alignment, all closure-theoretic data
required by the paper's Boolean-factor argument is canonical.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RadicalSquareZero

open RadicalSquareZeroCombinatorics.CoreFamily.TopCoverage
open SeparatedTriangularAlgebra

universe u v w x y

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]
variable [IsNoetherianRing (TrivSqZeroExt S J)]
variable [IsNoetherianRing (Algebra S J)]
variable {Nonsimple : Type x} {Vertex : Type y}
  [Fintype Nonsimple] [DecidableEq Nonsimple]
  [Fintype Vertex] [DecidableEq Vertex]
variable
  {sigma : IndecomposableSkeleton.{max u v, max x y, w}
    (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)}

namespace OriginalNonsimpleLabelData

/-- The exact separated quotient model obtained from actual labeled
skeletons and their objectwise separated-data alignment. -/
noncomputable def toSeparatedQuotientModel
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (tau : IndecomposableSkeleton.{max u v, max x y, w}
      (Algebra S J) (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (E : SeparatedSimpleLabelData tau)
    (G : SeparatedNonsimpleFreeData tau)
    (A : SeparatedCoreAlignment sigma tau G) :
    SeparatedQuotientModel sigma tau Vertex
      (AdmissibleCore (Generates (sigma := sigma)))
      Nonsimple Nonsimple := by
  let P : PairedClosureMembership sigma.qClosure tau.qClosure :=
    { Generates := Generates (sigma := sigma)
      forcedTop := forcedTop (sigma := sigma)
      a_nonsimple_mem := fun T z ↦ D.nonsimple_mem_qClosure_iff T z
      a_simple_mem := fun T v ↦ D.simple_mem_qClosure_iff T v
      b_nonsimple_mem := fun T z ↦
        (E.nonsimple_mem_qClosure_iff T z).trans
          (A.b_nonsimple_core (bNonsimplePart T) z)
      b_covered_simple_mem := fun T v ↦
        (E.covered_simple_mem_qClosure_iff T v).trans <| by
          rw [A.b_covered_core (bNonsimplePart T) v]
      b_free_simple_mem := fun T v ↦
        (E.free_simple_mem_qClosure_iff T v).trans <| by
          simp [G.free_not_mem_qClosure_nonsimpleSupport
            (bNonsimplePart T) v] }
  exact
    { originalLabels := Equiv.refl _
      separatedLabels := Equiv.refl _
      coreFamily := P.coreFamily
      originalTopCoverage := by
        simpa using P.toATopCoverageData
      separatedTopCoverage := by
        simpa using P.toBTopCoverageData }

omit [DecidableEq Nonsimple] in
/-- Paper's Boolean-factor identity for a labeled and aligned separated
realization. -/
theorem separatedLevelPolynomial_eq_original_mul_of_alignment
    (D : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (tau : IndecomposableSkeleton.{max u v, max x y, w}
      (Algebra S J) (Nonsimple ⊕ (Vertex ⊕ Vertex)))
    (E : SeparatedSimpleLabelData tau)
    (G : SeparatedNonsimpleFreeData tau)
    (A : SeparatedCoreAlignment sigma tau G) :
    tau.qClosure.levelPolynomial =
      sigma.qClosure.levelPolynomial *
        (1 + Polynomial.X) ^ Fintype.card Vertex :=
  (D.toSeparatedQuotientModel tau E G A).separatedLevelPolynomial_eq_original_mul

end OriginalNonsimpleLabelData

end OpConjecture.RadicalSquareZero
