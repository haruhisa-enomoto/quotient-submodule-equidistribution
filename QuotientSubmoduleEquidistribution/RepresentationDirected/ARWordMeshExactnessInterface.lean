import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordMeshKnitting

/-!
# Manuscript-facing interface for finite mesh exactness

The representation-directed proof invokes Iyama's theorem in its direct
categorical form: a positive right-additive function on the finite word
translation quiver makes its representable mesh complexes exact.  The
subsequent numerical argument uses only their nonnegative Hom dimensions and
the resulting mesh recurrence.

This file records exactly that boundary and proves that it supplies the
finite-mesh hypothesis consumed by the directed-sorting development.  It
does not postulate Iyama's theorem and contains no concrete algebra, quiver
presentation, or module classification.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.MeshExactness

open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.MeshKnitting
open QuotientSubmoduleEquidistribution.RepresentationDirected.MeshKnitting.Word

universe u

variable {L : Type u}

/-- The exact numerical content of the representable mesh complexes.

`homDimension a x` models `dim M_Q(a,x)`.  Exactness of

`0 -> M_Q(-,p(x)) -> ⊕_{y in mid(x)} M_Q(-,y)
   -> M_Q(-,x) -> S_x -> 0`

is retained as its dimension recurrence.  Natural-number values expose the
categorical effectivity used to prove entrywise nonnegativity. -/
structure RepresentableMeshExactnessData
    (G : SimpleGraph L) (Q : List L) where
  homDimension : Fin Q.length → Fin Q.length → ℕ
  exact_recurrence :
    SatisfiesWordMeshInverseRecurrence G Q
      (fun a x ↦ (homDimension a x : ℤ))

/-- Any integral inverse-mesh solution is the literal Hom-dimension matrix
carried by the representable mesh-exactness data. -/
theorem recurrenceSolution_eq_homDimension
    (G : SimpleGraph L) (Q : List L)
    (E : RepresentableMeshExactnessData G Q)
    (M : Fin Q.length → Fin Q.length → ℤ)
    (hM : SatisfiesWordMeshInverseRecurrence G Q M) :
    M = fun a x ↦ (E.homDimension a x : ℤ) :=
  satisfiesWordMeshInverseRecurrence_unique
    G Q hM E.exact_recurrence

/-- Exact representable mesh complexes give the nonnegative solution of the
word mesh inverse recurrence. -/
theorem recurrenceSolution_nonnegative
    (G : SimpleGraph L) (Q : List L)
    (E : RepresentableMeshExactnessData G Q)
    (M : Fin Q.length → Fin Q.length → ℤ)
    (hM : SatisfiesWordMeshInverseRecurrence G Q M) :
    ∀ a x, 0 ≤ M a x := by
  have hEq := recurrenceSolution_eq_homDimension G Q E M hM
  intro a x
  rw [hEq]
  exact Int.natCast_nonneg (E.homDimension a x)

/-- The exact literature boundary used in the manuscript.

For a boundary-run word, a positive right-additive function is required to
produce the Hom-dimension data of exact representable mesh complexes.  The
literal quotient tau-category implementation used by the algebra endpoint is
constructed in `IyamaFactorCategoryARWord`; the abstract interface remains
useful for other word realizations. -/
def PositiveRightAdditiveHasRepresentableMeshExactness
    (G : SimpleGraph L) (Q : List L) : Prop :=
  ARWord.HasOnlyBoundaryRepeatedRuns G Q →
    (∃ lambda : Fin Q.length → ℤ,
      IsPositiveRightAdditive G Q lambda) →
      Nonempty (RepresentableMeshExactnessData G Q)

/-- The manuscript-facing exactness interface discharges the finite-mesh
hypothesis used by directed sorting. -/
theorem positiveRightAdditiveForcesMeshInverseNonnegative
    (G : SimpleGraph L) (Q : List L)
    (hIyama : PositiveRightAdditiveHasRepresentableMeshExactness G Q) :
    PositiveRightAdditiveForcesMeshInverseNonnegative G Q := by
  intro hRuns lambda hlambda M hM
  obtain ⟨E⟩ := hIyama hRuns ⟨lambda, hlambda⟩
  exact recurrenceSolution_nonnegative G Q E M hM

/-- The smaller numerical strictness interface supported by the production
knitting proof. -/
def PositiveRightAdditiveForcesNoTruncation
    (G : SimpleGraph L) (Q : List L) : Prop :=
  ARWord.HasOnlyBoundaryRepeatedRuns G Q →
    ∀ lambda : Fin Q.length → ℤ,
      IsPositiveRightAdditive G Q lambda →
        TruncationNeverActivates
          (incomingMatrix G Q) (translationMatrix Q)

/-- Numerical no-truncation also discharges the same finite-mesh
hypothesis through the already proved knitting telescope. -/
theorem positiveRightAdditiveForcesMeshInverseNonnegative_of_noTruncation
    (G : SimpleGraph L) (Q : List L)
    (hIyama : PositiveRightAdditiveForcesNoTruncation G Q) :
    PositiveRightAdditiveForcesMeshInverseNonnegative G Q := by
  intro hRuns lambda hlambda M hM
  exact satisfiesWordMeshInverseRecurrence_nonnegative_of_noTruncation
    G Q M (hIyama hRuns lambda hlambda) hM

/-- The manuscript applies finite mesh exactness to every row-restricted
selected segment of one ambient word. -/
def UniformSelectedSegmentRepresentableMeshExactness
    (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ (D : Finset (Fin Q.length)) (a : Fin Q.length),
    PositiveRightAdditiveHasRepresentableMeshExactness
      (ARWord.SelectedSegments.segmentGraph G Q
        (rowRestrictedOmissions D a))
      (ARWord.SelectedSegments.segmentWord Q
        (rowRestrictedOmissions D a))

/-- Uniform representable mesh exactness supplies exactly the family of
finite-mesh hypotheses consumed by directed sorting and the quotient
profile. -/
theorem uniformSelectedSegmentMeshInverseNonnegative
    (G : SimpleGraph L) (Q : List L)
    (hIyama : UniformSelectedSegmentRepresentableMeshExactness G Q) :
    ∀ (D : Finset (Fin Q.length)) (a : Fin Q.length),
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (ARWord.SelectedSegments.segmentGraph G Q
          (rowRestrictedOmissions D a))
        (ARWord.SelectedSegments.segmentWord Q
          (rowRestrictedOmissions D a)) := by
  intro D a
  exact positiveRightAdditiveForcesMeshInverseNonnegative
    _ _ (hIyama D a)

end QuotientSubmoduleEquidistribution.RepresentationDirected.MeshExactness
