import OpConjecture.RepresentationDirected.IyamaWordMeshRightRealization
import OpConjecture.RepresentationDirected.IyamaWordMeshStartingExactness

/-!
# Left corepresentable meshes in the word-mesh additive hull

This file transports the outgoing, target-evaluated exactness of
`IyamaWordMeshStartingExactness` to genuine morphisms in the finite matrix
additive hull.  The resulting complex starts at a singleton word vertex,
passes through the sum of its outgoing middle vertices, and ends at the sum
of its next occurrences.

The construction is entirely abstract.  It uses no concrete algebra, quiver
presentation, module enumeration, or classification.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.LeftRealization

open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMeshStartingExactness
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.RightRealization

universe uK uC vC uL

variable {K : Type uK} [Field K]

/-- Evaluation on the unique target column identifies maps into a one-term
matrix object with a dependent family of maps. -/
def homToEmbeddingLinearEquiv
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (M : Mat_ C) (X : C) :
    (M ⟶ (Mat_.embedding C).obj X) ≃ₗ[K]
      ((i : M.ι) → (M.X i ⟶ X)) where
  toFun f i := f i PUnit.unit
  invFun g i _ := g i
  left_inv f := by
    ext i ⟨⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' k f := by
    ext i
    change k • f i PUnit.unit = k • f i PUnit.unit
    rfl

@[simp]
theorem homToEmbeddingLinearEquiv_apply
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (M : Mat_ C) (X : C) (f : M ⟶ (Mat_.embedding C).obj X)
    (i : M.ι) :
    homToEmbeddingLinearEquiv (K := K) C M X f i = f i PUnit.unit :=
  by simp [homToEmbeddingLinearEquiv]

@[simp]
theorem homToEmbeddingLinearEquiv_symm_apply
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (M : Mat_ C) (X : C) (g : (i : M.ι) → (M.X i ⟶ X))
    (i : M.ι) (j : ((Mat_.embedding C).obj X).ι) :
    (homToEmbeddingLinearEquiv (K := K) C M X).symm g i j = g i := by
  cases j
  simp [homToEmbeddingLinearEquiv]

variable {L : Type uL}

/-- The formal direct sum of outgoing middle vertices at `x`. -/
def outgoingMiddleObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Mat_ (MeshCategory (K := K) G Q hAlt) where
  ι := {y : Fin Q.length // IsMiddle G Q x y}
  X y := WordMesh.obj (K := K) G Q hAlt y.1

/-- The formal direct sum of next occurrences of the label at `x`. -/
def nextObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Mat_ (MeshCategory (K := K) G Q hAlt) where
  ι := {b : Fin Q.length // IsPrevious Q x b}
  X b := WordMesh.obj (K := K) G Q hAlt b.1

/-- Evaluation equivalence for the outgoing-middle object. -/
def outgoingMiddleHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    (outgoingMiddleObj (K := K) G Q hAlt x ⟶
        vertexObj (K := K) G Q hAlt t) ≃ₗ[K]
      ((y : {y : Fin Q.length // IsMiddle G Q x y}) →
        (WordMesh.obj (K := K) G Q hAlt y.1 ⟶
          WordMesh.obj (K := K) G Q hAlt t)) :=
  homToEmbeddingLinearEquiv (K := K)
    (MeshCategory (K := K) G Q hAlt)
    (outgoingMiddleObj (K := K) G Q hAlt x)
    (WordMesh.obj (K := K) G Q hAlt t)

/-- Evaluation equivalence for the next-occurrence object. -/
def nextHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    (nextObj (K := K) G Q hAlt x ⟶
        vertexObj (K := K) G Q hAlt t) ≃ₗ[K]
      ((b : {b : Fin Q.length // IsPrevious Q x b}) →
        (WordMesh.obj (K := K) G Q hAlt b.1 ⟶
          WordMesh.obj (K := K) G Q hAlt t)) :=
  homToEmbeddingLinearEquiv (K := K)
    (MeshCategory (K := K) G Q hAlt)
    (nextObj (K := K) G Q hAlt x)
    (WordMesh.obj (K := K) G Q hAlt t)

/-- The first, outgoing mesh map as a one-row matrix. -/
def vertexToOutgoingMiddle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    vertexObj (K := K) G Q hAlt x ⟶
      outgoingMiddleObj (K := K) G Q hAlt x :=
  fun _ y ↦ quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2

/-- The second mesh map, from outgoing middle vertices to next occurrences. -/
def outgoingMiddleToNext
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    outgoingMiddleObj (K := K) G Q hAlt x ⟶
      nextObj (K := K) G Q hAlt x :=
  fun y b ↦ quotientMiddleNextArrow (K := K) G Q hAlt b.2 y.2

/-! ## Compatibility with dependent-family maps -/

/-- Precomposition by the outgoing map is the previously proved evaluated
outgoing-arrow map. -/
theorem vertexHomLinearEquiv_precomp_vertexToOutgoingMiddle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length)
    (f : outgoingMiddleObj (K := K) G Q hAlt x ⟶
      vertexObj (K := K) G Q hAlt t) :
    vertexHomLinearEquiv (K := K) G Q hAlt x t
        (vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ f) =
      quotientOutgoingMap (K := K) G Q hAlt x t
        (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t f) := by
  classical
  change (∑ y, quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2 ≫
      f y PUnit.unit) =
    ∑ y, quotientOutgoingMiddleArrow (K := K) G Q hAlt y.2 ≫
      f y PUnit.unit
  rfl

/-- Precomposition by the middle-to-next map is the previously proved
next-occurrence map. -/
theorem outgoingMiddleHomLinearEquiv_precomp_outgoingMiddleToNext
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length)
    (f : nextObj (K := K) G Q hAlt x ⟶
      vertexObj (K := K) G Q hAlt t) :
    outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t
        (outgoingMiddleToNext (K := K) G Q hAlt x ≫ f) =
      quotientNextMap (K := K) G Q hAlt x t
        (nextHomLinearEquiv (K := K) G Q hAlt x t f) := by
  classical
  funext y
  change (∑ b, quotientMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫
      f b PUnit.unit) =
    ∑ b, quotientMiddleNextArrow (K := K) G Q hAlt b.2 y.2 ≫
      f b PUnit.unit
  rfl

/-- The diagonal cosimple quotient on singleton matrix Hom spaces. -/
def matCosimpleQuotient
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    (vertexObj (K := K) G Q hAlt x ⟶
      vertexObj (K := K) G Q hAlt t) →ₗ[K]
      SimpleCorepresentableFiber K x t :=
  (quotientCosimpleMap (K := K) G Q hAlt x t).comp
    (vertexHomLinearEquiv (K := K) G Q hAlt x t).toLinearMap

@[simp]
theorem matCosimpleQuotient_apply
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length)
    (f : vertexObj (K := K) G Q hAlt x ⟶
      vertexObj (K := K) G Q hAlt t) :
    matCosimpleQuotient (K := K) G Q hAlt x t f =
      quotientCosimpleMap (K := K) G Q hAlt x t
        (vertexHomLinearEquiv (K := K) G Q hAlt x t f) :=
  rfl

/-! ## Transported exactness -/

/-- Exactness at the singleton source term, including its diagonal cosimple
quotient. -/
theorem mat_exact_at_source
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    Function.Exact
      (fun f : outgoingMiddleObj (K := K) G Q hAlt x ⟶
          vertexObj (K := K) G Q hAlt t ↦
        vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ f)
      (matCosimpleQuotient (K := K) G Q hAlt x t) := by
  classical
  intro f
  constructor
  · intro hf
    have hq :
        quotientCosimpleMap (K := K) G Q hAlt x t
            (vertexHomLinearEquiv (K := K) G Q hAlt x t f) = 0 := by
      exact hf
    obtain ⟨a, ha⟩ :=
      (quotient_exact_at_source (K := K) G Q hAlt x t
        (vertexHomLinearEquiv (K := K) G Q hAlt x t f)).mp hq
    let g :=
      (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t).symm a
    refine ⟨g, ?_⟩
    apply (vertexHomLinearEquiv (K := K) G Q hAlt x t).injective
    rw [vertexHomLinearEquiv_precomp_vertexToOutgoingMiddle]
    change quotientOutgoingMap (K := K) G Q hAlt x t
        (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t g) =
      vertexHomLinearEquiv (K := K) G Q hAlt x t f
    rw [show outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t g = a by
      exact LinearEquiv.apply_symm_apply
        (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t) a]
    exact ha
  · rintro ⟨g, rfl⟩
    change quotientCosimpleMap (K := K) G Q hAlt x t
      (vertexHomLinearEquiv (K := K) G Q hAlt x t
        (vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ g)) = 0
    rw [vertexHomLinearEquiv_precomp_vertexToOutgoingMiddle]
    exact quotientCosimpleMap_outgoing_eq_zero G Q hAlt x t
      (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t g)

/-- Exactness at the outgoing-middle matrix object, tested against a
singleton target. -/
theorem mat_exact_at_outgoing_middle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    Function.Exact
      (fun f : nextObj (K := K) G Q hAlt x ⟶
          vertexObj (K := K) G Q hAlt t ↦
        outgoingMiddleToNext (K := K) G Q hAlt x ≫ f)
      (fun f : outgoingMiddleObj (K := K) G Q hAlt x ⟶
          vertexObj (K := K) G Q hAlt t ↦
        vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ f) := by
  classical
  intro f
  constructor
  · intro hf
    change vertexToOutgoingMiddle (K := K) G Q hAlt x ≫ f = 0 at hf
    have hq :
        quotientOutgoingMap (K := K) G Q hAlt x t
            (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t f) = 0 := by
      rw [← vertexHomLinearEquiv_precomp_vertexToOutgoingMiddle]
      rw [hf, map_zero]
    obtain ⟨a, ha⟩ :=
      (quotient_exact_at_outgoing_middle (K := K) G Q hAlt x t
        (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t f)).mp hq
    let g := (nextHomLinearEquiv (K := K) G Q hAlt x t).symm a
    refine ⟨g, ?_⟩
    apply (outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t).injective
    rw [outgoingMiddleHomLinearEquiv_precomp_outgoingMiddleToNext]
    change quotientNextMap (K := K) G Q hAlt x t
        (nextHomLinearEquiv (K := K) G Q hAlt x t g) =
      outgoingMiddleHomLinearEquiv (K := K) G Q hAlt x t f
    rw [show nextHomLinearEquiv (K := K) G Q hAlt x t g = a by
      exact LinearEquiv.apply_symm_apply
        (nextHomLinearEquiv (K := K) G Q hAlt x t) a]
    exact ha
  · rintro ⟨g, rfl⟩
    apply (vertexHomLinearEquiv (K := K) G Q hAlt x t).injective
    rw [map_zero]
    rw [vertexHomLinearEquiv_precomp_vertexToOutgoingMiddle,
      outgoingMiddleHomLinearEquiv_precomp_outgoingMiddleToNext]
    exact quotientOutgoingMap_nextMap_eq_zero G Q hAlt x t
      (nextHomLinearEquiv (K := K) G Q hAlt x t g)

/-- The matrix cosimple quotient is surjective. -/
theorem matCosimpleQuotient_surjective
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x t : Fin Q.length) :
    Function.Surjective (matCosimpleQuotient (K := K) G Q hAlt x t) := by
  intro q
  obtain ⟨f, hf⟩ := quotientCosimpleMap_surjective
    (K := K) G Q hAlt x t q
  refine ⟨(vertexHomLinearEquiv (K := K) G Q hAlt x t).symm f, ?_⟩
  change quotientCosimpleMap (K := K) G Q hAlt x t
    (vertexHomLinearEquiv (K := K) G Q hAlt x t
      ((vertexHomLinearEquiv (K := K) G Q hAlt x t).symm f)) = q
  rw [LinearEquiv.apply_symm_apply]
  exact hf

/-! ## Boundary and singleton identifications -/

/-- With no next occurrence, the final matrix object has empty indexing type
and is a zero object. -/
theorem nextObj_isZero_of_last
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x : Fin Q.length) (hlast : ¬ ∃ b, IsPrevious Q x b) :
    IsZero (nextObj (K := K) G Q hAlt x) := by
  rw [IsZero.iff_id_eq_zero]
  apply Mat_.hom_ext
  intro b c
  exact (hlast ⟨b.1, b.2⟩).elim

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.LeftRealization
