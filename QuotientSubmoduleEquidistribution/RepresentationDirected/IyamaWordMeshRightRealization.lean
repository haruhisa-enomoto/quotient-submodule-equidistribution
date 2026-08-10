import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshAdditiveHull
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshRecurrence

/-!
# Right representable meshes in the word-mesh additive hull

This file packages the dependent families of vertex morphisms from
`IyamaWordMeshRecurrence` as genuine morphisms in the finite matrix additive
hull. Evaluation on the unique row of a singleton vertex identifies matrix
postcomposition with the predecessor and incoming-arrow maps already proved
exact. The resulting matrix complex supplies a full `WordRightMeshRealization`.

The construction is entirely abstract. It uses no concrete algebra, quiver
presentation, module enumeration, or classification.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.RightRealization

open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh
open QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMeshRecurrence
open QuotientSubmoduleEquidistribution.CategoryTheory

universe uK uC vC uL

variable {K : Type uK} [Field K]

/-- Evaluation on the unique source row identifies maps out of a one-term
matrix object with a dependent family of maps. -/
def homFromEmbeddingLinearEquiv
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (X : C) (M : Mat_ C) :
    ((Mat_.embedding C).obj X ⟶ M) ≃ₗ[K]
      ((j : M.ι) → (X ⟶ M.X j)) where
  toFun f j := f PUnit.unit j
  invFun g _ j := g j
  left_inv f := by
    ext ⟨⟩ j
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' k f := by
    ext j
    change k • f PUnit.unit j = k • f PUnit.unit j
    rfl

@[simp]
theorem homFromEmbeddingLinearEquiv_apply
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (X : C) (M : Mat_ C) (f : (Mat_.embedding C).obj X ⟶ M)
    (j : M.ι) :
    homFromEmbeddingLinearEquiv (K := K) C X M f j = f PUnit.unit j :=
  by simp [homFromEmbeddingLinearEquiv]

@[simp]
theorem homFromEmbeddingLinearEquiv_symm_apply
    (C : Type uC) [CategoryTheory.Category.{vC} C]
    [Preadditive C] [Linear K C]
    (X : C) (M : Mat_ C) (g : (j : M.ι) → (X ⟶ M.X j))
    (i : ((Mat_.embedding C).obj X).ι) (j : M.ι) :
    (homFromEmbeddingLinearEquiv (K := K) C X M).symm g i j = g j := by
  cases i
  simp [homFromEmbeddingLinearEquiv]

variable {L : Type uL}

abbrev MeshCategory
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :=
  WordMesh.Category (K := K) G Q hAlt

/-- The established singleton vertex object in the word-mesh additive hull. -/
abbrev vertexObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Mat_ (MeshCategory (K := K) G Q hAlt) :=
  AdditiveHull.vertexObj (K := K) G Q hAlt x

/-- The formal direct sum of predecessor vertices at `x`. -/
def previousObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Mat_ (MeshCategory (K := K) G Q hAlt) where
  ι := {p : Fin Q.length // IsPrevious Q p x}
  X p := WordMesh.obj (K := K) G Q hAlt p.1

/-- The formal direct sum of incoming middle vertices at `x`. -/
def middleObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Mat_ (MeshCategory (K := K) G Q hAlt) where
  ι := {y : Fin Q.length // IsMiddle G Q y x}
  X y := WordMesh.obj (K := K) G Q hAlt y.1

/-- Evaluation equivalence for the predecessor object. -/
def previousHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    (vertexObj (K := K) G Q hAlt s ⟶ previousObj (K := K) G Q hAlt x) ≃ₗ[K]
      ((p : {p : Fin Q.length // IsPrevious Q p x}) →
        (WordMesh.obj (K := K) G Q hAlt s ⟶
          WordMesh.obj (K := K) G Q hAlt p.1)) :=
  homFromEmbeddingLinearEquiv (K := K)
    (MeshCategory (K := K) G Q hAlt)
    (WordMesh.obj (K := K) G Q hAlt s)
    (previousObj (K := K) G Q hAlt x)

/-- Evaluation equivalence for the middle object. -/
def middleHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    (vertexObj (K := K) G Q hAlt s ⟶ middleObj (K := K) G Q hAlt x) ≃ₗ[K]
      ((y : {y : Fin Q.length // IsMiddle G Q y x}) →
        (WordMesh.obj (K := K) G Q hAlt s ⟶
          WordMesh.obj (K := K) G Q hAlt y.1)) :=
  homFromEmbeddingLinearEquiv (K := K)
    (MeshCategory (K := K) G Q hAlt)
    (WordMesh.obj (K := K) G Q hAlt s)
    (middleObj (K := K) G Q hAlt x)

/-- Evaluation equivalence between one-by-one matrices and the underlying
vertex Hom space. -/
def vertexHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    (vertexObj (K := K) G Q hAlt s ⟶ vertexObj (K := K) G Q hAlt x) ≃ₗ[K]
      (WordMesh.obj (K := K) G Q hAlt s ⟶
        WordMesh.obj (K := K) G Q hAlt x) where
  toFun f := f PUnit.unit PUnit.unit
  invFun g _ _ := g
  left_inv f := by
    ext ⟨⟩ ⟨⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' k f := by
    change k • f PUnit.unit PUnit.unit =
      k • f PUnit.unit PUnit.unit
    rfl

/-- The first mesh map as a matrix. -/
def previousToMiddle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    previousObj (K := K) G Q hAlt x ⟶ middleObj (K := K) G Q hAlt x :=
  fun p y ↦ quotientPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2

/-- The second mesh map as a one-column matrix. -/
def middleToVertex
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    middleObj (K := K) G Q hAlt x ⟶ vertexObj (K := K) G Q hAlt x :=
  fun y _ ↦ quotientMiddleArrow (K := K) G Q hAlt y.2

/-! ## Compatibility with the dependent-family maps -/

/-- Postcomposition by the matrix middle-to-vertex map is the previously
proved incoming-arrow map after evaluating the unique source row. -/
theorem vertexHomLinearEquiv_postcomp_middleToVertex
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length)
    (f : vertexObj (K := K) G Q hAlt s ⟶ middleObj (K := K) G Q hAlt x) :
    vertexHomLinearEquiv (K := K) G Q hAlt s x
        (f ≫ middleToVertex (K := K) G Q hAlt x) =
      quotientIncomingMap (K := K) G Q hAlt s x
        (middleHomLinearEquiv (K := K) G Q hAlt s x f) := by
  classical
  change (∑ y, f PUnit.unit y ≫
      quotientMiddleArrow (K := K) G Q hAlt y.2) =
    ∑ y, f PUnit.unit y ≫
      quotientMiddleArrow (K := K) G Q hAlt y.2
  rfl

/-- Postcomposition by the predecessor-to-middle matrix is the previously
proved predecessor map after evaluating the unique source row. -/
theorem middleHomLinearEquiv_postcomp_previousToMiddle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length)
    (f : vertexObj (K := K) G Q hAlt s ⟶ previousObj (K := K) G Q hAlt x) :
    middleHomLinearEquiv (K := K) G Q hAlt s x
        (f ≫ previousToMiddle (K := K) G Q hAlt x) =
      quotientPreviousMap (K := K) G Q hAlt s x
        (previousHomLinearEquiv (K := K) G Q hAlt s x f) := by
  classical
  funext y
  change (∑ p, f PUnit.unit p ≫
      quotientPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2) =
    ∑ p, f PUnit.unit p ≫
      quotientPreviousMiddleArrow (K := K) G Q hAlt p.2 y.2
  rfl

/-- The simple quotient on singleton matrix Hom spaces. -/
def matSimpleQuotient
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    (vertexObj (K := K) G Q hAlt s ⟶ vertexObj (K := K) G Q hAlt x) →ₗ[K]
      SimpleRepresentableFiber K s x :=
  (quotientSimpleMap (K := K) G Q hAlt s x).comp
    (vertexHomLinearEquiv (K := K) G Q hAlt s x).toLinearMap

@[simp]
theorem matSimpleQuotient_apply
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length)
    (f : vertexObj (K := K) G Q hAlt s ⟶ vertexObj (K := K) G Q hAlt x) :
    matSimpleQuotient (K := K) G Q hAlt s x f =
      quotientSimpleMap (K := K) G Q hAlt s x
        (vertexHomLinearEquiv (K := K) G Q hAlt s x f) :=
  rfl

/-! ## Transported exactness -/

/-- Exactness at the matrix middle object, tested against a singleton vertex
source. -/
theorem mat_exact_at_middle
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    Function.Exact
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := vertexObj (K := K) G Q hAlt s)
        (previousToMiddle (K := K) G Q hAlt x))
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := vertexObj (K := K) G Q hAlt s)
        (middleToVertex (K := K) G Q hAlt x)) := by
  classical
  intro f
  constructor
  · intro hf
    change f ≫ middleToVertex (K := K) G Q hAlt x = 0 at hf
    have hq :
        quotientIncomingMap (K := K) G Q hAlt s x
            (middleHomLinearEquiv (K := K) G Q hAlt s x f) = 0 := by
      rw [← vertexHomLinearEquiv_postcomp_middleToVertex]
      rw [hf, map_zero]
    obtain ⟨a, ha⟩ :=
      (quotient_exact_at_middle (K := K) G Q hAlt s x
        (middleHomLinearEquiv (K := K) G Q hAlt s x f)).mp hq
    let g :=
      (previousHomLinearEquiv (K := K) G Q hAlt s x).symm a
    refine ⟨g, ?_⟩
    change g ≫ previousToMiddle (K := K) G Q hAlt x = f
    apply (middleHomLinearEquiv (K := K) G Q hAlt s x).injective
    rw [middleHomLinearEquiv_postcomp_previousToMiddle]
    change quotientPreviousMap (K := K) G Q hAlt s x
        (previousHomLinearEquiv (K := K) G Q hAlt s x g) =
      middleHomLinearEquiv (K := K) G Q hAlt s x f
    rw [show previousHomLinearEquiv (K := K) G Q hAlt s x g = a by
      exact LinearEquiv.apply_symm_apply
        (previousHomLinearEquiv (K := K) G Q hAlt s x) a]
    exact ha
  · rintro ⟨g, rfl⟩
    simp only [QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap_apply]
    apply (vertexHomLinearEquiv (K := K) G Q hAlt s x).injective
    rw [map_zero]
    rw [vertexHomLinearEquiv_postcomp_middleToVertex,
      middleHomLinearEquiv_postcomp_previousToMiddle]
    exact quotientIncomingMap_previousMap_eq_zero G Q hAlt s x
      (previousHomLinearEquiv (K := K) G Q hAlt s x g)

/-- Exactness at the singleton target, including its simple quotient. -/
theorem mat_exact_at_right
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    Function.Exact
      (QuotientSubmoduleEquidistribution.RepresentationDirected.postcompLinearMap
        (K := K) (X := vertexObj (K := K) G Q hAlt s)
        (middleToVertex (K := K) G Q hAlt x))
      (matSimpleQuotient (K := K) G Q hAlt s x) := by
  classical
  intro f
  constructor
  · intro hf
    have hq :
        quotientSimpleMap (K := K) G Q hAlt s x
            (vertexHomLinearEquiv (K := K) G Q hAlt s x f) = 0 := by
      exact hf
    obtain ⟨a, ha⟩ :=
      (quotient_exact_at_right (K := K) G Q hAlt s x
        (vertexHomLinearEquiv (K := K) G Q hAlt s x f)).mp hq
    let g :=
      (middleHomLinearEquiv (K := K) G Q hAlt s x).symm a
    refine ⟨g, ?_⟩
    change g ≫ middleToVertex (K := K) G Q hAlt x = f
    apply (vertexHomLinearEquiv (K := K) G Q hAlt s x).injective
    rw [vertexHomLinearEquiv_postcomp_middleToVertex]
    change quotientIncomingMap (K := K) G Q hAlt s x
        (middleHomLinearEquiv (K := K) G Q hAlt s x g) =
      vertexHomLinearEquiv (K := K) G Q hAlt s x f
    rw [show middleHomLinearEquiv (K := K) G Q hAlt s x g = a by
      exact LinearEquiv.apply_symm_apply
        (middleHomLinearEquiv (K := K) G Q hAlt s x) a]
    exact ha
  · rintro ⟨g, rfl⟩
    change quotientSimpleMap (K := K) G Q hAlt s x
      (vertexHomLinearEquiv (K := K) G Q hAlt s x
        (g ≫ middleToVertex (K := K) G Q hAlt x)) = 0
    rw [vertexHomLinearEquiv_postcomp_middleToVertex]
    exact quotientSimpleMap_incoming_eq_zero G Q hAlt s x
      (middleHomLinearEquiv (K := K) G Q hAlt s x g)

/-- The matrix simple quotient is surjective. -/
theorem matSimpleQuotient_surjective
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (s x : Fin Q.length) :
    Function.Surjective (matSimpleQuotient (K := K) G Q hAlt s x) := by
  intro q
  obtain ⟨f, hf⟩ :=
    quotientSimpleMap_surjective (K := K) G Q hAlt s x q
  refine ⟨(vertexHomLinearEquiv (K := K) G Q hAlt s x).symm f, ?_⟩
  change quotientSimpleMap (K := K) G Q hAlt s x
    (vertexHomLinearEquiv (K := K) G Q hAlt s x
      ((vertexHomLinearEquiv (K := K) G Q hAlt s x).symm f)) = q
  rw [LinearEquiv.apply_symm_apply]
  exact hf

/-- The dependent-family recurrence therefore supplies the complete
representable mesh-complex package on singleton vertices of the additive
envelope. -/
def rightRepresentableMeshComplex
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    RightRepresentableMeshComplex (K := K)
      (vertexObj (K := K) G Q hAlt)
      (previousObj (K := K) G Q hAlt)
      (middleObj (K := K) G Q hAlt) where
  nu := previousToMiddle (K := K) G Q hAlt
  mu := middleToVertex (K := K) G Q hAlt
  simpleQuotient := matSimpleQuotient (K := K) G Q hAlt
  exact_at_middle := mat_exact_at_middle (K := K) G Q hAlt
  exact_at_right := mat_exact_at_right (K := K) G Q hAlt
  simpleQuotient_surjective :=
    matSimpleQuotient_surjective (K := K) G Q hAlt

/-! ## Structural dimension identifications -/

/-- If p is the predecessor of x, the predecessor matrix object has
exactly that one summand, hence the expected representable dimension. -/
theorem previousHom_finrank_of_previous
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (a p x : Fin Q.length) (hp : IsPrevious Q p x) :
    Module.finrank K
        (vertexObj (K := K) G Q hAlt a ⟶
          previousObj (K := K) G Q hAlt x) =
      Module.finrank K
        (vertexObj (K := K) G Q hAlt a ⟶
          vertexObj (K := K) G Q hAlt p) := by
  classical
  let p₀ : {q : Fin Q.length // IsPrevious Q q x} := ⟨p, hp⟩
  calc
    Module.finrank K
        (vertexObj (K := K) G Q hAlt a ⟶
          previousObj (K := K) G Q hAlt x) =
        Module.finrank K
          ((q : {q : Fin Q.length // IsPrevious Q q x}) →
            (WordMesh.obj (K := K) G Q hAlt a ⟶
              WordMesh.obj (K := K) G Q hAlt q.1)) :=
      (previousHomLinearEquiv (K := K) G Q hAlt a x).finrank_eq
    _ = ∑ q : {q : Fin Q.length // IsPrevious Q q x},
          Module.finrank K
            (WordMesh.obj (K := K) G Q hAlt a ⟶
              WordMesh.obj (K := K) G Q hAlt q.1) := by
      rw [Module.finrank_pi_fintype K]
    _ = Module.finrank K
          (WordMesh.obj (K := K) G Q hAlt a ⟶
            WordMesh.obj (K := K) G Q hAlt p) := by
      apply Finset.sum_eq_single p₀
      · intro q hq hne
        exfalso
        apply hne
        apply Subtype.ext
        exact isPrevious_unique q.2 hp
      · intro hp₀
        exact (hp₀ (Finset.mem_univ p₀)).elim
    _ = Module.finrank K
          (vertexObj (K := K) G Q hAlt a ⟶
            vertexObj (K := K) G Q hAlt p) :=
      (vertexHomLinearEquiv (K := K) G Q hAlt a p).finrank_eq.symm

/-- With no predecessor, the predecessor matrix has an empty indexing type
and is a zero object. -/
theorem previousObj_isZero_of_first
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (x : Fin Q.length) (hfirst : ¬ ∃ p, IsPrevious Q p x) :
    IsZero (previousObj (K := K) G Q hAlt x) := by
  rw [IsZero.iff_id_eq_zero]
  apply Mat_.hom_ext
  intro p q
  exact (hfirst ⟨p.1, p.2⟩).elim

/-- The middle matrix dimension is the filtered sum appearing in the word
recurrence. -/
theorem middleHom_finrank
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (a x : Fin Q.length) :
    Module.finrank K
        (vertexObj (K := K) G Q hAlt a ⟶
          middleObj (K := K) G Q hAlt x) =
      wordMiddleFinrank G Q
        (fun b y ↦ Module.finrank K
          (vertexObj (K := K) G Q hAlt b ⟶
            vertexObj (K := K) G Q hAlt y)) a x := by
  classical
  calc
    Module.finrank K
        (vertexObj (K := K) G Q hAlt a ⟶
          middleObj (K := K) G Q hAlt x) =
        Module.finrank K
          ((y : {y : Fin Q.length // IsMiddle G Q y x}) →
            (WordMesh.obj (K := K) G Q hAlt a ⟶
              WordMesh.obj (K := K) G Q hAlt y.1)) :=
      (middleHomLinearEquiv (K := K) G Q hAlt a x).finrank_eq
    _ = ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
          Module.finrank K
            (WordMesh.obj (K := K) G Q hAlt a ⟶
              WordMesh.obj (K := K) G Q hAlt y.1) := by
      rw [Module.finrank_pi_fintype K]
    _ = ∑ y : {y : Fin Q.length // IsMiddle G Q y x},
          Module.finrank K
            (vertexObj (K := K) G Q hAlt a ⟶
              vertexObj (K := K) G Q hAlt y.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact (vertexHomLinearEquiv (K := K) G Q hAlt a y.1).finrank_eq.symm
    _ = wordMiddleFinrank G Q
          (fun b y ↦ Module.finrank K
            (vertexObj (K := K) G Q hAlt b ⟶
              vertexObj (K := K) G Q hAlt y)) a x := by
      unfold wordMiddleFinrank
      symm
      apply Finset.sum_subtype
      intro y
      simp

/-- Full word-level realization in the matrix additive envelope. -/
def wordRightMeshRealization
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    WordRightMeshRealization (K := K) G Q
      (vertexObj (K := K) G Q hAlt)
      (previousObj (K := K) G Q hAlt)
      (middleObj (K := K) G Q hAlt) where
  toRightRepresentableMeshComplex :=
    rightRepresentableMeshComplex (K := K) G Q hAlt
  left_finrank_of_previous :=
    previousHom_finrank_of_previous (K := K) G Q hAlt
  left_isZero_of_first :=
    previousObj_isZero_of_first (K := K) G Q hAlt
  middle_finrank :=
    middleHom_finrank (K := K) G Q hAlt

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.RightRealization
