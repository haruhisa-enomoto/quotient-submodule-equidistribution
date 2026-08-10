import QuotientSubmoduleEquidistribution.CategoryTheory.LinearMat
import QuotientSubmoduleEquidistribution.CategoryTheory.DirectedIdempotentCompletion
import QuotientSubmoduleEquidistribution.CategoryTheory.FiniteBiproductIteration
import QuotientSubmoduleEquidistribution.CategoryTheory.MatrixIdempotent
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordMeshCategory
import QuotientSubmoduleEquidistribution.Foundation.RingTheory.LocalRing.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The additive hull of the finite word mesh category

This file forms the finite matrix category on the abstract word mesh
category.  It proves that every object is a finite biproduct of singleton
word vertices, that all Hom spaces are finite-dimensional, and that the
singleton vertices remain indecomposable with local endomorphism rings.  It
also proves that the additive hull is idempotent complete by grouping each
object into its ordered homogeneous vertex blocks.

No concrete algebra, quiver instance, or module classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord
open QuotientSubmoduleEquidistribution.CategoryTheory.DirectedIdempotent
open QuotientSubmoduleEquidistribution.CategoryTheory.MatrixIdempotent

/-- The finite additive hull of the abstract word mesh category. -/
abbrev Category (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :=
  Mat_ (WordMesh.Category (K := K) G Q hAlt)

/-- The finite-biproduct structure on `Mat_` supplies binary biproducts,
which Mathlib intentionally does not install as a global instance. -/
instance hasBinaryBiproducts
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    HasBinaryBiproducts (Category (K := K) G Q hAlt) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- A word-mesh vertex as a singleton object of the additive hull. -/
def vertexObj (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Category (K := K) G Q hAlt :=
  (Mat_.embedding (WordMesh.Category (K := K) G Q hAlt)).obj
    (WordMesh.obj (K := K) G Q hAlt x)

/-- Hom spaces in the additive hull are finite-dimensional. -/
instance homModuleFinite (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (X Y : Category (K := K) G Q hAlt) : Module.Finite K (X ⟶ Y) := by
  infer_instance

/-- Every additive-hull object is a `Fin`-indexed biproduct of singleton
word-mesh vertices. -/
theorem exists_iso_fin_biproduct_vertexObj
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (M : Category (K := K) G Q hAlt) :
    ∃ (n : ℕ) (label : Fin n → Fin Q.length),
      Nonempty (M ≅ ⨁ fun i ↦ vertexObj (K := K) G Q hAlt (label i)) := by
  let e : M.ι ≃ Fin (Fintype.card M.ι) := Fintype.equivFin M.ι
  let label : Fin (Fintype.card M.ι) → Fin Q.length :=
    fun i ↦ M.X (e.symm i)
  refine ⟨Fintype.card M.ι, label, ⟨M.isoBiproductEmbedding ≪≫ ?_⟩⟩
  exact biproduct.whiskerEquiv e
    (fun i ↦ eqToIso (by simp [label, vertexObj, WordMesh.obj]))

/-- Evaluation of a singleton matrix on its unique entry, as a ring map on
endomorphisms. -/
def vertexEndRingHom
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    End (vertexObj (K := K) G Q hAlt x) →+*
      End (WordMesh.obj (K := K) G Q hAlt x) where
  toFun := fun f ↦ f PUnit.unit PUnit.unit
  map_zero' := rfl
  map_one' := by simp [vertexObj, Mat_.embedding]
  map_add' := fun _ _ ↦ rfl
  map_mul' := by
    intro f g
    change (∑ i : PUnit, g PUnit.unit i ≫ f i PUnit.unit) =
      g PUnit.unit PUnit.unit ≫ f PUnit.unit PUnit.unit
    simp

/-- Singleton-matrix evaluation identifies the vertex endomorphism ring in
the additive hull with its endomorphism ring in the raw mesh category. -/
def vertexEndRingEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    End (vertexObj (K := K) G Q hAlt x) ≃+*
      End (WordMesh.obj (K := K) G Q hAlt x) :=
  RingEquiv.ofBijective (vertexEndRingHom (K := K) G Q hAlt x) ⟨by
    intro f g h
    apply Mat_.hom_ext
    intro i j
    cases i
    cases j
    exact h, by
    intro f
    refine ⟨fun _ _ ↦ f, ?_⟩
    rfl⟩

/-- An additive-hull vertex still has the coefficient field as its
endomorphism ring. -/
def vertexSelfHomRingEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    End (vertexObj (K := K) G Q hAlt x) ≃+* K :=
  (vertexEndRingEquiv (K := K) G Q hAlt x).trans
    (WordMesh.selfHomRingEquiv (K := K) G Q hAlt x)

/-- Vertex endomorphism rings remain local after passing to the additive
hull. -/
instance vertexEndIsLocalRing
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    IsLocalRing (End (vertexObj (K := K) G Q hAlt x)) :=
  (vertexSelfHomRingEquiv (K := K) G Q hAlt x).symm.isLocalRing

/-- In a preadditive category with binary biproducts, a local endomorphism
ring forces categorical indecomposability. -/
theorem indecomposable_of_local_end
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    [HasBinaryBiproducts C]
    (X : C) [IsLocalRing (End X)] : Indecomposable X := by
  constructor
  · intro hX
    have hid := (IsZero.iff_id_eq_zero X).mp hX
    change (1 : End X) = 0 at hid
    exact one_ne_zero hid
  · intro Y Z e
    let p : End X :=
      e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    have hp : IsIdempotentElem p := by
      change p * p = p
      simp only [End.mul_def]
      simp [p, CategoryTheory.Category.assoc]
    rcases QuotientSubmoduleEquidistribution.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hp with
      hp₀ | hp₁
    · left
      apply (IsZero.iff_id_eq_zero Y).mpr
      have hproj : (biprod.fst : Y ⊞ Z ⟶ Y) ≫
          (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, CategoryTheory.Category.assoc]
          _ = 0 := by rw [hp₀]; simp; rfl
      have h := congrArg
        (fun q : End (Y ⊞ Z) ↦ biprod.inl ≫ q ≫ biprod.fst) hproj
      simpa [CategoryTheory.Category.assoc] using h
    · right
      apply (IsZero.iff_id_eq_zero Z).mpr
      have hproj : (biprod.fst : Y ⊞ Z ⟶ Y) ≫
          (biprod.inl : Y ⟶ Y ⊞ Z) = 𝟙 (Y ⊞ Z) := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, CategoryTheory.Category.assoc]
          _ = 𝟙 (Y ⊞ Z) := by rw [hp₁]; simp
      have h := congrArg
        (fun q : End (Y ⊞ Z) ↦ biprod.inr ≫ q ≫ biprod.snd) hproj
      simpa [CategoryTheory.Category.assoc] using h.symm

/-- Singleton word-mesh vertices are indecomposable in the additive hull. -/
theorem vertexObj_indec
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length) :
    Indecomposable (vertexObj (K := K) G Q hAlt x) :=
  indecomposable_of_local_end _

/-- A finite tuple all of whose entries are the same word-mesh vertex. -/
def homogeneousVertexBlock
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (I : Type) [Fintype I] : Category (K := K) G Q hAlt :=
  { ι := I
    X := fun _ ↦ WordMesh.obj (K := K) G Q hAlt x }

/-- Entrywise scalar coordinates identify morphisms between homogeneous
vertex blocks with ordinary matrices over the coefficient field. -/
def homogeneousHomLinearEquiv
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (I J : Type) [Fintype I] [Fintype J] :
    (homogeneousVertexBlock (K := K) G Q hAlt x I ⟶
        homogeneousVertexBlock (K := K) G Q hAlt x J) ≃ₗ[K]
      Matrix I J K where
  toFun f i j := WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x (f i j)
  invFun A i j :=
    (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).symm (A i j)
  left_inv f := by
    apply Mat_.hom_ext
    intro i j
    exact (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).symm_apply_apply (f i j)
  right_inv A := by
    apply Matrix.ext
    intro i j
    exact (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).apply_symm_apply (A i j)
  map_add' f g := by
    apply Matrix.ext
    intro i j
    exact (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).map_add (f i j) (g i j)
  map_smul' k f := by
    apply Matrix.ext
    intro i j
    exact (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).map_smul k (f i j)

@[simp]
lemma homogeneousHomLinearEquiv_id
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (I : Type) [Fintype I] [DecidableEq I] :
    homogeneousHomLinearEquiv (K := K) G Q hAlt x I I
        (𝟙 (homogeneousVertexBlock (K := K) G Q hAlt x I)) =
      1 := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq]
    change WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x
      ((𝟙 (homogeneousVertexBlock (K := K) G Q hAlt x I)) i i) = 1
    rw [Mat_.id_apply_self]
    change WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x
      (𝟙 (WordMesh.obj (K := K) G Q hAlt x)) = 1
    exact WordMesh.selfHomLinearEquiv_id G Q hAlt x
  · rw [Matrix.one_apply_ne h]
    change WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x
      ((𝟙 (homogeneousVertexBlock (K := K) G Q hAlt x I)) i j) = 0
    rw [Mat_.id_apply_of_ne _ _ _ h]
    exact (WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x).map_zero

@[simp]
lemma homogeneousHomLinearEquiv_comp
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (I J H : Type) [Fintype I] [Fintype J] [Fintype H]
    (f : homogeneousVertexBlock (K := K) G Q hAlt x I ⟶
      homogeneousVertexBlock (K := K) G Q hAlt x J)
    (g : homogeneousVertexBlock (K := K) G Q hAlt x J ⟶
      homogeneousVertexBlock (K := K) G Q hAlt x H) :
    homogeneousHomLinearEquiv (K := K) G Q hAlt x I H (f ≫ g) =
      homogeneousHomLinearEquiv (K := K) G Q hAlt x I J f *
        homogeneousHomLinearEquiv (K := K) G Q hAlt x J H g := by
  classical
  apply Matrix.ext
  intro i k
  change WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x
      (∑ j, f i j ≫ g j k) =
    ∑ j, WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x (f i j) *
      WordMesh.selfHomLinearEquiv (K := K) G Q hAlt x (g j k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact WordMesh.selfHomLinearEquiv_comp G Q hAlt x (f i j) (g j k)

/-- Every idempotent on a homogeneous finite vertex block splits in the
additive hull. -/
theorem split_homogeneous_idempotent
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) (x : Fin Q.length)
    (I : Type) [Fintype I]
    (p : homogeneousVertexBlock (K := K) G Q hAlt x I ⟶
      homogeneousVertexBlock (K := K) G Q hAlt x I)
    (hp : p ≫ p = p) :
    ∃ (Y : Category (K := K) G Q hAlt)
      (i : Y ⟶ homogeneousVertexBlock (K := K) G Q hAlt x I)
      (e : homogeneousVertexBlock (K := K) G Q hAlt x I ⟶ Y),
      i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  classical
  let pK : Matrix I I K :=
    homogeneousHomLinearEquiv (K := K) G Q hAlt x I I p
  have hpK : pK * pK = pK := by
    rw [← homogeneousHomLinearEquiv_comp, hp]
  obtain ⟨n, iK, eK, hiK, heK⟩ := split_small_matrix_idempotent I pK hpK
  let Y : Category (K := K) G Q hAlt :=
    homogeneousVertexBlock (K := K) G Q hAlt x (Fin n)
  let i : Y ⟶ homogeneousVertexBlock (K := K) G Q hAlt x I :=
    (homogeneousHomLinearEquiv (K := K) G Q hAlt x (Fin n) I).symm iK
  let e : homogeneousVertexBlock (K := K) G Q hAlt x I ⟶ Y :=
    (homogeneousHomLinearEquiv (K := K) G Q hAlt x I (Fin n)).symm eK
  refine ⟨Y, i, e, ?_, ?_⟩
  · apply (homogeneousHomLinearEquiv (K := K) G Q hAlt x
      (Fin n) (Fin n)).injective
    rw [homogeneousHomLinearEquiv_comp,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hiK,
      homogeneousHomLinearEquiv_id]
  · apply (homogeneousHomLinearEquiv (K := K) G Q hAlt x I I).injective
    rw [homogeneousHomLinearEquiv_comp,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, heK]

/-- The indices of an additive-hull object lying over one fixed mesh
vertex. -/
def vertexFiber
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt)
    (x : Fin Q.length) : Type :=
  {i : N.ι // N.X i = WordMesh.obj (K := K) G Q hAlt x}

instance vertexFiberFintype
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt)
    (x : Fin Q.length) : Fintype (vertexFiber (K := K) G Q hAlt N x) := by
  classical
  unfold vertexFiber
  infer_instance

/-- The homogeneous block of all summands of `N` at a fixed mesh vertex. -/
def vertexBlock
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt)
    (x : Fin Q.length) : Category (K := K) G Q hAlt :=
  homogeneousVertexBlock (K := K) G Q hAlt x
    (vertexFiber (K := K) G Q hAlt N x)

/-- Regroup an arbitrary additive-hull object by the mesh vertex of each
entry. -/
def matrixIsoBiproductVertexBlocks
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt) :
    N ≅ (⨁ fun x : Fin Q.length ↦
      vertexBlock (K := K) G Q hAlt N x) := by
  let e : N.ι ≃ Σ x : Fin Q.length, vertexFiber (K := K) G Q hAlt N x :=
    { toFun := fun i ↦ ⟨N.X i, ⟨i, rfl⟩⟩
      invFun := fun p ↦ p.2.1
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨x, i, hi⟩
        cases hi
        rfl }
  let E : N.ι → Category (K := K) G Q hAlt :=
    fun i ↦ (Mat_.embedding _).obj (N.X i)
  let B : (x : Fin Q.length) →
      vertexFiber (K := K) G Q hAlt N x →
        Category (K := K) G Q hAlt :=
    fun x _ ↦ (Mat_.embedding _).obj (WordMesh.obj (K := K) G Q hAlt x)
  exact Mat_.isoBiproductEmbedding N ≪≫
    biproduct.whiskerEquiv
      (f := E) (g := fun p ↦ B p.1 p.2) e (fun _ ↦ Iso.refl _) ≪≫
    (biproductBiproductIso
      (fun x : Fin Q.length ↦ vertexFiber (K := K) G Q hAlt N x) B).symm ≪≫
    biproduct.mapIso (fun x ↦ (Mat_.isoBiproductEmbedding
      (vertexBlock (K := K) G Q hAlt N x)).symm)

/-- Regroup an additive-hull object into the right-associated ordered list
of its homogeneous vertex blocks. -/
def matrixIsoIteratedVertexBlocks
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt) :
    N ≅ iteratedBiprod
      (List.ofFn (fun x : Fin Q.length ↦
        vertexBlock (K := K) G Q hAlt N x)) :=
  matrixIsoBiproductVertexBlocks (K := K) G Q hAlt N ≪≫
    finBiproductIsoIterated
      (fun x : Fin Q.length ↦ vertexBlock (K := K) G Q hAlt N x)

/-- Later homogeneous vertex blocks have no morphisms back to earlier
ones. -/
theorem vertexBlock_noBackward
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt)
    {x y : Fin Q.length} (hxy : x < y) :
    NoBackward
      (vertexBlock (K := K) G Q hAlt N x)
      (vertexBlock (K := K) G Q hAlt N y) := by
  intro f
  apply Mat_.hom_ext
  intro i j
  exact WordMesh.hom_eq_zero_of_not_le G Q hAlt
    (not_le_of_gt hxy) (f i j)

/-- The ordered vertex blocks of every additive-hull object are directed. -/
theorem vertexBlocks_pairwise
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (N : Category (K := K) G Q hAlt) :
    (List.ofFn (fun x : Fin Q.length ↦
      vertexBlock (K := K) G Q hAlt N x)).Pairwise NoBackward := by
  rw [List.pairwise_ofFn]
  intro i j hij
  exact vertexBlock_noBackward G Q hAlt N hij

/-- The vertex-fiber decomposition supplies the abstract directed-block
interface for the additive hull. -/
def directedBlockDecomposition
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    DirectedBlockDecomposition (C := Category (K := K) G Q hAlt) where
  blocks N := List.ofFn (fun x : Fin Q.length ↦
    vertexBlock (K := K) G Q hAlt N x)
  decompositionIso N := matrixIsoIteratedVertexBlocks (K := K) G Q hAlt N
  directed N := vertexBlocks_pairwise G Q hAlt N
  blockSplit N B hB := by
    rw [List.mem_ofFn'] at hB
    obtain ⟨x, rfl⟩ := hB
    intro p hp
    exact split_homogeneous_idempotent G Q hAlt x
      (vertexFiber (K := K) G Q hAlt N x) p hp

/-- The additive hull of the finite directed word mesh category is
idempotent complete. -/
theorem category_isIdempotentComplete
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    IsIdempotentComplete (Category (K := K) G Q hAlt) :=
  isIdempotentComplete_of_directedBlockDecomposition
    (directedBlockDecomposition (K := K) G Q hAlt)

instance categoryIsIdempotentComplete
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q) :
    IsIdempotentComplete (Category (K := K) G Q hAlt) :=
  category_isIdempotentComplete G Q hAlt

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
