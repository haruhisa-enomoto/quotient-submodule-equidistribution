import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection

/-!
# Splitting finite scalar-matrix idempotents

An idempotent matrix over a field splits through a basis of the range of its
associated linear projection.  Hence Mathlib's category `Mat K` is
idempotent complete.  A second form chooses a `Fin n` basis so that the
splitting index remains in universe zero.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Module

namespace QuotientSubmoduleEquidistribution.CategoryTheory.MatrixIdempotent

universe u

variable {K : Type u} [Field K]

/-- A linear map written as a morphism in Mathlib's row-source matrix
category.  The transpose corrects the convention of `LinearMap.toMatrix`. -/
def matrixOfLinearMap {X Y : Mat K}
    (f : (X → K) →ₗ[K] (Y → K)) : X ⟶ Y :=
  by
    classical
    letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
    letI : Fintype Y.obj := @FintypeCat.fintype (show FintypeCat from Y)
    letI : DecidableEq X.obj := Classical.decEq _
    letI : DecidableEq Y.obj := Classical.decEq _
    exact Matrix.transpose
      (LinearMap.toMatrix (Pi.basisFun K X) (Pi.basisFun K Y) f)

@[simp]
lemma matrixOfLinearMap_id (X : Mat K) :
    matrixOfLinearMap (LinearMap.id (R := K) (M := X → K)) = 𝟙 X := by
  classical
  letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
  letI : DecidableEq X.obj := Classical.decEq _
  change Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K X) (Pi.basisFun K X)
    (LinearMap.id (R := K) (M := X → K))) = 1
  rw [LinearMap.toMatrix_id, Matrix.transpose_one]

@[simp]
lemma matrixOfLinearMap_comp {X Y Z : Mat K}
    (f : (X → K) →ₗ[K] (Y → K))
    (g : (Y → K) →ₗ[K] (Z → K)) :
    matrixOfLinearMap f ≫ matrixOfLinearMap g =
      matrixOfLinearMap (g.comp f) := by
  classical
  letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
  letI : Fintype Y.obj := @FintypeCat.fintype (show FintypeCat from Y)
  letI : Fintype Z.obj := @FintypeCat.fintype (show FintypeCat from Z)
  letI : DecidableEq X.obj := Classical.decEq _
  letI : DecidableEq Y.obj := Classical.decEq _
  letI : DecidableEq Z.obj := Classical.decEq _
  change
    Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K X) (Pi.basisFun K Y) f) *
      Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K Y) (Pi.basisFun K Z) g) =
    Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K X) (Pi.basisFun K Z) (g.comp f))
  have h := congrArg Matrix.transpose
    (LinearMap.toMatrix_comp (Pi.basisFun K X) (Pi.basisFun K Y)
      (Pi.basisFun K Z) g f)
  rw [Matrix.transpose_mul] at h
  exact h.symm

/-- A row-source matrix regarded as a linear map, again correcting conventions
by transposition. -/
def linearMapOfMatrix {X Y : Mat K} (p : X ⟶ Y) :
    (X → K) →ₗ[K] (Y → K) := by
  classical
  letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
  letI : Fintype Y.obj := @FintypeCat.fintype (show FintypeCat from Y)
  letI : DecidableEq X.obj := Classical.decEq _
  letI : DecidableEq Y.obj := Classical.decEq _
  exact Matrix.toLin (Pi.basisFun K X) (Pi.basisFun K Y) (Matrix.transpose p)

/-- A row-source matrix is recovered from the linear map represented by its
transpose. -/
@[simp]
lemma matrixOfLinearMap_toLin_transpose {X Y : Mat K} (p : X ⟶ Y) :
    matrixOfLinearMap (linearMapOfMatrix p) = p := by
  classical
  letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
  letI : Fintype Y.obj := @FintypeCat.fintype (show FintypeCat from Y)
  letI : DecidableEq X.obj := Classical.decEq _
  letI : DecidableEq Y.obj := Classical.decEq _
  unfold matrixOfLinearMap linearMapOfMatrix
  rw [LinearMap.toMatrix_toLin, Matrix.transpose_transpose]

/-- Every idempotent matrix over a field splits through a matrix whose index
type is a basis of the range of the associated linear projection. -/
theorem split_matrix_idempotent (X : Mat K) (p : X ⟶ X)
    (hp : p ≫ p = p) :
    ∃ (Y : Mat K) (i : Y ⟶ X) (e : X ⟶ Y),
      i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  classical
  letI : Fintype X.obj := @FintypeCat.fintype (show FintypeCat from X)
  letI : DecidableEq X.obj := Classical.decEq _
  let T : (X → K) →ₗ[K] (X → K) := linearMapOfMatrix p
  have hpMul : (show Matrix X X K from p) * (show Matrix X X K from p) = p := hp
  have hpTranspose : Matrix.transpose p * Matrix.transpose p = Matrix.transpose p := by
    rw [← Matrix.transpose_mul, hpMul]
  have hT : T.comp T = T := by
    dsimp [T, linearMapOfMatrix]
    rw [← Matrix.toLin_mul, hpTranspose]
  let W : Submodule K (X → K) := LinearMap.range T
  let bW : Basis (Basis.ofVectorSpaceIndex K W) K W := Basis.ofVectorSpace K W
  let Y : Mat K := FintypeCat.of (Basis.ofVectorSpaceIndex K W)
  letI : Fintype Y.obj := @FintypeCat.fintype (show FintypeCat from Y)
  letI : DecidableEq Y.obj := Classical.decEq _
  let incl : W →ₗ[K] (X → K) := W.subtype
  let proj : (X → K) →ₗ[K] W := T.rangeRestrict
  let coord : (Y → K) ≃ₗ[K] W := bW.equivFun.symm
  let iLin : (Y → K) →ₗ[K] (X → K) := incl.comp coord.toLinearMap
  let eLin : (X → K) →ₗ[K] (Y → K) := coord.symm.toLinearMap.comp proj
  have hproj_incl : proj.comp incl = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rcases w.property with ⟨x, hx⟩
    change T (w : X → K) = w
    calc
      T (w : X → K) = T (T x) := congrArg T hx.symm
      _ = (T.comp T) x := rfl
      _ = T x := LinearMap.congr_fun hT x
      _ = w := hx
  have hincl_proj : incl.comp proj = T := by
    rfl
  have he_i : eLin.comp iLin = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change coord.symm (proj (incl (coord x))) = x
    have hw : proj (incl (coord x)) = coord x :=
      LinearMap.congr_fun hproj_incl (coord x)
    rw [hw]
    exact coord.symm_apply_apply x
  have hi_e : iLin.comp eLin = T := by
    apply LinearMap.ext
    intro x
    change incl (coord (coord.symm (proj x))) = T x
    rw [coord.apply_symm_apply]
    exact LinearMap.congr_fun hincl_proj x
  refine ⟨Y, matrixOfLinearMap iLin, matrixOfLinearMap eLin, ?_, ?_⟩
  · rw [matrixOfLinearMap_comp, he_i, matrixOfLinearMap_id]
  · rw [matrixOfLinearMap_comp, hi_e]
    exact matrixOfLinearMap_toLin_transpose p

/-- The category of finite matrices over a field is idempotent complete. -/
instance mat_isIdempotentComplete : IsIdempotentComplete (Mat K) where
  idempotents_split := split_matrix_idempotent

/-- A linear map between small coordinate spaces, in row-source matrix
convention.  Unlike `matrixOfLinearMap`, the index types stay in universe
zero even when the coefficient field is large. -/
def smallMatrixOfLinearMap {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (f : (I → K) →ₗ[K] (J → K)) : Matrix I J K :=
  Matrix.transpose
    (LinearMap.toMatrix (Pi.basisFun K I) (Pi.basisFun K J) f)

@[simp]
lemma smallMatrixOfLinearMap_id (I : Type) [Fintype I] [DecidableEq I] :
    smallMatrixOfLinearMap (LinearMap.id (R := K) (M := I → K)) = 1 := by
  unfold smallMatrixOfLinearMap
  rw [LinearMap.toMatrix_id, Matrix.transpose_one]

@[simp]
lemma smallMatrixOfLinearMap_comp
    {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [DecidableEq I] [DecidableEq J] [DecidableEq H]
    (f : (I → K) →ₗ[K] (J → K))
    (g : (J → K) →ₗ[K] (H → K)) :
    smallMatrixOfLinearMap f * smallMatrixOfLinearMap g =
      smallMatrixOfLinearMap (g.comp f) := by
  change
    Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K I) (Pi.basisFun K J) f) *
      Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K J) (Pi.basisFun K H) g) =
    Matrix.transpose (LinearMap.toMatrix (Pi.basisFun K I) (Pi.basisFun K H) (g.comp f))
  have h := congrArg Matrix.transpose
    (LinearMap.toMatrix_comp (Pi.basisFun K I) (Pi.basisFun K J)
      (Pi.basisFun K H) g f)
  rw [Matrix.transpose_mul] at h
  exact h.symm

/-- A small row-source matrix as a linear map, again correcting conventions
by transposition. -/
def smallLinearMapOfMatrix {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (p : Matrix I J K) : (I → K) →ₗ[K] (J → K) :=
  Matrix.toLin (Pi.basisFun K I) (Pi.basisFun K J) (Matrix.transpose p)

@[simp]
lemma smallMatrixOfLinearMap_toLin_transpose
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p : Matrix I J K) :
    smallMatrixOfLinearMap (smallLinearMapOfMatrix p) = p := by
  unfold smallMatrixOfLinearMap smallLinearMapOfMatrix
  rw [LinearMap.toMatrix_toLin, Matrix.transpose_transpose]

/-- Every idempotent matrix with universe-zero index type splits through a
matrix indexed by `Fin n`.  Thus the splitting index remains small even when
the coefficient field lives in a higher universe. -/
theorem split_small_matrix_idempotent
    (I : Type) [Fintype I] (p : Matrix I I K)
    (hp : p * p = p) :
    ∃ (n : ℕ) (i : Matrix (Fin n) I K) (e : Matrix I (Fin n) K),
      i * e = 1 ∧ e * i = p := by
  classical
  let T : (I → K) →ₗ[K] (I → K) := smallLinearMapOfMatrix p
  have hpTranspose : Matrix.transpose p * Matrix.transpose p = Matrix.transpose p := by
    rw [← Matrix.transpose_mul, hp]
  have hT : T.comp T = T := by
    dsimp [T, smallLinearMapOfMatrix]
    rw [← Matrix.toLin_mul, hpTranspose]
  let W : Submodule K (I → K) := LinearMap.range T
  let bW : Basis (Fin (finrank K W)) K W := Module.finBasis K W
  let incl : W →ₗ[K] (I → K) := W.subtype
  let proj : (I → K) →ₗ[K] W := T.rangeRestrict
  let coord : (Fin (finrank K W) → K) ≃ₗ[K] W := bW.equivFun.symm
  let iLin : (Fin (finrank K W) → K) →ₗ[K] (I → K) :=
    incl.comp coord.toLinearMap
  let eLin : (I → K) →ₗ[K] (Fin (finrank K W) → K) :=
    coord.symm.toLinearMap.comp proj
  have hproj_incl : proj.comp incl = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rcases w.property with ⟨x, hx⟩
    change T (w : I → K) = w
    calc
      T (w : I → K) = T (T x) := congrArg T hx.symm
      _ = (T.comp T) x := rfl
      _ = T x := LinearMap.congr_fun hT x
      _ = w := hx
  have hincl_proj : incl.comp proj = T := by
    rfl
  have he_i : eLin.comp iLin = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change coord.symm (proj (incl (coord x))) = x
    have hw : proj (incl (coord x)) = coord x :=
      LinearMap.congr_fun hproj_incl (coord x)
    rw [hw]
    exact coord.symm_apply_apply x
  have hi_e : iLin.comp eLin = T := by
    apply LinearMap.ext
    intro x
    change incl (coord (coord.symm (proj x))) = T x
    rw [coord.apply_symm_apply]
    exact LinearMap.congr_fun hincl_proj x
  refine ⟨finrank K W, smallMatrixOfLinearMap iLin,
    smallMatrixOfLinearMap eLin, ?_, ?_⟩
  · rw [smallMatrixOfLinearMap_comp, he_i, smallMatrixOfLinearMap_id]
  · rw [smallMatrixOfLinearMap_comp, hi_e]
    exact smallMatrixOfLinearMap_toLin_transpose p

end QuotientSubmoduleEquidistribution.CategoryTheory.MatrixIdempotent
