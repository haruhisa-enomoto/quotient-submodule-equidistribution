import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoRankCore

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.YonedaExtReflection

universe w v u

variable {K : Type u} [Field K]
  {C : Type v} [Category.{w} C] [Abelian C] [Linear K C]
  [HasFiniteBiproducts C]

/-- The scalar matrix `P` acting on a biproduct of copies of `X`. -/
def scalarBiproductEnd
    {I : Type} [Fintype I] (X : C) (P : Matrix I I K) :
    (⨁ fun _ : I ↦ X) ⟶ (⨁ fun _ : I ↦ X) :=
  biproduct.matrix fun i j ↦ P j i • 𝟙 X

theorem scalarBiproductEnd_comp
    {I : Type} [Fintype I] (X : C) (P Q : Matrix I I K) :
    scalarBiproductEnd X P ≫ scalarBiproductEnd X Q =
      scalarBiproductEnd X (Q * P) := by
  classical
  apply (biproduct.matrixEquiv (f := fun _ : I ↦ X)
    (g := fun _ : I ↦ X)).injective
  funext i j
  change
    biproduct.components
        (scalarBiproductEnd X P ≫ scalarBiproductEnd X Q) i j =
      biproduct.components (scalarBiproductEnd X (Q * P)) i j
  simp only [biproduct.components, scalarBiproductEnd,
    ← Category.assoc, biproduct.ι_matrix, biproduct.matrix_π]
  rw [biproduct.lift_matrix]
  simp only [biproduct.lift_π, Matrix.mul_apply, Category.comp_id,
    Linear.comp_smul, smul_smul, biproduct.ι_desc]
  change
    (∑ x ∈ Finset.univ, (Q j x * P x i) • 𝟙 X) =
      (∑ x ∈ Finset.univ, Q j x * P x i) • 𝟙 X
  rw [Finset.sum_smul]

theorem scalarBiproductEnd_zero
    {I : Type} [Fintype I] (X : C) :
    scalarBiproductEnd X (0 : Matrix I I K) = 0 := by
  classical
  ext i j
  simp [scalarBiproductEnd]

theorem scalarBiproductEnd_one
    {I : Type} [Fintype I] [DecidableEq I] (X : C) :
    scalarBiproductEnd X (1 : Matrix I I K) = 𝟙 _ := by
  classical
  apply (biproduct.matrixEquiv (f := fun _ : I ↦ X)
    (g := fun _ : I ↦ X)).injective
  funext i j
  change
    biproduct.components (scalarBiproductEnd X 1) i j =
      biproduct.components
        (𝟙 (⨁ fun _ : I ↦ X)) i j
  simp only [scalarBiproductEnd, biproduct.matrix_components]
  by_cases h : i = j
  · subst j
    simp [biproduct.components]
  · simp [h, Ne.symm h, biproduct.components]

/--
On a nonzero object, the categorical action of a scalar matrix on an
isotypic biproduct remembers the matrix.
-/
theorem scalarBiproductEnd_injective
    {I : Type} [Fintype I] (X : C) (hX : 𝟙 X ≠ 0) :
    Function.Injective
      (scalarBiproductEnd (K := K) X :
        Matrix I I K →
          ((⨁ fun _ : I ↦ X) ⟶ (⨁ fun _ : I ↦ X))) := by
  classical
  intro P Q hPQ
  ext i j
  have hcomponent :=
    congrArg
      (fun f ↦ biproduct.components f j i)
      hPQ
  simp only [scalarBiproductEnd, biproduct.matrix_components] at hcomponent
  have hsmul :
      (P i j - Q i j) • 𝟙 X = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hcomponent
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hX)

theorem scalarBiproductEnd_eq_zero_iff
    {I : Type} [Fintype I] (X : C) (hX : 𝟙 X ≠ 0)
    (P : Matrix I I K) :
    scalarBiproductEnd X P = 0 ↔ P = 0 := by
  classical
  constructor
  · intro hP
    apply scalarBiproductEnd_injective X hX
    simpa [scalarBiproductEnd_zero] using hP
  · rintro rfl
    exact scalarBiproductEnd_zero X

theorem scalarBiproductEnd_eq_id_iff
    {I : Type} [Fintype I] [DecidableEq I]
    (X : C) (hX : 𝟙 X ≠ 0) (P : Matrix I I K) :
    scalarBiproductEnd X P = 𝟙 _ ↔ P = 1 := by
  classical
  constructor
  · intro hP
    apply scalarBiproductEnd_injective X hX
    simpa [scalarBiproductEnd_one] using hP
  · rintro rfl
    exact scalarBiproductEnd_one X

variable [HasExt C]

/-- The `(i,j)` component of an extension between two finite biproducts. -/
def biproductExtComponent
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1)
    (i : I) (j : J) : Ext X Y 1 :=
  (Ext.mk₀ (biproduct.ι (fun _ : I ↦ X) i)).comp
    (ξ.comp (Ext.mk₀ (biproduct.π (fun _ : J ↦ Y) j))
      (add_zero 1))
    (zero_add 1)

theorem ext_eq_of_biproductExtComponent_eq
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C)
    {ξ η : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1}
    (h :
      ∀ i j,
        biproductExtComponent X Y ξ i j =
          biproductExtComponent X Y η i j) :
    ξ = η := by
  apply
    (Ext.biproductAddEquiv
      (biproduct.isBilimit fun _ : I ↦ X)
      (⨁ fun _ : J ↦ Y) 1).injective
  funext i
  apply
    (Ext.addEquivBiproduct X
      (biproduct.isBilimit fun _ : J ↦ Y) 1).injective
  funext j
  change
    ((Ext.mk₀ (biproduct.ι (fun _ : I ↦ X) i)).comp ξ
        (zero_add 1)).comp
          (Ext.mk₀ (biproduct.π (fun _ : J ↦ Y) j))
          (add_zero 1) =
      ((Ext.mk₀ (biproduct.ι (fun _ : I ↦ X) i)).comp η
        (zero_add 1)).comp
          (Ext.mk₀ (biproduct.π (fun _ : J ↦ Y) j))
          (add_zero 1)
  rw [Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero]
  exact h i j

theorem biproductExtComponent_post_scalarBiproductEnd
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1)
    (Q : Matrix J J K) (i : I) (j : J) :
    biproductExtComponent X Y
        (ξ.comp (Ext.mk₀ (scalarBiproductEnd Y Q)) (add_zero 1))
        i j =
      ∑ k, Q j k •
        biproductExtComponent X Y ξ i k := by
  classical
  simp only [biproductExtComponent,
    Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  rw [scalarBiproductEnd, biproduct.matrix_π,
    biproduct.desc_eq, Ext.mk₀_sum, Ext.comp_sum]
  rw [Ext.comp_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Linear.comp_smul, Category.comp_id,
    Ext.mk₀_smul (R := K), Ext.comp_smul, Ext.comp_smul]

theorem biproductExtComponent_pre_scalarBiproductEnd
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1)
    (P : Matrix I I K) (i : I) (j : J) :
    biproductExtComponent X Y
        ((Ext.mk₀ (scalarBiproductEnd X P)).comp ξ (zero_add 1))
        i j =
      ∑ k, P k i • biproductExtComponent X Y ξ k j := by
  classical
  simp only [biproductExtComponent,
    Ext.comp_assoc_of_third_deg_zero]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [scalarBiproductEnd, biproduct.ι_matrix,
    biproduct.lift_eq, Ext.mk₀_sum, Ext.sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Linear.smul_comp, Category.id_comp,
    Ext.mk₀_smul (R := K), Ext.smul_comp]

/--
Every finite-dimensional vector space of dimension at most one admits an
injective linear map to the ground field. This handles the zero-dimensional
case without choosing a nonexistent basis vector.
-/
theorem exists_injective_linearMap_to_field_of_finrank_le_one
    {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (hE : Module.finrank K E ≤ 1) :
    ∃ ℓ : E →ₗ[K] K, Function.Injective ℓ := by
  have hzero_or_one :
      Module.finrank K E = 0 ∨ Module.finrank K E = 1 := by
    omega
  rcases hzero_or_one with hzero | hone
  · haveI : Subsingleton E :=
      Module.finrank_zero_iff.mp hzero
    exact ⟨0, fun x y _ ↦ Subsingleton.elim x y⟩
  · let e : E ≃ₗ[K] K :=
      Classical.choice
        (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
          (by simpa using hone))
    exact ⟨e, e.injective⟩

/-- Scalarize the matrix of an extension using an injective functional on
the common entry `Ext¹`-space. -/
def scalarizedExtMatrix
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C) (ℓ : Ext X Y 1 →ₗ[K] K)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1) :
    Matrix J I K :=
  fun j i ↦ ℓ (biproductExtComponent X Y ξ i j)

/--
A matrix commutation relation after injective scalarization is exactly the
`Ext¹` compatibility needed to lift the corresponding scalar endpoint
endomorphisms.
-/
theorem ext_compatibility_of_scalarized_matrix_commute
    {I J : Type} [Fintype I] [Fintype J]
    (X Y : C) (ℓ : Ext X Y 1 →ₗ[K] K)
    (hℓ : Function.Injective ℓ)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1)
    (P : Matrix I I K) (Q : Matrix J J K)
    (hcomm :
      Q * scalarizedExtMatrix X Y ℓ ξ =
        scalarizedExtMatrix X Y ℓ ξ * P) :
    ξ.comp (Ext.mk₀ (scalarBiproductEnd Y Q)) (add_zero 1) =
      (Ext.mk₀ (scalarBiproductEnd X P)).comp ξ (zero_add 1) := by
  classical
  apply ext_eq_of_biproductExtComponent_eq X Y
  intro i j
  rw [biproductExtComponent_post_scalarBiproductEnd,
    biproductExtComponent_pre_scalarBiproductEnd]
  apply hℓ
  simp only [map_sum, map_smul]
  simpa only [Matrix.mul_apply, scalarizedExtMatrix, smul_eq_mul,
    mul_comm] using congrFun (congrFun hcomm j) i

/-- The linear map represented by the scalarized `Ext¹`-matrix. -/
def scalarizedExtLinearMap
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (X Y : C) (ℓ : Ext X Y 1 →ₗ[K] K)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1) :
    (I → K) →ₗ[K] (J → K) :=
  Matrix.toLin' (scalarizedExtMatrix X Y ℓ ξ)

/--
If compatible idempotents on the two biproduct endpoints of an extension are
trivial, then its injectively scalarized matrix is an idempotent-indecomposable
one-arrow representation.

The endpoint hypothesis is precisely what the Yoneda reflection plus Fitting
argument supplies for the radical sequence of an indecomposable finite-length
module.
-/
theorem scalarizedExtLinearMap_isIdempotentIndecomposable
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X Y : C) (hX : 𝟙 X ≠ 0) (hY : 𝟙 Y ≠ 0)
    (ℓ : Ext X Y 1 →ₗ[K] K) (hℓ : Function.Injective ℓ)
    (ξ : Ext (⨁ fun _ : I ↦ X) (⨁ fun _ : J ↦ Y) 1)
    (hendpoint :
      ∀ (a₁ :
          (⨁ fun _ : J ↦ Y) ⟶ (⨁ fun _ : J ↦ Y))
        (a₃ :
          (⨁ fun _ : I ↦ X) ⟶ (⨁ fun _ : I ↦ X)),
        a₁ ≫ a₁ = a₁ →
        a₃ ≫ a₃ = a₃ →
        ξ.comp (Ext.mk₀ a₁) (add_zero 1) =
          (Ext.mk₀ a₃).comp ξ (zero_add 1) →
        (a₁ = 0 ∧ a₃ = 0) ∨
          (a₁ = 𝟙 _ ∧ a₃ = 𝟙 _)) :
    LoewyTwoRankCore.IsIdempotentIndecomposable
      (scalarizedExtLinearMap X Y ℓ ξ) := by
  classical
  intro p q hp hq hcomm
  let P : Matrix I I K := LinearMap.toMatrix' p
  let Q : Matrix J J K := LinearMap.toMatrix' q
  have hP : P * P = P := by
    simpa only [P, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hp
  have hQ : Q * Q = Q := by
    simpa only [Q, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hq
  have hPcat :
      scalarBiproductEnd X P ≫ scalarBiproductEnd X P =
        scalarBiproductEnd X P := by
    rw [scalarBiproductEnd_comp, hP]
  have hQcat :
      scalarBiproductEnd Y Q ≫ scalarBiproductEnd Y Q =
        scalarBiproductEnd Y Q := by
    rw [scalarBiproductEnd_comp, hQ]
  have hmatrix :
      Q * scalarizedExtMatrix X Y ℓ ξ =
        scalarizedExtMatrix X Y ℓ ξ * P := by
    simpa only [Q, P, scalarizedExtLinearMap,
      LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
      congrArg LinearMap.toMatrix' hcomm
  have hext :
      ξ.comp (Ext.mk₀ (scalarBiproductEnd Y Q)) (add_zero 1) =
        (Ext.mk₀ (scalarBiproductEnd X P)).comp ξ (zero_add 1) :=
    ext_compatibility_of_scalarized_matrix_commute
      X Y ℓ hℓ ξ P Q hmatrix
  rcases hendpoint
      (scalarBiproductEnd Y Q)
      (scalarBiproductEnd X P)
      hQcat hPcat hext with hzero | hone
  · left
    have hPzero : P = 0 :=
      (scalarBiproductEnd_eq_zero_iff X hX P).mp hzero.2
    have hQzero : Q = 0 :=
      (scalarBiproductEnd_eq_zero_iff Y hY Q).mp hzero.1
    constructor
    · apply LinearMap.toMatrix'.injective
      simpa only [P, map_zero] using hPzero
    · apply LinearMap.toMatrix'.injective
      simpa only [Q, map_zero] using hQzero
  · right
    have hPone : P = 1 :=
      (scalarBiproductEnd_eq_id_iff X hX P).mp hone.2
    have hQone : Q = 1 :=
      (scalarBiproductEnd_eq_id_iff Y hY Q).mp hone.1
    constructor
    · apply LinearMap.toMatrix'.injective
      simpa only [P, LinearMap.toMatrix'_id] using hPone
    · apply LinearMap.toMatrix'.injective
      simpa only [Q, LinearMap.toMatrix'_id] using hQone

end QuotientSubmoduleEquidistribution.YonedaExtReflection
