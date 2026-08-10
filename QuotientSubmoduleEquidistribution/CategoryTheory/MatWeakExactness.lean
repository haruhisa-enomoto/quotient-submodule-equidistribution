import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaTauSequence
import QuotientSubmoduleEquidistribution.CategoryTheory.LinearMat

/-!
# Weak exactness in finite matrix additive hulls

Exactness against every singleton source (respectively singleton target)
extends rowwise (respectively columnwise) to a weak kernel (respectively
weak cokernel) in `Mat_ C`.  These lemmas isolate the finite-matrix transport
used by the abstract word-mesh category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.Iyama

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Exactness of a matrix short complex against every singleton source is
enough to make its first map a weak kernel of its second map. -/
theorem mat_isWeakKernel_of_exact_embedding
    (S : ShortComplex (Mat_ C))
    (hS : ∀ X : C,
      Function.Exact
        (fun l : (Mat_.embedding C).obj X ⟶ S.X₁ ↦ l ≫ S.f)
        (fun k : (Mat_.embedding C).obj X ⟶ S.X₂ ↦ k ≫ S.g)) :
    ShortComplex.IsWeakKernel S := by
  rw [ShortComplex.isWeakKernel_iff]
  intro W k hk
  let row (i : W.ι) : (Mat_.embedding C).obj (W.X i) ⟶ S.X₂ :=
    fun _ j ↦ k i j
  have hrow (i : W.ι) : row i ≫ S.g = 0 := by
    apply Mat_.hom_ext
    intro a j
    cases a
    have hij := congrFun (congrFun hk i) j
    exact hij
  choose lift hlift using fun i ↦ (hS (W.X i) (row i)).mp (hrow i)
  let l : W ⟶ S.X₁ := fun i j ↦ lift i PUnit.unit j
  refine ⟨l, ?_⟩
  apply Mat_.hom_ext
  intro i j
  have hij := congrFun (congrFun (hlift i) PUnit.unit) j
  exact hij

/-- Exactness of a matrix short complex against every singleton target is
enough to make its second map a weak cokernel of its first map. -/
theorem mat_isWeakCokernel_of_exact_embedding
    (S : ShortComplex (Mat_ C))
    (hS : ∀ X : C,
      Function.Exact
        (fun l : S.X₃ ⟶ (Mat_.embedding C).obj X ↦ S.g ≫ l)
        (fun k : S.X₂ ⟶ (Mat_.embedding C).obj X ↦ S.f ≫ k)) :
    ShortComplex.IsWeakCokernel S := by
  rw [ShortComplex.isWeakCokernel_iff]
  intro W k hk
  let column (j : W.ι) : S.X₂ ⟶ (Mat_.embedding C).obj (W.X j) :=
    fun i _ ↦ k i j
  have hcolumn (j : W.ι) : S.f ≫ column j = 0 := by
    apply Mat_.hom_ext
    intro i b
    cases b
    have hij := congrFun (congrFun hk i) j
    exact hij
  choose lift hlift using fun j ↦ (hS (W.X j) (column j)).mp (hcolumn j)
  let l : S.X₃ ⟶ W := fun i j ↦ lift j i PUnit.unit
  refine ⟨l, ?_⟩
  apply Mat_.hom_ext
  intro i j
  have hij := congrFun (congrFun (hlift j) i) PUnit.unit
  exact hij

end QuotientSubmoduleEquidistribution.Iyama
