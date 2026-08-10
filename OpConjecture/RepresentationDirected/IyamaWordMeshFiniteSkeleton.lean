import OpConjecture.CategoryTheory.FiniteBiproductIteration
import OpConjecture.RepresentationDirected.IyamaWordMeshAdditiveHull

/-!
# The finite vertex skeleton of the word-mesh additive hull

This file proves that distinct word positions give nonisomorphic singleton
objects and that every indecomposable object in the additive hull is
isomorphic to one of those singleton vertices.

No concrete algebra, quiver instance, or module classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull

open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.CategoryTheory

universe uK uL v u

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-- Directed Hom vanishing passes from the raw word-mesh category to its
singleton objects in the additive hull. -/
theorem vertexHom_eq_zero_of_not_le
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x y : Fin Q.length} (hxy : ¬ x ≤ y)
    (f : vertexObj (K := K) G Q hAlt x ⟶
      vertexObj (K := K) G Q hAlt y) :
    f = 0 := by
  apply Mat_.hom_ext
  intro i j
  cases i
  cases j
  change f PUnit.unit PUnit.unit = 0
  exact WordMesh.hom_eq_zero_of_not_le G Q hAlt hxy
    (f PUnit.unit PUnit.unit)

/-- Distinct word positions give nonisomorphic singleton objects in the
additive hull. -/
theorem obj_skeletal
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    {x y : Fin Q.length}
    (h : Nonempty (vertexObj (K := K) G Q hAlt x ≅
      vertexObj (K := K) G Q hAlt y)) :
    x = y := by
  obtain ⟨e⟩ := h
  apply le_antisymm
  · by_contra hxy
    have hzero := vertexHom_eq_zero_of_not_le G Q hAlt hxy e.hom
    have hid : 𝟙 (vertexObj (K := K) G Q hAlt x) = 0 := by
      rw [← e.hom_inv_id, hzero, zero_comp]
    exact (vertexObj_indec (K := K) G Q hAlt x).1
      ((IsZero.iff_id_eq_zero _).mpr hid)
  · by_contra hyx
    have hzero := vertexHom_eq_zero_of_not_le G Q hAlt hyx e.inv
    have hid : 𝟙 (vertexObj (K := K) G Q hAlt y) = 0 := by
      rw [← e.inv_hom_id, hzero, zero_comp]
    exact (vertexObj_indec (K := K) G Q hAlt y).1
      ((IsZero.iff_id_eq_zero _).mpr hid)

/-- An indecomposable object which is a finite biproduct of nonzero objects
is isomorphic to one of those objects. -/
theorem exists_iso_summand_of_indec_iso_fin_biproduct
    {C : Type u} [CategoryTheory.Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C]
    {X : C} (hX : Indecomposable X)
    {n : ℕ} (F : Fin n → C) (hF : ∀ i, ¬ IsZero (F i))
    (e : X ≅ ⨁ F) :
    ∃ i : Fin n, Nonempty (X ≅ F i) := by
  cases n with
  | zero =>
      exfalso
      apply hX.1
      have hzero : IsZero (⨁ F) := by
        rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      exact hzero.of_iso e
  | succ n =>
      let d : X ≅ F 0 ⊞ (⨁ fun i : Fin n ↦ F i.succ) :=
        e ≪≫ DirectedIdempotent.finSuccBiproductIso F
      rcases hX.2 _ _ d with hhead | htail
      · exact False.elim (hF 0 hhead)
      · exact ⟨0, ⟨d ≪≫ (isoBiprodZero htail).symm⟩⟩

/-- Every indecomposable object of the word-mesh additive hull is
isomorphic to a singleton word vertex. -/
theorem obj_complete
    (G : SimpleGraph L) (Q : List L)
    (hAlt : HasInteriorAlternation G Q)
    (M : Category (K := K) G Q hAlt)
    (hM : Indecomposable M) :
    ∃ x : Fin Q.length,
      Nonempty (M ≅ vertexObj (K := K) G Q hAlt x) := by
  obtain ⟨n, label, ⟨e⟩⟩ :=
    exists_iso_fin_biproduct_vertexObj (K := K) G Q hAlt M
  obtain ⟨i, hi⟩ := exists_iso_summand_of_indec_iso_fin_biproduct
    hM (fun i ↦ vertexObj (K := K) G Q hAlt (label i))
    (fun i ↦ (vertexObj_indec (K := K) G Q hAlt (label i)).1)
    e
  exact ⟨label i, hi⟩

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
