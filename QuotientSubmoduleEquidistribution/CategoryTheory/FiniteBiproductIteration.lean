import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.List.OfFn

import QuotientSubmoduleEquidistribution.CategoryTheory.DirectedIdempotentCompletion

/-!
# Finite biproducts as ordered iterated binary biproducts
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.CategoryTheory.DirectedIdempotent

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C] [HasZeroObject C]

/-- Split a biproduct indexed by `Fin (n + 1)` into its first summand and
the biproduct indexed by the remaining `Fin n`. -/
def finSuccBiproductIso {n : ℕ} (F : Fin (n + 1) → C) :
    (⨁ F) ≅ (F 0 ⊞ (⨁ fun i : Fin n ↦ F i.succ)) := by
  let T : Fin n → C := fun i ↦ F i.succ
  let q : (⨁ F) ⟶ (⨁ T) :=
    biproduct.lift fun i : Fin n ↦ biproduct.π F i.succ
  let r : (⨁ T) ⟶ (⨁ F) :=
    biproduct.desc fun i : Fin n ↦ biproduct.ι F i.succ
  have hhead_q : biproduct.ι F 0 ≫ q = 0 := by
    apply biproduct.hom_ext
    intro i
    rw [Category.assoc, biproduct.lift_π, zero_comp]
    exact biproduct.ι_π_ne F (Fin.succ_ne_zero i).symm
  have htail_q (i : Fin n) : biproduct.ι F i.succ ≫ q = biproduct.ι T i := by
    apply biproduct.hom_ext
    intro j
    by_cases h : i = j
    · subst h
      simp [q, T, Category.assoc]
    · rw [Category.assoc, biproduct.lift_π,
          biproduct.ι_π_ne F (fun hs ↦ h (Fin.succ_inj.mp hs)),
          biproduct.ι_π_ne T h]
  have hr_head : r ≫ biproduct.π F 0 = 0 := by
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, biproduct.ι_desc, comp_zero]
    exact biproduct.ι_π_ne F (Fin.succ_ne_zero i)
  have hr_tail (i : Fin n) : r ≫ biproduct.π F i.succ = biproduct.π T i := by
    apply biproduct.hom_ext'
    intro j
    by_cases h : j = i
    · subst h
      simp [r, T]
    · rw [← Category.assoc, biproduct.ι_desc,
          biproduct.ι_π_ne F (fun hs ↦ h (Fin.succ_inj.mp hs)),
          biproduct.ι_π_ne T h]
  have hrq : r ≫ q = 𝟙 (⨁ T) := by
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, biproduct.ι_desc, htail_q, Category.comp_id]
  have hhead_qr : biproduct.ι F 0 ≫ q ≫ r = 0 := by
    rw [← Category.assoc, hhead_q, zero_comp]
  have htail_qr (i : Fin n) :
      biproduct.ι F i.succ ≫ q ≫ r = biproduct.ι F i.succ := by
    rw [← Category.assoc, htail_q, biproduct.ι_desc]
  exact
    { hom := biprod.lift (biproduct.π F 0) q
      inv := biprod.desc (biproduct.ι F 0) r
      hom_inv_id := by
        apply biproduct.hom_ext'
        intro j
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simpa using hhead_qr
        · simpa using htail_qr i
      inv_hom_id := by
        apply biprod.hom_ext'
        · apply biprod.hom_ext
          · simp
          · simpa [Category.assoc] using hhead_q
        · apply biprod.hom_ext
          · simpa [Category.assoc] using hr_head
          · simpa [Category.assoc] using hrq }

/-- A biproduct over `Fin n` is canonically isomorphic to the right-associated
binary biproduct of the corresponding ordered list. -/
def finBiproductIsoIterated : ∀ {n : ℕ} (F : Fin n → C),
    (⨁ F) ≅ iteratedBiprod (List.ofFn F)
  | 0, F =>
      { hom := 0
        inv := 0
        hom_inv_id := by
          apply biproduct.hom_ext
          intro j
          exact Fin.elim0 j
        inv_hom_id := (isZero_zero C).eq_of_src _ _ }
  | n + 1, F => by
      rw [List.ofFn_succ]
      exact finSuccBiproductIso F ≪≫
        biprod.mapIso (Iso.refl _) (finBiproductIsoIterated (fun i : Fin n ↦ F i.succ))

end QuotientSubmoduleEquidistribution.CategoryTheory.DirectedIdempotent
