import QuotientSubmoduleEquidistribution.RepresentationDirected.HomBiproductFinrank
import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts

/-!
# Reindexing multiplicity biproducts

These isomorphisms split one label's copies from a finite multiplicity
biproduct.  The final form is the associativity/reindexing step required by
the directed effective-lifting induction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe uI uJ uK uC vC

variable {I : Type uI} [DecidableEq I]

private def eraseForward
    (S : Finset I) {i : I} (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a)
    (p : MultiplicityIndex S n) :
    MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) := by
  by_cases hpi : p.1.1 = i
  · exact Sum.inr (Fin.cast (congrArg n hpi) p.2)
  · exact Sum.inl
      ⟨⟨p.1.1, Finset.mem_erase.mpr ⟨hpi, p.1.2⟩⟩,
        Fin.cast (hcount p.1.1
          (Finset.mem_erase.mpr ⟨hpi, p.1.2⟩)).symm p.2⟩

private def eraseBackward
    (S : Finset I) {i : I} (hi : i ∈ S)
    (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a) :
    MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) →
      MultiplicityIndex S n
  | Sum.inl p =>
      ⟨⟨p.1.1, (Finset.mem_erase.mp p.1.2).2⟩,
        Fin.cast (hcount p.1.1 p.1.2) p.2⟩
  | Sum.inr p => ⟨⟨i, hi⟩, p⟩

/-- The multiplicity index on `S` is the disjoint union of the index on
`S.erase i` and the copies belonging to `i`. -/
def multiplicityIndexEraseEquiv
    (S : Finset I) {i : I} (hi : i ∈ S)
    (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a) :
    MultiplicityIndex S n ≃
      MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) where
  toFun := eraseForward S n n' hcount
  invFun := eraseBackward S hi n n' hcount
  left_inv p := by
    by_cases hpi : p.1.1 = i
    · subst i
      simp [eraseForward, eraseBackward]
    · simp [eraseForward, eraseBackward, hpi]
  right_inv p := by
    cases p with
    | inl p =>
        have hpi : p.1.1 ≠ i := (Finset.mem_erase.mp p.1.2).1
        simp [eraseForward, eraseBackward, hpi]
    | inr p => simp [eraseForward, eraseBackward]

section BiproductSum

variable {J : Type uJ} {K : Type uK} [Fintype J] [Fintype K]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- A biproduct indexed by a sum type is the binary biproduct of its two
indexed pieces. -/
def biproductSumIso (X : J → C) (Y : K → C) :
    (⨁ fun p : J ⊕ K => Sum.elim X Y p) ≅
      biprod (⨁ X) (⨁ Y) := by
  let h : IsLimit
      (Fan.mk (biprod (⨁ X) (⨁ Y))
        (Fan.combPairHoms
          (biproduct.bicone X).toCone
          (biproduct.bicone Y).toCone
          (BinaryBiproduct.bicone (⨁ X) (⨁ Y)).toCone)) :=
    Fan.combPairIsLimit
      (biproduct.isLimit X)
      (biproduct.isLimit Y)
      (BinaryBiproduct.isLimit (⨁ X) (⨁ Y))
  exact (h.conePointUniqueUpToIso
    (biproduct.isLimit (fun p : J ⊕ K => Sum.elim X Y p))).symm

end BiproductSum

section MultiplicityBiproductErase

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- Split off the copies belonging to one support index, while replacing
the multiplicities on the erased support by pointwise equal ones. -/
def multiplicityBiproductEraseIso
    (X : I → C) (S : Finset I) {i : I} (hi : i ∈ S)
    (n n' : I → ℕ)
    (hcount : ∀ a, a ∈ S.erase i → n' a = n a) :
    multiplicityBiproduct X S n ≅
      biprod (multiplicityBiproduct X (S.erase i) n')
        (⨁ fun _ : Fin (n i) => X i) := by
  let e := multiplicityIndexEraseEquiv S hi n n' hcount
  let X' : MultiplicityIndex (S.erase i) n' → C := fun p => X p.1
  let Xi : Fin (n i) → C := fun _ => X i
  let Xsum : MultiplicityIndex (S.erase i) n' ⊕ Fin (n i) → C :=
    Sum.elim X' Xi
  let reindex : multiplicityBiproduct X S n ≅ ⨁ Xsum := by
    change (⨁ fun p : MultiplicityIndex S n => X p.1) ≅ ⨁ Xsum
    exact biproduct.whiskerEquiv e (fun p => by
      by_cases hpi : p.1.1 = i
      · subst i
        simpa [e, Xsum, X', Xi, multiplicityIndexEraseEquiv,
          eraseForward] using (Iso.refl (X p.1.1))
      · simpa [e, Xsum, X', Xi, multiplicityIndexEraseEquiv,
          eraseForward, hpi] using (Iso.refl (X p.1.1)))
  exact reindex.trans (biproductSumIso X' Xi)

/-- Enlarging `D` by a fresh index removes precisely that label from the
complementary support and splits off its copies. -/
def multiplicityBiproductConsIso
    [Fintype I] (X : I → C) (D : Finset I) {i : I} (hi : i ∉ D)
    (n n' : I → ℕ)
    (hcount : ∀ a, a ∉ D.cons i hi → n' a = n a) :
    multiplicityBiproduct X (Finset.univ \ D) n ≅
      biprod
        (multiplicityBiproduct X (Finset.univ \ D.cons i hi) n')
        (⨁ fun _ : Fin (n i) => X i) := by
  have hiSupport : i ∈ Finset.univ \ D := by simp [hi]
  have hsupport : (Finset.univ \ D).erase i =
      Finset.univ \ D.cons i hi := by
    ext a
    simp
  have hcountErase : ∀ a, a ∈ (Finset.univ \ D).erase i → n' a = n a := by
    intro a ha
    apply hcount a
    have ha' := Finset.mem_erase.mp ha
    have haNotD := (Finset.mem_sdiff.mp ha'.2).2
    simp [ha'.1, haNotD]
  simpa only [hsupport] using
    (multiplicityBiproductEraseIso X (Finset.univ \ D) hiSupport n n' hcountErase)

end MultiplicityBiproductErase

end QuotientSubmoduleEquidistribution.RepresentationDirected
