import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.CategoryTheory.Simple
import OpConjecture.CategoryTheory.FiniteBiproductIteration
import OpConjecture.RepresentationTheory.FactorCategoryRightTauSequences

/-!
# Krull--Schmidt data in the literal factor category

This file proves that the surviving skeleton objects in
`add(ind R) / [add K]` retain local endomorphism rings, are indecomposable,
and remain pairwise nonisomorphic.  It also constructs finite biproduct
decompositions using only those surviving objects.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

open CategoricalRadical

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The endomorphism ring of a surviving object remains local after passage
to the ideal quotient. -/
theorem factorObject_end_local (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    IsLocalRing (End (σ.factorObject K x)) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let F := σ.factorFunctor K
  letI : Nontrivial (End (σ.factorObject K x)) :=
    ⟨𝟙 (σ.factorObject K x), 0, by
    intro h
    apply σ.factorObject_not_isZero K x
    rw [IsZero.iff_id_eq_zero]
    change
      (𝟙 (σ.factorObject K x) :
        σ.factorObject K x ⟶ σ.factorObject K x) = 0 at h
    exact h⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro q
  obtain ⟨q', hq'⟩ := F.map_surjective q
  let f : σ.obj x.1 ⟶ σ.obj x.1 := q'.hom
  letI : IsLocalRing (Module.End R (σ.obj x.1)) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength x.1) (σ.indecomposable x.1)
  have hsum : IsUnit (f.hom.hom + (1 - f.hom.hom)) := by
    rw [add_sub_cancel]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with
    hunit | hsubunit
  · have hIsoModule : IsIso f := isIso_of_isUnit_hom_hom f hunit
    let U := ObjectProperty.ι (σ.generated Set.univ).carrier
    have hIsoAdd : IsIso q' := by
      have hmap : IsIso (U.map q') := by
        change IsIso f
        exact hIsoModule
      letI : IsIso (U.map q') := hmap
      exact Functor.ReflectsIsomorphisms.reflects U q'
    letI : IsIso q' := hIsoAdd
    haveI : IsIso (F.map q') := inferInstance
    have hIsoQ : IsIso q := by
      rw [← hq']
      infer_instance
    letI : IsIso q := hIsoQ
    apply Or.inl
    refine ⟨⟨q, inv q, ?_, ?_⟩, rfl⟩
    · change inv q ≫ q = 𝟙 _
      simp
    · change q ≫ inv q = 𝟙 _
      simp
  · let qSub := 𝟙 _ - q'
    have hIsoModule : IsIso qSub.hom := by
      apply isIso_of_isUnit_hom_hom qSub.hom
      change IsUnit (1 - f.hom.hom)
      exact hsubunit
    let U := ObjectProperty.ι (σ.generated Set.univ).carrier
    have hIsoAdd : IsIso qSub := by
      have hmap : IsIso (U.map qSub) := by
        exact hIsoModule
      letI : IsIso (U.map qSub) := hmap
      exact Functor.ReflectsIsomorphisms.reflects U qSub
    letI : IsIso qSub := hIsoAdd
    haveI : IsIso (F.map qSub) := inferInstance
    apply Or.inr
    have hmapSub : F.map qSub =
        (1 : End (σ.factorObject K x)) - q := by
      simp [qSub, hq', F]
      rfl
    have hsIso : IsIso
        ((1 : End (σ.factorObject K x)) - q) := by
      rw [← hmapSub]
      infer_instance
    letI : IsIso ((1 : End (σ.factorObject K x)) - q) := hsIso
    refine
      ⟨⟨(1 : End (σ.factorObject K x)) - q,
          inv ((1 : End (σ.factorObject K x)) - q), ?_, ?_⟩,
        rfl⟩
    · change
        inv ((1 : End (σ.factorObject K x)) - q) ≫
            ((1 : End (σ.factorObject K x)) - q) = 𝟙 _
      simp
    · change
        ((1 : End (σ.factorObject K x)) - q) ≫
            inv ((1 : End (σ.factorObject K x)) - q) = 𝟙 _
      simp

/-- A surviving skeleton object remains indecomposable in the factor
category. -/
theorem factorObject_indec (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : HasFiniteBiproducts (σ.FactorCategory K) :=
      σ.factorQuotientHasFiniteBiproducts Set.univ K
    letI : HasBinaryBiproducts (σ.FactorCategory K) :=
      HasBinaryBiproducts.of_hasBinaryCoproducts
    Indecomposable (σ.factorObject K x) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  letI : HasBinaryBiproducts (σ.FactorCategory K) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  let X := σ.factorObject K x
  letI : IsLocalRing (End X) := σ.factorObject_end_local K x
  constructor
  · exact σ.factorObject_not_isZero K x
  · intro Y Z e
    let p : End X :=
      e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
    have hp : IsIdempotentElem p := by
      change p * p = p
      simp only [End.mul_def]
      simp [p, Category.assoc]
    rcases OpConjecture.Foundation.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem hp with
      hp₀ | hp₁
    · left
      apply (IsZero.iff_id_eq_zero Y).mpr
      have hproj : (biprod.fst : Y ⊞ Z ⟶ Y) ≫
          (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, Category.assoc]
          _ = 0 := by rw [hp₀]; simp; rfl
      have h := congrArg
        (fun q : End (Y ⊞ Z) ↦ biprod.inl ≫ q ≫ biprod.fst) hproj
      simpa [Category.assoc] using h
    · right
      apply (IsZero.iff_id_eq_zero Z).mpr
      have hproj : (biprod.fst : Y ⊞ Z ⟶ Y) ≫
          (biprod.inl : Y ⟶ Y ⊞ Z) = 𝟙 (Y ⊞ Z) := by
        calc
          biprod.fst ≫ biprod.inl = e.inv ≫ p ≫ e.hom := by
            simp [p, Category.assoc]
          _ = 𝟙 (Y ⊞ Z) := by rw [hp₁]; simp [X]
      have h := congrArg
        (fun q : End (Y ⊞ Z) ↦ biprod.inr ≫ q ≫ biprod.snd) hproj
      simpa [Category.assoc] using h.symm

/-- Distinct surviving skeleton labels remain nonisomorphic in the ideal
quotient. -/
theorem factorObject_skeletal (K : Set ι) {x y : DeletedLabel K}
    (e : Nonempty (σ.factorObject K x ≅ σ.factorObject K y)) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    x = y := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let F := σ.factorFunctor K
  obtain ⟨e⟩ := e
  obtain ⟨f, hf⟩ := F.map_surjective e.hom
  have hsplit : IsSplitMono f.hom := by
    by_contra hnot
    have hradModule : IsRadicalMorphism f.hom :=
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj f.hom).2 hnot
    have hradAdd : IsRadicalMorphism f := by
      intro g
      let U := ObjectProperty.ι (σ.generated Set.univ).carrier
      let q := 𝟙 _ - f ≫ g
      have hq : IsIso (U.map q) := by
        dsimp only [U, q]
        exact hradModule g.hom
      letI : IsIso (U.map q) := hq
      exact Functor.ReflectsIsomorphisms.reflects U q
    have hradMap : IsRadicalMorphism (F.map f) :=
      I.map_isRadicalMorphism f hradAdd
    have hradHom : IsRadicalMorphism e.hom := by
      rw [← hf]
      exact hradMap
    letI : IsIso e.hom := e.isIso_hom
    have hzero : IsZero (σ.factorObject K x) :=
      hradHom.isZero_source_of_isSplitMono
    exact (σ.factorObject_not_isZero K x) hzero
  obtain ⟨sm⟩ := hsplit.exists_splitMono
  let rt : Retract (σ.obj x.1) (σ.obj y.1) :=
    { i := f.hom
      r := sm.retraction
      retract := sm.id }
  have hxy : x.1 = y.1 := by
    simpa only [Set.mem_singleton_iff] using
      index_mem_of_retract_inAdd σ rt
        (inAdd_obj σ (Set.mem_singleton y.1))
  apply Subtype.ext
  exact hxy

/-- The two canonical ways of sending a skeleton object to the factor
category differ only in the proof that the module lies in `add(ind R)`. -/
def factorAmbientPointIsoFactorModule (K : Set ι) (i : ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (σ.factorFunctor K).obj (σ.ambientAddPoint i) ≅
      (factorModuleFunctor σ K).obj (σ.obj i) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  exact eqToIso (by
    apply CategoryTheory.Quotient.ext
    apply ObjectProperty.FullSubcategory.ext
    rfl)

/-- Every object of the literal factor category is a finite biproduct of
the surviving skeleton objects. -/
theorem factorCategory_obj_decomposition
    [Fintype ι] (K : Set ι) (X : σ.FactorCategory K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : HasFiniteBiproducts (σ.FactorCategory K) :=
      σ.factorQuotientHasFiniteBiproducts Set.univ K
    ∃ (n : ℕ) (label : Fin n → DeletedLabel K),
      Nonempty
        (X ≅ ⨁ fun i ↦ σ.factorObject K (label i)) := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  let FM := factorModuleFunctor σ K
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes X.as.obj
  let J := {i : Fin n // a i ∉ K}
  let ε : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let label : Fin (Fintype.card J) → DeletedLabel K :=
    fun t ↦ ⟨a (ε.symm t), (ε.symm t).2⟩
  let eSource : X ≅ FM.obj X.as.obj :=
    eqToIso (by
      apply CategoryTheory.Quotient.ext
      apply ObjectProperty.FullSubcategory.ext
      rfl)
  let eAll : X ≅
      ⨁ fun i : Fin n ↦ FM.obj (σ.obj (a i)) :=
    eSource.trans ((FM.mapIso e).trans
      (FM.mapBiproduct (fun i : Fin n ↦ σ.obj (a i))))
  let eDelete :
      (⨁ fun i : Fin n ↦ FM.obj (σ.obj (a i))) ≅
        ⨁ fun i : J ↦ FM.obj (σ.obj (a i.1)) :=
    biproductIsoSubtypeOfIsZero
      (fun i : Fin n ↦ FM.obj (σ.obj (a i)))
      (fun i ↦ a i ∉ K) (by
        intro i hi
        have hiK : a i ∈ K := not_not.mp hi
        exact (σ.factorObject_isZero_of_mem K hiK).of_iso
          (σ.factorAmbientPointIsoFactorModule K (a i)))
  let eReindex :
      (⨁ fun i : J ↦ FM.obj (σ.obj (a i.1))) ≅
        ⨁ fun t : Fin (Fintype.card J) ↦
          σ.factorObject K (label t) :=
    biproduct.whiskerEquiv ε
      (fun i : J ↦ eqToIso (by
        apply CategoryTheory.Quotient.ext
        apply ObjectProperty.FullSubcategory.ext
        simp [label, FM]
        rfl))
  exact ⟨Fintype.card J, label,
    ⟨eAll.trans (eDelete.trans eReindex)⟩⟩

/-- The surviving labels exhaust the indecomposable objects of the literal
factor category. -/
theorem factorCategory_obj_complete
    [Fintype ι] (K : Set ι) (X : σ.FactorCategory K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : HasFiniteBiproducts (σ.FactorCategory K) :=
      σ.factorQuotientHasFiniteBiproducts Set.univ K
    letI : HasBinaryBiproducts (σ.FactorCategory K) :=
      HasBinaryBiproducts.of_hasBinaryCoproducts
    Indecomposable X →
      ∃ x : DeletedLabel K,
        Nonempty (X ≅ σ.factorObject K x) := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  letI : HasBinaryBiproducts (σ.FactorCategory K) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  intro hX
  obtain ⟨n, label, ⟨e⟩⟩ := σ.factorCategory_obj_decomposition K X
  cases n with
  | zero =>
      have hzeroSum : IsZero
          (⨁ fun i : Fin 0 ↦ σ.factorObject K (label i)) := by
        rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      exact (hX.1 (hzeroSum.of_iso e)).elim
  | succ n =>
      let F : Fin (n + 1) → σ.FactorCategory K :=
        fun i ↦ σ.factorObject K (label i)
      let eSplit : X ≅
          F 0 ⊞ (⨁ fun i : Fin n ↦ F i.succ) :=
        e.trans
          (OpConjecture.CategoryTheory.DirectedIdempotent.finSuccBiproductIso F)
      rcases hX.2 _ _ eSplit with hhead | htail
      · exact ((σ.factorObject_not_isZero K (label 0)) hhead).elim
      · haveI : IsIso
            (biprod.inl : F 0 ⟶ F 0 ⊞ (⨁ fun i : Fin n ↦ F i.succ)) :=
          (Biprod.isIso_inl_iff_isZero _ _).2 htail
        exact ⟨label 0, ⟨eSplit.trans (asIso biprod.inl).symm⟩⟩

end OpConjecture.IndecomposableSkeleton
