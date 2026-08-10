import OpConjecture.RepresentationTheory.FactorCategoryLeftTauSequences
import OpConjecture.RepresentationTheory.FactorCategoryRightTauData
import OpConjecture.RepresentationTheory.FactorCategoryIdempotentComplete

/-!
# Two-sided tau-category data for the literal factor category

The restricted AR translation is bijective between its nonzero source and
target supports. The chosen quotient left meshes assemble over finite
biproducts and are compatible with the already packaged right meshes,
yielding the source-faithful finite tau-category extension.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- The restricted AR translation is injective wherever it is defined. -/
theorem factorLadderTauTarget_some_injective
    (K : Set ι) {x₁ x₂ y : DeletedLabel K}
    (h₁ : factorLadderTauTarget (σ := σ) (D := D) K x₁ = some y)
    (h₂ : factorLadderTauTarget (σ := σ) (D := D) K x₂ = some y) :
    x₁ = x₂ := by
  classical
  by_cases hp₁ : Projective (σ.obj x₁.1)
  · simp [factorLadderTauTarget, hp₁] at h₁
  · by_cases hm₁ : (arTranslation σ D ⟨x₁.1, hp₁⟩).1 ∈ K
    · simp [factorLadderTauTarget, hp₁, hm₁] at h₁
    · by_cases hθ₁ :
        factorLadderTheta (σ := σ) (D := D) K
          (FactorLadder.basis x₁) = 0
      · simp [factorLadderTauTarget, hp₁, hm₁, hθ₁] at h₁
      · by_cases hp₂ : Projective (σ.obj x₂.1)
        · simp [factorLadderTauTarget, hp₂] at h₂
        · by_cases hm₂ :
            (arTranslation σ D ⟨x₂.1, hp₂⟩).1 ∈ K
          · simp [factorLadderTauTarget, hp₂, hm₂] at h₂
          · by_cases hθ₂ :
              factorLadderTheta (σ := σ) (D := D) K
                (FactorLadder.basis x₂) = 0
            · simp [factorLadderTauTarget, hp₂, hm₂, hθ₂] at h₂
            · have hv₁ :
                  (arTranslation σ D ⟨x₁.1, hp₁⟩).1 = y.1 := by
                have hs := h₁
                simp [factorLadderTauTarget, hp₁, hm₁, hθ₁] at hs
                exact congrArg Subtype.val hs
              have hv₂ :
                  (arTranslation σ D ⟨x₂.1, hp₂⟩).1 = y.1 := by
                have hs := h₂
                simp [factorLadderTauTarget, hp₂, hm₂, hθ₂] at hs
                exact congrArg Subtype.val hs
              have hnp : (⟨x₁.1, hp₁⟩ : σ.NonprojectiveLabel) =
                  ⟨x₂.1, hp₂⟩ := by
                apply arTranslation_injective σ D
                apply Subtype.ext
                exact hv₁.trans hv₂.symm
              apply Subtype.ext
              exact congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) hnp

/-- An explicitly retained target makes its source the selected inverse
restricted translation. -/
theorem factorLadderTauSource_eq_some_of_target_eq_some
    (K : Set ι) (x y : DeletedLabel K)
    (hxy : factorLadderTauTarget (σ := σ) (D := D) K x = some y) :
    factorLadderTauSource σ D K y = some x := by
  classical
  simp only [factorLadderTauSource]
  split
  next h =>
    apply congrArg some
    exact factorLadderTauTarget_some_injective σ D K
      (Classical.choose_spec h) hxy
  next h => exact (h ⟨x, hxy⟩).elim

/-- The optional restricted translation and its chosen inverse source are
mutually inverse on their defined branches. -/
theorem factorLadderTauSource_eq_some_iff_target_eq_some
    (K : Set ι) (x y : DeletedLabel K) :
    factorLadderTauSource σ D K y = some x ↔
      factorLadderTauTarget (σ := σ) (D := D) K x = some y := by
  constructor
  · exact factorLadderTauTarget_eq_some_of_tauSource_eq_some σ D K y x
  · exact factorLadderTauSource_eq_some_of_target_eq_some σ D K x y

/-- A defined restricted translation identifies the ambient left-mesh target
with its predecessor label. -/
theorem moduleLeftMesh_X₃_eq_obj_of_tauTarget_eq_some
    (K : Set ι) (x y : DeletedLabel K)
    (hxy : factorLadderTauTarget (σ := σ) (D := D) K x = some y) :
    (moduleLeftMesh (k := k) σ D y.1).X₃ = σ.obj x.1 := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · simp [factorLadderTauTarget, hx] at hxy
  · by_cases htx : (arTranslation σ D ⟨x.1, hx⟩).1 ∈ K
    · simp [factorLadderTauTarget, hx, htx] at hxy
    · by_cases hmiddle :
        factorLadderTheta (σ := σ) (D := D) K
          (FactorLadder.basis x) = 0
      · simp [factorLadderTauTarget, hx, htx, hmiddle] at hxy
      · have hxy' := hxy
        simp [factorLadderTauTarget, hx, htx, hmiddle] at hxy'
        have hy : y =
            ⟨(arTranslation σ D ⟨x.1, hx⟩).1, htx⟩ := hxy'.symm
        subst y
        let xNP : σ.NonprojectiveLabel := ⟨x.1, hx⟩
        let yNI : σ.NoninjectiveLabel := arTranslationEquiv σ D xNP
        have hyNI :
            (⟨(arTranslation σ D xNP).1, yNI.2⟩ :
              σ.NoninjectiveLabel) = yNI := Subtype.ext rfl
        rw [moduleLeftMesh_X₃_of_not_injective
          (k := k) σ D (arTranslation σ D xNP).1 yNI.2]
        rw [hyNI, (arTranslationEquiv σ D).symm_apply_apply]

/-- The chosen quotient left mesh starts at the supplied factor object. -/
theorem factorCategoryLeftMesh_X₁
    (K : Set ι) (y : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (factorCategoryLeftMesh (k := k) σ D K y).X₁ =
      σ.factorObject K y := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  cases hsource : factorLadderTauSource σ D K y <;>
    simp [factorCategoryLeftMesh, factorCategoryZeroRightLeftMesh,
      hsource, factorCategoryRawLeftMesh_X₁ (k := k) σ D K y]

/-- A selected predecessor identifies the right endpoint of the chosen left
mesh with the predecessor factor object. -/
def factorCategoryLeftMeshRightIso_of_tauSource_eq_some
    (K : Set ι) (y x : DeletedLabel K)
    (hsource : factorLadderTauSource σ D K y = some x) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (factorCategoryLeftMesh (k := k) σ D K y).X₃ ≅
      σ.factorObject K x := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  have hxy := factorLadderTauTarget_eq_some_of_tauSource_eq_some
    σ D K y x hsource
  let e₀ : (factorCategoryLeftMesh (k := k) σ D K y).X₃ ≅
      (factorCategoryRawLeftMesh (k := k) σ D K y.1).X₃ :=
    eqToIso (by simp [factorCategoryLeftMesh, hsource])
  let e₁ : (factorCategoryRawLeftMesh (k := k) σ D K y.1).X₃ ≅
      σ.factorObject K x :=
    eqToIso (by
      change (factorModuleFunctor σ K).obj
        (moduleLeftMesh (k := k) σ D y.1).X₃ =
        σ.factorObject K x
      rw [moduleLeftMesh_X₃_eq_obj_of_tauTarget_eq_some
        (k := k) σ D K x y hxy]
      rfl)
  exact e₀.trans e₁

/-- The chosen quotient left mesh has zero right endpoint exactly when the
inverse restricted translation is undefined. -/
theorem factorCategoryLeftMesh_X₃_isZero_iff_tauSource_eq_none
    (K : Set ι) (y : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    IsZero (factorCategoryLeftMesh (k := k) σ D K y).X₃ ↔
      factorLadderTauSource σ D K y = none := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  constructor
  · intro hzero
    cases hsource : factorLadderTauSource σ D K y with
    | none => rfl
    | some x =>
        have hxzero : IsZero (σ.factorObject K x) :=
          IsZero.of_iso hzero
            (factorCategoryLeftMeshRightIso_of_tauSource_eq_some
              (k := k) σ D K y x hsource).symm
        exact ((σ.factorObject_not_isZero K x) hxzero).elim
  · intro hsource
    simpa [factorCategoryLeftMesh, factorCategoryZeroRightLeftMesh, hsource]
      using factorCategoryZeroObject_isZero σ K

/-- A defined restricted translation identifies the ambient right mesh with
the ambient left mesh at its target. -/
def moduleRightMeshIso_moduleLeftMesh_of_tauTarget_eq_some
    (K : Set ι) (x y : DeletedLabel K)
    (hxy : factorLadderTauTarget (σ := σ) (D := D) K x = some y) :
    moduleRightMesh σ D x.1 ≅ moduleLeftMesh (k := k) σ D y.1 := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · simp [factorLadderTauTarget, hx] at hxy
  · by_cases htx : (arTranslation σ D ⟨x.1, hx⟩).1 ∈ K
    · simp [factorLadderTauTarget, hx, htx] at hxy
    · by_cases hmiddle :
        factorLadderTheta (σ := σ) (D := D) K
          (FactorLadder.basis x) = 0
      · simp [factorLadderTauTarget, hx, htx, hmiddle] at hxy
      · have hxy' := hxy
        simp [factorLadderTauTarget, hx, htx, hmiddle] at hxy'
        have hy : y =
            ⟨(arTranslation σ D ⟨x.1, hx⟩).1, htx⟩ := hxy'.symm
        subst y
        let xNP : σ.NonprojectiveLabel := ⟨x.1, hx⟩
        let eR : moduleRightMesh σ D x.1 ≅
            nonprojectiveRightMesh σ D xNP :=
          eqToIso (by simp [moduleRightMesh, hx, xNP])
        let eL : moduleLeftMesh (k := k) σ D
              (arTranslationEquiv σ D xNP).1 ≅
            moduleLeftMesh (k := k) σ D (arTranslation σ D xNP).1 :=
          eqToIso (by rfl)
        exact eR.trans ((nonprojectiveRightMeshIso_moduleLeftMesh
          (k := k) σ D xNP).trans eL)

/-- A defined restricted translation identifies the chosen quotient right
mesh with the chosen quotient left mesh at its target. -/
def factorCategoryRightLeftMeshIso_of_tauTarget_eq_some
    (K : Set ι) (x y : DeletedLabel K)
    (hxy : factorLadderTauTarget (σ := σ) (D := D) K x = some y) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    factorCategoryRightMesh σ D K x ≅
      factorCategoryLeftMesh (k := k) σ D K y := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  let hsource := factorLadderTauSource_eq_some_of_target_eq_some
    σ D K x y hxy
  let eR : factorCategoryRightMesh σ D K x ≅
      factorCategoryRawRightMesh σ D K x.1 :=
    eqToIso (by simp [factorCategoryRightMesh, hxy])
  let eA := (factorModuleFunctor σ K).mapShortComplex.mapIso
    (moduleRightMeshIso_moduleLeftMesh_of_tauTarget_eq_some
      (k := k) σ D K x y hxy)
  let eL : factorCategoryRawLeftMesh (k := k) σ D K y.1 ≅
      factorCategoryLeftMesh (k := k) σ D K y :=
    eqToIso (by simp [factorCategoryLeftMesh, hsource])
  exact eR.trans (eA.trans eL)

end FiniteARTranslationData

/-- The literal factor category, with the proved right and left meshes, is a
finite two-sided tau-category. -/
def finiteDimensionalFactorCategoryTauData
    (K : Set ι)
    (hidem : IsIdempotentComplete (σ.FactorCategory K)) :
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
    letI : IsIdempotentComplete (σ.FactorCategory K) := hidem
    letI : Fintype (DeletedLabel K) := Fintype.ofFinite _
    Iyama.FiniteTauCategoryData
      (σ.FactorCategory K) (DeletedLabel K) := by
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
  letI : IsIdempotentComplete (σ.FactorCategory K) := hidem
  letI : Fintype (DeletedLabel K) := Fintype.ofFinite _
  let D := σ.finiteDimensionalARTranslationData k R
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let n : σ.FactorCategory K → ℕ := fun X ↦
    Classical.choose (σ.factorCategory_obj_decomposition K X)
  let label : ∀ X : σ.FactorCategory K, Fin (n X) → DeletedLabel K :=
    fun X ↦ Classical.choose
      (Classical.choose_spec (σ.factorCategory_obj_decomposition K X))
  let decompositionIso : ∀ X : σ.FactorCategory K,
      X ≅ ⨁ fun i : Fin (n X) ↦ σ.factorObject K (label X i) :=
    fun X ↦ Nonempty.some
      (Classical.choose_spec
        (Classical.choose_spec (σ.factorCategory_obj_decomposition K X)))
  let leftMesh : σ.FactorCategory K →
      ShortComplex (σ.FactorCategory K) := fun X ↦
    Iyama.shortComplexBiproduct
      (fun i : Fin (n X) ↦
        FiniteARTranslationData.factorCategoryLeftMesh
          (k := k) σ D K (label X i))
  let leftTermIso : ∀ X : σ.FactorCategory K,
      (leftMesh X).X₁ ≅ X := fun X ↦ by
    let eComponents :
        (⨁ fun i : Fin (n X) ↦
            (FiniteARTranslationData.factorCategoryLeftMesh
              (k := k) σ D K (label X i)).X₁) ≅
          ⨁ fun i : Fin (n X) ↦
            σ.factorObject K (label X i) :=
      biproduct.mapIso fun i ↦ eqToIso
        (FiniteARTranslationData.factorCategoryLeftMesh_X₁
          (k := k) σ D K (label X i))
    exact eComponents.trans (decompositionIso X).symm
  let leftTau : ∀ X : σ.FactorCategory K,
      Iyama.LeftTauSequence (leftMesh X) := fun X ↦
    Iyama.leftTauSequence_shortComplexBiproduct T.radical
      (fun i : Fin (n X) ↦
        FiniteARTranslationData.factorCategoryLeftMesh
          (k := k) σ D K (label X i))
      (fun i ↦ FiniteARTranslationData.factorCategoryLeftTau
        (k := k) σ D K (label X i))
  let leftMeshFactorIso : ∀ y : DeletedLabel K,
      Nonempty
        (leftMesh (σ.factorObject K y) ≅
          FiniteARTranslationData.factorCategoryLeftMesh
            (k := k) σ D K y) := fun y ↦
    Iyama.LeftTauSequence.nonempty_iso_of_iso_X₁
      (leftTau (σ.factorObject K y))
      (FiniteARTranslationData.factorCategoryLeftTau
        (k := k) σ D K y)
      ((leftTermIso (σ.factorObject K y)).trans
        (eqToIso
          (FiniteARTranslationData.factorCategoryLeftMesh_X₁
            (k := k) σ D K y)).symm)
  let RightSupport :=
    {X : DeletedLabel K //
      ¬ IsZero (T.rightMesh (σ.factorObject K X)).X₁}
  let LeftSupport :=
    {Y : DeletedLabel K //
      ¬ IsZero (leftMesh (σ.factorObject K Y)).X₃}
  let targetExists : ∀ X : RightSupport,
      ∃ y : DeletedLabel K,
        FiniteARTranslationData.factorLadderTauTarget
          (σ := σ) (D := D) K X.1 = some y := fun X ↦ by
    cases htarget : FiniteARTranslationData.factorLadderTauTarget
        (σ := σ) (D := D) K X.1 with
    | none =>
        exfalso
        obtain ⟨eR⟩ := σ.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
          (k := k) (R := R) K hidem X.1
        have hExplicit : IsZero
            (FiniteARTranslationData.factorCategoryRightMesh
              σ D K X.1).X₁ :=
          (FiniteARTranslationData.factorCategoryRightMesh_X₁_isZero_iff_tauTarget_eq_none
            σ D K X.1).2 htarget
        exact X.2 (IsZero.of_iso hExplicit
          (ShortComplex.π₁.mapIso eR))
    | some y => exact ⟨y, rfl⟩
  let targetOf : RightSupport → DeletedLabel K := fun X ↦
    Classical.choose (targetExists X)
  let targetOf_spec : ∀ X : RightSupport,
      FiniteARTranslationData.factorLadderTauTarget
        (σ := σ) (D := D) K X.1 = some (targetOf X) := fun X ↦
    Classical.choose_spec (targetExists X)
  let tauPlus : RightSupport → LeftSupport := fun X ↦ by
    let y := targetOf X
    have htarget := targetOf_spec X
    refine ⟨y, ?_⟩
    intro hzero
    obtain ⟨eL⟩ := leftMeshFactorIso y
    have hExplicit : IsZero
        (FiniteARTranslationData.factorCategoryLeftMesh
          (k := k) σ D K y).X₃ :=
      IsZero.of_iso hzero (ShortComplex.π₃.mapIso eL).symm
    have hnone :=
      (FiniteARTranslationData.factorCategoryLeftMesh_X₃_isZero_iff_tauSource_eq_none
        (k := k) σ D K y).1 hExplicit
    have hsome :=
      FiniteARTranslationData.factorLadderTauSource_eq_some_of_target_eq_some
        σ D K X.1 y htarget
    rw [hsome] at hnone
    simp at hnone
  let tauPlusInjective : Function.Injective tauPlus := by
    intro X₁ X₂ h
    apply Subtype.ext
    have hy : (tauPlus X₁).1 = (tauPlus X₂).1 :=
      congrArg Subtype.val h
    change targetOf X₁ = targetOf X₂ at hy
    apply FiniteARTranslationData.factorLadderTauTarget_some_injective
      σ D K
    · exact targetOf_spec X₁
    · rw [hy]
      exact targetOf_spec X₂
  let tauPlusSurjective : Function.Surjective tauPlus := by
    intro Y
    have hdefined : ∃ x : DeletedLabel K,
        FiniteARTranslationData.factorLadderTauTarget
          (σ := σ) (D := D) K x = some Y.1 := by
      by_contra hnone
      have hsource : FiniteARTranslationData.factorLadderTauSource
          σ D K Y.1 = none :=
        (FiniteARTranslationData.factorLadderTauSource_eq_none_iff
          σ D K Y.1).2 hnone
      obtain ⟨eL⟩ := leftMeshFactorIso Y.1
      have hExplicit : IsZero
          (FiniteARTranslationData.factorCategoryLeftMesh
            (k := k) σ D K Y.1).X₃ :=
        (FiniteARTranslationData.factorCategoryLeftMesh_X₃_isZero_iff_tauSource_eq_none
          (k := k) σ D K Y.1).2 hsource
      exact Y.2 (IsZero.of_iso hExplicit
        (ShortComplex.π₃.mapIso eL))
    let x : DeletedLabel K := Classical.choose hdefined
    have htarget : FiniteARTranslationData.factorLadderTauTarget
        (σ := σ) (D := D) K x = some Y.1 :=
      Classical.choose_spec hdefined
    have hxNonzero : ¬ IsZero
        (T.rightMesh (σ.factorObject K x)).X₁ := by
      intro hzero
      obtain ⟨eR⟩ := σ.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
        (k := k) (R := R) K hidem x
      have hExplicit : IsZero
          (FiniteARTranslationData.factorCategoryRightMesh σ D K x).X₁ :=
        IsZero.of_iso hzero (ShortComplex.π₁.mapIso eR).symm
      have hnone :=
        (FiniteARTranslationData.factorCategoryRightMesh_X₁_isZero_iff_tauTarget_eq_none
          σ D K x).1 hExplicit
      rw [htarget] at hnone
      simp at hnone
    let X : RightSupport := ⟨x, hxNonzero⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    exact Option.some.inj ((targetOf_spec X).symm.trans htarget)
  let tauPlusEquiv : RightSupport ≃ LeftSupport :=
    Equiv.ofBijective tauPlus ⟨tauPlusInjective, tauPlusSurjective⟩
  exact
    { toFiniteRightTauCategoryData := T
      leftMesh := leftMesh
      leftTermIso := leftTermIso
      leftTau := leftTau
      tauPlusEquiv := tauPlusEquiv
      rightLeftMeshIso := fun X ↦ by
        let y : DeletedLabel K := (tauPlusEquiv X).1
        have htarget : FiniteARTranslationData.factorLadderTauTarget
            (σ := σ) (D := D) K X.1 = some y := by
          change FiniteARTranslationData.factorLadderTauTarget
            (σ := σ) (D := D) K X.1 = some (targetOf X)
          exact targetOf_spec X
        let eR := Nonempty.some
          (σ.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
            (k := k) (R := R) K hidem X.1)
        let eM :=
          FiniteARTranslationData.factorCategoryRightLeftMeshIso_of_tauTarget_eq_some
            (k := k) σ D K X.1 y htarget
        let eL := Nonempty.some (leftMeshFactorIso y)
        exact eR.trans (eM.trans eL.symm) }

/-- The constructed two-sided quotient tau-category literally extends the
previously packaged right tau-category data. -/
def finiteDimensionalFactorCategoryTauExtension (K : Set ι) :
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
    let hidem := σ.factorCategory_isIdempotentComplete
      (k := k) (R := R) K
    letI : IsIdempotentComplete (σ.FactorCategory K) := hidem
    letI : Fintype (DeletedLabel K) := Fintype.ofFinite _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    Iyama.FiniteTauCategoryExtension T := by
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
  let hidem : IsIdempotentComplete (σ.FactorCategory K) :=
    σ.factorCategory_isIdempotentComplete (k := k) (R := R) K
  letI : IsIdempotentComplete (σ.FactorCategory K) := hidem
  letI : Fintype (DeletedLabel K) := Fintype.ofFinite _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  exact
    { data := σ.finiteDimensionalFactorCategoryTauData
        (k := k) (R := R) K hidem
      right_eq := rfl }

end OpConjecture.IndecomposableSkeleton

