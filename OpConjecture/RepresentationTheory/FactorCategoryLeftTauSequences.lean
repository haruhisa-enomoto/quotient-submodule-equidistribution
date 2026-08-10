import OpConjecture.RepresentationTheory.FactorCategoryRightTauSequences
import OpConjecture.RepresentationTheory.ModuleLeftTauSequences

/-!
# Left tau meshes in the literal factor category

The raw image of every ambient module left mesh remains a radical
approximation and a weak cokernel in `add(ind R) / [add K]`. After
minimalizing the right endpoint, the inverse restricted AR translation
selects a genuine left tau-sequence at every surviving label.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace OpConjecture.IndecomposableSkeleton

open CategoricalRadical

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- The literal image in the factor category of the ambient module left
mesh at `x`. -/
def factorCategoryRawLeftMesh (K : Set ι) (x : ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    ShortComplex (σ.FactorCategory K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  exact (moduleLeftMesh (k := k) σ D x).map (factorModuleFunctor σ K)

/-- Both arrows in the raw quotient left mesh remain radical. -/
theorem factorCategoryRawLeftMesh_radical
    (K : Set ι) (x : ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    let S := factorCategoryRawLeftMesh (k := k) σ D K x
    IsRadicalMorphism S.f ∧ IsRadicalMorphism S.g := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let A := moduleLeftTau (k := k) σ D x
  constructor
  · exact I.map_isRadicalMorphism _
      (ambientAddFunctor_map_isRadicalMorphism σ _ A.f_radical)
  · exact I.map_isRadicalMorphism _
      (ambientAddFunctor_map_isRadicalMorphism σ _ A.g_radical)

/-- The left endpoint of the raw quotient left mesh at a deleted label is
the literal factor object. -/
theorem factorCategoryRawLeftMesh_X₁
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₁ =
      σ.factorObject K x := by
  dsimp only
  change
    (factorModuleFunctor σ K).obj
      (moduleLeftMesh (k := k) σ D x.1).X₁ =
      σ.factorObject K x
  rw [moduleLeftMesh_X₁]
  rfl

/-- Radical maps out of a surviving left endpoint factor through the raw
quotient left-mesh map. -/
theorem factorCategoryRawLeftMesh_factors_from_left
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    let S := factorCategoryRawLeftMesh (k := k) σ D K x.1
    ∀ {W : σ.FactorCategory K} (a : S.X₁ ⟶ W),
      IsRadicalMorphism a →
        ∃ b : S.X₂ ⟶ W, S.f ≫ b = a := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := σ.factorFunctor K
  let S := moduleLeftMesh (k := k) σ D x.1
  let A := moduleLeftTau (k := k) σ D x.1
  intro W a ha
  obtain ⟨a', rfl⟩ := F.map_surjective a
  have hnot : ¬ IsSplitMono a'.hom := by
    intro hsplit
    letI : IsSplitMono a'.hom := hsplit
    let sm : SplitMono a' := {
      retraction := ObjectProperty.homMk (retraction a'.hom)
      id := by
        apply ObjectProperty.hom_ext
        exact IsSplitMono.id a'.hom }
    have hz : IsZero
        (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₁ :=
      ha.isZero_source_of_splitMono (sm.map F)
    rw [factorCategoryRawLeftMesh_X₁ (k := k) σ D K x] at hz
    exact (σ.factorObject_not_isZero K x) hz
  let eX : S.X₁ ≅ σ.obj x.1 :=
    eqToIso (moduleLeftMesh_X₁ (k := k) σ D x.1)
  let aX : σ.obj x.1 ⟶ W.as.obj := eX.inv ≫ a'.hom
  have hnotX : ¬ IsSplitMono aX := by
    intro hsplit
    letI : IsSplitMono aX := hsplit
    letI : IsSplitMono eX.hom := inferInstance
    have hs : IsSplitMono (eX.hom ≫ aX) := inferInstance
    have heq : eX.hom ≫ aX = a'.hom := by simp [aX]
    exact hnot (heq ▸ hs)
  have haRad : IsRadicalMorphism a'.hom := by
    have haXRad : IsRadicalMorphism aX :=
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj aX).2 hnotX
    have h := isRadicalMorphism_precomp eX.hom haXRad
    simpa [aX] using h
  obtain ⟨b, hb⟩ := A.factors_from_left a'.hom haRad
  refine ⟨F.map ((ambientAddFunctor σ).map b), ?_⟩
  change F.map ((ambientAddFunctor σ).map S.f) ≫
      F.map ((ambientAddFunctor σ).map b) = F.map a'
  rw [← F.map_comp]
  apply congrArg F.map
  apply ObjectProperty.hom_ext
  exact hb

/-- Radical maps into the raw quotient left mesh's right endpoint factor
through its second arrow. -/
theorem factorCategoryRawLeftMesh_factors_into_right
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    let S := factorCategoryRawLeftMesh (k := k) σ D K x.1
    ∀ {W : σ.FactorCategory K} (a : W ⟶ S.X₃),
      IsRadicalMorphism a →
        ∃ b : W ⟶ S.X₂, b ≫ S.g = a := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := σ.factorFunctor K
  let S := moduleLeftMesh (k := k) σ D x.1
  let A := moduleLeftTau (k := k) σ D x.1
  intro W a ha
  classical
  by_cases hx : Injective (σ.obj x.1)
  · have hS₃ : IsZero S.X₃ :=
      moduleLeftMesh_X₃_isZero_of_injective (k := k) σ D x.1 hx
    have hQ₃ : IsZero
        (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ :=
      (factorModuleFunctor σ K).map_isZero hS₃
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hQ₃.eq_of_tgt a 0
    rw [ha0]
    simp
  · let zx : ι :=
      ((arTranslationEquiv σ D).symm ⟨x.1, hx⟩).1
    by_cases hzx : zx ∈ K
    · have htarget :
          (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ =
            F.obj (σ.ambientAddPoint zx) := by
        change (factorModuleFunctor σ K).obj S.X₃ =
          F.obj (σ.ambientAddPoint zx)
        rw [moduleLeftMesh_X₃_of_not_injective
          (k := k) σ D x.1 hx]
        rfl
      have hQ₃ : IsZero
          (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ := by
        rw [htarget]
        exact σ.factorObject_isZero_of_mem K hzx
      refine ⟨0, ?_⟩
      have ha0 : a = 0 := hQ₃.eq_of_tgt a 0
      rw [ha0]
      simp
    · let z : DeletedLabel K := ⟨zx, hzx⟩
      have htarget :
          (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ =
            σ.factorObject K z := by
        change (factorModuleFunctor σ K).obj S.X₃ =
          σ.factorObject K z
        rw [moduleLeftMesh_X₃_of_not_injective
          (k := k) σ D x.1 hx]
        rfl
      obtain ⟨a', rfl⟩ := F.map_surjective a
      have hnot : ¬ IsSplitEpi a'.hom := by
        intro hsplit
        letI : IsSplitEpi a'.hom := hsplit
        let se : SplitEpi a' := {
          section_ := ObjectProperty.homMk (section_ a'.hom)
          id := by
            apply ObjectProperty.hom_ext
            exact IsSplitEpi.id a'.hom }
        have hz0 : IsZero
            (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ :=
          ha.isZero_target_of_splitEpi (se.map F)
        rw [htarget] at hz0
        exact (σ.factorObject_not_isZero K z) hz0
      let eZ : S.X₃ ≅ σ.obj z.1 :=
        eqToIso (moduleLeftMesh_X₃_of_not_injective
          (k := k) σ D x.1 hx)
      let aZ : W.as.obj ⟶ σ.obj z.1 := a'.hom ≫ eZ.hom
      have hnotZ : ¬ IsSplitEpi aZ := by
        intro hsplit
        letI : IsSplitEpi aZ := hsplit
        letI : IsSplitEpi eZ.inv := inferInstance
        have hs : IsSplitEpi (aZ ≫ eZ.inv) := inferInstance
        have heq : aZ ≫ eZ.inv = a'.hom := by simp [aZ]
        exact hnot (heq ▸ hs)
      have haRad : IsRadicalMorphism a'.hom := by
        have haZRad : IsRadicalMorphism aZ :=
          (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj aZ).2 hnotZ
        have h := isRadicalMorphism_postcomp eZ.inv haZRad
        simpa [aZ] using h
      obtain ⟨b, hb⟩ := A.factors_into_right a'.hom haRad
      refine ⟨F.map ((ambientAddFunctor σ).map b), ?_⟩
      change F.map ((ambientAddFunctor σ).map b) ≫
          F.map ((ambientAddFunctor σ).map S.g) = F.map a'
      rw [← F.map_comp]
      apply congrArg F.map
      apply ObjectProperty.hom_ext
      exact hb

/-- The raw quotient left mesh remains a weak cokernel at every surviving
left endpoint. -/
theorem factorCategoryRawLeftMesh_isWeakCokernel
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    Iyama.ShortComplex.IsWeakCokernel
      (factorCategoryRawLeftMesh (k := k) σ D K x.1) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := σ.factorFunctor K
  let S := moduleLeftMesh (k := k) σ D x.1
  let A := moduleLeftTau (k := k) σ D x.1
  rw [Iyama.ShortComplex.isWeakCokernel_iff]
  intro W q hq
  obtain ⟨q', rfl⟩ := F.map_surjective q
  let fAdd := (ambientAddFunctor σ).map S.f
  have hqmap : F.map (fAdd ≫ q') = 0 := by
    change F.map fAdd ≫ F.map q' = 0 at hq
    simpa only [← F.map_comp] using hq
  have hfac := (I.map_eq_zero_iff (fAdd ≫ q')).1 hqmap
  rcases hfac with ⟨M, hM, left, right, hcomp⟩
  have hleftNot : ¬ IsSplitMono left := by
    intro hsplit
    letI : IsSplitMono left := hsplit
    let eX : S.X₁ ≅ σ.obj x.1 :=
      eqToIso (moduleLeftMesh_X₁ (k := k) σ D x.1)
    let rt : Retract (σ.obj x.1) M :=
      { i := eX.inv ≫ left
        r := retraction left ≫ eX.hom
        retract := by simp }
    exact x.2 (index_mem_of_retract_inAdd σ rt hM)
  let eX : S.X₁ ≅ σ.obj x.1 :=
    eqToIso (moduleLeftMesh_X₁ (k := k) σ D x.1)
  let leftX : σ.obj x.1 ⟶ M := eX.inv ≫ left
  have hleftXNot : ¬ IsSplitMono leftX := by
    intro hsplit
    letI : IsSplitMono leftX := hsplit
    letI : IsSplitMono eX.hom := inferInstance
    have hs : IsSplitMono (eX.hom ≫ leftX) := inferInstance
    have heq : eX.hom ≫ leftX = left := by simp [leftX]
    exact hleftNot (heq ▸ hs)
  have hleftRad : IsRadicalMorphism left := by
    have hlX : IsRadicalMorphism leftX :=
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj leftX).2
        hleftXNot
    have hl := isRadicalMorphism_precomp eX.hom hlX
    simpa [leftX] using hl
  obtain ⟨v, hv⟩ := A.factors_from_left left hleftRad
  let q₀ : S.X₂ ⟶ W.as.obj := q'.hom - v ≫ right
  have hq₀ : S.f ≫ q₀ = 0 := by
    dsimp only [q₀]
    rw [Preadditive.comp_sub, ← Category.assoc, hv]
    have hc : left ≫ right = S.f ≫ q'.hom := by
      change left ≫ right = S.f ≫ q'.hom at hcomp
      exact hcomp
    rw [hc, sub_self]
  obtain ⟨l, hl⟩ :=
    (Iyama.ShortComplex.isWeakCokernel_iff S).1
      A.minimalWeakCokernel.1 q₀ hq₀
  refine ⟨F.map ((ambientAddFunctor σ).map l), ?_⟩
  change F.map ((ambientAddFunctor σ).map S.g) ≫
      F.map ((ambientAddFunctor σ).map l) = F.map q'
  rw [← F.map_comp, ← sub_eq_zero, ← F.map_sub]
  apply (I.map_eq_zero_iff _).2
  refine ⟨M, hM, -v, right, ?_⟩
  change (-v) ≫ right = (S.g ≫ l) - q'.hom
  rw [hl]
  dsimp only [q₀]
  simp

/-- The raw quotient left mesh satisfies the full radical approximation
condition. -/
theorem factorCategoryRawLeftMesh_tauApproximation
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    Iyama.TauApproximation
      (factorCategoryRawLeftMesh (k := k) σ D K x.1) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  exact
    { f_radical :=
        (factorCategoryRawLeftMesh_radical (k := k) σ D K x.1).1
      g_radical :=
        (factorCategoryRawLeftMesh_radical (k := k) σ D K x.1).2
      factors_from_left :=
        factorCategoryRawLeftMesh_factors_from_left (k := k) σ D K x
      factors_into_right :=
        factorCategoryRawLeftMesh_factors_into_right (k := k) σ D K x }

/-- If the raw quotient left mesh has a surviving indecomposable right
endpoint and a nonzero second arrow, that arrow is left minimal. -/
theorem factorCategoryRawLeftMesh_isLeftMinimal_of_target_eq
    (K : Set ι) (x y : DeletedLabel K)
    (htarget :
      (moduleLeftMesh (k := k) σ D x.1).X₃ = σ.obj y.1) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (factorCategoryRawLeftMesh (k := k) σ D K x.1).g ≠ 0 →
      IsLeftMinimal
        (factorCategoryRawLeftMesh (k := k) σ D K x.1).g := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let F := σ.factorFunctor K
  let S := moduleLeftMesh (k := k) σ D x.1
  intro hg e he
  obtain ⟨e', rfl⟩ := F.map_surjective e
  change F.map ((ambientAddFunctor σ).map S.g) ≫ F.map e' =
    F.map ((ambientAddFunctor σ).map S.g) at he
  let eT : S.X₃ ≅ σ.obj y.1 := eqToIso htarget
  let eY : σ.obj y.1 ⟶ σ.obj y.1 :=
    eT.inv ≫ e'.hom ≫ eT.hom
  letI : IsLocalRing (Module.End R (σ.obj y.1)) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength y.1) (σ.indecomposable y.1)
  have hsum : IsUnit (eY.hom.hom + (1 - eY.hom.hom)) := by
    rw [add_sub_cancel]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with
    hunit | hsubunit
  · have hIsoY : IsIso eY := isIso_of_isUnit_hom_hom eY hunit
    letI : IsIso eY := hIsoY
    have heq : e'.hom = eT.hom ≫ eY ≫ eT.inv := by
      simp [eY]
    have hIsoUnderlying : IsIso e'.hom := heq ▸ inferInstance
    let U := ObjectProperty.ι (σ.generated Set.univ).carrier
    have hmap : IsIso (U.map e') := by
      change IsIso e'.hom
      exact hIsoUnderlying
    letI : IsIso (U.map e') := hmap
    have hIsoAdd : IsIso e' :=
      Functor.ReflectsIsomorphisms.reflects U e'
    letI : IsIso e' := hIsoAdd
    exact (F.mapIso (asIso e')).isIso_hom
  · have hIsoSubY : IsIso (𝟙 _ - eY) := by
      apply isIso_of_isUnit_hom_hom (𝟙 _ - eY)
      change IsUnit (1 - eY.hom.hom)
      exact hsubunit
    letI : IsIso (𝟙 _ - eY) := hIsoSubY
    have heq : 𝟙 S.X₃ - e'.hom =
        eT.hom ≫ (𝟙 _ - eY) ≫ eT.inv := by
      simp [eY, Preadditive.comp_sub, Preadditive.sub_comp]
    have hIsoUnderlying : IsIso (𝟙 S.X₃ - e'.hom) :=
      heq ▸ inferInstance
    let qAdd := 𝟙 _ - e'
    let U := ObjectProperty.ι (σ.generated Set.univ).carrier
    have hmap : IsIso (U.map qAdd) := by
      change IsIso (𝟙 S.X₃ - e'.hom)
      exact hIsoUnderlying
    letI : IsIso (U.map qAdd) := hmap
    have hIsoAdd : IsIso qAdd :=
      Functor.ReflectsIsomorphisms.reflects U qAdd
    letI : IsIso qAdd := hIsoAdd
    letI : IsIso (F.map qAdd) := inferInstance
    have hmapq : F.map qAdd = 𝟙 _ - F.map e' := by
      dsimp only [qAdd]
      rw [F.map_sub, F.map_id]
    have hgq : F.map ((ambientAddFunctor σ).map S.g) ≫
        F.map qAdd = 0 := by
      rw [hmapq, Preadditive.comp_sub, Category.comp_id]
      exact sub_eq_zero.mpr he.symm
    have hgzero :
        (factorCategoryRawLeftMesh (k := k) σ D K x.1).g = 0 := by
      change F.map ((ambientAddFunctor σ).map S.g) = 0
      calc
        F.map ((ambientAddFunctor σ).map S.g) =
            (F.map ((ambientAddFunctor σ).map S.g) ≫
              F.map qAdd) ≫ inv (F.map qAdd) := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        _ = 0 := by rw [hgq, zero_comp]
    exact (hg hgzero).elim

/-- A nonzero restricted AR middle makes the second arrow of the raw right
mesh nonzero. -/
theorem factorCategoryRawRightMesh_g_ne_zero_of_theta_ne_zero
    (K : Set ι) (x : DeletedLabel K)
    (hx : ¬ Projective (σ.obj x.1))
    (hmiddle :
      factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) ≠ 0) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (factorCategoryRawRightMesh σ D K x.1).g ≠ 0 := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let F := σ.factorFunctor K
  let S := moduleRightMesh σ D x.1
  let A := moduleRightTau σ D x.1
  intro hgzero
  let gAdd := (ambientAddFunctor σ).map S.g
  have hgmap : F.map gAdd = 0 := by
    change (factorCategoryRawRightMesh σ D K x.1).g = 0
    exact hgzero
  have hfac := (I.map_eq_zero_iff gAdd).1 hgmap
  rcases hfac with ⟨M, hM, left, right, hcomp⟩
  let eX : S.X₃ ≅ σ.obj x.1 :=
    eqToIso (moduleRightMesh_X₃ σ D x.1)
  have hrightNot : ¬ IsSplitEpi right := by
    intro hsplit
    letI : IsSplitEpi right := hsplit
    let rt : Retract (σ.obj x.1) M :=
      { i := eX.inv ≫ section_ right
        r := right ≫ eX.hom
        retract := by simp }
    exact x.2 (index_mem_of_retract_inAdd σ rt hM)
  let rightX : M ⟶ σ.obj x.1 := right ≫ eX.hom
  have hrightXNot : ¬ IsSplitEpi rightX := by
    intro hsplit
    letI : IsSplitEpi rightX := hsplit
    letI : IsSplitEpi eX.inv := inferInstance
    have hs : IsSplitEpi (rightX ≫ eX.inv) := inferInstance
    have heq : rightX ≫ eX.inv = right := by simp [rightX]
    exact hrightNot (heq ▸ hs)
  have hrightRad : IsRadicalMorphism right := by
    have hrX : IsRadicalMorphism rightX :=
      (σ.isRadicalMorphism_iff_not_isSplitEpi_to_obj rightX).2
        hrightXNot
    have hr := isRadicalMorphism_postcomp eX.inv hrX
    simpa [rightX] using hr
  obtain ⟨t, ht⟩ := A.factors_into_right right hrightRad
  have hend : (left ≫ t) ≫ S.g = S.g := by
    rw [Category.assoc, ht]
    change left ≫ right = S.g at hcomp
    exact hcomp
  have hrightMinimal : IsRightMinimal S.g := by
    have hS : S = nonprojectiveRightMesh σ D ⟨x.1, hx⟩ := by
      simp [S, moduleRightMesh, hx]
    rw [hS]
    exact (chosenRightAR σ D ⟨x.1, hx⟩).rightMinimal
  have hIsoEnd : IsIso (left ≫ t) :=
    hrightMinimal (left ≫ t) hend
  letI : IsIso (left ≫ t) := hIsoEnd
  let rtMiddle : Retract S.X₂ M :=
    { i := left
      r := t ≫ inv (left ≫ t)
      retract := by rw [← Category.assoc, IsIso.hom_inv_id] }
  have hMiddle : σ.InAdd K S.X₂ := inAdd_of_retract σ rtMiddle hM
  obtain ⟨s, hs⟩ :=
    (factorLadderTheta_basis_ne_zero_iff σ D K x).1 hmiddle
  let AR := factorLadderRightARAt σ D x.1
  let rtLabel : Retract (σ.obj (AR.label s)) AR.middle :=
    { i := biproduct.ι (fun j : AR.index ↦ σ.obj (AR.label j)) s ≫
          AR.decomposition.inv
      r := AR.decomposition.hom ≫
          biproduct.π (fun j : AR.index ↦ σ.obj (AR.label j)) s
      retract := by simp }
  have hARMiddle : σ.InAdd K AR.middle := by
    change σ.InAdd K (factorLadderRightARAt σ D x.1).middle
    rw [← moduleRightMesh_X₂ σ D x.1]
    exact hMiddle
  exact hs (index_mem_of_retract_inAdd σ rtLabel hARMiddle)

/-- If a predecessor right mesh has a nonzero restricted middle, the raw
left mesh at its retained translate has nonzero second arrow. -/
theorem factorCategoryRawLeftMesh_g_ne_zero_of_predecessor
    (K : Set ι) (z : DeletedLabel K)
    (hz : ¬ Projective (σ.obj z.1))
    (htz : (arTranslation σ D ⟨z.1, hz⟩).1 ∉ K)
    (hmiddle :
      factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis z) ≠ 0) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    let y : DeletedLabel K :=
      ⟨(arTranslation σ D ⟨z.1, hz⟩).1, htz⟩
    (factorCategoryRawLeftMesh (k := k) σ D K y.1).g ≠ 0 := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let y : DeletedLabel K :=
    ⟨(arTranslation σ D ⟨z.1, hz⟩).1, htz⟩
  let zNP : σ.NonprojectiveLabel := ⟨z.1, hz⟩
  let eR : moduleRightMesh σ D z.1 ≅
      nonprojectiveRightMesh σ D zNP :=
    eqToIso (by simp [moduleRightMesh, hz, zNP])
  let eL : moduleLeftMesh (k := k) σ D
        (arTranslationEquiv σ D zNP).1 ≅
      moduleLeftMesh (k := k) σ D y.1 :=
    eqToIso (by rfl)
  let eA : moduleRightMesh σ D z.1 ≅
      moduleLeftMesh (k := k) σ D y.1 :=
    eR.trans ((nonprojectiveRightMeshIso_moduleLeftMesh
      (k := k) σ D zNP).trans eL)
  let eQ := (factorModuleFunctor σ K).mapShortComplex.mapIso eA
  have hright : (factorCategoryRawRightMesh σ D K z.1).g ≠ 0 :=
    factorCategoryRawRightMesh_g_ne_zero_of_theta_ne_zero
      σ D K z hz hmiddle
  intro hleft
  apply hright
  change ((factorModuleFunctor σ K).mapShortComplex.obj
    (moduleRightMesh σ D z.1)).g = 0
  apply (cancel_mono eQ.hom.τ₃).1
  have hcomm := eQ.hom.comm₂₃
  have hleft' : ((factorModuleFunctor σ K).mapShortComplex.obj
      (moduleLeftMesh (k := k) σ D y.1)).g = 0 := by
    change (factorCategoryRawLeftMesh (k := k) σ D K y.1).g = 0
    exact hleft
  rw [← hcomm, hleft', comp_zero, zero_comp]

/-- In the retained-predecessor, nonzero-restricted-middle branch, the raw
quotient left mesh is already left minimal and hence a left tau-sequence. -/
theorem factorCategoryRawLeftTau_of_predecessor
    (K : Set ι) (z : DeletedLabel K)
    (hz : ¬ Projective (σ.obj z.1))
    (htz : (arTranslation σ D ⟨z.1, hz⟩).1 ∉ K)
    (hmiddle :
      factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis z) ≠ 0) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    let y : DeletedLabel K :=
      ⟨(arTranslation σ D ⟨z.1, hz⟩).1, htz⟩
    Iyama.LeftTauSequence
      (factorCategoryRawLeftMesh (k := k) σ D K y.1) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  let zNP : σ.NonprojectiveLabel := ⟨z.1, hz⟩
  let y : DeletedLabel K :=
    ⟨(arTranslation σ D zNP).1, htz⟩
  let yNI : σ.NoninjectiveLabel := arTranslationEquiv σ D zNP
  have hyNI : (⟨y.1, yNI.2⟩ : σ.NoninjectiveLabel) = yNI :=
    Subtype.ext rfl
  have htarget : (moduleLeftMesh (k := k) σ D y.1).X₃ =
      σ.obj z.1 := by
    rw [moduleLeftMesh_X₃_of_not_injective
      (k := k) σ D y.1 yNI.2]
    rw [hyNI, (arTranslationEquiv σ D).symm_apply_apply]
  let A := factorCategoryRawLeftMesh_tauApproximation
    (k := k) σ D K y
  exact
    { toTauApproximation := A
      minimalWeakCokernel :=
        ⟨factorCategoryRawLeftMesh_isWeakCokernel
            (k := k) σ D K y,
          factorCategoryRawLeftMesh_isLeftMinimal_of_target_eq
            (k := k) σ D K y z htarget
            (factorCategoryRawLeftMesh_g_ne_zero_of_predecessor
              (k := k) σ D K z hz htz hmiddle)⟩ }

/-- The optional predecessor under the restricted AR translation. -/
def factorLadderTauSource (K : Set ι) (y : DeletedLabel K) :
    Option (DeletedLabel K) := by
  classical
  exact if h : ∃ z : DeletedLabel K,
      factorLadderTauTarget (σ := σ) (D := D) K z = some y
    then some (Classical.choose h)
    else none

/-- A selected restricted predecessor really maps to the supplied label. -/
theorem factorLadderTauTarget_eq_some_of_tauSource_eq_some
    (K : Set ι) (y z : DeletedLabel K)
    (hsource : factorLadderTauSource σ D K y = some z) :
    factorLadderTauTarget (σ := σ) (D := D) K z = some y := by
  classical
  simp only [factorLadderTauSource] at hsource
  split at hsource
  next h =>
    have hz : Classical.choose h = z := Option.some.inj hsource
    rw [← hz]
    exact Classical.choose_spec h
  next h => simp at hsource

/-- A missing selected predecessor is equivalent to absence of any
restricted predecessor. -/
theorem factorLadderTauSource_eq_none_iff
    (K : Set ι) (y : DeletedLabel K) :
    factorLadderTauSource σ D K y = none ↔
      ¬ ∃ z : DeletedLabel K,
        factorLadderTauTarget (σ := σ) (D := D) K z = some y := by
  classical
  simp [factorLadderTauSource]

/-- Paper-operator form of the surviving branch: a selected predecessor
makes the raw quotient left mesh a left tau-sequence. -/
theorem factorCategoryRawLeftTau_of_tauSource_eq_some
    (K : Set ι) (y z : DeletedLabel K)
    (hsource : factorLadderTauSource σ D K y = some z) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    Iyama.LeftTauSequence
      (factorCategoryRawLeftMesh (k := k) σ D K y.1) := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  have hzy := factorLadderTauTarget_eq_some_of_tauSource_eq_some
    σ D K y z hsource
  by_cases hz : Projective (σ.obj z.1)
  · simp [factorLadderTauTarget, hz] at hzy
  · by_cases htz : (arTranslation σ D ⟨z.1, hz⟩).1 ∈ K
    · simp [factorLadderTauTarget, hz, htz] at hzy
    · by_cases hmiddle :
        factorLadderTheta (σ := σ) (D := D) K
          (FactorLadder.basis z) = 0
      · simp [factorLadderTauTarget, hz, htz, hmiddle] at hzy
      · have hzy' := hzy
        simp [factorLadderTauTarget, hz, htz, hmiddle] at hzy'
        have hy : y =
            ⟨(arTranslation σ D ⟨z.1, hz⟩).1, htz⟩ := hzy'.symm
        subst y
        exact factorCategoryRawLeftTau_of_predecessor
          (k := k) σ D K z hz htz hmiddle

/-- The raw quotient left mesh with its right term replaced by the chosen
factor-category zero object. -/
def factorCategoryZeroRightLeftMesh (K : Set ι) (x : ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    ShortComplex (σ.FactorCategory K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  let T := factorCategoryRawLeftMesh (k := k) σ D K x
  exact ShortComplex.mk T.f
    (0 : T.X₂ ⟶ factorCategoryZeroObject σ K) (by simp)

/-- Replacing the right term by zero gives a left tau-sequence whenever
the raw target is zero or the raw second arrow vanishes. -/
theorem factorCategoryZeroRightLeftTau
    (K : Set ι) (x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    (IsZero (factorCategoryRawLeftMesh (k := k) σ D K x.1).X₃ ∨
      (factorCategoryRawLeftMesh (k := k) σ D K x.1).g = 0) →
      Iyama.LeftTauSequence
        (factorCategoryZeroRightLeftMesh (k := k) σ D K x.1) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  let T := factorCategoryRawLeftMesh (k := k) σ D K x.1
  let A := factorCategoryRawLeftMesh_tauApproximation
    (k := k) σ D K x
  have hZ : IsZero (factorCategoryZeroObject σ K) :=
    factorCategoryZeroObject_isZero σ K
  intro hzero
  refine
    { f_radical := A.f_radical
      g_radical := isRadicalMorphism_zero
      factors_from_left := A.factors_from_left
      factors_into_right := ?_
      minimalWeakCokernel := ?_ }
  · intro W a _ha
    refine ⟨0, ?_⟩
    have ha0 : a = 0 := hZ.eq_of_tgt a 0
    rw [ha0]
    simp
  · constructor
    · rw [Iyama.ShortComplex.isWeakCokernel_iff]
      intro W q hq
      obtain ⟨l, hl⟩ :=
        (Iyama.ShortComplex.isWeakCokernel_iff T).1
          (factorCategoryRawLeftMesh_isWeakCokernel
            (k := k) σ D K x) q hq
      have hq0 : q = 0 := by
        rcases hzero with htarget | hg
        · have hl0 : l = 0 := htarget.eq_of_src l 0
          rw [hl0, comp_zero] at hl
          exact hl.symm
        · rw [hg, zero_comp] at hl
          exact hl.symm
      refine ⟨0, ?_⟩
      rw [hq0]
      simp
    · intro e _he
      have heq : e = 𝟙 _ := hZ.eq_of_src e (𝟙 _)
      rw [heq]
      infer_instance

/-- A missing restricted predecessor is exactly a branch in which the raw
right endpoint is zero in the quotient or the raw second arrow vanishes. -/
theorem factorCategoryRawLeftMesh_zero_condition_of_tauSource_eq_none
    (K : Set ι) (y : DeletedLabel K)
    (hnone : factorLadderTauSource σ D K y = none) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    IsZero (factorCategoryRawLeftMesh (k := k) σ D K y.1).X₃ ∨
      (factorCategoryRawLeftMesh (k := k) σ D K y.1).g = 0 := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  let F := σ.factorFunctor K
  let S := moduleLeftMesh (k := k) σ D y.1
  have hnopred : ¬ ∃ z : DeletedLabel K,
      factorLadderTauTarget (σ := σ) (D := D) K z = some y :=
    (factorLadderTauSource_eq_none_iff σ D K y).1 hnone
  by_cases hy : Injective (σ.obj y.1)
  · left
    have hS₃ : IsZero S.X₃ :=
      moduleLeftMesh_X₃_isZero_of_injective (k := k) σ D y.1 hy
    exact (factorModuleFunctor σ K).map_isZero hS₃
  · let yNI : σ.NoninjectiveLabel := ⟨y.1, hy⟩
    let zNP : σ.NonprojectiveLabel :=
      (arTranslationEquiv σ D).symm yNI
    let zx : ι := zNP.1
    by_cases hzx : zx ∈ K
    · left
      have htarget :
          (factorCategoryRawLeftMesh (k := k) σ D K y.1).X₃ =
            F.obj (σ.ambientAddPoint zx) := by
        change (factorModuleFunctor σ K).obj S.X₃ =
          F.obj (σ.ambientAddPoint zx)
        rw [moduleLeftMesh_X₃_of_not_injective
          (k := k) σ D y.1 hy]
        rfl
      rw [htarget]
      exact σ.factorObject_isZero_of_mem K hzx
    · let z : DeletedLabel K := ⟨zx, hzx⟩
      have hz : ¬ Projective (σ.obj z.1) := by
        simpa [z, zx] using zNP.2
      by_cases hmiddle :
          factorLadderTheta (σ := σ) (D := D) K
            (FactorLadder.basis z) = 0
      · right
        let AR := factorLadderRightARAt σ D z.1
        have hall : ∀ t : AR.index, AR.label t ∈ K := by
          intro t
          by_contra ht
          have hne :
              factorLadderTheta (σ := σ) (D := D) K
                (FactorLadder.basis z) ≠ 0 :=
            (factorLadderTheta_basis_ne_zero_iff σ D K z).2 ⟨t, ht⟩
          exact hne hmiddle
        have hAR : σ.InAdd K AR.middle := ⟨{
          index := AR.index
          label := AR.label
          mem := hall
          iso := AR.decomposition }⟩
        have hRightMiddle :
            σ.InAdd K (moduleRightMesh σ D z.1).X₂ := by
          rw [moduleRightMesh_X₂ σ D z.1]
          exact hAR
        have hyval : (arTranslationEquiv σ D zNP).1 = y.1 :=
          congrArg Subtype.val
            ((arTranslationEquiv σ D).apply_symm_apply yNI)
        let eR : moduleRightMesh σ D z.1 ≅
            nonprojectiveRightMesh σ D zNP :=
          eqToIso (by simp [moduleRightMesh, hz, z, zx, zNP])
        let eL : moduleLeftMesh (k := k) σ D
              (arTranslationEquiv σ D zNP).1 ≅ S :=
          eqToIso (congrArg (moduleLeftMesh (k := k) σ D) hyval)
        let eA : moduleRightMesh σ D z.1 ≅ S :=
          eR.trans ((nonprojectiveRightMeshIso_moduleLeftMesh
            (k := k) σ D zNP).trans eL)
        let e₂ : (moduleRightMesh σ D z.1).X₂ ≅ S.X₂ :=
          ShortComplex.π₂.mapIso eA
        have hLeftMiddle : σ.InAdd K S.X₂ :=
          (σ.inAdd_iff_of_iso e₂).1 hRightMiddle
        have hQ₂ : IsZero
            (factorCategoryRawLeftMesh (k := k) σ D K y.1).X₂ := by
          rw [IsZero.iff_id_eq_zero]
          change 𝟙 (F.obj (ambientAddObject σ S.X₂)) = 0
          rw [← F.map_id]
          apply (I.map_eq_zero_iff _).2
          exact ⟨S.X₂, hLeftMiddle, 𝟙 S.X₂, 𝟙 S.X₂, by simp⟩
        exact hQ₂.eq_of_src
          (factorCategoryRawLeftMesh (k := k) σ D K y.1).g 0
      · exfalso
        have htranslate : arTranslationEquiv σ D zNP = yNI :=
          (arTranslationEquiv σ D).apply_symm_apply yNI
        have htranslateAR : arTranslation σ D zNP = yNI :=
          htranslate
        let zNP' : σ.NonprojectiveLabel := ⟨z.1, hz⟩
        have hzNP : zNP' = zNP := Subtype.ext rfl
        have htranslate' : arTranslation σ D zNP' = yNI := by
          rw [hzNP]
          exact htranslateAR
        have htz : (arTranslation σ D zNP').1 ∉ K := by
          rw [congrArg Subtype.val htranslate']
          exact y.2
        have hs := factorLadderTauTarget_eq_some
          σ D K z hz htz hmiddle
        have hlabel :
            (⟨(arTranslation σ D zNP').1, htz⟩ : DeletedLabel K) = y := by
          apply Subtype.ext
          exact congrArg (fun q : σ.NoninjectiveLabel ↦ q.1) htranslate'
        rw [hlabel] at hs
        exact hnopred ⟨z, hs⟩

/-- The minimal factor-category left mesh selected by the inverse restricted
translation operator. -/
def factorCategoryLeftMesh (K : Set ι) (y : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    ShortComplex (σ.FactorCategory K) := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  match factorLadderTauSource σ D K y with
  | some _ => exact factorCategoryRawLeftMesh (k := k) σ D K y.1
  | none => exact factorCategoryZeroRightLeftMesh (k := k) σ D K y.1

/-- Every minimal factor-category left mesh is a left tau-sequence. -/
theorem factorCategoryLeftTau (K : Set ι) (y : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    Iyama.LeftTauSequence
      (factorCategoryLeftMesh (k := k) σ D K y) := by
  classical
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  cases hsource : factorLadderTauSource σ D K y with
  | none =>
      simpa [factorCategoryLeftMesh, hsource] using
        factorCategoryZeroRightLeftTau (k := k) σ D K y
          (factorCategoryRawLeftMesh_zero_condition_of_tauSource_eq_none
            (k := k) σ D K y hsource)
  | some z =>
      simpa [factorCategoryLeftMesh, hsource] using
        factorCategoryRawLeftTau_of_tauSource_eq_some
          (k := k) σ D K y z hsource

end FiniteARTranslationData
end OpConjecture.IndecomposableSkeleton
