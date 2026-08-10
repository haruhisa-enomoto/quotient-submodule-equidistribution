import OpConjecture.RepresentationTheory.ExtClassReflection
import OpConjecture.RepresentationTheory.ExtMatrixBridge
import OpConjecture.RepresentationTheory.TwoTargetRankCore

/-!
# The one-source, two-target Ext-matrix bridge

This file scalarizes an extension whose submodule endpoint is the
binary biproduct of two isotypic blocks.  The two resulting matrices form a
one-source, two-target representation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.YonedaExtReflection

universe w v u

variable {K : Type u} [Field K]
  {C : Type v} [Category.{w} C] [Abelian C] [Linear K C]
  [HasFiniteBiproducts C] [HasExt C]

/-- The first scalarized matrix of an extension with a two-block second
endpoint. -/
def firstTargetScalarizedExtLinearMap
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I]
    (X Y Z : C)
    (ℓY : Ext X Y 1 →ₗ[K] K)
    (ξ : Ext
      (⨁ fun _ : I ↦ X)
      ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) 1) :
    (I → K) →ₗ[K] (J → K) :=
  scalarizedExtLinearMap X Y ℓY
    (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1))

/-- The second scalarized matrix of an extension with a two-block second
endpoint. -/
def secondTargetScalarizedExtLinearMap
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I]
    (X Y Z : C)
    (ℓZ : Ext X Z 1 →ₗ[K] K)
    (ξ : Ext
      (⨁ fun _ : I ↦ X)
      ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) 1) :
    (I → K) →ₗ[K] (L → K) :=
  scalarizedExtLinearMap X Z ℓZ
    (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1))

private theorem ext_compatibility_of_twoTarget_scalarized_commute
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    (X Y Z : C)
    (ℓY : Ext X Y 1 →ₗ[K] K) (hℓY : Function.Injective ℓY)
    (ℓZ : Ext X Z 1 →ₗ[K] K) (hℓZ : Function.Injective ℓZ)
    (ξ : Ext
      (⨁ fun _ : I ↦ X)
      ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) 1)
    (P : Matrix I I K) (Q : Matrix J J K) (T : Matrix L L K)
    (hcommY :
      Q * scalarizedExtMatrix X Y ℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) =
        scalarizedExtMatrix X Y ℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) * P)
    (hcommZ :
      T * scalarizedExtMatrix X Z ℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) =
        scalarizedExtMatrix X Z ℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) * P) :
    ξ.comp
        (Ext.mk₀
          (biprod.map
            (scalarBiproductEnd Y Q)
            (scalarBiproductEnd Z T)))
        (add_zero 1) =
      (Ext.mk₀ (scalarBiproductEnd X P)).comp ξ (zero_add 1) := by
  apply Ext.addEquivBiprod.injective
  apply Prod.ext
  · change
      (ξ.comp
          (Ext.mk₀
            (biprod.map
              (scalarBiproductEnd Y Q)
              (scalarBiproductEnd Z T)))
          (add_zero 1)).comp
            (Ext.mk₀ biprod.fst) (add_zero 1) =
        ((Ext.mk₀ (scalarBiproductEnd X P)).comp ξ
          (zero_add 1)).comp
            (Ext.mk₀ biprod.fst) (add_zero 1)
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      biprod.map_fst,
      ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero]
    simpa only [Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero] using
        (ext_compatibility_of_scalarized_matrix_commute
          X Y ℓY hℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1))
          P Q hcommY)
  · change
      (ξ.comp
          (Ext.mk₀
            (biprod.map
              (scalarBiproductEnd Y Q)
              (scalarBiproductEnd Z T)))
          (add_zero 1)).comp
            (Ext.mk₀ biprod.snd) (add_zero 1) =
        ((Ext.mk₀ (scalarBiproductEnd X P)).comp ξ
          (zero_add 1)).comp
            (Ext.mk₀ biprod.snd) (add_zero 1)
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      biprod.map_snd,
      ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero]
    simpa only [Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero] using
        (ext_compatibility_of_scalarized_matrix_commute
          X Z ℓZ hℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1))
          P T hcommZ)

/-- If compatible idempotents on the two endpoints of an extension are
trivial, then its two scalarized matrices form an
idempotent-indecomposable one-source, two-target representation. -/
theorem twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (X Y Z : C) (hX : 𝟙 X ≠ 0) (hY : 𝟙 Y ≠ 0) (hZ : 𝟙 Z ≠ 0)
    (ℓY : Ext X Y 1 →ₗ[K] K) (hℓY : Function.Injective ℓY)
    (ℓZ : Ext X Z 1 →ₗ[K] K) (hℓZ : Function.Injective ℓZ)
    (ξ : Ext
      (⨁ fun _ : I ↦ X)
      ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) 1)
    (hendpoint :
      ∀ (a₁ :
          ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) ⟶
            ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)))
        (a₃ :
          (⨁ fun _ : I ↦ X) ⟶ (⨁ fun _ : I ↦ X)),
        a₁ ≫ a₁ = a₁ →
        a₃ ≫ a₃ = a₃ →
        ξ.comp (Ext.mk₀ a₁) (add_zero 1) =
          (Ext.mk₀ a₃).comp ξ (zero_add 1) →
        (a₁ = 0 ∧ a₃ = 0) ∨
          (a₁ = 𝟙 _ ∧ a₃ = 𝟙 _)) :
    LoewyTwoRankCore.IsTwoTargetIdempotentIndecomposable
      (firstTargetScalarizedExtLinearMap X Y Z ℓY ξ)
      (secondTargetScalarizedExtLinearMap X Y Z ℓZ ξ) := by
  classical
  intro p q r hp hq hr hcommY hcommZ
  let P : Matrix I I K := LinearMap.toMatrix' p
  let Q : Matrix J J K := LinearMap.toMatrix' q
  let T : Matrix L L K := LinearMap.toMatrix' r
  have hP : P * P = P := by
    simpa only [P, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hp
  have hQ : Q * Q = Q := by
    simpa only [Q, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hq
  have hT : T * T = T := by
    simpa only [T, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hr
  let aX := scalarBiproductEnd X P
  let aY := scalarBiproductEnd Y Q
  let aZ := scalarBiproductEnd Z T
  let aYZ := biprod.map aY aZ
  have haX : aX ≫ aX = aX := by
    dsimp only [aX]
    rw [scalarBiproductEnd_comp, hP]
  have haY : aY ≫ aY = aY := by
    dsimp only [aY]
    rw [scalarBiproductEnd_comp, hQ]
  have haZ : aZ ≫ aZ = aZ := by
    dsimp only [aZ]
    rw [scalarBiproductEnd_comp, hT]
  have haYZ : aYZ ≫ aYZ = aYZ := by
    dsimp only [aYZ]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      rw [← Category.assoc, biprod.map_fst, Category.assoc, haY]
    · simp only [Category.assoc, biprod.map_snd]
      rw [← Category.assoc, biprod.map_snd, Category.assoc, haZ]
  have hmatrixY :
      Q * scalarizedExtMatrix X Y ℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) =
        scalarizedExtMatrix X Y ℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) * P := by
    change
      q.comp
          (scalarizedExtLinearMap X Y ℓY
            (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1))) =
        (scalarizedExtLinearMap X Y ℓY
          (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1))).comp p
      at hcommY
    simpa only [Q, P, scalarizedExtLinearMap,
      LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
      congrArg LinearMap.toMatrix' hcommY
  have hmatrixZ :
      T * scalarizedExtMatrix X Z ℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) =
        scalarizedExtMatrix X Z ℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) * P := by
    change
      r.comp
          (scalarizedExtLinearMap X Z ℓZ
            (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1))) =
        (scalarizedExtLinearMap X Z ℓZ
          (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1))).comp p
      at hcommZ
    simpa only [T, P, scalarizedExtLinearMap,
      LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
      congrArg LinearMap.toMatrix' hcommZ
  have hext :
      ξ.comp (Ext.mk₀ aYZ) (add_zero 1) =
        (Ext.mk₀ aX).comp ξ (zero_add 1) := by
    exact ext_compatibility_of_twoTarget_scalarized_commute
      X Y Z ℓY hℓY ℓZ hℓZ ξ P Q T hmatrixY hmatrixZ
  rcases hendpoint aYZ aX haYZ haX hext with hzero | hone
  · left
    have haYzero : aY = 0 := by
      calc
        aY = biprod.inl ≫ aYZ ≫ biprod.fst := by
          simp [aYZ, aY]
        _ = biprod.inl ≫ (0 : _ ⟶ _) ≫ biprod.fst := by
          rw [hzero.1]
        _ = 0 := by simp
    have haZzero : aZ = 0 := by
      calc
        aZ = biprod.inr ≫ aYZ ≫ biprod.snd := by
          simp [aYZ, aZ]
        _ = biprod.inr ≫ (0 : _ ⟶ _) ≫ biprod.snd := by
          rw [hzero.1]
        _ = 0 := by simp
    have hPzero : P = 0 :=
      (scalarBiproductEnd_eq_zero_iff X hX P).mp hzero.2
    have hQzero : Q = 0 :=
      (scalarBiproductEnd_eq_zero_iff Y hY Q).mp haYzero
    have hTzero : T = 0 :=
      (scalarBiproductEnd_eq_zero_iff Z hZ T).mp haZzero
    refine ⟨?_, ?_, ?_⟩
    · apply LinearMap.toMatrix'.injective
      simpa only [P, map_zero] using hPzero
    · apply LinearMap.toMatrix'.injective
      simpa only [Q, map_zero] using hQzero
    · apply LinearMap.toMatrix'.injective
      simpa only [T, map_zero] using hTzero
  · right
    have haYone : aY = 𝟙 _ := by
      calc
        aY = biprod.inl ≫ aYZ ≫ biprod.fst := by
          simp [aYZ, aY]
        _ = biprod.inl ≫ 𝟙 _ ≫ biprod.fst := by
          rw [hone.1]
        _ = 𝟙 _ := by simp
    have haZone : aZ = 𝟙 _ := by
      calc
        aZ = biprod.inr ≫ aYZ ≫ biprod.snd := by
          simp [aYZ, aZ]
        _ = biprod.inr ≫ 𝟙 _ ≫ biprod.snd := by
          rw [hone.1]
        _ = 𝟙 _ := by simp
    have hPone : P = 1 :=
      (scalarBiproductEnd_eq_id_iff X hX P).mp hone.2
    have hQone : Q = 1 :=
      (scalarBiproductEnd_eq_id_iff Y hY Q).mp haYone
    have hTone : T = 1 :=
      (scalarBiproductEnd_eq_id_iff Z hZ T).mp haZone
    refine ⟨?_, ?_, ?_⟩
    · apply LinearMap.toMatrix'.injective
      simpa only [P, LinearMap.toMatrix'_id] using hPone
    · apply LinearMap.toMatrix'.injective
      simpa only [Q, LinearMap.toMatrix'_id] using hQone
    · apply LinearMap.toMatrix'.injective
      simpa only [T, LinearMap.toMatrix'_id] using hTone

section ModuleCat

variable {R : Type u} [Ring R] [Algebra K R] [Small.{v} R]

/-- A short exact sequence with indecomposable finite-length middle object
supplies the endpoint-idempotent hypothesis in the preceding theorem. -/
theorem shortExact_twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (X Y Z M : ModuleCat.{v} R)
    (hX : 𝟙 X ≠ 0) (hY : 𝟙 Y ≠ 0) (hZ : 𝟙 Z ≠ 0)
    (f : ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) ⟶ M)
    (g : M ⟶ (⨁ fun _ : I ↦ X))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M)
    (ℓY : Ext X Y 1 →ₗ[K] K) (hℓY : Function.Injective ℓY)
    (ℓZ : Ext X Z 1 →ₗ[K] K) (hℓZ : Function.Injective ℓZ) :
    LoewyTwoRankCore.IsTwoTargetIdempotentIndecomposable
      (firstTargetScalarizedExtLinearMap
        X Y Z ℓY hS.extClass)
      (secondTargetScalarizedExtLinearMap
        X Y Z ℓZ hS.extClass) := by
  apply twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
    X Y Z hX hY hZ ℓY hℓY ℓZ hℓZ hS.extClass
  intro a₁ a₃ ha₁ ha₃ hcompat
  exact endpoint_idempotents_trivial_of_extClass_compatibility
    hS hM a₁ a₃ ha₁ ha₃ hcompat

/-- If the common source multiplicity is one, both target multiplicities
in the preceding short-exact two-target model are at most one. -/
theorem shortExact_twoTarget_target_finrank_le_one
    {I J L : Type} [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (X Y Z M : ModuleCat.{v} R)
    (hX : 𝟙 X ≠ 0) (hY : 𝟙 Y ≠ 0) (hZ : 𝟙 Z ≠ 0)
    (f : ((⨁ fun _ : J ↦ Y) ⊞ (⨁ fun _ : L ↦ Z)) ⟶ M)
    (g : M ⟶ (⨁ fun _ : I ↦ X))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M)
    (ℓY : Ext X Y 1 →ₗ[K] K) (hℓY : Function.Injective ℓY)
    (ℓZ : Ext X Z 1 →ₗ[K] K) (hℓZ : Function.Injective ℓZ)
    (hI : Module.finrank K (I → K) = 1) :
    Module.finrank K (J → K) ≤ 1 ∧
      Module.finrank K (L → K) ≤ 1 := by
  apply LoewyTwoRankCore.twoTarget_target_finrank_le_one hI
  exact
    shortExact_twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
      X Y Z M hX hY hZ f g hfg hS hM ℓY hℓY ℓZ hℓZ

end ModuleCat

end OpConjecture.YonedaExtReflection
