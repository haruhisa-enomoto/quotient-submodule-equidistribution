import OpConjecture.RepresentationTheory.ExtForkSemisimpleLayers
import OpConjecture.RepresentationTheory.SerialRingBridge

/-!
# Reductions toward the Artinian serial endpoint

This file develops general categorical and module-theoretic reductions for
the remaining serial-ring step.  It constructs no bound quiver algebra and
uses no classification of modules over a concrete algebra.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.SerialEndpointReduction

universe w v

variable {C : Type v} [Category.{w} C] [Abelian C]
  [HasFiniteBiproducts C] [HasExt C]

/-- The `(left,left)` entry of a binary-by-binary Yoneda extension. -/
def extLL {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1) : Ext S P 1 :=
  (Ext.mk₀ biprod.inl).comp
    (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) (zero_add 1)

/-- The `(left,right)` entry of a binary-by-binary Yoneda extension. -/
def extLR {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1) : Ext S Q 1 :=
  (Ext.mk₀ biprod.inl).comp
    (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) (zero_add 1)

/-- The `(right,left)` entry of a binary-by-binary Yoneda extension. -/
def extRL {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1) : Ext T P 1 :=
  (Ext.mk₀ biprod.inr).comp
    (ξ.comp (Ext.mk₀ biprod.fst) (add_zero 1)) (zero_add 1)

/-- The `(right,right)` entry of a binary-by-binary Yoneda extension. -/
def extRR {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1) : Ext T Q 1 :=
  (Ext.mk₀ biprod.inr).comp
    (ξ.comp (Ext.mk₀ biprod.snd) (add_zero 1)) (zero_add 1)

omit [HasFiniteBiproducts C] in
theorem ext_eq_of_four_entries_eq
    {S T P Q : C} {ξ η : Ext (S ⊞ T) (P ⊞ Q) 1}
    (hLL : extLL ξ = extLL η)
    (hLR : extLR ξ = extLR η)
    (hRL : extRL ξ = extRL η)
    (hRR : extRR ξ = extRR η) :
    ξ = η := by
  apply Ext.addEquivBiprod.injective
  apply Prod.ext
  · apply Ext.biprodAddEquiv.injective
    exact Prod.ext hLL hRL
  · apply Ext.biprodAddEquiv.injective
    exact Prod.ext hLR hRR

omit [HasFiniteBiproducts C] in
/-- Vanishing off-diagonal entries make the two left-block endpoint
projections compatible with the Yoneda extension. -/
theorem diagonal_projection_compatible
    {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1)
    (hLR : extLR ξ = 0) (hRL : extRL ξ = 0) :
    ξ.comp
        (Ext.mk₀
          (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
            (𝟙 P) (0 : Q ⟶ Q)))
        (add_zero 1) =
      (Ext.mk₀
          (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
            (𝟙 S) (0 : T ⟶ T))).comp ξ (zero_add 1) := by
  apply ext_eq_of_four_entries_eq
  · simp [extLL,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd]
  · simpa [extLR,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd,
      Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀] using hLR.symm
  · simpa [extRL,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd,
      Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀] using hRL
  · simp [extRR,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd]

omit [HasFiniteBiproducts C] in
/-- Vanishing diagonal entries make the left kernel projection compatible
with the right quotient projection. -/
theorem antidiagonal_projection_compatible
    {S T P Q : C} (ξ : Ext (S ⊞ T) (P ⊞ Q) 1)
    (hLL : extLL ξ = 0) (hRR : extRR ξ = 0) :
    ξ.comp
        (Ext.mk₀
          (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
            (𝟙 P) (0 : Q ⟶ Q)))
        (add_zero 1) =
      (Ext.mk₀
          (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
            (0 : S ⟶ S) (𝟙 T))).comp ξ (zero_add 1) := by
  apply ext_eq_of_four_entries_eq
  · simpa [extLL,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd,
      Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀] using hLL
  · simp [extLR,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd]
  · simp [extRL,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd]
  · simpa [extRR,
      OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd,
      Ext.comp_assoc_of_second_deg_zero,
      Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀] using hRR.symm

section ModuleCategory

universe u

variable {R : Type u} [Ring R] [Small.{v} R]

/-- An indecomposable finite-length middle term forbids a block-diagonal
binary-by-binary extension with two nonzero kernel blocks. -/
theorem offdiagonal_entries_not_both_zero
    {S T P Q M : ModuleCat.{v} R}
    (hP : 𝟙 P ≠ 0) (hQ : 𝟙 Q ≠ 0)
    (f : P ⊞ Q ⟶ M) (g : M ⟶ S ⊞ T) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    ¬ (extLR hS.extClass = 0 ∧ extRL hS.extClass = 0) := by
  rintro ⟨hLR, hRL⟩
  let p : P ⊞ Q ⟶ P ⊞ Q :=
    OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
      (𝟙 P) (0 : Q ⟶ Q)
  let q : S ⊞ T ⟶ S ⊞ T :=
    OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
      (𝟙 S) (0 : T ⟶ T)
  have hp : p ≫ p = p := by
    dsimp [p]
    rw [OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_comp]
    simp
  have hq : q ≫ q = q := by
    dsimp [q]
    rw [OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_comp]
    simp
  have hcompat :
      hS.extClass.comp (Ext.mk₀ p) (add_zero 1) =
        (Ext.mk₀ q).comp hS.extClass (zero_add 1) :=
    diagonal_projection_compatible hS.extClass hLR hRL
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM p q hp hq hcompat with hzero | hone
  · exact hP <|
      (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_eq_zero_iff
        (𝟙 P) (0 : Q ⟶ Q)).mp hzero.1 |>.1
  · exact hQ <|
      ((OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_eq_id_iff
        (𝟙 P) (0 : Q ⟶ Q)).mp hone.1 |>.2).symm

/-- An indecomposable finite-length middle term likewise forbids a
block-antidiagonal binary-by-binary extension. -/
theorem diagonal_entries_not_both_zero
    {S T P Q M : ModuleCat.{v} R}
    (hP : 𝟙 P ≠ 0) (hQ : 𝟙 Q ≠ 0)
    (f : P ⊞ Q ⟶ M) (g : M ⟶ S ⊞ T) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M) :
    ¬ (extLL hS.extClass = 0 ∧ extRR hS.extClass = 0) := by
  rintro ⟨hLL, hRR⟩
  let p : P ⊞ Q ⟶ P ⊞ Q :=
    OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
      (𝟙 P) (0 : Q ⟶ Q)
  let q : S ⊞ T ⟶ S ⊞ T :=
    OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd
      (0 : S ⟶ S) (𝟙 T)
  have hp : p ≫ p = p := by
    dsimp [p]
    rw [OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_comp]
    simp
  have hq : q ≫ q = q := by
    dsimp [q]
    rw [OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_comp]
    simp
  have hcompat :
      hS.extClass.comp (Ext.mk₀ p) (add_zero 1) =
        (Ext.mk₀ q).comp hS.extClass (zero_add 1) :=
    antidiagonal_projection_compatible hS.extClass hLL hRR
  rcases
      OpConjecture.YonedaExtReflection.endpoint_idempotents_trivial_of_extClass_compatibility
        hS hM p q hp hq hcompat with hzero | hone
  · exact hP <|
      (OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_eq_zero_iff
        (𝟙 P) (0 : Q ⟶ Q)).mp hzero.1 |>.1
  · exact hQ <|
      ((OpConjecture.YonedaExtReflection.blockDiagonalBiprodEnd_eq_id_iff
        (𝟙 P) (0 : Q ⟶ Q)).mp hone.1 |>.2).symm

end ModuleCategory

/-- A two-by-two support with no empty row or column and degree at most one
at both endpoints is either diagonal or antidiagonal. -/
theorem binary_support_diagonal_or_antidiagonal
    {α β γ δ : Prop} [Decidable α] [Decidable β]
    (row₁ : ¬ (¬ α ∧ ¬ β))
    (col₁ : ¬ (¬ α ∧ ¬ γ))
    (row₁_degree : ¬ (α ∧ β))
    (row₂_degree : ¬ (γ ∧ δ))
    (col₁_degree : ¬ (α ∧ γ)) :
    (¬ β ∧ ¬ γ) ∨ (¬ α ∧ ¬ δ) := by
  by_cases hα : α
  · left
    exact ⟨fun hβ ↦ row₁_degree ⟨hα, hβ⟩,
      fun hγ ↦ col₁_degree ⟨hα, hγ⟩⟩
  · right
    have hβ : β := by
      by_contra h
      exact row₁ ⟨hα, h⟩
    have hγ : γ := by
      by_contra h
      exact col₁ ⟨hα, h⟩
    exact ⟨hα, fun hδ ↦ row₂_degree ⟨hγ, hδ⟩⟩

section ModuleCategory

universe u

variable {R : Type u} [Ring R] [Small.{v} R]

/-- The categorical two-by-two matching obstruction.  If each row and one
column of the four simple-endpoint `Ext¹` entries has degree at most one,
then a short exact sequence with four nonzero endpoint blocks cannot have
an indecomposable finite-length middle term. -/
theorem false_of_binary_ext_degree_one
    {S T P Q M : ModuleCat.{v} R}
    (hS₀ : 𝟙 S ≠ 0)
    (hP₀ : 𝟙 P ≠ 0) (hQ₀ : 𝟙 Q ≠ 0)
    (f : P ⊞ Q ⟶ M) (g : M ⟶ S ⊞ T) (hfg : f ≫ g = 0)
    (hseq : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R M] [IsArtinian R M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R M)
    (hRowS :
      ¬ (extLL hseq.extClass ≠ 0 ∧ extLR hseq.extClass ≠ 0))
    (hRowT :
      ¬ (extRL hseq.extClass ≠ 0 ∧ extRR hseq.extClass ≠ 0))
    (hColP :
      ¬ (extLL hseq.extClass ≠ 0 ∧ extRL hseq.extClass ≠ 0)) :
    False := by
  classical
  have hKernel₀ : 𝟙 (P ⊞ Q) ≠ 0 := by
    intro h
    apply hP₀
    simpa using congrArg (fun z ↦ biprod.inl ≫ z ≫ biprod.fst) h
  have hQuotient₀ : 𝟙 (S ⊞ T) ≠ 0 := by
    intro h
    apply hS₀
    simpa using congrArg (fun z ↦ biprod.inl ≫ z ≫ biprod.fst) h
  have hRowSClass :
      (Ext.mk₀ biprod.inl).comp hseq.extClass (zero_add 1) ≠ 0 :=
    OpConjecture.ExtForkSemisimpleLayers.biprod_inl_comp_extClass_ne_zero
      hKernel₀ hS₀ f g hfg hseq hM
  have hRowSNonempty :
      ¬ (¬ extLL hseq.extClass ≠ 0 ∧
        ¬ extLR hseq.extClass ≠ 0) := by
    rintro ⟨hLL, hLR⟩
    apply hRowSClass
    apply Ext.addEquivBiprod.injective
    apply Prod.ext
    · simpa [extLL, Ext.comp_assoc_of_second_deg_zero,
        Ext.comp_assoc_of_third_deg_zero] using (not_ne_iff.mp hLL)
    · simpa [extLR, Ext.comp_assoc_of_second_deg_zero,
        Ext.comp_assoc_of_third_deg_zero] using (not_ne_iff.mp hLR)
  have hColPClass :
      hseq.extClass.comp (Ext.mk₀ biprod.fst) (add_zero 1) ≠ 0 :=
    OpConjecture.ExtForkSemisimpleLayers.extClass_comp_biprod_fst_ne_zero
      hP₀ hQuotient₀ f g hfg hseq hM
  have hColPNonempty :
      ¬ (¬ extLL hseq.extClass ≠ 0 ∧
        ¬ extRL hseq.extClass ≠ 0) := by
    rintro ⟨hLL, hRL⟩
    apply hColPClass
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa [extLL, Ext.comp_assoc_of_second_deg_zero,
        Ext.comp_assoc_of_third_deg_zero] using (not_ne_iff.mp hLL)
    · simpa [extRL, Ext.comp_assoc_of_second_deg_zero,
        Ext.comp_assoc_of_third_deg_zero] using (not_ne_iff.mp hRL)
  rcases binary_support_diagonal_or_antidiagonal
      hRowSNonempty hColPNonempty hRowS hRowT hColP with
    hDiagonal | hAntidiagonal
  · apply offdiagonal_entries_not_both_zero
      hP₀ hQ₀ f g hfg hseq hM
    exact ⟨not_ne_iff.mp hDiagonal.1, not_ne_iff.mp hDiagonal.2⟩
  · apply diagonal_entries_not_both_zero
      hP₀ hQ₀ f g hfg hseq hM
    exact ⟨not_ne_iff.mp hAntidiagonal.1,
      not_ne_iff.mp hAntidiagonal.2⟩

end ModuleCategory

section SkeletonSupport

universe u i

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {κ : Type i} [Finite κ]
  (τ : OpConjecture.IndecomposableSkeleton.{u, i, u} A κ)

open OpConjecture.GabrielArrowBridge
open OpConjecture.ExtDegreeNakayamaReduction

omit [IsAlgClosed K] [IsArtinianRing A] [Finite κ] in
/-- Source- and target-degree one rule out an indecomposable extension whose
kernel and quotient each visibly split into two *distinct* chosen simple
types.  This is the first genuine two-sided matching case in the serial-ring
argument; repeated isotypic blocks require the separate rank-normal-form
step. -/
theorem false_of_two_distinct_simple_kernel_and_quotient
    (hFinite : FiniteExtOneSupport (K := K) τ)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) τ))
    (hTarget :
      Function.Injective
        (ExtGabrielArrowIndex.target (K := K) τ))
    (s t p q : τ.SimpleIndex) (hst : s ≠ t) (hpq : p ≠ q)
    {M : ModuleCat.{u} A}
    (f : (τ.obj p.1).obj ⊞ (τ.obj q.1).obj ⟶ M)
    (g : M ⟶ (τ.obj s.1).obj ⊞ (τ.obj t.1).obj)
    (hfg : f ≫ g = 0)
    (hseq : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian A M] [IsArtinian A M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A M) :
    False := by
  letI : IsSimpleModule A (τ.obj s.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (τ.obj s.1)).mp s.2
  letI : IsSimpleModule A (τ.obj t.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (τ.obj t.1)).mp t.2
  letI : IsSimpleModule A (τ.obj p.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (τ.obj p.1)).mp p.2
  letI : IsSimpleModule A (τ.obj q.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (τ.obj q.1)).mp q.2
  letI : Simple (τ.obj s.1).obj :=
    (simple_iff_isSimpleModule' (τ.obj s.1).obj).mpr inferInstance
  letI : Simple (τ.obj p.1).obj :=
    (simple_iff_isSimpleModule' (τ.obj p.1).obj).mpr inferInstance
  letI : Simple (τ.obj q.1).obj :=
    (simple_iff_isSimpleModule' (τ.obj q.1).obj).mpr inferInstance
  letI : Nontrivial (τ.obj s.1) :=
    IsSimpleModule.nontrivial A (τ.obj s.1)
  letI : Nontrivial (τ.obj p.1) :=
    IsSimpleModule.nontrivial A (τ.obj p.1)
  letI : Nontrivial (τ.obj q.1) :=
    IsSimpleModule.nontrivial A (τ.obj q.1)
  have hRowS :
      ¬ (extLL hseq.extClass ≠ 0 ∧ extLR hseq.extClass ≠ 0) := by
    rintro ⟨hLL, hLR⟩
    letI : FiniteDimensional K (ExtOne τ s p) := hFinite s p
    letI : FiniteDimensional K (ExtOne τ s q) := hFinite s q
    letI : Nontrivial (ExtOne τ s p) :=
      ⟨extLL hseq.extClass, 0, hLL⟩
    letI : Nontrivial (ExtOne τ s q) :=
      ⟨extLR hseq.extClass, 0, hLR⟩
    let a : ExtGabrielArrowIndex (K := K) τ :=
      ⟨s, p, ⟨0, Module.finrank_pos⟩⟩
    let b : ExtGabrielArrowIndex (K := K) τ :=
      ⟨s, q, ⟨0, Module.finrank_pos⟩⟩
    apply hpq
    exact congrArg (ExtGabrielArrowIndex.target τ) (hSource (by rfl :
      ExtGabrielArrowIndex.source τ a =
        ExtGabrielArrowIndex.source τ b))
  have hRowT :
      ¬ (extRL hseq.extClass ≠ 0 ∧ extRR hseq.extClass ≠ 0) := by
    rintro ⟨hRL, hRR⟩
    letI : FiniteDimensional K (ExtOne τ t p) := hFinite t p
    letI : FiniteDimensional K (ExtOne τ t q) := hFinite t q
    letI : Nontrivial (ExtOne τ t p) :=
      ⟨extRL hseq.extClass, 0, hRL⟩
    letI : Nontrivial (ExtOne τ t q) :=
      ⟨extRR hseq.extClass, 0, hRR⟩
    let a : ExtGabrielArrowIndex (K := K) τ :=
      ⟨t, p, ⟨0, Module.finrank_pos⟩⟩
    let b : ExtGabrielArrowIndex (K := K) τ :=
      ⟨t, q, ⟨0, Module.finrank_pos⟩⟩
    apply hpq
    exact congrArg (ExtGabrielArrowIndex.target τ) (hSource (by rfl :
      ExtGabrielArrowIndex.source τ a =
        ExtGabrielArrowIndex.source τ b))
  have hColP :
      ¬ (extLL hseq.extClass ≠ 0 ∧ extRL hseq.extClass ≠ 0) := by
    rintro ⟨hLL, hRL⟩
    letI : FiniteDimensional K (ExtOne τ s p) := hFinite s p
    letI : FiniteDimensional K (ExtOne τ t p) := hFinite t p
    letI : Nontrivial (ExtOne τ s p) :=
      ⟨extLL hseq.extClass, 0, hLL⟩
    letI : Nontrivial (ExtOne τ t p) :=
      ⟨extRL hseq.extClass, 0, hRL⟩
    let a : ExtGabrielArrowIndex (K := K) τ :=
      ⟨s, p, ⟨0, Module.finrank_pos⟩⟩
    let b : ExtGabrielArrowIndex (K := K) τ :=
      ⟨t, p, ⟨0, Module.finrank_pos⟩⟩
    apply hst
    exact congrArg (ExtGabrielArrowIndex.source τ) (hTarget (by rfl :
      ExtGabrielArrowIndex.target τ a =
        ExtGabrielArrowIndex.target τ b))
  exact false_of_binary_ext_degree_one
    (CategoryTheory.id_nonzero _)
    (CategoryTheory.id_nonzero _)
    (CategoryTheory.id_nonzero _)
    f g hfg hseq hM hRowS hRowT hColP

end SkeletonSupport

section UniserialGeneration

universe u i

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {κ : Type i}
  (τ : OpConjecture.IndecomposableSkeleton.{u, i, u} R κ)

/-- The right-serial projective boundary already implies the first
constructive ingredient in Nakayama's decomposition theorem: every chosen
nonzero indecomposable contains a nonzero uniserial submodule, namely the
range of a nonzero component of a projective presentation. -/
theorem exists_nonzero_uniserial_submodule_of_projective_boundary
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton τ)
    (i : κ) :
    ∃ U : Submodule R (τ.obj i),
      U ≠ ⊥ ∧ OpConjecture.IsUniserialModule R U := by
  classical
  obtain ⟨P⟩ :=
    OpConjecture.NakayamaRepresentationFiniteBridge.inFac_projectiveLabels
      τ (τ.obj i)
  letI : Epi P.map := P.epi
  have hmap : P.map ≠ 0 := by
    intro hzero
    have hz : IsZero (τ.obj i) :=
      IsZero.of_epi_eq_zero P.map hzero
    have hz' :
        IsZero
          ((forget₂ (FGModuleCat.{u} R)
            (ModuleCat.{u} R)).obj (τ.obj i)) :=
      (forget₂ (FGModuleCat.{u} R)
        (ModuleCat.{u} R)).map_isZero hz
    letI : Nontrivial (τ.obj i) := (τ.indecomposable i).nontrivial
    exact
      not_subsingleton (τ.obj i)
        ((ModuleCat.isZero_iff_subsingleton).mp hz')
  have hcomponent :
      ∃ t : P.index,
        biproduct.ι (fun a : P.index ↦ τ.obj (P.label a)) t ≫
          P.map ≠ 0 := by
    by_contra h
    push Not at h
    apply hmap
    apply biproduct.hom_ext'
    intro t
    exact h t
  obtain ⟨t, ht⟩ := hcomponent
  let g : τ.obj (P.label t) ⟶ τ.obj i :=
    biproduct.ι (fun a : P.index ↦ τ.obj (P.label a)) t ≫ P.map
  let U : Submodule R (τ.obj i) := LinearMap.range g.hom.hom
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply ht
    apply FGModuleCat.hom_ext
    exact LinearMap.range_eq_bot.mp hbot
  have hSource : OpConjecture.IsUniserialModule R (τ.obj (P.label t)) :=
    hProjective (P.label t) (P.mem t)
  have hQuotient :
      OpConjecture.IsUniserialModule R
        ((τ.obj (P.label t)) ⧸ LinearMap.ker g.hom.hom) :=
    hSource.quotient (LinearMap.ker g.hom.hom)
  refine ⟨U, hUne, ?_⟩
  exact
    OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
      g.hom.hom.quotKerEquivRange hQuotient

/-- Noetherianity upgrades the preceding seed to a maximal nonzero
uniserial submodule.  The remaining classical serial-ring step is to prove
that such a maximal uniserial submodule splits (over the appropriate
radical-power quotient). -/
theorem exists_maximal_nonzero_uniserial_submodule_of_projective_boundary
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton τ)
    (i : κ) :
    ∃ U : Submodule R (τ.obj i),
      U ≠ ⊥ ∧
        OpConjecture.IsUniserialModule R U ∧
          ∀ V : Submodule R (τ.obj i),
            U ≤ V →
              V ≠ ⊥ →
                OpConjecture.IsUniserialModule R V → V ≤ U := by
  obtain ⟨U, hUne, hU⟩ :=
    exists_nonzero_uniserial_submodule_of_projective_boundary
      τ hProjective i
  obtain ⟨V, hUV, hVmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT
      (fun W : Submodule R (τ.obj i) ↦
        W ≠ ⊥ ∧ OpConjecture.IsUniserialModule R W)
      U ⟨hUne, hU⟩
  exact ⟨V, hVmax.1.1, hVmax.1.2,
    fun W hVW hWne hW ↦ hVmax.2 ⟨hWne, hW⟩ hVW⟩

/-- The exact maximal-summand input in the finite Nakayama decomposition
argument.  The standard serial-ring proof obtains this by proving a
maximal-length uniserial submodule injective over the radical-power quotient
annihilating the ambient module. -/
def MaximalNonzeroUniserialSubmodulesSplit : Prop :=
  ∀ (i : κ) (U : Submodule R (τ.obj i)),
    U ≠ ⊥ →
      OpConjecture.IsUniserialModule R U →
        (∀ V : Submodule R (τ.obj i),
          U ≤ V →
            V ≠ ⊥ →
              OpConjecture.IsUniserialModule R V → V ≤ U) →
          ∃ V : Submodule R (τ.obj i), IsCompl U V

/-- Once the maximal uniserial submodule splits, indecomposability forces
it to be the whole object.  Thus the projective boundary plus the exact
maximal-splitting input proves the full Nakayama skeleton. -/
theorem isNakayamaSkeleton_of_projective_boundary_of_maximal_uniserial_splits
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton τ)
    (hSplit : MaximalNonzeroUniserialSubmodulesSplit τ) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton τ := by
  intro i
  obtain ⟨U, hUne, hU, hUmax⟩ :=
    exists_maximal_nonzero_uniserial_submodule_of_projective_boundary
      τ hProjective i
  obtain ⟨V, hUV⟩ := hSplit i U hUne hU hUmax
  rcases (τ.indecomposable i).eq_bot_or_eq_bot hUV with hUbot | hVbot
  · exact False.elim (hUne hUbot)
  · have hUtop : U = ⊤ := by
      apply top_unique
      simpa [hVbot] using hUV.sup_eq_top.ge
    exact
      OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
        (LinearEquiv.ofTop U hUtop) hU

end UniserialGeneration

section UniserialCogeneration

universe u i

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {K R : Type u}
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {κ : Type i} [Finite κ]
  (τ : OpConjecture.IndecomposableSkeleton.{u, i, u} R κ)

open OpConjecture.IndecomposableSkeleton.FaithfulCore

include K in
/-- Dually, the injective uniserial boundary supplies a nonzero uniserial
quotient of every chosen indecomposable: take a nonzero component of the
finite injective-cogenerator embedding and then its range. -/
theorem exists_nonzero_uniserial_quotient_of_injective_boundary
    (hInjective :
      OpConjecture.SerialRingBridge.IsInjectiveNakayamaSkeleton τ)
    (i : κ) :
    ∃ U : FGModuleCat.{u} R,
      Nontrivial U ∧
        OpConjecture.IsUniserialModule R U ∧
          ∃ q : τ.obj i ⟶ U, Epi q := by
  classical
  have hCogenerates :
      OpConjecture.IndecomposableSkeleton.InSubOfModule
        (injectiveCogenerator τ) (τ.obj i) :=
    (concreteBasicInjectiveCogeneratorData τ K).cogenerates (τ.obj i)
  have hSub :
      τ.InSub (injectiveLabels τ) (τ.obj i) :=
    (τ.inSubOfModule_basicModule_iff
      (injectiveCogeneratorSupport τ) (τ.obj i)).mp hCogenerates
  obtain ⟨P⟩ := hSub
  letI : Mono P.map := P.mono
  have hmap : P.map ≠ 0 := by
    intro hzero
    have hz : IsZero (τ.obj i) :=
      IsZero.of_mono_eq_zero P.map hzero
    have hz' :
        IsZero
          ((forget₂ (FGModuleCat.{u} R)
            (ModuleCat.{u} R)).obj (τ.obj i)) :=
      (forget₂ (FGModuleCat.{u} R)
        (ModuleCat.{u} R)).map_isZero hz
    letI : Nontrivial (τ.obj i) := (τ.indecomposable i).nontrivial
    exact
      not_subsingleton (τ.obj i)
        ((ModuleCat.isZero_iff_subsingleton).mp hz')
  have hcomponent :
      ∃ t : P.index,
        P.map ≫
          biproduct.π (fun a : P.index ↦ τ.obj (P.label a)) t ≠ 0 := by
    by_contra h
    push Not at h
    apply hmap
    apply biproduct.hom_ext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hcomponent
  let g : τ.obj i ⟶ τ.obj (P.label t) :=
    P.map ≫ biproduct.π (fun a : P.index ↦ τ.obj (P.label a)) t
  let V : Submodule R (τ.obj (P.label t)) :=
    LinearMap.range g.hom.hom
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply ht
    apply FGModuleCat.hom_ext
    exact LinearMap.range_eq_bot.mp hbot
  let U : FGModuleCat.{u} R := FGModuleCat.of R V
  let q : τ.obj i ⟶ U :=
    FGModuleCat.ofHom g.hom.hom.rangeRestrict
  have hqSurjective : Function.Surjective q.hom.hom :=
    LinearMap.surjective_rangeRestrict g.hom.hom
  letI : Epi q :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      hqSurjective
  have hTarget :
      OpConjecture.IsUniserialModule R (τ.obj (P.label t)) :=
    hInjective (P.label t) (P.mem t)
  have hU : OpConjecture.IsUniserialModule R U :=
    hTarget.submodule V
  haveI : Nontrivial U :=
    Submodule.nontrivial_iff_ne_bot.mpr hVne
  exact ⟨U, inferInstance, hU, q, inferInstance⟩

end UniserialCogeneration

section HomComparability

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {P X : FGModuleCat.{u} R}

omit [IsNoetherianRing R] in
/-- If the range of `f : P → X` lies in the range of `g` and `P` is
projective, then `f` is an endomorphism multiple of `g`.  This is the
lifting step in the Hom-uniserial comparison. -/
theorem exists_endomorphism_comp_eq_of_range_le
    [CategoryTheory.Projective P]
    (f g : P ⟶ X)
    (hRange : LinearMap.range f.hom.hom ≤ LinearMap.range g.hom.hom) :
    ∃ a : P ⟶ P, a ≫ g = f := by
  let G : FGModuleCat.{u} R :=
    FGModuleCat.of R (LinearMap.range g.hom.hom)
  let q : P ⟶ G :=
    FGModuleCat.ofHom g.hom.hom.rangeRestrict
  have hqSurjective : Function.Surjective q.hom.hom :=
    LinearMap.surjective_rangeRestrict g.hom.hom
  letI : Epi q :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      hqSurjective
  let inc : G ⟶ X :=
    FGModuleCat.ofHom (LinearMap.range g.hom.hom).subtype
  let f' : P ⟶ G :=
    FGModuleCat.ofHom <|
      f.hom.hom.codRestrict (LinearMap.range g.hom.hom)
        (fun x ↦ hRange ⟨x, rfl⟩)
  have hqinc : q ≫ inc = g := by
    apply FGModuleCat.hom_ext
    rfl
  have hfinc : f' ≫ inc = f := by
    apply FGModuleCat.hom_ext
    rfl
  let a : P ⟶ P := CategoryTheory.Projective.factorThru f' q
  refine ⟨a, ?_⟩
  calc
    a ≫ g = a ≫ (q ≫ inc) := by rw [hqinc]
    _ = (a ≫ q) ≫ inc := by simp only [Category.assoc]
    _ = f' ≫ inc := by
      rw [CategoryTheory.Projective.factorThru_comp]
    _ = f := hfinc

omit [IsNoetherianRing R] in
/-- **Hom-uniserial comparability.**  Maps from a projective module into a
uniserial module are comparable under right multiplication by
endomorphisms of the projective source.  This is the formal core of the
comparison used in the standard proof that dominant projective summands are
injective over radical-power quotients. -/
theorem hom_to_uniserial_factor_comparable
    [CategoryTheory.Projective P]
    (hX : OpConjecture.IsUniserialModule R X)
    (f g : P ⟶ X) :
    (∃ a : P ⟶ P, a ≫ g = f) ∨
      (∃ b : P ⟶ P, b ≫ f = g) := by
  unfold OpConjecture.IsUniserialModule at hX
  rcases hX.total
      (LinearMap.range f.hom.hom)
      (LinearMap.range g.hom.hom) with hfg | hgf
  · exact Or.inl <|
      exists_endomorphism_comp_eq_of_range_le f g hfg
  · exact Or.inr <|
      exists_endomorphism_comp_eq_of_range_le g f hgf

end HomComparability

end OpConjecture.SerialEndpointReduction
