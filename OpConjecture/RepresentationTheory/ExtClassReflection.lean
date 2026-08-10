import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import OpConjecture.RepresentationTheory.LoewyTwoRankCore

noncomputable section

open CategoryTheory

namespace OpConjecture.YonedaExtReflection

open CategoryTheory.Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/--
The converse to `ShortComplex.ShortExact.extClass_naturality`: compatible
morphisms between the two ends of short exact sequences lift to a morphism
between their middle objects.
-/
theorem exists_middle_morphism_of_extClass_compatibility
    {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (a₁ : S₁.X₁ ⟶ S₂.X₁) (a₃ : S₁.X₃ ⟶ S₂.X₃)
    (hcompat :
      h₁.extClass.comp (Ext.mk₀ a₁) (add_zero 1) =
        (Ext.mk₀ a₃).comp h₂.extClass (zero_add 1)) :
    ∃ a₂ : S₁.X₂ ⟶ S₂.X₂,
      a₁ ≫ S₂.f = S₁.f ≫ a₂ ∧
        a₂ ≫ S₂.g = S₁.g ≫ a₃ := by
  have hliftObstruction :
      (Ext.mk₀ (S₁.g ≫ a₃)).comp h₂.extClass (zero_add 1) = 0 := by
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      ← hcompat, ← Ext.comp_assoc_of_third_deg_zero,
      h₁.comp_extClass, Ext.zero_comp]
  obtain ⟨a₂Ext, ha₂Ext⟩ :=
    Ext.covariant_sequence_exact₃
      (X := S₁.X₂) h₂ (Ext.mk₀ (S₁.g ≫ a₃))
      (rfl : 0 + 1 = 1) hliftObstruction
  let a₂₀ : S₁.X₂ ⟶ S₂.X₂ := Ext.addEquiv₀ a₂Ext
  have ha₂₀g : a₂₀ ≫ S₂.g = S₁.g ≫ a₃ := by
    apply (Ext.mk₀_bijective S₁.X₂ S₂.X₃).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa [a₂₀] using ha₂Ext
  have hrestrictionObstruction :
      (Ext.mk₀ (S₁.f ≫ a₂₀)).comp (Ext.mk₀ S₂.g) (add_zero 0) = 0 := by
    simp [ha₂₀g]
  obtain ⟨a₁Ext, ha₁Ext⟩ :=
    Ext.covariant_sequence_exact₂
      (X := S₁.X₁) h₂ (Ext.mk₀ (S₁.f ≫ a₂₀))
      hrestrictionObstruction
  let a₁₀ : S₁.X₁ ⟶ S₂.X₁ := Ext.addEquiv₀ a₁Ext
  have ha₁₀f : a₁₀ ≫ S₂.f = S₁.f ≫ a₂₀ := by
    apply (Ext.mk₀_bijective S₁.X₁ S₂.X₂).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa [a₁₀] using ha₁Ext
  let φ₀ : S₁ ⟶ S₂ :=
    { τ₁ := a₁₀
      τ₂ := a₂₀
      τ₃ := a₃
      comm₁₂ := ha₁₀f
      comm₂₃ := ha₂₀g }
  have hnatural :
      h₁.extClass.comp (Ext.mk₀ a₁₀) (add_zero 1) =
        (Ext.mk₀ a₃).comp h₂.extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ₀
  have hcorrectionObstruction :
      h₁.extClass.comp (Ext.mk₀ (a₁₀ - a₁)) (add_zero 1) = 0 := by
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add,
      Ext.comp_neg, hnatural, hcompat]
    simp
  obtain ⟨kExt, hkExt⟩ :=
    Ext.contravariant_sequence_exact₁ h₁ S₂.X₁
      (Ext.mk₀ (a₁₀ - a₁)) (rfl : 1 + 0 = 1)
      hcorrectionObstruction
  let k : S₁.X₂ ⟶ S₂.X₁ := Ext.addEquiv₀ kExt
  have hfk : S₁.f ≫ k = a₁₀ - a₁ := by
    apply (Ext.mk₀_bijective S₁.X₁ S₂.X₁).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa [k] using hkExt
  refine ⟨a₂₀ - k ≫ S₂.f, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← ha₁₀f, ← Category.assoc, hfk,
      Preadditive.sub_comp]
    simp
  · rw [Preadditive.sub_comp, ha₂₀g, Category.assoc, S₂.zero,
      CategoryTheory.Limits.comp_zero, sub_zero]

/--
Endomorphism form of
`exists_middle_morphism_of_extClass_compatibility`.
-/
theorem exists_middle_endomorphism_of_extClass_compatibility
    {S : ShortComplex C} (hS : S.ShortExact)
    (a₁ : S.X₁ ⟶ S.X₁) (a₃ : S.X₃ ⟶ S.X₃)
    (hcompat :
      hS.extClass.comp (Ext.mk₀ a₁) (add_zero 1) =
        (Ext.mk₀ a₃).comp hS.extClass (zero_add 1)) :
    ∃ a₂ : S.X₂ ⟶ S.X₂,
      a₁ ≫ S.f = S.f ≫ a₂ ∧
        a₂ ≫ S.g = S.g ≫ a₃ :=
  exists_middle_morphism_of_extClass_compatibility hS hS a₁ a₃ hcompat

/--
For a finite-length indecomposable middle module, a compatible pair of
idempotents on the endpoints of a short exact sequence is simultaneously
zero or simultaneously the identity.

The lifted middle map need not itself be idempotent: Fitting's lemma says it
is nilpotent or bijective, and either alternative already forces the stated
conclusion on the endpoint idempotents.
-/
theorem endpoint_idempotents_trivial_of_extClass_compatibility
    {R : Type u} [Ring R] [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact)
    [IsNoetherian R S.X₂] [IsArtinian R S.X₂]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R S.X₂)
    (a₁ : S.X₁ ⟶ S.X₁) (a₃ : S.X₃ ⟶ S.X₃)
    (ha₁ : a₁ ≫ a₁ = a₁) (ha₃ : a₃ ≫ a₃ = a₃)
    (hcompat :
      hS.extClass.comp (Ext.mk₀ a₁) (add_zero 1) =
        (Ext.mk₀ a₃).comp hS.extClass (zero_add 1)) :
    (a₁ = 0 ∧ a₃ = 0) ∨
      (a₁ = 𝟙 _ ∧ a₃ = 𝟙 _) := by
  obtain ⟨a₂, ha₁₂, ha₂₃⟩ :=
    exists_middle_endomorphism_of_extClass_compatibility
      hS a₁ a₃ hcompat
  have hpow₁₂ :
      ∀ n : ℕ,
        ((CategoryTheory.End.of a₁) ^ n) ≫ S.f =
          S.f ≫ ((CategoryTheory.End.of a₂) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, CategoryTheory.End.mul_def, pow_succ,
          CategoryTheory.End.mul_def, Category.assoc, ih,
          ← Category.assoc, ha₁₂, Category.assoc]
  have hpow₂₃ :
      ∀ n : ℕ,
        ((CategoryTheory.End.of a₂) ^ n) ≫ S.g =
          S.g ≫ ((CategoryTheory.End.of a₃) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, CategoryTheory.End.mul_def, pow_succ,
          CategoryTheory.End.mul_def, Category.assoc, ih,
          ← Category.assoc, ha₂₃, Category.assoc]
  rcases hM.isNilpotent_or_bijective a₂.hom with hnil | hbij
  · left
    obtain ⟨n, hnlin⟩ := hnil
    have hn : (CategoryTheory.End.of a₂) ^ n = 0 := by
      apply (ModuleCat.endRingEquiv S.X₂).injective
      change
        (ModuleCat.endRingEquiv S.X₂)
              ((CategoryTheory.End.of a₂) ^ n) =
          (ModuleCat.endRingEquiv S.X₂) 0
      simpa only [map_pow, map_zero, ModuleCat.endRingEquiv_apply] using
        hnlin
    change
      ((CategoryTheory.End.of a₂) ^ n : S.X₂ ⟶ S.X₂) = 0 at hn
    letI : Mono S.f := hS.mono_f
    letI : Epi S.g := hS.epi_g
    have hn₁ : (CategoryTheory.End.of a₁) ^ n = 0 := by
      apply (cancel_mono S.f).mp
      calc
        ((CategoryTheory.End.of a₁) ^ n) ≫ S.f =
            S.f ≫ ((CategoryTheory.End.of a₂) ^ n) :=
          hpow₁₂ n
        _ = S.f ≫ (0 : S.X₂ ⟶ S.X₂) :=
          congrArg (fun z : S.X₂ ⟶ S.X₂ ↦ S.f ≫ z) hn
        _ = 0 := CategoryTheory.Limits.comp_zero
        _ = (0 : S.X₁ ⟶ S.X₁) ≫ S.f :=
          CategoryTheory.Limits.zero_comp.symm
    have hn₃ : (CategoryTheory.End.of a₃) ^ n = 0 := by
      apply (cancel_epi S.g).mp
      calc
        S.g ≫ ((CategoryTheory.End.of a₃) ^ n) =
            ((CategoryTheory.End.of a₂) ^ n) ≫ S.g :=
          (hpow₂₃ n).symm
        _ = (0 : S.X₂ ⟶ S.X₂) ≫ S.g :=
          congrArg (fun z : S.X₂ ⟶ S.X₂ ↦ z ≫ S.g) hn
        _ = 0 := CategoryTheory.Limits.zero_comp
        _ = S.g ≫ (0 : S.X₃ ⟶ S.X₃) :=
          CategoryTheory.Limits.comp_zero.symm
    exact
      ⟨(isIdempotentElem_iff.mpr ha₁).eq_zero_of_isNilpotent ⟨n, hn₁⟩,
        (isIdempotentElem_iff.mpr ha₃).eq_zero_of_isNilpotent ⟨n, hn₃⟩⟩
  · right
    letI : IsIso a₂ :=
      (ConcreteCategory.isIso_iff_bijective a₂).2 hbij
    letI : Mono S.f := hS.mono_f
    letI : Epi S.g := hS.epi_g
    haveI : Mono a₁ := by
      constructor
      intro Z x y hxy
      apply (cancel_mono S.f).mp
      apply (cancel_mono a₂).mp
      simpa only [Category.assoc, ha₁₂] using
        congrArg (fun q ↦ q ≫ S.f) hxy
    haveI : Epi a₃ := by
      constructor
      intro Z x y hxy
      apply (cancel_epi S.g).mp
      apply (cancel_epi a₂).mp
      simpa only [← Category.assoc, ha₂₃] using
        congrArg (fun q ↦ S.g ≫ q) hxy
    constructor
    · rw [← cancel_mono a₁, ha₁, Category.id_comp]
    · rw [← cancel_epi a₃, ha₃, Category.comp_id]

end OpConjecture.YonedaExtReflection
