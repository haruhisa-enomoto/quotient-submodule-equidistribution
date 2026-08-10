import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Degree-one Ext from a short injective presentation

In a linear abelian category, a short exact sequence

`0 ⟶ T ⟶ I ⟶ C ⟶ 0`

with injective middle term computes `Ext¹(Y,T)` as the scalar quotient of
`Hom(Y,C)` by the image of `Hom(Y,I)`.  This file constructs the linear
quotient equivalence and proves its naturality under pullback in `Y`.

The quotient term here is the actual third object of a short exact sequence.
For an exact copresentation `T ⟶ I ⟶ J` whose second map need not be epic,
one must first replace `J` by the cokernel of `T ⟶ I`, equivalently the image
of `I ⟶ J`.  In particular, this is not the unrestricted cokernel of
`Hom(Y,I) ⟶ Hom(Y,J)` unless `I ⟶ J` is epic.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.InjectivePresentationExt

universe uk w v u

variable {k : Type uk} [CommRing k]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [HasExt.{w} C]

/-- The connecting map of a short exact sequence, as a linear map. -/
def connectingLinear {S : ShortComplex C} (hS : S.ShortExact) (Y : C) :
    (Y ⟶ S.X₃) →ₗ[k] Ext.{w} Y S.X₁ 1 :=
  (hS.extClass.postcompOfLinear k Y (rfl : 0 + 1 = 1)).comp
    (Ext.linearEquiv₀ (R := k)).symm.toLinearMap

/-- Postcomposition with the second morphism in a short complex. -/
def presentationPostcompLinear (S : ShortComplex C) (Y : C) :
    (Y ⟶ S.X₂) →ₗ[k] (Y ⟶ S.X₃) :=
  CategoryTheory.Linear.rightComp k Y S.g

/-- The image of postcomposition with the displayed presentation morphism
`S.g`; these are the presentation coboundaries. -/
abbrev presentationRange (S : ShortComplex C) (Y : C) :
    Submodule k (Y ⟶ S.X₃) :=
  (presentationPostcompLinear (k := k) S Y).range

omit [HasExt C] in
@[simp]
theorem mem_presentationRange_iff (S : ShortComplex C) (Y : C)
    (f : Y ⟶ S.X₃) :
    f ∈ presentationRange (k := k) S Y ↔
      ∃ u : Y ⟶ S.X₂, u ≫ S.g = f := by
  rfl

/-- Exactness identifies presentation coboundaries with the kernel of the
connecting map. -/
theorem presentationRange_eq_connectingLinear_ker
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) :
    presentationRange (k := k) S Y =
      (connectingLinear (k := k) hS Y).ker := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    change (Ext.mk₀ (u ≫ S.g)).comp hS.extClass (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀_assoc]
    simp
  · intro hf
    change (Ext.mk₀ f).comp hS.extClass (zero_add 1) = 0 at hf
    obtain ⟨x₂, hx₂⟩ :=
      Ext.covariant_sequence_exact₃
        (X := Y) hS (Ext.mk₀ f) (rfl : 0 + 1 = 1) hf
    refine ⟨Ext.linearEquiv₀ (R := k) x₂, ?_⟩
    apply (Ext.mk₀_bijective Y S.X₃).1
    change Ext.mk₀ (Ext.linearEquiv₀ (R := k) x₂ ≫ S.g) = Ext.mk₀ f
    rw [← Ext.mk₀_comp_mk₀]
    simpa using hx₂

/-- Injectivity of the middle term makes the connecting map surjective. -/
theorem connectingLinear_surjective
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) : Function.Surjective (connectingLinear (k := k) hS Y) := by
  intro ξ
  have hzero :
      ξ.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ :=
    Ext.covariant_sequence_exact₁
      (X := Y) hS ξ hzero (rfl : 0 + 1 = 1)
  refine ⟨Ext.linearEquiv₀ (R := k) x₃, ?_⟩
  simpa [connectingLinear] using hx₃

/-- A short exact sequence with injective middle term computes `Ext¹` as the
quotient by the image of `Hom(Y,S.X₂) -> Hom(Y,S.X₃)` induced by `S.g`. -/
def quotientLinearEquivExtOne
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) :
    ((Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) ≃ₗ[k]
      Ext.{w} Y S.X₁ 1 :=
  (Submodule.quotEquivOfEq
      (presentationRange (k := k) S Y)
      (connectingLinear (k := k) hS Y).ker
      (presentationRange_eq_connectingLinear_ker (k := k) hS Y)).trans
    ((connectingLinear (k := k) hS Y).quotKerEquivOfSurjective
      (connectingLinear_surjective (k := k) hS Y))

@[simp]
theorem quotientLinearEquivExtOne_mk
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) (f : Y ⟶ S.X₃) :
    quotientLinearEquivExtOne (k := k) hS Y (Submodule.Quotient.mk f) =
      (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
  simp [quotientLinearEquivExtOne, connectingLinear]

@[simp]
theorem quotientLinearEquivExtOne_symm_connectingLinear
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (Y : C) (f : Y ⟶ S.X₃) :
    (quotientLinearEquivExtOne (k := k) hS Y).symm
        (connectingLinear (k := k) hS Y f) =
      Submodule.Quotient.mk f := by
  apply (quotientLinearEquivExtOne (k := k) hS Y).injective
  simp [connectingLinear]

/-- Precomposition descends to the presentation quotient. -/
def precompQuotient (S : ShortComplex C)
    {Y' Y : C} (a : Y' ⟶ Y) :
    ((Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) →ₗ[k]
      ((Y' ⟶ S.X₃) ⧸ presentationRange (k := k) S Y') :=
  (presentationRange (k := k) S Y).mapQ
    (presentationRange (k := k) S Y')
    (CategoryTheory.Linear.leftComp k S.X₃ a) (by
      intro f hf
      obtain ⟨u, rfl⟩ := hf
      refine ⟨a ≫ u, ?_⟩
      simp [presentationPostcompLinear, Category.assoc])

omit [HasExt C] in
@[simp]
theorem precompQuotient_mk
    (S : ShortComplex C) {Y' Y : C}
    (a : Y' ⟶ Y) (f : Y ⟶ S.X₃) :
    precompQuotient (k := k) S a (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (a ≫ f) := by
  rfl

/-- Pullback on `Ext¹`, as a linear map. -/
def pullbackLinear (S : ShortComplex C)
    {Y' Y : C} (a : Y' ⟶ Y) :
    Ext.{w} Y S.X₁ 1 →ₗ[k] Ext.{w} Y' S.X₁ 1 :=
  Ext.precompOfLinear (Ext.mk₀ a) k S.X₁ (zero_add 1)

theorem connectingLinear_precomp
    {S : ShortComplex C} (hS : S.ShortExact)
    {Y' Y : C} (a : Y' ⟶ Y) (f : Y ⟶ S.X₃) :
    connectingLinear (k := k) hS Y' (a ≫ f) =
      pullbackLinear (k := k) S a
        (connectingLinear (k := k) hS Y f) := by
  change
    (Ext.mk₀ (a ≫ f)).comp hS.extClass (zero_add 1) =
      (Ext.mk₀ a).comp
        ((Ext.mk₀ f).comp hS.extClass (zero_add 1)) (zero_add 1)
  symm
  exact Ext.mk₀_comp_mk₀_assoc a f hS.extClass

/-- The quotient description of `Ext¹` is natural under pullback. -/
theorem quotientLinearEquivExtOne_precompQuotient
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    {Y' Y : C} (a : Y' ⟶ Y)
    (q : (Y ⟶ S.X₃) ⧸ presentationRange (k := k) S Y) :
    quotientLinearEquivExtOne (k := k) hS Y'
        (precompQuotient (k := k) S a q) =
      pullbackLinear (k := k) S a
        (quotientLinearEquivExtOne (k := k) hS Y q) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp [pullbackLinear]

end OpConjecture.InjectivePresentationExt
