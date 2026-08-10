import QuotientSubmoduleEquidistribution.CategoryTheory.FiniteGeneratorRadicalNilpotence
import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderEndArtinian
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryRadicalFiltration

/-!
# Nilpotence of the finite factor-category radical

For a finite-dimensional representation-finite algebra, the literal factor
category `add(ind A) / [add K]` has a finite additive generator.  Its
endomorphism ring is a quotient of the Artinian Auslander endomorphism ring,
so the categorical radical is nilpotent.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open AuslanderEquivalence
open AuslanderEquivalence.CoordinateIdempotent
open LegalQuotientDeletionChain

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The full-skeleton additive generator regarded as an object of
`add(ind A)`. -/
def ambientAdditiveGenerator : σ.AddCategory Set.univ :=
  ⟨skeletonGenerator σ, by
    classical
    let ε : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let a : Fin (Fintype.card ι) → ι := fun t ↦ ε.symm t
    exact ⟨{
      index := FintypeCat.of (Fin (Fintype.card ι))
      label := a
      mem := fun _ ↦ Set.mem_univ _
      iso := biproduct.whiskerEquiv ε
        (fun t ↦ eqToIso (by
          simp only [a, Equiv.symm_apply_apply])) }⟩⟩

/-- The full-skeleton generator remains a finite additive generator inside
the explicit full additive subcategory. -/
theorem ambientAdditiveGenerator_isFiniteAddGenerator :
    letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
      σ.addCategoryHasFiniteBiproducts Set.univ
    IsFiniteAddGenerator (σ.ambientAdditiveGenerator) := by
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  intro X
  let P : FiniteAddPresentation (skeletonGenerator σ) X.obj :=
    (FiniteTypeGenerator.additiveGenerator_isFiniteAddGenerator σ
      X.obj).some
  let F := ObjectProperty.ι (σ.generated Set.univ).carrier
  let φ :
      F.obj (⨁ fun _ : Fin P.n ↦ σ.ambientAdditiveGenerator) ≅
        ⨁ fun _ : Fin P.n ↦ skeletonGenerator σ :=
    F.mapBiproduct (fun _ : Fin P.n ↦ σ.ambientAdditiveGenerator)
  refine ⟨{
    n := P.n
    retract :=
      { i := ObjectProperty.homMk (P.retract.i ≫ φ.inv)
        r := ObjectProperty.homMk (φ.hom ≫ P.retract.r)
        retract := ?_ } }⟩
  apply ObjectProperty.hom_ext
  change
    (P.retract.i ≫ φ.inv) ≫ (φ.hom ≫ P.retract.r) =
      𝟙 X.obj
  rw [Category.assoc, φ.inv_hom_id_assoc,
    P.retract.retract]

include k in
/-- The endomorphism ring of the full-skeleton additive generator is
Artinian. -/
theorem ambientAdditiveGenerator_end_isArtinian :
    IsArtinianRing (End (σ.ambientAdditiveGenerator)) := by
  letI (i : ι) : Module k (σ.obj i) :=
    Module.restrictScalars k R (σ.obj i)
  letI (i : ι) : IsScalarTower k R (σ.obj i) :=
    IsScalarTower.restrictScalars k R (σ.obj i)
  letI (i : ι) : FiniteDimensional k (σ.obj i) :=
    Module.Finite.trans R (σ.obj i)
  let m : End (skeletonGenerator σ) ≃*
      End (σ.ambientAdditiveGenerator) :=
    (InducedCategory.endEquiv
      (C := FGModuleCat.{u} R)
      (F := fun X : σ.AddCategory Set.univ ↦ X.obj)
      (X := σ.ambientAdditiveGenerator)).symm
  let e : End (skeletonGenerator σ) ≃+*
      End (σ.ambientAdditiveGenerator) :=
    { m with
      map_add' := fun _ _ ↦ rfl }
  letI : IsArtinianRing (End (skeletonGenerator σ)) :=
    isArtinianRing_skeletonAuslanderAlgebra (K := k) σ
  exact e.isArtinianRing

include k in
/-- The ambient additive category has canonical nilpotent categorical-radical
data under the finite-dimensional representation-finite hypotheses. -/
def ambientAddCategoryNilpotentRadicalData :
    letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
      σ.addCategoryHasFiniteBiproducts Set.univ
    CategoricalRadical.NilpotentRadicalData
      (σ.AddCategory Set.univ) := by
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  letI : IsArtinianRing (End (σ.ambientAdditiveGenerator)) :=
    σ.ambientAdditiveGenerator_end_isArtinian (k := k) (R := R)
  exact CategoricalRadical.nilpotentRadicalDataOfArtinianGenerator
    (σ.ambientAdditiveGenerator)
    (σ.ambientAdditiveGenerator_isFiniteAddGenerator)

/-- The image of the full-skeleton generator in the literal factor
category. -/
abbrev factorGenerator (K : Set ι) : σ.FactorCategory K :=
  (σ.factorFunctor K).obj (σ.ambientAdditiveGenerator)

/-- The quotient generator is a finite additive generator of the literal
factor category. -/
theorem factorGenerator_isFiniteAddGenerator (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
      σ.addCategoryHasFiniteBiproducts Set.univ
    letI : HasFiniteBiproducts (σ.FactorCategory K) :=
      σ.factorQuotientHasFiniteBiproducts Set.univ K
    IsFiniteAddGenerator (σ.factorGenerator K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  exact CategoricalRadical.isFiniteAddGenerator_map
    (σ.factorFunctor K) (σ.ambientAdditiveGenerator)
    (σ.ambientAdditiveGenerator_isFiniteAddGenerator)

include k in
/-- The quotient generator has an Artinian endomorphism ring, as a
surjective ring image of the finite-dimensional skeleton Auslander algebra. -/
theorem factorGenerator_end_isArtinian (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    IsArtinianRing (End (σ.factorGenerator K)) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : IsArtinianRing (End (σ.ambientAdditiveGenerator)) :=
    σ.ambientAdditiveGenerator_end_isArtinian (k := k) (R := R)
  let φ : End (σ.ambientAdditiveGenerator) →+*
      End (σ.factorGenerator K) :=
    { (σ.factorFunctor K).mapEnd
        (σ.ambientAdditiveGenerator) with
      map_zero' := by
        exact (σ.factorFunctor K).map_zero
          (σ.ambientAdditiveGenerator)
          (σ.ambientAdditiveGenerator)
      map_add' := fun f g ↦ by
        exact (σ.factorFunctor K).map_add }
  have hsurjective : Function.Surjective φ := by
    intro q
    obtain ⟨f, rfl⟩ := (σ.factorFunctor K).map_surjective q
    exact ⟨f, rfl⟩
  exact hsurjective.isArtinianRing

/-- The literal factor category has canonical nilpotent categorical-radical
data under the paper's finite-dimensional representation-finite hypotheses. -/
def factorCategoryNilpotentRadicalData (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    CategoricalRadical.NilpotentRadicalData
      (σ.FactorCategory K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  letI : IsArtinianRing (End (σ.factorGenerator K)) :=
    σ.factorGenerator_end_isArtinian (k := k) (R := R) K
  exact CategoricalRadical.nilpotentRadicalDataOfArtinianGenerator
    (σ.factorGenerator K)
    (σ.factorGenerator_isFiniteAddGenerator K)

/-- Paper-facing reduction: in the finite-dimensional setting, the exact
radical-layer multiplicity formula is the sole remaining input needed to
construct the full forward factor-ladder interface.  Radical nilpotence,
factor-Hom separation, nonnegativity, and eventual vanishing are automatic. -/
def finiteDimensionalFactorLadderIyamaInput_of_layerFormula
    (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    let Q := σ.factorCategoryNilpotentRadicalData
      (k := k) (R := R) K
    (∀ n p x,
      Q.LayerNonzero n
          (σ.factorObject K p) (σ.factorObject K x) ↔
        0 <
          (σ.finiteDimensionalFactorLadderData k R K).ladder
            x n p) →
    FactorLadder.IyamaRadicalLayerInput
      (σ.finiteDimensionalFactorLadderData k R K)
      (factorHomNonzero σ K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  intro hlayer
  exact σ.factorLadderIyamaInput_of_radicalLayerFormula
    (σ.finiteDimensionalARTranslationData k R) K
    (σ.factorCategoryNilpotentRadicalData
      (k := k) (R := R) K) hlayer

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
