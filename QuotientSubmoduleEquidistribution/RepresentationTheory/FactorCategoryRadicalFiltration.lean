import QuotientSubmoduleEquidistribution.CategoryTheory.RadicalLayerFiltration
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryRealization
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderARData
import QuotientSubmoduleEquidistribution.RepresentationTheory.IyamaRadicalLayerReduction
import QuotientSubmoduleEquidistribution.RepresentationTheory.ReverseFactorHomRealization

/-!
# Radical filtration of the literal factor category

This file connects both orientations of the paper's factor-Hom predicates to
the radical-power filtration of the literal ideal quotient.  The only input
is nilpotence of that quotient category's categorical radical.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- Literal factor Hom is nonzero exactly when some categorical radical
layer between the corresponding quotient objects is nonzero. -/
theorem factorHomNonzero_iff_exists_radicalLayer
    (K : Set ι) (p x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    ∀ Q : CategoricalRadical.NilpotentRadicalData
        (σ.FactorCategory K),
      factorHomNonzero σ K p x ↔
        ∃ n, Q.LayerNonzero n
          (σ.factorObject K p) (σ.factorObject K x) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  intro Q
  exact
    (factorHomNonzero_iff_exists_ne_zero_quotient_morphism
      σ K p x).trans
      (Q.exists_ne_zero_iff_exists_layerNonzero
        (σ.factorObject K p) (σ.factorObject K x))

section ARLadder

variable [Fintype ι]

/-- For the actual AR factor-ladder operators, nilpotence and the exact
radical-layer multiplicity formula construct the complete Iyama input.
In particular, factor-Hom detection and eventual ladder vanishing are no
longer independent hypotheses. -/
def factorLadderIyamaInput_of_radicalLayerFormula
    (D : σ.FiniteARTranslationData) (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    ∀ Q : CategoricalRadical.NilpotentRadicalData
        (σ.FactorCategory K),
      (∀ n p x,
        Q.LayerNonzero n
            (σ.factorObject K p) (σ.factorObject K x) ↔
          0 <
            (D.factorLadderData σ K).ladder x n p) →
      FactorLadder.IyamaRadicalLayerInput
        (D.factorLadderData σ K) (factorHomNonzero σ K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  intro Q hlayer
  exact FactorLadder.IyamaRadicalLayerInput.ofNilpotentRadical
    (D.factorLadderData σ K) (σ.factorObject K)
    (factorHomNonzero σ K) Q
    (fun p x ↦
      factorHomNonzero_iff_exists_ne_zero_quotient_morphism
        σ K p x)
    (D.factorLadderData_ladder_nonneg σ K) hlayer

end ARLadder

/-- The reverse factor-Hom predicate is literal nonvanishing of the
oppositely oriented Hom set in the same ideal quotient. -/
theorem reverseFactorHomNonzero_iff_exists_ne_zero_quotient_morphism
    (K : Set ι) (i x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    reverseFactorHomNonzero σ K i x ↔
      ∃ q : σ.factorObject K x ⟶ σ.factorObject K i,
        q ≠ 0 := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := σ.factorFunctor K
  constructor
  · rintro ⟨f, hf⟩
    let fAdd : σ.deletedAddPoint x ⟶ σ.deletedAddPoint i :=
      ObjectProperty.homMk f
    refine ⟨F.map fAdd, ?_⟩
    intro hzero
    apply hf
    exact (I.map_eq_zero_iff fAdd).1 hzero
  · rintro ⟨q, hq⟩
    obtain ⟨f, rfl⟩ := F.map_surjective q
    refine ⟨f.hom, ?_⟩
    intro hfac
    apply hq
    exact (I.map_eq_zero_iff f).2 hfac

/-- Reverse factor Hom is nonzero exactly when some radical layer in the
reverse orientation is nonzero. -/
theorem reverseFactorHomNonzero_iff_exists_radicalLayer
    (K : Set ι) (i x : DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    ∀ Q : CategoricalRadical.NilpotentRadicalData
        (σ.FactorCategory K),
      reverseFactorHomNonzero σ K i x ↔
        ∃ n, Q.LayerNonzero n
          (σ.factorObject K x) (σ.factorObject K i) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  intro Q
  exact
    (reverseFactorHomNonzero_iff_exists_ne_zero_quotient_morphism
      σ K i x).trans
      (Q.exists_ne_zero_iff_exists_layerNonzero
        (σ.factorObject K x) (σ.factorObject K i))

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
