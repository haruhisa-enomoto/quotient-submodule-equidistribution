import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderProjectiveCover
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryKrullSchmidt
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryRadicalNilpotence

/-!
# Finite right tau data for the literal factor category

This file packages the complete surviving skeleton, the canonical
nilpotent radical, and the quotient right tau-sequences into the right-sided
categorical interface used by Iyama's projective-cover theorem.  No chosen
left meshes are required.  Idempotent completeness is kept explicit: it is
the remaining categorical closure property not yet constructed for the
literal ideal quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The literal factor category, with its proved surviving skeleton and
right tau-sequences, is a finite right tau-category as soon as its
idempotents are known to split. -/
def finiteDimensionalFactorCategoryRightTauData
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
    Iyama.FiniteRightTauCategoryData
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
  let Q := σ.factorCategoryNilpotentRadicalData (k := k) (R := R) K
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
  let mesh : σ.FactorCategory K → ShortComplex (σ.FactorCategory K) :=
    fun X ↦ Iyama.shortComplexBiproduct
      (fun i : Fin (n X) ↦
        FiniteARTranslationData.factorCategoryRightMesh
          σ D K (label X i))
  exact
    { obj := σ.factorObject K
      obj_indec := σ.factorObject_indec K
      obj_end_local := σ.factorObject_end_local K
      obj_decomposition := σ.factorCategory_obj_decomposition K
      obj_complete := fun X hX ↦ σ.factorCategory_obj_complete K X hX
      obj_skeletal := fun e ↦ σ.factorObject_skeletal K e
      radical := Q
      rightMesh := mesh
      rightTermIso := fun X ↦ by
        let eComponents :
            (⨁ fun i : Fin (n X) ↦
                (FiniteARTranslationData.factorCategoryRightMesh
                  σ D K (label X i)).X₃) ≅
              ⨁ fun i : Fin (n X) ↦
                σ.factorObject K (label X i) :=
          biproduct.mapIso fun i ↦ eqToIso
            (FiniteARTranslationData.factorCategoryRightMesh_X₃
              σ D K (label X i))
        exact eComponents.trans (decompositionIso X).symm
      rightTau := fun X ↦ by
        exact Iyama.rightTauSequence_shortComplexBiproduct Q
          (fun i : Fin (n X) ↦
            FiniteARTranslationData.factorCategoryRightMesh
              σ D K (label X i))
          (fun i ↦ FiniteARTranslationData.factorCategoryRightTau
            σ D K (label X i)) }

/-- On a surviving indecomposable, the packaged chosen right mesh is
isomorphic to the explicit quotient mesh constructed from the ambient
Auslander--Reiten sequence. -/
theorem finiteDimensionalFactorCategoryRightMesh_factorObject_iso
    (K : Set ι)
    (hidem : IsIdempotentComplete (σ.FactorCategory K))
    (x : DeletedLabel K) :
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let D := σ.finiteDimensionalARTranslationData k R
    Nonempty
      (T.rightMesh (σ.factorObject K x) ≅
        FiniteARTranslationData.factorCategoryRightMesh σ D K x) := by
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
  letI : DecidableEq (DeletedLabel K) := Classical.decEq _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let D := σ.finiteDimensionalARTranslationData k R
  apply Iyama.RightTauSequence.nonempty_iso_of_iso_X₃
    (T.rightTau (σ.factorObject K x))
    (FiniteARTranslationData.factorCategoryRightTau σ D K x)
  exact (T.rightTermIso (σ.factorObject K x)).trans
    (eqToIso
      (FiniteARTranslationData.factorCategoryRightMesh_X₃ σ D K x)).symm

/-- Specialized projective-cover consequence: the `n`th radical layer
between surviving indecomposables is nonzero exactly when the target label
occurs in the `n`th object of the canonical zero-initial right ladder. -/
theorem finiteDimensionalFactorCategory_layerNonzero_iff_rightLadderMultiplicity
    (K : Set ι)
    (hidem : IsIdempotentComplete (σ.FactorCategory K))
    (x p : DeletedLabel K) (n : ℕ) :
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let L := Iyama.RightLadder.zeroInitialRightLadder T
      (σ.factorObject K x)
    T.radical.LayerNonzero n
        (σ.factorObject K p) (σ.factorObject K x) ↔
      0 < T.chosenLabelMultiplicity p (L.Y n) := by
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
  letI : DecidableEq (DeletedLabel K) := Classical.decEq _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  exact
    Iyama.FiniteRightTauCategoryData.zeroInitialRightLadder_layerNonzero_iff_multiplicity_pos
      T (σ.factorObject K x) n p

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
