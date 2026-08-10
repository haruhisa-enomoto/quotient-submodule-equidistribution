import OpConjecture.RepresentationTheory.FactorCategoryTauData
import OpConjecture.RepresentationTheory.FactorLadderCategoricalRecurrence
import OpConjecture.RepresentationTheory.FactorHomRealization

/-!
# The factor-ladder recurrence in the literal factor category

This file identifies the two numerical operators in the manuscript with the
left and middle terms of the chosen right meshes in the literal ideal
quotient. The constructed two-sided quotient tau-category discharges
Iyama's orthogonality and makes the forward factor-ladder criterion
unconditional.
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

/-- On a surviving indecomposable, the middle term of the packaged right
mesh has exactly the multiplicity vector prescribed by `theta_D`. -/
theorem finiteDimensionalFactorCategoryRightMesh_theta_basis
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
    let A := σ.finiteDimensionalFactorLadderData k R K
    A.theta (FactorLadder.basis x) =
      T.chosenMultiplicityVector
        (T.rightMesh (σ.factorObject K x)).X₂ := by
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
  let D := σ.finiteDimensionalARTranslationData k R
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let A := σ.finiteDimensionalFactorLadderData k R K
  let S := FiniteARTranslationData.factorCategoryRightMesh σ D K x
  obtain ⟨ePack⟩ :=
    σ.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
      (k := k) (R := R) K hidem x
  have hpack :
      T.chosenMultiplicityVector (T.rightMesh (σ.factorObject K x)).X₂ =
        T.chosenMultiplicityVector S.X₂ :=
    T.chosenMultiplicityVector_iso_invariant
      ⟨ShortComplex.π₂.mapIso ePack⟩
  let AR := FiniteARTranslationData.factorLadderRightARAt σ D x.1
  letI : Fintype AR.index := FintypeCat.fintype
  let middleLabel :=
    FiniteARTranslationData.factorCategoryMiddleLabel σ D K x
  let eMiddle : S.X₂ ≅
      (⨁ fun t : FiniteARTranslationData.factorCategoryMiddleIndex
        σ D K x ↦ σ.factorObject K (middleLabel t)) :=
    FiniteARTranslationData.factorCategoryRightMeshMiddleIso σ D K x
  have hmiddle :
      T.chosenMultiplicityVector S.X₂ =
        ∑ t, FactorLadder.basis (middleLabel t) := by
    calc
      T.chosenMultiplicityVector S.X₂ =
          T.chosenMultiplicityVector
            (⨁ fun t : FiniteARTranslationData.factorCategoryMiddleIndex
                σ D K x ↦ σ.factorObject K (middleLabel t)) :=
        T.chosenMultiplicityVector_iso_invariant ⟨eMiddle⟩
      _ = ∑ t, T.chosenMultiplicityVector
          (σ.factorObject K (middleLabel t)) :=
        T.chosenMultiplicityVector_finBiproduct _
      _ = ∑ t, FactorLadder.basis (middleLabel t) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact T.chosenMultiplicityVector_obj _
  rw [hpack, hmiddle]
  funext p
  change
    FiniteARTranslationData.factorLadderTheta (σ := σ) (D := D) K
        (FactorLadder.basis x) p =
      (∑ t, FactorLadder.basis (middleLabel t)) p
  rw [FiniteARTranslationData.factorLadderTheta_basis_apply]
  rw [← FiniteARTranslationData.factorCategoryMiddleMultiplicity_eq_deletedMiddleMultiplicity]
  simp [FiniteARTranslationData.factorCategoryMiddleMultiplicity,
    FactorLadder.basis, middleLabel, Finset.sum_apply, eq_comm]

/-- On a surviving indecomposable, the left term of the packaged right mesh
has exactly the multiplicity vector prescribed by `tau_D`. -/
theorem finiteDimensionalFactorCategoryRightMesh_tau_basis
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
    let A := σ.finiteDimensionalFactorLadderData k R K
    A.tau (FactorLadder.basis x) =
      T.chosenMultiplicityVector
        (T.rightMesh (σ.factorObject K x)).X₁ := by
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
  let D := σ.finiteDimensionalARTranslationData k R
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let A := σ.finiteDimensionalFactorLadderData k R K
  let S := FiniteARTranslationData.factorCategoryRightMesh σ D K x
  obtain ⟨ePack⟩ :=
    σ.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
      (k := k) (R := R) K hidem x
  have hpack :
      T.chosenMultiplicityVector (T.rightMesh (σ.factorObject K x)).X₁ =
        T.chosenMultiplicityVector S.X₁ :=
    T.chosenMultiplicityVector_iso_invariant
      ⟨ShortComplex.π₁.mapIso ePack⟩
  cases htarget :
      FiniteARTranslationData.factorLadderTauTarget
        (σ := σ) (D := D) K x with
  | none =>
      have hA : A.tau (FactorLadder.basis x) = 0 := by
        exact FiniteARTranslationData.factorLadderTau_basis_eq_zero_of_target_eq_none
          σ D K x htarget
      have hSzero : IsZero S.X₁ :=
        FiniteARTranslationData.factorCategoryRightMesh_X₁_isZero_of_tauTarget_eq_none
          σ D K x htarget
      have hSv : T.chosenMultiplicityVector S.X₁ = 0 :=
        T.chosenMultiplicityVector_eq_zero_of_isZero hSzero
      exact hA.trans (hSv.symm.trans hpack.symm)
  | some y =>
      have hA :
          A.tau (FactorLadder.basis x) = FactorLadder.basis y := by
        exact FiniteARTranslationData.factorLadderTau_basis_eq_basis_of_target_eq_some
          σ D K x y htarget
      let eLeft : S.X₁ ≅ T.obj y :=
        FiniteARTranslationData.factorCategoryRightMeshLeftIso_of_tauTarget_eq_some
          σ D K x y htarget
      have hSv :
          T.chosenMultiplicityVector S.X₁ = FactorLadder.basis y :=
        (T.chosenMultiplicityVector_iso_invariant ⟨eLeft⟩).trans
          (T.chosenMultiplicityVector_obj y)
      exact hA.trans (hSv.symm.trans hpack.symm)

/-- The paper's `theta_D` and `tau_D` operators are exactly the middle- and
left-term multiplicity operators of the packaged factor-category right
meshes, on every object. -/
theorem finiteDimensionalFactorCategoryRightMeshOperatorRealization
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let A := σ.finiteDimensionalFactorLadderData k R K
    Iyama.RightLadder.RightMeshOperatorRealization T A := by
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
  let A := σ.finiteDimensionalFactorLadderData k R K
  apply Iyama.RightLadder.RightMeshOperatorRealization.of_obj T A
  · intro x
    exact σ.finiteDimensionalFactorCategoryRightMesh_theta_basis
      (k := k) (R := R) K hidem x
  · intro x
    exact σ.finiteDimensionalFactorCategoryRightMesh_tau_basis
      (k := k) (R := R) K hidem x

/-- Under the single orthogonality statement in Iyama 7.1, the categorical
zero-initial right ladder has exactly the coefficient vectors recursively
defined in the manuscript. -/
theorem finiteDimensionalFactorCategory_rightLadderMultiplicityVector_eq_factorLadder
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
    let A := σ.finiteDimensionalFactorLadderData k R K
    let L := Iyama.RightLadder.zeroInitialRightLadder T
      (σ.factorObject K x)
    (∀ n, T.RadicalOrthogonal (L.U n) (L.Y (n + 1))) →
      ∀ n, T.chosenMultiplicityVector (L.Y n) = A.ladder x n := by
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
  let A := σ.finiteDimensionalFactorLadderData k R K
  let L := Iyama.RightLadder.zeroInitialRightLadder T
    (σ.factorObject K x)
  intro horth
  exact
    Iyama.RightLadder.RightMeshOperatorRealization.zeroInitialRightLadder_multiplicityVector_eq_ladder_of_radicalOrthogonal
      T A
      (σ.finiteDimensionalFactorCategoryRightMeshOperatorRealization
        (k := k) (R := R) K hidem)
      x horth

/-- Orthogonality upgrades the existing categorical projective-cover result
to the literal coefficient formula in the manuscript. -/
theorem finiteDimensionalFactorCategory_layerNonzero_iff_factorLadderCoefficient
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
    let A := σ.finiteDimensionalFactorLadderData k R K
    let L := Iyama.RightLadder.zeroInitialRightLadder T
      (σ.factorObject K x)
    (∀ m, T.RadicalOrthogonal (L.U m) (L.Y (m + 1))) →
      (T.radical.LayerNonzero n
          (σ.factorObject K p) (σ.factorObject K x) ↔
        0 < A.ladder x n p) := by
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
  let A := σ.finiteDimensionalFactorLadderData k R K
  let L := Iyama.RightLadder.zeroInitialRightLadder T
    (σ.factorObject K x)
  intro horth
  have hlayer :=
    σ.finiteDimensionalFactorCategory_layerNonzero_iff_rightLadderMultiplicity
      (k := k) (R := R) K hidem x p n
  dsimp only at hlayer
  change
    T.radical.LayerNonzero n
        (σ.factorObject K p) (σ.factorObject K x) ↔
      0 < T.chosenLabelMultiplicity p (L.Y n) at hlayer
  rw [hlayer]
  have hrec :=
    σ.finiteDimensionalFactorCategory_rightLadderMultiplicityVector_eq_factorLadder
      (k := k) (R := R) K hidem x horth n
  have hcoord := congrFun hrec p
  rw [T.chosenMultiplicityVector_apply] at hcoord
  rw [← hcoord]
  exact Int.natCast_pos.symm

/-- Paper-facing assembly: idempotent completeness and Iyama's
orthogonality lemma now suffice to construct the complete radical-layer
input consumed by the forward factor-ladder closure criterion. -/
def finiteDimensionalFactorLadderIyamaInput_of_rightLadderOrthogonality
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let A := σ.finiteDimensionalFactorLadderData k R K
    (∀ x : DeletedLabel K,
      let L := Iyama.RightLadder.zeroInitialRightLadder T
        (σ.factorObject K x)
      ∀ n, T.RadicalOrthogonal (L.U n) (L.Y (n + 1))) →
      FactorLadder.IyamaRadicalLayerInput A (factorHomNonzero σ K) := by
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
  let A := σ.finiteDimensionalFactorLadderData k R K
  intro horth
  apply σ.finiteDimensionalFactorLadderIyamaInput_of_layerFormula
    (k := k) (R := R) K
  intro n p x
  have h :=
    σ.finiteDimensionalFactorCategory_layerNonzero_iff_factorLadderCoefficient
      (k := k) (R := R) K hidem x p n (horth x)
  exact h

/-- The forward factor-ladder criterion in the literal module category,
with the remaining Iyama orthogonality hypothesis stated explicitly.
No concrete algebra or module classification enters the theorem. -/
theorem finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective_of_orthogonality
    (K : Set ι) :
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let A := σ.finiteDimensionalFactorLadderData k R K
    (∀ x : DeletedLabel K,
      let L := Iyama.RightLadder.zeroInitialRightLadder T
        (σ.factorObject K x)
      ∀ n, T.RadicalOrthogonal (L.U n) (L.Y (n + 1))) →
      ((σ.generated K).carrier.IsClosedUnderQuotients ↔
        ∀ x : DeletedLabel K,
          A.ReachesBoundary (deletedProjectiveSet σ K) x) := by
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
  letI : DecidableEq (DeletedLabel K) := Classical.decEq _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  let A := σ.finiteDimensionalFactorLadderData k R K
  intro horth
  exact
    σ.generated_isClosedUnderQuotients_iff_every_deleted_ladder_reaches_projective
      K A (deletedProjectiveSet σ K) (σ.holeFactorHomInput K)
      (σ.finiteDimensionalFactorLadderIyamaInput_of_rightLadderOrthogonality
        (k := k) (R := R) K hidem horth)

/-- Source-faithful forward factor-ladder criterion from a two-sided
tau-category extension. The following theorem supplies this input for the
literal factor quotient. -/
theorem finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective_of_finiteTauExtension
    (K : Set ι) :
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
    letI : DecidableEq (DeletedLabel K) := Classical.decEq _
    let T := σ.finiteDimensionalFactorCategoryRightTauData
      (k := k) (R := R) K hidem
    let A := σ.finiteDimensionalFactorLadderData k R K
    Iyama.FiniteTauCategoryExtension T →
      ((σ.generated K).carrier.IsClosedUnderQuotients ↔
        ∀ x : DeletedLabel K,
          A.ReachesBoundary (deletedProjectiveSet σ K) x) := by
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
  letI : DecidableEq (DeletedLabel K) := Classical.decEq _
  let T := σ.finiteDimensionalFactorCategoryRightTauData
    (k := k) (R := R) K hidem
  intro E
  apply
    σ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective_of_orthogonality
      (k := k) (R := R) K
  intro x
  dsimp only
  intro n q
  exact
    Iyama.RightLadder.FiniteTauCategoryExtension.zeroInitialRightLadder_discarded_radicalOrthogonal
      T E (σ.factorObject K x) n q

/-- Unconditional source-faithful forward factor-ladder criterion for the
literal ideal quotient. -/
theorem finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
    (K : Set ι) :
    ( σ.generated K).carrier.IsClosedUnderQuotients ↔
      ∀ x : DeletedLabel K,
        (σ.finiteDimensionalFactorLadderData k R K).ReachesBoundary
          (deletedProjectiveSet σ K) x := by
  exact
    (σ.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective_of_finiteTauExtension
      (k := k) (R := R) K)
      (σ.finiteDimensionalFactorCategoryTauExtension
        (k := k) (R := R) K)

end OpConjecture.IndecomposableSkeleton
