import OpConjecture.RepresentationDirected.IyamaPreStrictWordMesh
import OpConjecture.RepresentationDirected.IyamaWordMeshFiniteTauCategory

/-!
# The pre-strict realization of the abstract word mesh

This file aligns the finite tau-category carried by the abstract word-mesh
additive hull with the finite admissible translation quiver of the word.  It
packages the resulting categorical data as a `PreStrictWordMeshRealization`.

No concrete algebra, quiver presentation, module enumeration, or module
classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.PreStrictRealization

open OpConjecture.Iyama
open OpConjecture.RepresentationDirected.ARWord
open OpConjecture.RepresentationDirected.PrincipalPositivity
open OpConjecture.RepresentationDirected.IyamaMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.AdditiveHull
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.RightRealization
open OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.FiniteTau

universe uK uL

variable {K : Type uK} [Field K]
variable {L : Type uL}

/-! ## The middle-term indexing equivalence -/

/-- An actual incoming middle vertex is the same thing as a vertex together
with one of the copies prescribed by the word-quiver valuation. -/
def middleIndexEquiv
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    {y : Fin Q.length // IsMiddle G Q y x} ≃
      Σ y : Fin Q.length, Fin (Word.arrowMultiplicity G Q y x) where
  toFun y := ⟨y.1, ⟨0, by simp [Word.arrowMultiplicity, y.2]⟩⟩
  invFun i := ⟨i.1, by
    by_contra h
    have hzero : Word.arrowMultiplicity G Q i.1 x = 0 := by
      simp [Word.arrowMultiplicity, h]
    exact Fin.elim0 (hzero ▸ i.2)⟩
  left_inv y := by
    exact Subtype.ext rfl
  right_inv i := by
    rcases i with ⟨y, i⟩
    have hy : IsMiddle G Q y x := by
      by_contra h
      have hzero : Word.arrowMultiplicity G Q y x = 0 := by
        simp [Word.arrowMultiplicity, h]
      exact Fin.elim0 (hzero ▸ i)
    have hone : Word.arrowMultiplicity G Q y x = 1 := by
      simp [Word.arrowMultiplicity, hy]
    letI : Subsingleton (Fin (Word.arrowMultiplicity G Q y x)) := by
      rw [hone]
      infer_instance
    change (⟨y, _⟩ : Σ y : Fin Q.length,
      Fin (Word.arrowMultiplicity G Q y x)) = ⟨y, i⟩
    apply Sigma.ext (by rfl)
    exact heq_of_eq (Subsingleton.elim _ _)

/-- The middle object of the chosen categorical right mesh is the valuation
biproduct prescribed by the word translation quiver. -/
def thetaPlusMiddleObjectIso
    (G : SimpleGraph L) (Q : List L)
    (hRuns : HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    (FiniteTau.finiteTauCategoryData (K := K) G Q hRuns.hasInteriorAlternation
        weight hweight).thetaPlus x ≅
      (Word.translationQuiver G Q hRuns weight hweight).middleObject
        (FiniteTau.finiteTauCategoryData (K := K) G Q hRuns.hasInteriorAlternation
          weight hweight) x := by
  change (⨁ fun _ : PUnit ↦
      middleObj (K := K) G Q hRuns.hasInteriorAlternation x) ≅
    (⨁ fun i : Σ y : Fin Q.length,
        Fin (Word.arrowMultiplicity G Q y x) ↦
      AdditiveHull.vertexObj (K := K) G Q
        hRuns.hasInteriorAlternation i.1)
  calc
    _ ≅ middleObj (K := K) G Q hRuns.hasInteriorAlternation x :=
      biproductUniqueIso _
    _ ≅ (⨁ fun y : {y : Fin Q.length // IsMiddle G Q y x} ↦
        AdditiveHull.vertexObj (K := K) G Q
          hRuns.hasInteriorAlternation y.1) :=
      Mat_.isoBiproductEmbedding
        (middleObj (K := K) G Q hRuns.hasInteriorAlternation x)
    _ ≅ _ :=
      biproduct.whiskerEquiv (middleIndexEquiv G Q x)
        (fun y ↦ Iso.refl (AdditiveHull.vertexObj (K := K) G Q
          hRuns.hasInteriorAlternation y.1))

/-! ## Alignment with the finite translation quiver -/

/-- The finite tau-category of the word mesh realizes the projective
boundary, translation, and valuation middle terms of the word quiver. -/
theorem nakayamaStrictnessRealization
    (G : SimpleGraph L) (Q : List L)
    (hRuns : HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    NakayamaStrictnessRealization
      (FiniteTau.finiteTauCategoryData (K := K) G Q hRuns.hasInteriorAlternation
        weight hweight)
      (Word.translationQuiver G Q hRuns weight hweight) where
  projective_iff x := by
    change (¬ Word.HasPrevious Q x) ↔
      IsZero ((rightMesh (K := K) G Q hRuns.hasInteriorAlternation
        (AdditiveHull.vertexObj (K := K) G Q
          hRuns.hasInteriorAlternation x)).X₁)
    exact (rightVertexLeftTerm_isZero_iff
      (K := K) G Q hRuns.hasInteriorAlternation x).symm
  tau_alignment x hx := by
    change Word.tauTo Q
        ((rightBoundaryEquiv (K := K) G Q
          hRuns.hasInteriorAlternation) x) =
      Word.tauTo Q ⟨x.1, hx⟩
    congr 1
  middle_iso x :=
    ⟨thetaPlusMiddleObjectIso (K := K) G Q hRuns weight hweight x⟩

/-! ## The displayed first mesh maps -/

/-- A morphism is isomorphic in the arrow category to its external
one-element biproduct. -/
def arrowIsoSingletonBiproduct
    {C : Type*} [CategoryTheory.Category C] [Preadditive C]
    [HasFiniteBiproducts C]
    {X Y : C} (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (biproduct.map fun _ : PUnit ↦ f) := by
  let eX : X ≅ ⨁ fun _ : PUnit ↦ X :=
    (biproductUniqueIso (fun _ : PUnit ↦ X)).symm
  let eY : Y ≅ ⨁ fun _ : PUnit ↦ Y :=
    (biproductUniqueIso (fun _ : PUnit ↦ Y)).symm
  refine Arrow.isoMk' f (biproduct.map fun _ : PUnit ↦ f) eX eY ?_
  dsimp only [eX, eY]
  ext
  simp

/-- The displayed first map of the singleton word mesh agrees with the first
map chosen by the finite tau-category. -/
def rightFirstMapIso
    (G : SimpleGraph L) (Q : List L)
    (hRuns : HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (x : Fin Q.length) :
    Arrow.mk
        ((wordRightMeshRealization (K := K) G Q
          hRuns.hasInteriorAlternation).toRightRepresentableMeshComplex.nu x) ≅
      Arrow.mk
        ((FiniteTau.finiteTauCategoryData (K := K) G Q
          hRuns.hasInteriorAlternation weight hweight).nuPlus x) := by
  change Arrow.mk (previousToMiddle (K := K) G Q
      hRuns.hasInteriorAlternation x) ≅
    Arrow.mk (biproduct.map fun _ : PUnit ↦
      previousToMiddle (K := K) G Q hRuns.hasInteriorAlternation x)
  exact arrowIsoSingletonBiproduct _

/-! ## The complete pre-strict realization -/

/-- The abstract word mesh supplies all categorical input required before
Iyama's finite-ladder Nakayama strictness theorem is applied. -/
def preStrictWordMeshRealization
    (G : SimpleGraph L) (Q : List L)
    (hRuns : HasOnlyBoundaryRepeatedRuns G Q)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    PreStrictWordMeshRealization
      (wordRightMeshRealization (K := K) G Q
        hRuns.hasInteriorAlternation)
      hRuns weight hweight where
  tauCategory := FiniteTau.finiteTauCategoryData (K := K) G Q
    hRuns.hasInteriorAlternation weight hweight
  categorical := nakayamaStrictnessRealization
    (K := K) G Q hRuns weight hweight
  firstMapIso x := ⟨rightFirstMapIso
    (K := K) G Q hRuns weight hweight x⟩

/-! ## Numerical mesh exactness -/

include K in
/-- Iyama strictness for the abstract word-mesh category supplies the exact
representable-mesh recurrence required by the manuscript, for every finite
word and graph admitting the boundary-run and positivity hypotheses. -/
theorem positiveRightAdditiveHasRepresentableMeshExactness
    (G : SimpleGraph L) (Q : List L) :
    MeshExactness.PositiveRightAdditiveHasRepresentableMeshExactness G Q := by
  intro hRuns hpositive
  obtain ⟨weight, hweight⟩ := hpositive
  exact ⟨(preStrictWordMeshRealization
    (K := K) G Q hRuns weight hweight).toRepresentableMeshExactnessData⟩

include K in
/-- Consequently the mesh-exactness hypothesis holds uniformly for every
row-restricted selected segment of an ambient word. -/
theorem uniformSelectedSegmentRepresentableMeshExactness
    (G : SimpleGraph L) (Q : List L) :
    MeshExactness.UniformSelectedSegmentRepresentableMeshExactness G Q := by
  intro D a
  exact positiveRightAdditiveHasRepresentableMeshExactness (K := K) _ _

end OpConjecture.RepresentationDirected.IyamaMesh.WordMesh.PreStrictRealization
