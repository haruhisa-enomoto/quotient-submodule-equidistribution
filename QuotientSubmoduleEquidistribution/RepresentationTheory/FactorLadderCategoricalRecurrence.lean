import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderProjectiveCover
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaRightLadderOrthogonality
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadder

/-!
# The categorical source of the factor-ladder recurrence

This file isolates the numerical argument in Iyama, *Tau-categories I*,
7.1--7.2.  A right ladder supplies two biproduct identities at every rung.
Once the chosen right-mesh terms realize the two additive operators, the
positive-part recurrence follows from the single substantive input that the
next target and the discarded source complement have disjoint
Krull--Schmidt support.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe u v w

open CategoricalRadical

namespace Iyama.FiniteRightTauCategoryData

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

variable (T : FiniteRightTauCategoryData C Ind)

/-- The integral multiplicity vector of an object with respect to the
chosen finite indecomposable skeleton. -/
def chosenMultiplicityVector (X : C) : FactorLadder.IntVector Ind :=
  fun p ↦ T.chosenLabelWeight (fun q ↦ if q = p then 1 else 0) X

/-- The integral coordinate is the cast of the natural-number
multiplicity used in the projective-cover theorem. -/
theorem chosenMultiplicityVector_apply (X : C) (p : Ind) :
    T.chosenMultiplicityVector X p =
      (T.chosenLabelMultiplicity p X : ℤ) := by
  simp [chosenMultiplicityVector, chosenLabelWeight,
    chosenLabelMultiplicity]

/-- Object multiplicity vectors are coefficientwise nonnegative. -/
theorem chosenMultiplicityVector_nonneg (X : C) (p : Ind) :
    0 ≤ T.chosenMultiplicityVector X p := by
  rw [T.chosenMultiplicityVector_apply X p]
  exact Int.natCast_nonneg _

/-- Multiplicity vectors are invariant under object isomorphism. -/
theorem chosenMultiplicityVector_iso_invariant {X Y : C}
    (e : Nonempty (X ≅ Y)) :
    T.chosenMultiplicityVector X = T.chosenMultiplicityVector Y := by
  funext p
  exact T.chosenLabelWeight_iso_invariant
    (fun q ↦ if q = p then 1 else 0) e

/-- Multiplicity vectors turn binary biproducts into pointwise sums. -/
theorem chosenMultiplicityVector_biprod (X Y : C) :
    T.chosenMultiplicityVector (biprod X Y) =
      T.chosenMultiplicityVector X + T.chosenMultiplicityVector Y := by
  funext p
  exact T.chosenLabelWeight_biprod_additive
    (fun q ↦ if q = p then 1 else 0) X Y

/-- Multiplicity vectors turn arbitrary finite biproducts into finite
pointwise sums. -/
theorem chosenMultiplicityVector_finBiproduct
    {J : Type*} [Fintype J] (F : J → C) :
    T.chosenMultiplicityVector (⨁ F) =
      ∑ j, T.chosenMultiplicityVector (F j) := by
  funext p
  simp only [chosenMultiplicityVector, Finset.sum_apply]
  change
    T.chosenLabelWeight (fun q ↦ if q = p then 1 else 0) (⨁ F) =
      ∑ j, T.chosenLabelWeight (fun q ↦ if q = p then 1 else 0) (F j)
  exact
    (T.additiveObjectWeightOfLabelWeight
      (fun q ↦ if q = p then 1 else 0)).weight_biproduct F

/-- Every zero object has zero multiplicity vector. -/
theorem chosenMultiplicityVector_eq_zero_of_isZero
    {X : C} (hX : IsZero X) :
    T.chosenMultiplicityVector X = 0 := by
  funext p
  exact
    (T.additiveObjectWeightOfLabelWeight
      (fun q ↦ if q = p then 1 else 0)).weight_eq_zero_of_isZero hX

/-- A chosen indecomposable has the corresponding basis multiplicity
vector. -/
theorem chosenMultiplicityVector_obj (x : Ind) :
    T.chosenMultiplicityVector (T.obj x) = FactorLadder.basis x := by
  funext p
  simp only [chosenMultiplicityVector, FactorLadder.basis]
  have h := T.additiveObjectWeightOfLabelWeight_obj
    (fun q ↦ if q = p then 1 else 0) x
  change
    T.chosenLabelWeight (fun q ↦ if q = p then 1 else 0) (T.obj x) =
      (if x = p then 1 else 0) at h
  simpa only [eq_comm] using h

/-- The multiplicity vector of an arbitrary object is the sum of the basis
vectors in its chosen finite decomposition. -/
theorem chosenMultiplicityVector_eq_sum_basis (X : C) :
    T.chosenMultiplicityVector X =
      ∑ i, FactorLadder.basis (T.chosenDecompositionLabel X i) := by
  let F : Fin (T.chosenDecompositionSize X) → C :=
    fun i ↦ T.obj (T.chosenDecompositionLabel X i)
  calc
    T.chosenMultiplicityVector X = T.chosenMultiplicityVector (⨁ F) :=
      T.chosenMultiplicityVector_iso_invariant
        ⟨T.chosenDecompositionIso X⟩
    _ = ∑ i, T.chosenMultiplicityVector (F i) :=
      T.chosenMultiplicityVector_finBiproduct F
    _ = ∑ i, FactorLadder.basis (T.chosenDecompositionLabel X i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact T.chosenMultiplicityVector_obj _

/-- Two objects have disjoint Krull--Schmidt support when no chosen label
occurs in both.  This is the numerical content of Iyama's pairing
condition `⟨X,Y⟩ = 0`. -/
def MultiplicityOrthogonal (X Y : C) : Prop :=
  ∀ p : Ind,
    T.chosenMultiplicityVector X p = 0 ∨
      T.chosenMultiplicityVector Y p = 0

/-- Disjoint multiplicity support is symmetric. -/
theorem MultiplicityOrthogonal.symm {X Y : C}
    (h : T.MultiplicityOrthogonal X Y) :
    T.MultiplicityOrthogonal Y X := by
  intro p
  rcases h p with hX | hY
  · exact Or.inr hX
  · exact Or.inl hY

/-- Categorical orthogonality modulo the radical: every morphism from `X`
to `Y` belongs to the categorical radical.  This is Iyama's condition
`J^(0)(X,Y) = 0`. -/
def RadicalOrthogonal (X Y : C) : Prop :=
  ∀ f : X ⟶ Y, f ∈ T.radical.ideal.hom X Y

/-- Radical orthogonality forces disjoint Krull--Schmidt support. -/
theorem multiplicityOrthogonal_of_radicalOrthogonal
    {X Y : C} (horth : T.RadicalOrthogonal X Y) :
    T.MultiplicityOrthogonal X Y := by
  intro p
  rw [T.chosenMultiplicityVector_apply,
    T.chosenMultiplicityVector_apply]
  by_cases hX : T.chosenLabelMultiplicity p X = 0
  · left
    exact_mod_cast hX
  by_cases hY : T.chosenLabelMultiplicity p Y = 0
  · right
    exact_mod_cast hY
  exfalso
  obtain ⟨dX⟩ :=
    (T.chosenLabelMultiplicity_pos_iff_retract p X).1
      (Nat.pos_of_ne_zero hX)
  obtain ⟨dY⟩ :=
    (T.chosenLabelMultiplicity_pos_iff_retract p Y).1
      (Nat.pos_of_ne_zero hY)
  let f : X ⟶ Y := dX.r ≫ dY.i
  have hf : IsRadicalMorphism f :=
    (T.radical.mem_ideal_iff f).1 (horth f)
  have hi : IsRadicalMorphism dY.i := by
    have hpre := isRadicalMorphism_precomp dX.i hf
    simpa [f, Category.assoc, dX.retract] using hpre
  have hnotSplit :=
    (T.isRadicalMorphism_iff_not_isSplitMono_from_obj dY.i).1 hi
  apply hnotSplit
  exact IsSplitMono.mk' { retraction := dY.r, id := dY.retract }

end Iyama.FiniteRightTauCategoryData

namespace FactorLadder

/-- Coefficientwise subtraction followed by positive part recovers the
left vector when the two nonnegative vectors have disjoint support. -/
theorem positivePart_sub_eq_left_of_orthogonal
    {D : Type w} {a b : IntVector D}
    (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (horth : ∀ p, a p = 0 ∨ b p = 0) :
    positivePart (a - b) = a := by
  funext p
  rcases horth p with hap | hbp
  · simp [positivePart, hap, hb p]
  · simp [positivePart, hbp, ha p]

end FactorLadder

namespace Iyama.RightLadder

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]

open FiniteRightTauCategoryData

/-- The middle term of a right-ladder rung decomposes as the next target
plus the current essential source. -/
theorem InfiniteSpecialRightLadder.chosenMultiplicityVector_rightMesh_X₂
    {T : FiniteRightTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : InfiniteSpecialRightLadder T a₀) (n : ℕ) :
    T.chosenMultiplicityVector (T.rightMesh (L.Y n)).X₂ =
      T.chosenMultiplicityVector (L.Y (n + 1)) +
        T.chosenMultiplicityVector (L.Z n) := by
  obtain ⟨e⟩ := L.meshIso n
  calc
    T.chosenMultiplicityVector (T.rightMesh (L.Y n)).X₂ =
        T.chosenMultiplicityVector
          (stepComplex (L.b n) (L.b (n + 1))
            (L.f n) (L.g n) (L.h n) (L.comm n) (L.hzero n)).X₂ :=
      T.chosenMultiplicityVector_iso_invariant
        ⟨ShortComplex.π₂.mapIso e⟩
    _ = T.chosenMultiplicityVector (biprod (L.Y (n + 1)) (L.Z n)) := rfl
    _ = T.chosenMultiplicityVector (L.Y (n + 1)) +
        T.chosenMultiplicityVector (L.Z n) :=
      T.chosenMultiplicityVector_biprod _ _

/-- The left term of a right-ladder rung decomposes as the next essential
source plus the next discarded complement. -/
theorem InfiniteSpecialRightLadder.chosenMultiplicityVector_rightMesh_X₁
    {T : FiniteRightTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : InfiniteSpecialRightLadder T a₀) (n : ℕ) :
    T.chosenMultiplicityVector (T.rightMesh (L.Y n)).X₁ =
      T.chosenMultiplicityVector (L.Z (n + 1)) +
        T.chosenMultiplicityVector (L.U (n + 1)) := by
  obtain ⟨e⟩ := L.meshIso n
  calc
    T.chosenMultiplicityVector (T.rightMesh (L.Y n)).X₁ =
        T.chosenMultiplicityVector
          (stepComplex (L.b n) (L.b (n + 1))
            (L.f n) (L.g n) (L.h n) (L.comm n) (L.hzero n)).X₁ :=
      T.chosenMultiplicityVector_iso_invariant
        ⟨ShortComplex.π₁.mapIso e⟩
    _ = T.chosenMultiplicityVector (biprod (L.Z (n + 1)) (L.U (n + 1))) := rfl
    _ = T.chosenMultiplicityVector (L.Z (n + 1)) +
        T.chosenMultiplicityVector (L.U (n + 1)) :=
      T.chosenMultiplicityVector_biprod _ _

omit [DecidableEq Ind] in
/-- If the source of the initial arrow is zero, then so is the initial
essential source object. -/
theorem InfiniteSpecialRightLadder.initial_Z_isZero_of_isZero_source
    {T : FiniteRightTauCategoryData C Ind}
    {X₀ Y₀ : C} {a₀ : X₀ ⟶ Y₀}
    (L : InfiniteSpecialRightLadder T a₀)
    (hX₀ : IsZero X₀) : IsZero (L.Z 0) := by
  obtain ⟨e⟩ := L.initialIso
  let eX : X₀ ≅ biprod (L.Z 0) (L.U 0) := Arrow.leftFunc.mapIso e
  have hZU : IsZero (biprod (L.Z 0) (L.U 0)) := hX₀.of_iso eX.symm
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (L.Z 0) =
        (biprod.inl : L.Z 0 ⟶ biprod (L.Z 0) (L.U 0)) ≫ biprod.fst := by simp
    _ = 0 := by
      rw [hZU.eq_of_tgt
        (biprod.inl : L.Z 0 ⟶ biprod (L.Z 0) (L.U 0)) 0, zero_comp]

/-- Compatibility between the two numerical factor-ladder operators and
the left and middle objects of every chosen right mesh. -/
structure RightMeshOperatorRealization
    (T : FiniteRightTauCategoryData C Ind)
    (A : FactorLadder.Data Ind) : Prop where
  theta : ∀ X : C,
    A.theta (T.chosenMultiplicityVector X) =
      T.chosenMultiplicityVector (T.rightMesh X).X₂
  tau : ∀ X : C,
    A.tau (T.chosenMultiplicityVector X) =
      T.chosenMultiplicityVector (T.rightMesh X).X₁

namespace RightMeshOperatorRealization

/-- It suffices to identify the two mesh operators on the chosen
indecomposable representatives.  Additivity of the operators and uniqueness
of right tau-sequences propagate those identifications to every object. -/
theorem of_obj
    (T : FiniteRightTauCategoryData C Ind)
    (A : FactorLadder.Data Ind)
    (htheta : ∀ x : Ind,
      A.theta (FactorLadder.basis x) =
        T.chosenMultiplicityVector (T.rightMesh (T.obj x)).X₂)
    (htau : ∀ x : Ind,
      A.tau (FactorLadder.basis x) =
        T.chosenMultiplicityVector (T.rightMesh (T.obj x)).X₁) :
    RightMeshOperatorRealization T A where
  theta X := by
    let n := T.chosenDecompositionSize X
    let label : Fin n → Ind := T.chosenDecompositionLabel X
    let F : Fin n → C := fun i ↦ T.obj (label i)
    obtain ⟨eMesh⟩ :=
      T.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
        F X (T.chosenDecompositionIso X)
    have hright :
        T.chosenMultiplicityVector (T.rightMesh X).X₂ =
          ∑ i, T.chosenMultiplicityVector
            (T.rightMesh (T.obj (label i))).X₂ := by
      calc
        T.chosenMultiplicityVector (T.rightMesh X).X₂ =
            T.chosenMultiplicityVector
              (Iyama.shortComplexBiproduct
                (fun i ↦ T.rightMesh (T.obj (label i)))).X₂ :=
          T.chosenMultiplicityVector_iso_invariant
            ⟨ShortComplex.π₂.mapIso eMesh⟩
        _ = T.chosenMultiplicityVector
            (⨁ fun i ↦ (T.rightMesh (T.obj (label i))).X₂) := rfl
        _ = ∑ i, T.chosenMultiplicityVector
            (T.rightMesh (T.obj (label i))).X₂ :=
          T.chosenMultiplicityVector_finBiproduct _
    calc
      A.theta (T.chosenMultiplicityVector X) =
          A.theta (∑ i, FactorLadder.basis (label i)) := by
        rw [T.chosenMultiplicityVector_eq_sum_basis]
      _ = ∑ i, A.theta (FactorLadder.basis (label i)) :=
        map_sum A.theta (fun i ↦ FactorLadder.basis (label i)) Finset.univ
      _ = ∑ i, T.chosenMultiplicityVector
          (T.rightMesh (T.obj (label i))).X₂ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact htheta _
      _ = T.chosenMultiplicityVector (T.rightMesh X).X₂ := hright.symm
  tau X := by
    let n := T.chosenDecompositionSize X
    let label : Fin n → Ind := T.chosenDecompositionLabel X
    let F : Fin n → C := fun i ↦ T.obj (label i)
    obtain ⟨eMesh⟩ :=
      T.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
        F X (T.chosenDecompositionIso X)
    have hright :
        T.chosenMultiplicityVector (T.rightMesh X).X₁ =
          ∑ i, T.chosenMultiplicityVector
            (T.rightMesh (T.obj (label i))).X₁ := by
      calc
        T.chosenMultiplicityVector (T.rightMesh X).X₁ =
            T.chosenMultiplicityVector
              (Iyama.shortComplexBiproduct
                (fun i ↦ T.rightMesh (T.obj (label i)))).X₁ :=
          T.chosenMultiplicityVector_iso_invariant
            ⟨ShortComplex.π₁.mapIso eMesh⟩
        _ = T.chosenMultiplicityVector
            (⨁ fun i ↦ (T.rightMesh (T.obj (label i))).X₁) := rfl
        _ = ∑ i, T.chosenMultiplicityVector
            (T.rightMesh (T.obj (label i))).X₁ :=
          T.chosenMultiplicityVector_finBiproduct _
    calc
      A.tau (T.chosenMultiplicityVector X) =
          A.tau (∑ i, FactorLadder.basis (label i)) := by
        rw [T.chosenMultiplicityVector_eq_sum_basis]
      _ = ∑ i, A.tau (FactorLadder.basis (label i)) :=
        map_sum A.tau (fun i ↦ FactorLadder.basis (label i)) Finset.univ
      _ = ∑ i, T.chosenMultiplicityVector
          (T.rightMesh (T.obj (label i))).X₁ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact htau _
      _ = T.chosenMultiplicityVector (T.rightMesh X).X₁ := hright.symm

/-- Iyama's numerical recursion theorem for the zero-initial right ladder.
All formal mesh bookkeeping is discharged here; the only non-formal input
is orthogonality of `Y (n+1)` and `U n`. -/
theorem zeroInitialRightLadder_multiplicityVector_eq_ladder
    (T : FiniteRightTauCategoryData C Ind)
    (A : FactorLadder.Data Ind)
    (hmesh : RightMeshOperatorRealization T A)
    (x : Ind)
    (horth :
      let L := zeroInitialRightLadder T (T.obj x)
      ∀ n, T.MultiplicityOrthogonal (L.Y (n + 1)) (L.U n)) :
    let L := zeroInitialRightLadder T (T.obj x)
    ∀ n, T.chosenMultiplicityVector (L.Y n) = A.ladder x n := by
  let L := zeroInitialRightLadder T (T.obj x)
  dsimp only at horth ⊢
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      have hYzero : L.Y 0 = T.obj x := rfl
      rw [hYzero, T.chosenMultiplicityVector_obj, FactorLadder.Data.ladder_zero]
  | one =>
      have hYzero : L.Y 0 = T.obj x := rfl
      have hZzero : IsZero (L.Z 0) :=
        L.initial_Z_isZero_of_isZero_source (isZero_zero C)
      have hZv : T.chosenMultiplicityVector (L.Z 0) = 0 :=
        T.chosenMultiplicityVector_eq_zero_of_isZero hZzero
      have hmiddle := L.chosenMultiplicityVector_rightMesh_X₂ 0
      rw [hZv, add_zero] at hmiddle
      calc
        T.chosenMultiplicityVector (L.Y 1) =
            T.chosenMultiplicityVector (T.rightMesh (L.Y 0)).X₂ :=
          hmiddle.symm
        _ = A.theta (T.chosenMultiplicityVector (L.Y 0)) :=
          (hmesh.theta _).symm
        _ = A.theta (FactorLadder.basis x) := by
          rw [hYzero, T.chosenMultiplicityVector_obj]
        _ = A.ladder x 1 := FactorLadder.Data.ladder_one A x |>.symm
  | more n hn hn1 =>
      have hmiddle :
          T.chosenMultiplicityVector (T.rightMesh (L.Y (n + 1))).X₂ =
            T.chosenMultiplicityVector (L.Y (n + 2)) +
              T.chosenMultiplicityVector (L.Z (n + 1)) := by
        simpa [Nat.add_assoc] using
          L.chosenMultiplicityVector_rightMesh_X₂ (n + 1)
      have hleft := L.chosenMultiplicityVector_rightMesh_X₁ n
      have hdifference :
          A.theta (T.chosenMultiplicityVector (L.Y (n + 1))) -
              A.tau (T.chosenMultiplicityVector (L.Y n)) =
            T.chosenMultiplicityVector (L.Y (n + 2)) -
              T.chosenMultiplicityVector (L.U (n + 1)) := by
        rw [hmesh.theta, hmesh.tau, hmiddle, hleft]
        funext p
        dsimp
        omega
      rw [FactorLadder.Data.ladder_add_two, ← hn1, ← hn, hdifference]
      symm
      apply FactorLadder.positivePart_sub_eq_left_of_orthogonal
      · exact T.chosenMultiplicityVector_nonneg _
      · exact T.chosenMultiplicityVector_nonneg _
      · exact horth (n + 1)

/-- Source-faithful form of the recurrence theorem: it is enough that all
morphisms from each discarded complement to the next target vanish modulo
the categorical radical, exactly as in Iyama 7.1. -/
theorem zeroInitialRightLadder_multiplicityVector_eq_ladder_of_radicalOrthogonal
    (T : FiniteRightTauCategoryData C Ind)
    (A : FactorLadder.Data Ind)
    (hmesh : RightMeshOperatorRealization T A)
    (x : Ind)
    (horth :
      let L := zeroInitialRightLadder T (T.obj x)
      ∀ n, T.RadicalOrthogonal (L.U n) (L.Y (n + 1))) :
    let L := zeroInitialRightLadder T (T.obj x)
    ∀ n, T.chosenMultiplicityVector (L.Y n) = A.ladder x n := by
  dsimp only at horth ⊢
  exact zeroInitialRightLadder_multiplicityVector_eq_ladder T A hmesh x
    (fun n ↦
      (T.multiplicityOrthogonal_of_radicalOrthogonal (horth n)).symm)

set_option linter.unusedSectionVars false in
/-- In a finite two-sided tau-category, Iyama 7.1 supplies the radical
orthogonality hypothesis automatically for the zero-initial right ladder. -/
theorem FiniteTauCategoryData.zeroInitialRightLadder_radicalOrthogonal
    (T : FiniteTauCategoryData C Ind) (X : C) :
    let Tr := T.toFiniteRightTauCategoryData
    let L := zeroInitialRightLadder Tr X
    ∀ n, Tr.RadicalOrthogonal (L.U n) (L.Y (n + 1)) := by
  dsimp only
  intro n q
  exact
    FiniteTauCategoryData.zeroInitialRightLadder_discarded_radicalOrthogonal
      T X n q

/-- The source-faithful factor-ladder recurrence with Iyama 7.1 discharged
internally from the two-sided finite tau-category structure. -/
theorem zeroInitialRightLadder_multiplicityVector_eq_ladder_of_finiteTauCategory
    (T : FiniteTauCategoryData C Ind)
    (A : FactorLadder.Data Ind)
    (hmesh : RightMeshOperatorRealization
      T.toFiniteRightTauCategoryData A)
    (x : Ind) :
    let Tr := T.toFiniteRightTauCategoryData
    let L := zeroInitialRightLadder Tr (Tr.obj x)
    ∀ n, Tr.chosenMultiplicityVector (L.Y n) = A.ladder x n := by
  let Tr := T.toFiniteRightTauCategoryData
  apply zeroInitialRightLadder_multiplicityVector_eq_ladder_of_radicalOrthogonal
    Tr A hmesh x
  exact FiniteTauCategoryData.zeroInitialRightLadder_radicalOrthogonal
    T (Tr.obj x)

/-- Source-faithful extension form of the unconditional recurrence.  The
chosen right meshes remain literally the supplied one-sided data. -/
theorem zeroInitialRightLadder_multiplicityVector_eq_ladder_of_finiteTauExtension
    (Tr : FiniteRightTauCategoryData C Ind)
    (A : FactorLadder.Data Ind)
    (hmesh : RightMeshOperatorRealization Tr A)
    (E : FiniteTauCategoryExtension Tr)
    (x : Ind) :
    let L := zeroInitialRightLadder Tr (Tr.obj x)
    ∀ n, Tr.chosenMultiplicityVector (L.Y n) = A.ladder x n := by
  obtain ⟨T, rfl⟩ := E
  exact
    zeroInitialRightLadder_multiplicityVector_eq_ladder_of_finiteTauCategory
      T A hmesh x

end RightMeshOperatorRealization

end Iyama.RightLadder

end QuotientSubmoduleEquidistribution
