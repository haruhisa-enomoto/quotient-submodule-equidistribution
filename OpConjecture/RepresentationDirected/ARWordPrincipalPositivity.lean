import OpConjecture.RepresentationDirected.ARCoordinateRecurrence
import OpConjecture.RepresentationDirected.ARWordSegmentReducedness
import OpConjecture.RepresentationDirected.SimpleGraphRootMesh

/-!
# Principal positivity reduced to finite mesh exactness

This file formalizes the root-height and selected-coordinate parts of
`lem:directed-principal-positive`.  The one remaining input is isolated as
the finite mesh-exactness statement that a positive right-additive function
forces the inverse mesh recurrence to be nonnegative.
-/

noncomputable section

open scoped BigOperators

namespace OpConjecture.RepresentationDirected.PrincipalPositivity

open SimpleGraphCoxeter
open WordRootProcess

universe u

variable {L : Type u}

/-- The scalar middle sum used by the mesh recurrence. -/
def scalarMiddleSum (G : SimpleGraph L) (Q : List L)
    (lambda : Fin Q.length → ℤ) (x : Fin Q.length) : ℤ := by
  classical
  exact ∑ y ∈ Finset.univ.filter
    (fun y : Fin Q.length ↦ ARWord.IsMiddle G Q y x), lambda y

/-- The paper's positive right-additivity condition, stated without a mesh
category. -/
def IsPositiveRightAdditive (G : SimpleGraph L) (Q : List L)
    (lambda : Fin Q.length → ℤ) : Prop :=
  (∀ x, 0 < lambda x) ∧
  (∀ p x, ARWord.IsPrevious Q p x →
    lambda x - scalarMiddleSum G Q lambda x + lambda p = 0) ∧
  (∀ x, (¬ ∃ p, ARWord.IsPrevious Q p x) →
    0 < lambda x - scalarMiddleSum G Q lambda x)

/-- A row-wise solution of `H K_Q = I`, expressed by the literal mesh
recurrence rather than by matrices. -/
def SatisfiesWordMeshInverseRecurrence (G : SimpleGraph L) (Q : List L)
    (M : Fin Q.length → Fin Q.length → ℤ) : Prop :=
  ∀ a x,
    (∀ p, ARWord.IsPrevious Q p x →
      M a x = (if a = x then 1 else 0) +
        scalarMiddleSum G Q (M a) x - M a p) ∧
    ((¬ ∃ p, ARWord.IsPrevious Q p x) →
      M a x = (if a = x then 1 else 0) +
        scalarMiddleSum G Q (M a) x)

/-- The word-mesh inverse recurrence has at most one solution.  Every term on
the right at position `x` comes from a strictly earlier position, so this is
plain finite induction and uses no positivity or boundary-run hypothesis. -/
theorem satisfiesWordMeshInverseRecurrence_unique
    (G : SimpleGraph L) (Q : List L)
    {M N : Fin Q.length → Fin Q.length → ℤ}
    (hM : SatisfiesWordMeshInverseRecurrence G Q M)
    (hN : SatisfiesWordMeshInverseRecurrence G Q N) :
    M = N := by
  funext a x
  induction hx : x.val using Nat.strong_induction_on generalizing x with
  | h n ih =>
      have hearlier : ∀ y : Fin Q.length, y < x → M a y = N a y := by
        intro y hyx
        exact ih y.val (by omega) y rfl
      have hmiddle :
          scalarMiddleSum G Q (M a) x =
            scalarMiddleSum G Q (N a) x := by
        classical
        unfold scalarMiddleSum
        apply Finset.sum_congr rfl
        intro y hy
        have hyMiddle : ARWord.IsMiddle G Q y x := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
        apply hearlier y
        exact hyMiddle.2.1
      by_cases hprevious : ∃ p, ARWord.IsPrevious Q p x
      · obtain ⟨p, hp⟩ := hprevious
        rw [(hM a x).1 p hp, (hN a x).1 p hp, hmiddle,
          hearlier p hp.1]
      · rw [(hM a x).2 hprevious, (hN a x).2 hprevious, hmiddle]

/-- The single missing numerical consequence of mesh exactness.  This is the
abstract content of the Iyama step in the manuscript: for a word with the
translation-pairing/boundary-run property, a positive right-additive function
forces every integral solution of `H K_Q = I` to be entrywise nonnegative. -/
def PositiveRightAdditiveForcesMeshInverseNonnegative
    (G : SimpleGraph L) (Q : List L) : Prop :=
  ARWord.HasOnlyBoundaryRepeatedRuns G Q →
    ∀ (lambda : Fin Q.length → ℤ),
      IsPositiveRightAdditive G Q lambda →
        ∀ (M : Fin Q.length → Fin Q.length → ℤ),
          SatisfiesWordMeshInverseRecurrence G Q M →
            ∀ a x, 0 ≤ M a x

section RootHeight

variable [Fintype L]

/-- Height is additive. -/
theorem height_add (z w : RootLattice L) :
    height (z + w) = height z + height w := by
  simp [height, Finset.sum_add_distrib]

/-- Height respects subtraction. -/
theorem height_sub (z w : RootLattice L) :
    height (z - w) = height z - height w := by
  simp [height, Finset.sum_sub_distrib]

theorem height_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → RootLattice L) :
    height (∑ i ∈ s, f i) = ∑ i ∈ s, height (f i) := by
  classical
  simp only [height, Finset.sum_apply]
  rw [Finset.sum_comm]

/-- The height of the filtered root sum is the literal scalar middle sum of
the root heights. -/
theorem height_filteredMiddleRootSum (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) :
    height (filteredMiddleRootSum G Q x) =
      scalarMiddleSum G Q (fun y ↦ height (inversionRoot G Q y)) x := by
  classical
  unfold filteredMiddleRootSum scalarMiddleSum
  exact height_finsetSum _ _

/-- The first-occurrence correction has nonnegative height once all
inversion roots are positive. -/
theorem height_filteredEarlierNonLastAdjacentRootSum_nonnegative
    (G : SimpleGraph L) (Q : List L)
    (hPositive : HasPositiveInversionRoots G Q)
    (x : Fin Q.length) :
    0 ≤ height (filteredEarlierNonLastAdjacentRootSum G Q x) := by
  classical
  rw [show height (filteredEarlierNonLastAdjacentRootSum G Q x) =
      ∑ y ∈ Finset.univ.filter
          (fun y : Fin Q.length ↦ IsEarlierNonLastAdjacent G Q y x),
        height (inversionRoot G Q y) by
    unfold filteredEarlierNonLastAdjacentRootSum
    exact height_finsetSum _ _]
  exact Finset.sum_nonneg fun y _ ↦ (hPositive y).height_positive.le

/-- Existing root-mesh identities turn reducedness into the positive
right-additive height function used in the manuscript. -/
theorem inversionRootHeight_isPositiveRightAdditive
    (G : SimpleGraph L) (Q : List L)
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (hReduced : IsReduced G Q) :
    IsPositiveRightAdditive G Q
      (fun x ↦ height (inversionRoot G Q x)) := by
  have hPositive : HasPositiveInversionRoots G Q :=
    RootSignStrategy.reducedWordsHavePositiveInversionRoots G Q hReduced
  refine ⟨fun x ↦ (hPositive x).height_positive, ?_, ?_⟩
  · intro p x hpx
    have hmesh := congrArg height
      (inversionRoot_add_inversionRoot_eq_sum_isMiddle hRuns hpx)
    rw [height_add, height_filteredMiddleRootSum] at hmesh
    rw [← hmesh]
    ring
  · intro x hfirst
    have hdefect := congrArg height
      (inversionRoot_sub_sum_isMiddle_eq_sum_earlierNonLast
        (G := G) hfirst)
    rw [height_sub, height_filteredMiddleRootSum, height_add,
      height_simpleRoot] at hdefect
    have hnonneg :=
      height_filteredEarlierNonLastAdjacentRootSum_nonnegative
        G Q hPositive x
    rw [hdefect]
    omega

end RootHeight

open ARWord.SelectedSegments

/-- The middle sum restricted to selected original positions. -/
def selectedScalarMiddleSum (G : SimpleGraph L) (Q : List L)
    (C : Finset (Fin Q.length)) (f : Fin Q.length → ℤ)
    (x : Fin Q.length) : ℤ := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y : Fin Q.length ↦
    ARWord.IsMiddle G Q y x ∧ y ∈ C), f y

/-- Remove zero terms outside the selected set from a literal middle sum. -/
theorem sum_middle_eq_sum_selected_of_zero
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (x : Fin Q.length) (f : Fin Q.length → ℤ)
    (hzero : ∀ y, ARWord.IsMiddle G Q y x → y ∉ C → f y = 0) :
    scalarMiddleSum G Q f x = selectedScalarMiddleSum G Q C f x := by
  classical
  unfold scalarMiddleSum selectedScalarMiddleSum
  symm
  apply Finset.sum_subset
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.1
  · intro y hyMiddle hyNotSelected
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyMiddle
    have hyNC : y ∉ C := by
      intro hyC
      exact hyNotSelected (by simp [hyMiddle, hyC])
    exact hzero y hyMiddle hyNC

/-- Reindex a selected original middle sum by positions of the segment word. -/
theorem scalarMiddleSum_segment_eq_selected
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (f : Fin Q.length → ℤ)
    (x : Fin (segmentWord Q C).length) :
    scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
        (fun y ↦ f (positionInOriginal Q C y)) x =
      selectedScalarMiddleSum G Q C f (positionInOriginal Q C x) := by
  classical
  unfold scalarMiddleSum selectedScalarMiddleSum
  calc
    (∑ y ∈ Finset.univ.filter (fun y : Fin (segmentWord Q C).length ↦
        ARWord.IsMiddle (segmentGraph G Q C) (segmentWord Q C) y x),
        f (positionInOriginal Q C y)) =
        ∑ y : {y : Fin (segmentWord Q C).length //
          ARWord.IsMiddle (segmentGraph G Q C) (segmentWord Q C) y x},
          f (positionInOriginal Q C y.1) := by
      apply Finset.sum_subtype
      intro y
      simp
    _ = ∑ y : {y : Fin Q.length //
          ARWord.IsMiddle G Q y (positionInOriginal Q C x) ∧ y ∈ C},
          f y.1 := by
      exact Fintype.sum_equiv (middlePositionEquiv hRuns C x) _ _
        (fun y ↦ rfl)
    _ = ∑ y ∈ Finset.univ.filter (fun y : Fin Q.length ↦
          ARWord.IsMiddle G Q y (positionInOriginal Q C x) ∧ y ∈ C),
          f y := by
      symm
      apply Finset.sum_subtype
      intro y
      simp

/-- Any `Fintype` presentation of the middle-position subtype has the same
sum as the canonical filtered sum over word positions. -/
theorem subtypeMiddleSum_eq_scalarMiddleSum
    (G : SimpleGraph L) (Q : List L) (f : Fin Q.length → ℤ)
    (x : Fin Q.length)
    [F : Fintype {y : Fin Q.length // ARWord.IsMiddle G Q y x}] :
    (∑ y : {y : Fin Q.length // ARWord.IsMiddle G Q y x}, f y.1) =
      scalarMiddleSum G Q f x := by
  classical
  unfold scalarMiddleSum
  symm
  apply Finset.sum_subtype
  intro y
  simp

/-- The selected-position embedding is injective. -/
theorem positionInOriginal_injective (Q : List L)
    (C : Finset (Fin Q.length)) :
    Function.Injective (positionInOriginal Q C) := by
  intro x y hxy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ((positionInOriginal_lt_iff Q C x y).2 hlt).ne hxy
  · exact ((positionInOriginal_lt_iff Q C y x).2 hgt).ne hxy.symm

open DirectedAROrbit

section SelectedCoordinateTransport

universe uR uIota

variable {K R : Type uR} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

/-- On selected rows and columns, the manuscript's mixed multiplicities
satisfy the inverse mesh recurrence of the segment word.  This is the
coordinate/selected-window transport part of
`lem:directed-principal-positive`; it does not use reducedness. -/
theorem selectedWordMixedMultiplicity_satisfiesWordMeshInverseRecurrence
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (C : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns
      (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T)) :
    SatisfiesWordMeshInverseRecurrence
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) C)
      (segmentWord (OrderedARWord.word sigma H T) C)
      (fun a x ↦ wordMixedMultiplicity (K := K) (R := R) sigma H T C
        (positionInOriginal (OrderedARWord.word sigma H T) C a)
        (positionInOriginal (OrderedARWord.word sigma H T) C x)) := by
  classical
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  let pos := positionInOriginal Q C
  let mu := fun a x ↦
    wordMixedMultiplicity (K := K) (R := R) sigma H T C a x
  have hposInjective : Function.Injective pos :=
    positionInOriginal_injective Q C
  have middleSum_transport (a x : Fin (segmentWord Q C).length) :
      scalarMiddleSum G Q (mu (pos a)) (pos x) =
        scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
          (fun y ↦ mu (pos a) (pos y)) x := by
    have haC : pos a ∈ C := positionInOriginal_mem Q C a
    have hzero : ∀ y, ARWord.IsMiddle G Q y (pos x) →
        y ∉ C → mu (pos a) y = 0 := by
      intro y _ hyC
      change wordMixedMultiplicity (K := K) (R := R) sigma H T C
        (pos a) y = 0
      rw [wordMixedMultiplicity_eq_delta_of_not_mem
        (K := K) (R := R) sigma H T C (pos a) y hyC]
      have hne : pos a ≠ y := fun h ↦ hyC (h ▸ haC)
      simp [hne]
    exact (sum_middle_eq_sum_selected_of_zero G Q C (pos x)
      (mu (pos a)) hzero).trans
        (scalarMiddleSum_segment_eq_selected G Q C hRuns
          (mu (pos a)) x).symm
  simp only [mu] at middleSum_transport
  unfold SatisfiesWordMeshInverseRecurrence
  intro a x
  constructor
  · intro p hpx
    have hpxOriginal : ARWord.IsPrevious Q (pos p) (pos x) :=
      (isPrevious_segmentWord_iff C p x).1 hpx
    have hxC : pos x ∈ C := positionInOriginal_mem Q C x
    change wordMixedMultiplicity (K := K) (R := R) sigma H T C
        (pos a) (pos x) =
      (if a = x then 1 else 0) +
        scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
          (fun y ↦ mu (pos a) (pos y)) x - mu (pos a) (pos p)
    rw [wordMixedMultiplicity_recurrence_of_isPrevious
      (K := K) (R := R) sigma H T C (pos a) (pos p) (pos x)
      hpxOriginal hxC]
    rw [subtypeMiddleSum_eq_scalarMiddleSum]
    rw [middleSum_transport]
    simp only [hposInjective.eq_iff]
    rfl
  · intro hfirstSegment
    have hxC : pos x ∈ C := positionInOriginal_mem Q C x
    by_cases hpreviousOriginal : ∃ p, ARWord.IsPrevious Q p (pos x)
    · obtain ⟨p, hp⟩ := hpreviousOriginal
      have hpNC : p ∉ C := by
        intro hpC
        exact hfirstSegment
          ((exists_isPrevious_segmentWord_iff C x).2 ⟨p, hp, hpC⟩)
      have hpZero : mu (pos a) p = 0 := by
        change wordMixedMultiplicity (K := K) (R := R) sigma H T C
          (pos a) p = 0
        rw [wordMixedMultiplicity_eq_delta_of_not_mem
          (K := K) (R := R) sigma H T C (pos a) p hpNC]
        have haC : pos a ∈ C := positionInOriginal_mem Q C a
        have hne : pos a ≠ p := fun h ↦ hpNC (h ▸ haC)
        simp [hne]
      simp only [mu] at hpZero
      change wordMixedMultiplicity (K := K) (R := R) sigma H T C
          (pos a) (pos x) =
        (if a = x then 1 else 0) +
          scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
            (fun y ↦ mu (pos a) (pos y)) x
      rw [wordMixedMultiplicity_recurrence_of_isPrevious
        (K := K) (R := R) sigma H T C (pos a) p (pos x) hp hxC]
      rw [subtypeMiddleSum_eq_scalarMiddleSum]
      rw [middleSum_transport, hpZero]
      simp only [hposInjective.eq_iff, sub_zero]
      rfl
    · change wordMixedMultiplicity (K := K) (R := R) sigma H T C
          (pos a) (pos x) =
        (if a = x then 1 else 0) +
          scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
            (fun y ↦ mu (pos a) (pos y)) x
      rw [wordMixedMultiplicity_recurrence_of_no_previous
        (K := K) (R := R) sigma H T C (pos a) (pos x)
        hpreviousOriginal hxC]
      rw [subtypeMiddleSum_eq_scalarMiddleSum]
      rw [middleSum_transport]
      simp only [hposInjective.eq_iff]
      rfl

open SegmentReducedness

/-- Exact end-to-end reduction of selected principal positivity to the one
mesh-exactness bridge above.  Segment reducedness, all root calculations,
and all selected-coordinate transport are unconditional. -/
theorem selectedWordMixedMultiplicity_nonnegative_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (C : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hProjectedReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (selectedWord (OrderedARWord.word sigma H T) C))
    (hMeshExactness : PositiveRightAdditiveForcesMeshInverseNonnegative
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) C)
      (segmentWord (OrderedARWord.word sigma H T) C))
    (a x : Fin (segmentWord (OrderedARWord.word sigma H T) C).length) :
    0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T C
      (positionInOriginal (OrderedARWord.word sigma H T) C a)
      (positionInOriginal (OrderedARWord.word sigma H T) C x) := by
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  have hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q :=
    OrderedARWord.word_hasOnlyBoundaryRepeatedRuns sigma H T
  have hSegmentRuns : ARWord.HasOnlyBoundaryRepeatedRuns
      (segmentGraph G Q C) (segmentWord Q C) :=
    hasOnlyBoundaryRepeatedRuns_segmentWord hRuns C
  have hSegmentReduced : IsReduced
      (segmentGraph G Q C) (segmentWord Q C) :=
    segmentWord_isReduced G Q C hRuns hProjectedReduced
  have hRightAdditive := inversionRootHeight_isPositiveRightAdditive
    (segmentGraph G Q C) (segmentWord Q C)
      hSegmentRuns hSegmentReduced
  exact hMeshExactness hSegmentRuns _ hRightAdditive _
    (selectedWordMixedMultiplicity_satisfiesWordMeshInverseRecurrence
      (K := K) (R := R) sigma H T C hRuns) a x

/-- Original-position form: every selected matrix entry is nonnegative. -/
theorem wordMixedMultiplicity_nonnegative_on_selected_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (C : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hProjectedReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (selectedWord (OrderedARWord.word sigma H T) C))
    (hMeshExactness : PositiveRightAdditiveForcesMeshInverseNonnegative
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) C)
      (segmentWord (OrderedARWord.word sigma H T) C))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (ha : a ∈ C) (hx : x ∈ C) :
    0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T C a x := by
  let aSegment := positionOfSelected (OrderedARWord.word sigma H T) C a ha
  let xSegment := positionOfSelected (OrderedARWord.word sigma H T) C x hx
  have h := selectedWordMixedMultiplicity_nonnegative_of_meshExactness
    (K := K) (R := R) sigma H T C hProjectedReduced hMeshExactness
      aSegment xSegment
  simpa only [aSegment, xSegment, positionInOriginal_positionOfSelected] using h

/-- Selected rows and columns satisfy the segment-word inverse recurrence
for every explicit directed order. -/
private theorem selectedWordMixedMultiplicityFor_satisfiesWordMeshInverseRecurrence
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (OrderedARWord.wordFor sigma H T E).length)) :
    SatisfiesWordMeshInverseRecurrence
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) C)
      (segmentWord (OrderedARWord.wordFor sigma H T E) C)
      (fun a x ↦ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E C
        (positionInOriginal (OrderedARWord.wordFor sigma H T E) C a)
        (positionInOriginal (OrderedARWord.wordFor sigma H T E) C x)) := by
  classical
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  let pos := positionInOriginal Q C
  let mu := fun a x ↦
    wordMixedMultiplicityFor (K := K) (R := R) sigma H T E C a x
  have hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q :=
    OrderedARWord.wordFor_hasOnlyBoundaryRepeatedRuns sigma H T E
  have hposInjective : Function.Injective pos :=
    positionInOriginal_injective Q C
  have middleSum_transport (a x : Fin (segmentWord Q C).length) :
      scalarMiddleSum G Q (mu (pos a)) (pos x) =
        scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
          (fun y ↦ mu (pos a) (pos y)) x := by
    have haC : pos a ∈ C := positionInOriginal_mem Q C a
    have hzero : ∀ y, ARWord.IsMiddle G Q y (pos x) →
        y ∉ C → mu (pos a) y = 0 := by
      intro y _ hyC
      change wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E C (pos a) y = 0
      rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
        (K := K) (R := R) sigma H T E C (pos a) y hyC]
      have hne : pos a ≠ y := fun h ↦ hyC (h ▸ haC)
      simp [hne]
    exact (sum_middle_eq_sum_selected_of_zero G Q C (pos x)
      (mu (pos a)) hzero).trans
        (scalarMiddleSum_segment_eq_selected G Q C hRuns
          (mu (pos a)) x).symm
  simp only [mu] at middleSum_transport
  unfold SatisfiesWordMeshInverseRecurrence
  intro a x
  constructor
  · intro p hpx
    have hpxOriginal : ARWord.IsPrevious Q (pos p) (pos x) :=
      (isPrevious_segmentWord_iff C p x).1 hpx
    have hxC : pos x ∈ C := positionInOriginal_mem Q C x
    change wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E C (pos a) (pos x) =
      (if a = x then 1 else 0) +
        scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
          (fun y ↦ mu (pos a) (pos y)) x - mu (pos a) (pos p)
    rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
      (K := K) (R := R) sigma H T E C (pos a) (pos p) (pos x)
      hpxOriginal hxC]
    rw [subtypeMiddleSum_eq_scalarMiddleSum]
    rw [middleSum_transport]
    simp only [hposInjective.eq_iff]
    rfl
  · intro hfirstSegment
    have hxC : pos x ∈ C := positionInOriginal_mem Q C x
    by_cases hpreviousOriginal : ∃ p, ARWord.IsPrevious Q p (pos x)
    · obtain ⟨p, hp⟩ := hpreviousOriginal
      have hpNC : p ∉ C := by
        intro hpC
        exact hfirstSegment
          ((exists_isPrevious_segmentWord_iff C x).2 ⟨p, hp, hpC⟩)
      have hpZero : mu (pos a) p = 0 := by
        change wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E C (pos a) p = 0
        rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
          (K := K) (R := R) sigma H T E C (pos a) p hpNC]
        have haC : pos a ∈ C := positionInOriginal_mem Q C a
        have hne : pos a ≠ p := fun h ↦ hpNC (h ▸ haC)
        simp [hne]
      simp only [mu] at hpZero
      change wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E C (pos a) (pos x) =
        (if a = x then 1 else 0) +
          scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
            (fun y ↦ mu (pos a) (pos y)) x
      rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
        (K := K) (R := R) sigma H T E C (pos a) p (pos x) hp hxC]
      rw [subtypeMiddleSum_eq_scalarMiddleSum]
      rw [middleSum_transport, hpZero]
      simp only [hposInjective.eq_iff, sub_zero]
      rfl
    · change wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E C (pos a) (pos x) =
        (if a = x then 1 else 0) +
          scalarMiddleSum (segmentGraph G Q C) (segmentWord Q C)
            (fun y ↦ mu (pos a) (pos y)) x
      rw [wordMixedMultiplicityFor_recurrence_of_no_previous
        (K := K) (R := R) sigma H T E C (pos a) (pos x)
        hpreviousOriginal hxC]
      rw [subtypeMiddleSum_eq_scalarMiddleSum]
      rw [middleSum_transport]
      simp only [hposInjective.eq_iff]
      rfl

/-- Mesh exactness gives nonnegativity on the selected segment coordinates
for an explicit directed order. -/
private theorem selectedWordMixedMultiplicityFor_nonnegative_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hProjectedReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (selectedWord (OrderedARWord.wordFor sigma H T E) C))
    (hMeshExactness : PositiveRightAdditiveForcesMeshInverseNonnegative
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) C)
      (segmentWord (OrderedARWord.wordFor sigma H T E) C))
    (a x : Fin
      (segmentWord (OrderedARWord.wordFor sigma H T E) C).length) :
    0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E C
      (positionInOriginal (OrderedARWord.wordFor sigma H T E) C a)
      (positionInOriginal (OrderedARWord.wordFor sigma H T E) C x) := by
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  have hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q :=
    OrderedARWord.wordFor_hasOnlyBoundaryRepeatedRuns sigma H T E
  have hSegmentRuns : ARWord.HasOnlyBoundaryRepeatedRuns
      (segmentGraph G Q C) (segmentWord Q C) :=
    hasOnlyBoundaryRepeatedRuns_segmentWord hRuns C
  have hSegmentReduced : IsReduced
      (segmentGraph G Q C) (segmentWord Q C) :=
    segmentWord_isReduced G Q C hRuns hProjectedReduced
  have hRightAdditive := inversionRootHeight_isPositiveRightAdditive
    (segmentGraph G Q C) (segmentWord Q C)
      hSegmentRuns hSegmentReduced
  exact hMeshExactness hSegmentRuns _ hRightAdditive _
    (selectedWordMixedMultiplicityFor_satisfiesWordMeshInverseRecurrence
      (K := K) (R := R) sigma H T E C) a x

/-- Original-position form of explicit-order selected positivity. -/
theorem wordMixedMultiplicityFor_nonnegative_on_selected_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hProjectedReduced : IsReduced
      (OrderedARWord.orbitGraph sigma H T)
      (selectedWord (OrderedARWord.wordFor sigma H T E) C))
    (hMeshExactness : PositiveRightAdditiveForcesMeshInverseNonnegative
      (segmentGraph (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) C)
      (segmentWord (OrderedARWord.wordFor sigma H T E) C))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (ha : a ∈ C) (hx : x ∈ C) :
    0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E C a x := by
  let aSegment := positionOfSelected
    (OrderedARWord.wordFor sigma H T E) C a ha
  let xSegment := positionOfSelected
    (OrderedARWord.wordFor sigma H T E) C x hx
  have h := selectedWordMixedMultiplicityFor_nonnegative_of_meshExactness
    (K := K) (R := R) sigma H T E C
      hProjectedReduced hMeshExactness aSegment xSegment
  simpa only [aSegment, xSegment,
    positionInOriginal_positionOfSelected] using h

end SelectedCoordinateTransport

end OpConjecture.RepresentationDirected.PrincipalPositivity
