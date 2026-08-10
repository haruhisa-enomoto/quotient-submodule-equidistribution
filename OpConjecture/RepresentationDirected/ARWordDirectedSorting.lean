import OpConjecture.RepresentationDirected.ARWordPrincipalPositivity
import OpConjecture.RepresentationDirected.FixedWordSortingExchange
import OpConjecture.RepresentationDirected.ARWordFirstCancellation
import OpConjecture.RepresentationDirected.ClosureEffectivity

set_option autoImplicit false

noncomputable section

/-!
# Directed sorting from mesh positivity and first cancellation

This file proves the paper's three-way directed-sorting theorem at the
abstract representation-directed level.  The forward implication is reduced
to the isolated finite mesh-exactness input from `ARWordPrincipalPositivity`;
the converse is unconditional and uses the first-cancellation identity.

No concrete algebra, quiver presentation, or module classification occurs
here.
-/

namespace OpConjecture.RepresentationDirected.DirectedSorting

open OpConjecture.RepresentationDirected.FixedWord
open OpConjecture.RepresentationDirected
open OpConjecture.RepresentationDirected.ARWord.SelectedSegments
open OpConjecture.RepresentationDirected.DirectedAROrbit
open OpConjecture.RepresentationDirected.PrincipalPositivity
open OpConjecture.RepresentationDirected.SimpleGraphCoxeter
open OpConjecture.RepresentationDirected.FirstCancellation
open OpConjecture.RepresentationDirected.WordRootProcess

universe u

variable {L : Type u}

theorem selectedWord_eq_subwordAt (Q : List L)
    (C : Finset (Fin Q.length)) :
    selectedWord Q C = subwordAt Q C := by
  rw [selectedWord, subwordAt, List.ofFn_eq_map]
  change (List.finRange C.card).map
      (Q.get ∘ C.orderEmbOfFin rfl) =
    (C.sort (· ≤ ·)).map Q.get
  rw [← List.map_map,
    Finset.listMap_orderEmbOfFin_finRange C rfl]

/-- Selecting every position recovers the ambient word. -/
theorem subwordAt_univ (Q : List L) :
    subwordAt Q Finset.univ = Q := by
  rw [subwordAt, Fin.sort_univ, List.map_get_finRange]

universe uR uIota

variable {K R : Type uR} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

/-- Conditional forward half of directed sorting: local reducedness and the
finite mesh-exactness input imply nonnegativity of every mixed
multiplicity. -/
theorem wordMixedMultiplicity_nonnegative_of_allLocalReduced
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hLocal : SortingExchange.AreAllLocalSubwordsReduced
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.word sigma H T) D)
    (hMeshExactness : ∀ a : Fin (OrderedARWord.word sigma H T).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a)))
    (a x : Fin (OrderedARWord.word sigma H T).length) :
    0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x := by
  rw [wordMixedMultiplicity_row_transport
    (K := K) (R := R) sigma H T D a x]
  let C := rowRestrictedOmissions D a
  by_cases hxC : x ∈ C
  · apply wordMixedMultiplicity_nonnegative_on_selected_of_meshExactness
      (K := K) (R := R) sigma H T C
    · rw [selectedWord_eq_subwordAt]
      exact hLocal a
    · exact hMeshExactness a
    · simp [C]
    · exact hxC
  · rw [wordMixedMultiplicity_eq_delta_of_not_mem
      (K := K) (R := R) sigma H T C a x hxC]
    split <;> omega

/-- Closure effectivity in the ordered-word coordinates used by directed
sorting. -/
theorem qClosed_iff_wordMixedMultiplicity_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length)) :
    sigma.qClosure.IsClosed
        {i | i ∉ omittedLabelFinset sigma H T D} ↔
      ∀ a x : Fin (OrderedARWord.word sigma H T).length,
        0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x := by
  rw [H.qClosed_iff_mixedMultiplicity_obj_nonnegative
    (K := K) (R := R) sigma (omittedLabelFinset sigma H T D)]
  constructor
  · intro h a x
    exact h (OrderedARWord.positionEquiv sigma H T a)
      (OrderedARWord.positionEquiv sigma H T x)
  · intro h i j
    let a := (OrderedARWord.positionEquiv sigma H T).symm i
    let x := (OrderedARWord.positionEquiv sigma H T).symm j
    simpa [wordMixedMultiplicity, a, x] using h a x

section FirstNegative

variable [Fintype L]

/-- A positive real-root process ending in the negative cone has a first
negative update, and all states before that update are nonnegative. -/
theorem exists_firstNegativeOriginalUpdate
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (ps : List (Fin Q.length))
    (z : RootLattice L)
    (hpositive : IsPositive z)
    (hnegative : IsNegative
      (updateProduct (originalWordUpdate G Q D) ps z))
    (hsign : ∀ qs : List (Fin Q.length),
      IsPositive (updateProduct (originalWordUpdate G Q D) qs z) ∨
        IsNegative (updateProduct (originalWordUpdate G Q D) qs z)) :
    ∃ pre x post,
      ps = pre ++ x :: post ∧
        HasNonnegativeOriginalStates G Q D (pre ++ [x]) z ∧
        IsPositive
          (updateProduct (originalWordUpdate G Q D) pre z) ∧
        IsNegative
          (originalWordUpdate G Q D x
            (updateProduct (originalWordUpdate G Q D) pre z)) := by
  induction ps generalizing z with
  | nil =>
      exact (hpositive.not_isNegative (by simpa using hnegative)).elim
  | cons p ps ih =>
      let z' := originalWordUpdate G Q D p z
      have hsign' : IsPositive z' ∨ IsNegative z' := by
        simpa [z', updateProduct] using hsign [p]
      rcases hsign' with hpositive' | hnegative'
      · have hnegativeTail : IsNegative
            (updateProduct (originalWordUpdate G Q D) ps z') := by
          simpa [z', updateProduct] using hnegative
        have hsignTail : ∀ qs : List (Fin Q.length),
            IsPositive
                (updateProduct (originalWordUpdate G Q D) qs z') ∨
              IsNegative
                (updateProduct (originalWordUpdate G Q D) qs z') := by
          intro qs
          simpa [z', updateProduct] using hsign (p :: qs)
        obtain ⟨pre, x, post, hsplit, hnonnegative,
            hbefore, hafter⟩ :=
          ih z' hpositive' hnegativeTail hsignTail
        refine ⟨p :: pre, x, post, by simp [hsplit], ?_, ?_, ?_⟩
        · exact ⟨hpositive.1, hnonnegative⟩
        · simpa [z', updateProduct] using hbefore
        · simpa [z', updateProduct] using hafter
      · refine ⟨[], p, ps, rfl, ?_, ?_, ?_⟩
        · exact ⟨hpositive.1, trivial⟩
        · simpa [updateProduct] using hpositive
        · simpa [z', updateProduct] using hnegative'

/-- Filtering a complete discrete interval by the selected set gives the
sorted selected positions in that interval. -/
theorem filter_positionsIoc_eq_sort_filter
    {n : ℕ} (D : Finset (Fin n)) (a x : Fin n) :
    (positionsIoc a x).filter (fun p ↦ p ∈ D) =
      (D.filter fun p ↦ a < p ∧ p ≤ x).sort (· ≤ ·) := by
  apply List.Pairwise.eq_of_mem_iff
    ((positionsIoc_pairwise a x).filter _)
    ((D.filter fun p ↦ a < p ∧ p ≤ x).sortedLT_sort.pairwise)
  intro p
  simp [and_assoc, and_comm]

omit [Fintype L] in
/-- The selected labels in a complete interval are the literal subword on
the selected positions in that interval. -/
theorem selectedLabels_positionsIoc
    (Q : List L) (D : Finset (Fin Q.length))
    (a x : Fin Q.length) :
    selectedLabels Q D (positionsIoc a x) =
      ((D.filter fun p ↦ a < p ∧ p ≤ x).sort (· ≤ ·)).map
        (ARWord.label Q) := by
  rw [selectedLabels, filter_positionsIoc_eq_sort_filter]

omit [Fintype L] in
/-- At a greatest word position, the complete interval contains every
selected position strictly after its lower endpoint. -/
theorem selectedLabels_positionsIoc_greatest
    (Q : List L) (D : Finset (Fin Q.length))
    (a x : Fin Q.length) (hx : ∀ p : Fin Q.length, p ≤ x) :
    selectedLabels Q D (positionsIoc a x) =
      ((D.filter fun p ↦ a < p).sort (· ≤ ·)).map
        (ARWord.label Q) := by
  rw [selectedLabels_positionsIoc]
  congr 2
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpD, hap, _⟩
    exact ⟨hpD, hap⟩
  · rintro ⟨hpD, hap⟩
    exact ⟨hpD, hap, hx p⟩

/-- A reduced tail whose left extension is nonreduced sends the extending
simple root into the negative cone under the inverse tail action. -/
theorem selectedOperationalRootState_negative_of_tail
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length)) (a : Fin Q.length)
    (ps : List (Fin Q.length))
    (hTailReduced : (system G).IsReduced (selectedLabels Q D ps))
    (hConsNotReduced : ¬ (system G).IsReduced
      (ARWord.label Q a :: selectedLabels Q D ps)) :
    IsNegative (selectedOperationalRootState G Q D a ps) := by
  have hLeftDescent : (system G).IsLeftDescent
      ((system G).wordProd (selectedLabels Q D ps))
      (ARWord.label Q a) := by
    exact not_not.mp
      ((SortingExchange.isReduced_cons_iff_not_isLeftDescent
        (system G) (selectedLabels Q D ps) (ARWord.label Q a)
        hTailReduced).not.mp hConsNotReduced)
  rw [selectedOperationalRootState_eq_inverse_word_action]
  apply RootSignStrategy.rightDescentImpliesNegativeRoot_of_hasGlobalRootSignCompatibility
    G (RootSignStrategy.globalRootSignCompatibility G)
  exact ((system G).isRightDescent_inv_iff).2 hLeftDescent

omit [Fintype L] in
/-- If some local word is nonreduced, there is a rightmost such row.  Its
selected tail is reduced. -/
theorem exists_badRow_with_reduced_tail
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (hBad : ¬ SortingExchange.AreAllLocalSubwordsReduced
      (system G) Q D) :
    ∃ a : Fin Q.length,
      ¬ (system G).IsReduced
        (ARWord.label Q a ::
          ((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
            (ARWord.label Q)) ∧
      (system G).IsReduced
        (((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
          (ARWord.label Q)) := by
  classical
  have hExists : ∃ a : Fin Q.length,
      ¬ (system G).IsReduced
        (ARWord.label Q a ::
          ((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
            (ARWord.label Q)) := by
    rw [SortingExchange.AreAllLocalSubwordsReduced] at hBad
    push Not at hBad
    obtain ⟨a, ha⟩ := hBad
    refine ⟨a, ?_⟩
    rw [SortingExchange.subwordAt_localPositions,
      SortingExchange.filter_sort_eq_sort_filter] at ha
    exact ha
  let bad : Finset (Fin Q.length) := Finset.univ.filter fun a ↦
    ¬ (system G).IsReduced
      (ARWord.label Q a ::
        ((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
          (ARWord.label Q))
  have hBadNonempty : bad.Nonempty := by
    obtain ⟨a, ha⟩ := hExists
    refine ⟨a, ?_⟩
    change a ∈ Finset.univ.filter fun a ↦
      ¬ (system G).IsReduced
        (ARWord.label Q a ::
          ((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
            (ARWord.label Q))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
  let a := bad.max' hBadNonempty
  have haBad : a ∈ bad := bad.max'_mem hBadNonempty
  have haNonreduced : ¬ (system G).IsReduced
      (ARWord.label Q a ::
        ((D.filter fun d ↦ a < d).sort (· ≤ ·)).map
          (ARWord.label Q)) := by
    simpa [bad] using haBad
  refine ⟨a, haNonreduced, ?_⟩
  let tail : Finset (Fin Q.length) := D.filter fun d ↦ a < d
  by_cases hTail : tail.Nonempty
  · let b := tail.min' hTail
    have hbTail : b ∈ tail := tail.min'_mem hTail
    have hab : a < b := (Finset.mem_filter.mp hbTail).2
    have hbLocalReduced : (system G).IsReduced
        (ARWord.label Q b ::
          ((D.filter fun d ↦ b < d).sort (· ≤ ·)).map
            (ARWord.label Q)) := by
      by_contra hbBad
      have hbMemBad : b ∈ bad := by
        change b ∈ Finset.univ.filter fun b ↦
          ¬ (system G).IsReduced
            (ARWord.label Q b ::
              ((D.filter fun d ↦ b < d).sort (· ≤ ·)).map
                (ARWord.label Q))
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hbBad
      have hba : b ≤ a := bad.le_max' b hbMemBad
      exact (not_le_of_gt hab) hba
    have hTailEq : tail = insert b (D.filter fun d ↦ b < d) := by
      ext d
      constructor
      · intro hdTail
        have hdData := Finset.mem_filter.mp hdTail
        have hbd : b ≤ d := tail.min'_le d hdTail
        rcases hbd.eq_or_lt with hbd | hbd
        · simp [hbd]
        · simp [hdData.1, hbd]
      · intro hd
        simp only [Finset.mem_insert, Finset.mem_filter] at hd
        rcases hd with hdb | hd
        · subst d
          exact hbTail
        · exact Finset.mem_filter.mpr ⟨hd.1, hab.trans hd.2⟩
    have hSortTail : tail.sort (· ≤ ·) =
        b :: (D.filter fun d ↦ b < d).sort (· ≤ ·) := by
      rw [hTailEq]
      apply Finset.sort_insert
      · intro d hd
        exact (Finset.mem_filter.mp hd).2.le
      · simp
    simpa [tail, hSortTail] using hbLocalReduced
  · have hTailEmpty : tail = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTail
    change (system G).IsReduced
      ((tail.sort (· ≤ ·)).map (ARWord.label Q))
    rw [hTailEmpty]
    simp [CoxeterSystem.IsReduced]

/-- A nonreduced local row produces the exact first-negative interval data
consumed by the cancellation theorem. -/
theorem exists_firstNegativeInterval_of_not_allLocalReduced
    (G : SimpleGraph L) (Q : List L)
    (D : Finset (Fin Q.length))
    (hBad : ¬ SortingExchange.AreAllLocalSubwordsReduced
      (system G) Q D) :
    ∃ a x : Fin Q.length,
      a < x ∧ x ∈ D ∧
      HasNonnegativeOriginalStates G Q D (positionsIoc a x)
        (simpleRoot (ARWord.label Q a)) ∧
      IsNegative (originalWordUpdate G Q D x
        (selectedOperationalRootState G Q D a
          (positionsIoc a x).dropLast)) := by
  classical
  obtain ⟨a, hConsNotReduced, hTailReduced⟩ :=
    exists_badRow_with_reduced_tail G Q D hBad
  let last : Fin Q.length :=
    ⟨Q.length - 1,
      Nat.sub_lt (Nat.zero_lt_of_lt a.isLt) Nat.zero_lt_one⟩
  have hGreatest : ∀ p : Fin Q.length, p ≤ last := by
    intro p
    change p.val ≤ Q.length - 1
    omega
  let ps := positionsIoc a last
  have hSelectedLabels : selectedLabels Q D ps =
      ((D.filter fun p ↦ a < p).sort (· ≤ ·)).map
        (ARWord.label Q) := by
    exact selectedLabels_positionsIoc_greatest Q D a last hGreatest
  have hFinalNegative : IsNegative
      (selectedOperationalRootState G Q D a ps) := by
    apply selectedOperationalRootState_negative_of_tail
    · simpa [hSelectedLabels] using hTailReduced
    · simpa [hSelectedLabels] using hConsNotReduced
  have hStartPositive : IsPositive
      (simpleRoot (ARWord.label Q a)) :=
    simpleRoot_isPositive (ARWord.label Q a)
  have hSign : ∀ qs : List (Fin Q.length),
      IsPositive (updateProduct (originalWordUpdate G Q D) qs
        (simpleRoot (ARWord.label Q a))) ∨
      IsNegative (updateProduct (originalWordUpdate G Q D) qs
        (simpleRoot (ARWord.label Q a))) := by
    intro qs
    change IsPositive (selectedOperationalRootState G Q D a qs) ∨
      IsNegative (selectedOperationalRootState G Q D a qs)
    rw [selectedOperationalRootState_eq_inverse_word_action]
    exact RootSignStrategy.realRootSignDichotomy G _ _
  have hFinalNegative' : IsNegative
      (updateProduct (originalWordUpdate G Q D) ps
        (simpleRoot (ARWord.label Q a))) := hFinalNegative
  obtain ⟨pre, x, post, hsplit, hnonnegative,
      hBeforePositive, hAfterNegative⟩ :=
    exists_firstNegativeOriginalUpdate G Q D ps
      (simpleRoot (ARWord.label Q a)) hStartPositive
      hFinalNegative' hSign
  have hxPs : x ∈ ps := by
    rw [hsplit]
    simp
  have hax : a < x := (mem_positionsIoc.mp hxPs).1
  have hxD : x ∈ D := by
    by_contra hxD
    have hSame : originalWordUpdate G Q D x
        (updateProduct (originalWordUpdate G Q D) pre
          (simpleRoot (ARWord.label Q a))) =
      updateProduct (originalWordUpdate G Q D) pre
          (simpleRoot (ARWord.label Q a)) := by
      simp [originalWordUpdate, hxD]
    rw [hSame] at hAfterNegative
    exact hBeforePositive.not_isNegative hAfterNegative
  have hpairFull : (pre ++ x :: post).Pairwise (· < ·) := by
    rw [← hsplit]
    exact positionsIoc_pairwise a last
  have hpairData := List.pairwise_append.mp hpairFull
  have hpairPrefix : (pre ++ [x]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hpairData.1, by simp, ?_⟩
    intro p hp q hq
    simp only [List.mem_singleton] at hq
    subst q
    exact hpairData.2.2 p hp x (by simp)
  have hPrefix : pre ++ [x] = positionsIoc a x := by
    apply List.Pairwise.eq_of_mem_iff hpairPrefix
      (positionsIoc_pairwise a x)
    intro p
    constructor
    · intro hp
      have hpFull : p ∈ ps := by
        rw [hsplit]
        rcases List.mem_append.mp hp with hpPre | hpX
        · exact List.mem_append_left (x :: post) hpPre
        · apply List.mem_append_right pre
          exact List.mem_cons.mpr (Or.inl (by simpa using hpX))
      have hap : a < p := (mem_positionsIoc.mp hpFull).1
      have hpx : p ≤ x := by
        rcases List.mem_append.mp hp with hpPre | hpX
        · exact (hpairData.2.2 p hpPre x (by simp)).le
        · exact (show p = x by simpa using hpX).le
      exact mem_positionsIoc.mpr ⟨hap, hpx⟩
    · intro hp
      have hpData := mem_positionsIoc.mp hp
      have hxLast : x ≤ last := (mem_positionsIoc.mp hxPs).2
      have hpPs : p ∈ ps := mem_positionsIoc.mpr
        ⟨hpData.1, hpData.2.trans hxLast⟩
      rw [hsplit] at hpPs
      rcases List.mem_append.mp hpPs with hpPre | hpTail
      · exact List.mem_append_left [x] hpPre
      · rcases List.mem_cons.mp hpTail with hpx | hpPost
        · subst p
          simp
        · have hxp : x < p :=
            (List.pairwise_cons.mp hpairData.2.1).1 p hpPost
          exact (not_lt_of_ge hpData.2 hxp).elim
  have hPre : pre = (positionsIoc a x).dropLast := by
    rw [← hPrefix]
    simp
  refine ⟨a, x, hax, hxD, ?_, ?_⟩
  · simpa [hPrefix] using hnonnegative
  · change IsNegative (originalWordUpdate G Q D x
      (selectedOperationalRootState G Q D a pre)) at hAfterNegative
    simpa [← hPre] using hAfterNegative

/-- Converse half of directed sorting: global nonnegativity of the mixed
multiplicity matrix forces every local word to be reduced. -/
theorem allLocalReduced_of_wordMixedMultiplicity_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hNonnegative : ∀ a x : Fin (OrderedARWord.word sigma H T).length,
      0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x) :
    SortingExchange.AreAllLocalSubwordsReduced
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.word sigma H T) D := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  by_contra hBad
  let Q := OrderedARWord.word sigma H T
  let G := OrderedARWord.orbitGraph sigma H T
  obtain ⟨a, x, hax, hxD, hStates, hNegative⟩ :=
    exists_firstNegativeInterval_of_not_allLocalReduced G Q D hBad
  have hCancellation :=
    firstNegativeCancellation_with_positive_coefficients
      (K := K) (R := R) sigma H T D a x hax hxD hStates hNegative
  let c := orderedARWordOriginalCoefficient sigma H T D a
  let mu := fun e ↦ wordMixedMultiplicity (K := K) (R := R)
    sigma H T D e x
  have hSumNonnegative : 0 ≤
      unselectedContributionSum D c mu (positionsIoc a x) := by
    unfold unselectedContributionSum
    apply List.sum_nonneg
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    have heData := List.mem_filter.mp he
    have heNot : e ∉ D := by simpa using heData.2
    have hc : 0 ≤ c e := by
      by_cases hce : c e = 0
      · simp [hce]
      · exact (hCancellation.2 e heData.1 heNot hce).le
    exact mul_nonneg hc (hNonnegative e x)
  have hAxNonnegative := hNonnegative a x
  have hEq := hCancellation.1
  change wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      -1 - unselectedContributionSum D c mu (positionsIoc a x) at hEq
  omega

/-- The mathematical core of directed sorting, conditional only on the
isolated finite mesh-exactness theorem. -/
theorem allLocalReduced_iff_wordMixedMultiplicity_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hMeshExactness : ∀ a : Fin (OrderedARWord.word sigma H T).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    SortingExchange.AreAllLocalSubwordsReduced
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.word sigma H T) D ↔
      ∀ a x : Fin (OrderedARWord.word sigma H T).length,
        0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x := by
  constructor
  · intro hLocal a x
    exact wordMixedMultiplicity_nonnegative_of_allLocalReduced
      (K := K) (R := R) sigma H T D hLocal hMeshExactness a x
  · exact allLocalReduced_of_wordMixedMultiplicity_nonnegative
      (K := K) (R := R) sigma H T D

/-- Paper-facing three-way directed-sorting theorem: fixed-word sortedness,
mixed-coordinate nonnegativity, and quotient closure are equivalent. -/
theorem directedSorting
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (hMeshExactness : ∀ a : Fin (OrderedARWord.word sigma H T).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions D a))) :
    (OpConjecture.RepresentationDirected.FixedWord.IsLeftmostReducedSubwordFor
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.word sigma H T)
        ((system (OrderedARWord.orbitGraph sigma H T)).wordProd
          (subwordAt (OrderedARWord.word sigma H T) D)) D ↔
      ∀ a x : Fin (OrderedARWord.word sigma H T).length,
        0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x) ∧
    ((∀ a x : Fin (OrderedARWord.word sigma H T).length,
        0 ≤ wordMixedMultiplicity (K := K) (R := R) sigma H T D a x) ↔
      sigma.qClosure.IsClosed
        {i | i ∉ omittedLabelFinset sigma H T D}) := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  constructor
  · rw [SortingExchange.leftmostReducedSubwordFor_iff_allLocal_simpleGraph]
    exact allLocalReduced_iff_wordMixedMultiplicity_nonnegative
      (K := K) (R := R) sigma H T D hMeshExactness
  · exact (qClosed_iff_wordMixedMultiplicity_nonnegative
      (K := K) (R := R) sigma H T D).symm

include K in
/-- Applying directed sorting to the full position set proves that the
ordered Auslander--Reiten word is reduced.  As in the manuscript, reducedness
is a conclusion rather than an input. -/
theorem orderedARWord_isReduced_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (hMeshExactness : ∀ a : Fin (OrderedARWord.word sigma H T).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions Finset.univ a))
        (segmentWord (OrderedARWord.word sigma H T)
          (rowRestrictedOmissions Finset.univ a))) :
    IsReduced (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.word sigma H T) := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  have hClosed : sigma.qClosure.IsClosed
      {i | i ∉ omittedLabelFinset sigma H T
        (Finset.univ : Finset
          (Fin (OrderedARWord.word sigma H T).length))} := by
    simpa [omittedLabelFinset] using
      (IndecomposableSkeleton.qClosure_isClosed_empty sigma)
  have hThree := directedSorting (K := K) (R := R) sigma H T
    (Finset.univ : Finset
      (Fin (OrderedARWord.word sigma H T).length)) hMeshExactness
  have hNonnegative := hThree.2.mpr hClosed
  have hLeftmost := hThree.1.mpr hNonnegative
  change (system (OrderedARWord.orbitGraph sigma H T)).IsReduced
    (OrderedARWord.word sigma H T)
  simpa [subwordAt_univ] using hLeftmost.1.1

/-! ## Explicit-order directed sorting -/

/-- Local reducedness plus mesh exactness makes every explicit-order mixed
multiplicity nonnegative. -/
private theorem wordMixedMultiplicityFor_nonnegative_of_allLocalReduced
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hLocal : SortingExchange.AreAllLocalSubwordsReduced
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.wordFor sigma H T E) D)
    (hMeshExactness :
      ∀ a : Fin (OrderedARWord.wordFor sigma H T E).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a)))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D a x := by
  rw [wordMixedMultiplicityFor_row_transport
    (K := K) (R := R) sigma H T E D a x]
  let C := rowRestrictedOmissions D a
  by_cases hxC : x ∈ C
  · apply wordMixedMultiplicityFor_nonnegative_on_selected_of_meshExactness
      (K := K) (R := R) sigma H T E C
    · rw [selectedWord_eq_subwordAt]
      exact hLocal a
    · exact hMeshExactness a
    · simp [C]
    · exact hxC
  · rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
      (K := K) (R := R) sigma H T E C a x hxC]
    split <;> omega

/-- Closure effectivity transported through an arbitrary explicit position
equivalence. -/
private theorem qClosed_iff_wordMixedMultiplicityFor_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length)) :
    sigma.qClosure.IsClosed
        {i | i ∉ omittedLabelFinsetFor sigma H T E D} ↔
      ∀ a x : Fin (OrderedARWord.wordFor sigma H T E).length,
        0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x := by
  rw [H.qClosed_iff_mixedMultiplicity_obj_nonnegative
    (K := K) (R := R) sigma (omittedLabelFinsetFor sigma H T E D)]
  constructor
  · intro h a x
    exact h (OrderedARWord.positionEquivFor sigma H T E a)
      (OrderedARWord.positionEquivFor sigma H T E x)
  · intro h i j
    let a := (OrderedARWord.positionEquivFor sigma H T E).symm i
    let x := (OrderedARWord.positionEquivFor sigma H T E).symm j
    simpa [wordMixedMultiplicityFor, a, x] using h a x

/-- Global explicit-order mixed-coordinate nonnegativity forces all local
subwords to be reduced. -/
private theorem allLocalReduced_of_wordMixedMultiplicityFor_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hNonnegative :
      ∀ a x : Fin (OrderedARWord.wordFor sigma H T E).length,
      0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x) :
    SortingExchange.AreAllLocalSubwordsReduced
      (system (OrderedARWord.orbitGraph sigma H T))
      (OrderedARWord.wordFor sigma H T E) D := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  by_contra hBad
  let Q := OrderedARWord.wordFor sigma H T E
  let G := OrderedARWord.orbitGraph sigma H T
  obtain ⟨a, x, hax, hxD, hStates, hNegative⟩ :=
    exists_firstNegativeInterval_of_not_allLocalReduced G Q D hBad
  have hCancellation :=
    firstNegativeCancellation_with_positive_coefficientsFor
      (K := K) (R := R) sigma H T E D a x
        hax hxD hStates hNegative
  let c := orderedARWordOriginalCoefficientFor sigma H T E D a
  let mu := fun e ↦ wordMixedMultiplicityFor (K := K) (R := R)
    sigma H T E D e x
  have hSumNonnegative : 0 ≤
      unselectedContributionSum D c mu (positionsIoc a x) := by
    unfold unselectedContributionSum
    apply List.sum_nonneg
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨e, he, rfl⟩ := hz
    have heData := List.mem_filter.mp he
    have heNot : e ∉ D := by simpa using heData.2
    have hc : 0 ≤ c e := by
      by_cases hce : c e = 0
      · simp [hce]
      · exact (hCancellation.2 e heData.1 heNot hce).le
    exact mul_nonneg hc (hNonnegative e x)
  have hAxNonnegative := hNonnegative a x
  have hEq := hCancellation.1
  change wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D a x =
    -1 - unselectedContributionSum D c mu (positionsIoc a x) at hEq
  omega

/-- The explicit-order local-reducedness/nonnegativity equivalence. -/
private theorem allLocalReduced_iff_wordMixedMultiplicityFor_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hMeshExactness :
      ∀ a : Fin (OrderedARWord.wordFor sigma H T E).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a))) :
    SortingExchange.AreAllLocalSubwordsReduced
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.wordFor sigma H T E) D ↔
      ∀ a x : Fin (OrderedARWord.wordFor sigma H T E).length,
        0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x := by
  constructor
  · intro hLocal a x
    exact wordMixedMultiplicityFor_nonnegative_of_allLocalReduced
      (K := K) (R := R) sigma H T E D
        hLocal hMeshExactness a x
  · exact allLocalReduced_of_wordMixedMultiplicityFor_nonnegative
      (K := K) (R := R) sigma H T E D

/-- Three-way directed sorting for `OrderedARWord.wordFor`. -/
theorem directedSortingFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (hMeshExactness :
      ∀ a : Fin (OrderedARWord.wordFor sigma H T E).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a))
        (segmentWord (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions D a))) :
    (OpConjecture.RepresentationDirected.FixedWord.IsLeftmostReducedSubwordFor
        (system (OrderedARWord.orbitGraph sigma H T))
        (OrderedARWord.wordFor sigma H T E)
        ((system (OrderedARWord.orbitGraph sigma H T)).wordProd
          (subwordAt (OrderedARWord.wordFor sigma H T E) D)) D ↔
      ∀ a x : Fin (OrderedARWord.wordFor sigma H T E).length,
        0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x) ∧
    ((∀ a x : Fin (OrderedARWord.wordFor sigma H T E).length,
        0 ≤ wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x) ↔
      sigma.qClosure.IsClosed
        {i | i ∉ omittedLabelFinsetFor sigma H T E D}) := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  constructor
  · rw [SortingExchange.leftmostReducedSubwordFor_iff_allLocal_simpleGraph]
    exact allLocalReduced_iff_wordMixedMultiplicityFor_nonnegative
      (K := K) (R := R) sigma H T E D hMeshExactness
  · exact (qClosed_iff_wordMixedMultiplicityFor_nonnegative
      (K := K) (R := R) sigma H T E D).symm

include K in
/-- Full-position directed sorting proves reducedness of every explicitly
ordered AR word. -/
theorem orderedARWordFor_isReduced_of_meshExactness
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (hMeshExactness :
      ∀ a : Fin (OrderedARWord.wordFor sigma H T E).length,
      PositiveRightAdditiveForcesMeshInverseNonnegative
        (segmentGraph (OrderedARWord.orbitGraph sigma H T)
          (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions Finset.univ a))
        (segmentWord (OrderedARWord.wordFor sigma H T E)
          (rowRestrictedOmissions Finset.univ a))) :
    IsReduced (OrderedARWord.orbitGraph sigma H T)
      (OrderedARWord.wordFor sigma H T E) := by
  letI : Finite (ProjectiveLabel sigma) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ProjectiveLabel sigma) := Fintype.ofFinite _
  have hClosed : sigma.qClosure.IsClosed
      {i | i ∉ omittedLabelFinsetFor sigma H T E
        (Finset.univ : Finset
          (Fin (OrderedARWord.wordFor sigma H T E).length))} := by
    simpa [omittedLabelFinsetFor] using
      (IndecomposableSkeleton.qClosure_isClosed_empty sigma)
  have hThree := directedSortingFor (K := K) (R := R)
    sigma H T E
    (Finset.univ : Finset
      (Fin (OrderedARWord.wordFor sigma H T E).length)) hMeshExactness
  have hNonnegative := hThree.2.mpr hClosed
  have hLeftmost := hThree.1.mpr hNonnegative
  change (system (OrderedARWord.orbitGraph sigma H T)).IsReduced
    (OrderedARWord.wordFor sigma H T E)
  simpa [subwordAt_univ] using hLeftmost.1.1

end FirstNegative

end OpConjecture.RepresentationDirected.DirectedSorting
