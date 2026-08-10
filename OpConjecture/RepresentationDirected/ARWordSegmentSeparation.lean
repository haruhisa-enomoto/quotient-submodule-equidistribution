import OpConjecture.RepresentationDirected.ARWordSelectedSegments
import OpConjecture.RepresentationDirected.CoxeterEdgeDeletion

/-!
# Extra pullback edges have separated segment occurrences

Abstract interval claim needed by selected-segment reducedness.  No algebra,
quiver, or module classification enters this file.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.ARWord.SelectedSegments

open OpConjecture.RepresentationDirected.SegmentReducedness

universe u

variable {L : Type u}

/-- If a selected occurrence of `B` is bracketed by two occurrences of the
same selected segment `A`, and the projected labels are adjacent, then the
natural segment graph contains the edge `A-B`.

The least `A`-position after the bracketed `B`-position has a predecessor
before `B`.  After transport to the original word, interior alternation says
that `B` is the unique occurrence of its projected label in this predecessor
window, hence is an original middle position. -/
theorem segmentGraph_adj_of_bracket
    {G : SimpleGraph L} {Q : List L} {C : Finset (Fin Q.length)}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    {A B : SegmentLabel Q C}
    (hAB : G.Adj (projectLabel A) (projectLabel B))
    {x z y : Fin (segmentWord Q C).length}
    (hxA : ARWord.label (segmentWord Q C) x = A)
    (hzB : ARWord.label (segmentWord Q C) z = B)
    (hyA : ARWord.label (segmentWord Q C) y = A)
    (hxz : x < z) (hzy : z < y) :
    (segmentGraph G Q C).Adj A B := by
  classical
  let T : Finset (Fin (segmentWord Q C).length) :=
    Finset.univ.filter fun q ↦
      z < q ∧ ARWord.label (segmentWord Q C) q = A
  have hT : T.Nonempty := by
    refine ⟨y, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hzy, hyA⟩
  let q := T.min' hT
  have hqData :
      z < q ∧ ARWord.label (segmentWord Q C) q = A := by
    have hqMem := Finset.min'_mem T hT
    simpa only [q, T, Finset.mem_filter, Finset.mem_univ, true_and] using hqMem
  have hxq : x < q := hxz.trans hqData.1
  obtain ⟨p, hpq⟩ :=
    (ARWord.exists_isPrevious_iff_exists_lt_label_eq).2
      ⟨x, hxq, hxA.trans hqData.2.symm⟩
  have hpLabel : ARWord.label (segmentWord Q C) p = A :=
    hpq.2.1.trans hqData.2
  have hAneB : A ≠ B := by
    intro hEq
    exact hAB.ne (congrArg projectLabel hEq)
  have hpz : p < z := by
    rcases lt_trichotomy p z with hpz | hpz | hzp
    · exact hpz
    · subst p
      exact False.elim (hAneB (hpLabel.symm.trans hzB))
    · have hqLeP : q ≤ p := by
        apply Finset.min'_le T p
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hzp, hpLabel⟩
      exact False.elim ((not_lt_of_ge hqLeP) hpq.1)
  let op := positionInOriginal Q C p
  let oz := positionInOriginal Q C z
  let oq := positionInOriginal Q C q
  have hPrevOrig : ARWord.IsPrevious Q op oq := by
    exact (isPrevious_segmentWord_iff C p q).1 hpq
  have hOpOz : op < oz := by
    exact (positionInOriginal_lt_iff Q C p z).2 hpz
  have hOzOq : oz < oq := by
    exact (positionInOriginal_lt_iff Q C z q).2 hqData.1
  have hzOrig : ARWord.label Q oz = projectLabel B := by
    dsimp only [oz]
    rw [← projectLabel_label_segmentWord Q C z, hzB]
  have hqOrig : ARWord.label Q oq = projectLabel A := by
    dsimp only [oq]
    rw [← projectLabel_label_segmentWord Q C q, hqData.2]
  have hMiddleAdj : G.Adj (ARWord.label Q oz) (ARWord.label Q oq) := by
    rw [hzOrig, hqOrig]
    exact hAB.symm
  have hPrevAdj : G.Adj (ARWord.label Q op) (ARWord.label Q oz) := by
    rw [hPrevOrig.2.1]
    exact hMiddleAdj.symm
  have hMiddle : ARWord.IsMiddle G Q oz oq := by
    refine ⟨hMiddleAdj, hOzOq, ?_, ?_⟩
    · intro r hr
      rw [ARWord.isPrevious_unique hr hPrevOrig]
      exact hOpOz
    · intro t hOzT hTOq htLabel
      have htEq : t = oz :=
        hRuns.hasInteriorAlternation hPrevOrig hPrevAdj
          hOpOz hOzOq (hOpOz.trans hOzT) hTOq htLabel
      exact hOzT.ne htEq.symm
  exact ⟨q, z, hqData.2, hzB, Or.inr hMiddle⟩

/-- Failure of a universal occurrence order for two distinct labels produces
an occurrence of the second label strictly before one of the first. -/
theorem exists_reverse_occurrences_of_not_allOccurrencesBefore
    {Q : List L} {a b : L} (hab : a ≠ b)
    (h : ¬ AllOccurrencesBefore Q a b) :
    ∃ x y : Fin Q.length,
      ARWord.label Q x = a ∧ ARWord.label Q y = b ∧ y < x := by
  simp only [AllOccurrencesBefore] at h
  push Not at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨x, y, hx, hy, ?_⟩
  have hne : x ≠ y := by
    intro hEq
    subst y
    exact hab (hx.symm.trans hy)
  exact lt_of_le_of_ne hxy hne.symm

/-- Every pullback edge omitted by the natural selected-segment graph has
separated endpoint occurrences in the segment word. -/
theorem allOccurrencesBefore_or_reverse_of_projected_adj_of_not_segmentGraph_adj
    {G : SimpleGraph L} {Q : List L} {C : Finset (Fin Q.length)}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (A B : SegmentLabel Q C)
    (hAB : G.Adj (projectLabel A) (projectLabel B))
    (hNotAdj : ¬ (segmentGraph G Q C).Adj A B) :
    AllOccurrencesBefore (segmentWord Q C) A B ∨
      AllOccurrencesBefore (segmentWord Q C) B A := by
  classical
  by_contra hSeparated
  have hFailures := not_or.mp hSeparated
  have hAneB : A ≠ B := by
    intro hEq
    exact hAB.ne (congrArg projectLabel hEq)
  obtain ⟨aRight, bLeft, haRight, hbLeft, hBLeftARight⟩ :=
    exists_reverse_occurrences_of_not_allOccurrencesBefore hAneB hFailures.1
  obtain ⟨bRight, aLeft, hbRight, haLeft, hALeftBRight⟩ :=
    exists_reverse_occurrences_of_not_allOccurrencesBefore hAneB.symm hFailures.2
  rcases lt_trichotomy aLeft bLeft with hALeftBLeft | hEq | hBLeftALeft
  · apply hNotAdj
    exact segmentGraph_adj_of_bracket hRuns hAB
      haLeft hbLeft haRight hALeftBLeft hBLeftARight
  · subst bLeft
    exact False.elim (hAneB (haLeft.symm.trans hbLeft))
  · apply hNotAdj
    have hBA : (segmentGraph G Q C).Adj B A :=
      segmentGraph_adj_of_bracket hRuns hAB.symm
        hbLeft haLeft hbRight hBLeftALeft hALeftBRight
    exact ((segmentGraph G Q C).adj_comm A B).mpr hBA

end OpConjecture.RepresentationDirected.ARWord.SelectedSegments
