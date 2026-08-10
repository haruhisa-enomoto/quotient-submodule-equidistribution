import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphTits
import QuotientSubmoduleEquidistribution.RepresentationDirected.CoxeterEdgeDeletion

/-!
# Conditional separated-edge deletion

This file completes the coordinate argument of
`lem:directed-delete-separated-edge`.  The only exposed hypotheses are the
two standard geometric-representation inputs absent from pinned Mathlib:
reduced words have positive inversion roots (and conversely in the deleted
graph), and deleted-graph real roots are sign-coherent.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.SegmentReducedness

open QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphCoxeter
open QuotientSubmoduleEquidistribution.RepresentationDirected.WordRootProcess
open QuotientSubmoduleEquidistribution.RepresentationDirected.RootSignStrategy

universe u

variable {L : Type u} [Fintype L]

theorem inversionRoot_eq_actWord
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    inversionRoot G Q x =
      actWord G (Q.take x) (simpleRoot Q[x]) :=
  rfl

/-- Direct orientation of the separated-edge lemma. -/
theorem isReduced_deleteEdge_of_allOccurrencesBefore
    (G : SimpleGraph L) (Q : List L) (a b : L)
    (_hab : G.Adj a b)
    (hBefore : AllOccurrencesBefore Q a b)
    (hReducedToPositive : ∀ R : List L,
      IsReduced G R → HasPositiveInversionRoots G R)
    (hPositiveToReduced : ∀ R : List L,
      HasPositiveInversionRoots (deleteEdge G a b) R →
        IsReduced (deleteEdge G a b) R)
    (hSignCoherent : ∀ (R : List L) (x : Fin R.length),
      IsNonnegative (inversionRoot (deleteEdge G a b) R x) ∨
        IsNonpositive (inversionRoot (deleteEdge G a b) R x))
    (hReduced : IsReduced G Q) :
    IsReduced (deleteEdge G a b) Q := by
  obtain ⟨u, v, hQ, hbU, haV⟩ :=
    exists_append_not_mem_of_allOccurrencesBefore hBefore
  subst Q
  have hPositiveQ : HasPositiveInversionRoots G (u ++ v) :=
    hReducedToPositive (u ++ v) hReduced
  have hReducedV : IsReduced G v := by
    have hDrop := hReduced.drop u.length
    simpa only [SimpleGraphCoxeter.IsReduced, List.drop_left] using hDrop
  have hPositiveV : HasPositiveInversionRoots G v :=
    hReducedToPositive v hReducedV
  apply hPositiveToReduced (u ++ v)
  intro x
  by_cases hxU : x.val < u.length
  · have hTake : (u ++ v).take x.val = u.take x.val :=
      List.take_append_of_le_length hxU.le
    let xu : Fin u.length := ⟨x.val, hxU⟩
    have hLabel : (u ++ v).get x = u.get xu := by
      exact List.getElem_append_left hxU
    have hbTake : b ∉ u.take x.val := by
      intro hb
      apply hbU
      exact List.mem_of_mem_take hb
    have hbLabel : b ≠ (u ++ v).get x := by
      intro h
      apply hbU
      rw [hLabel] at h
      rw [h]
      exact List.get_mem u xu
    have hRootEq :
        inversionRoot (deleteEdge G a b) (u ++ v) x =
          inversionRoot G (u ++ v) x := by
      rw [inversionRoot_eq_actWord, inversionRoot_eq_actWord, hTake]
      apply actWord_deleteEdge_eq_of_not_mem_of_coord_eq_zero
        G a b (u.take x.val) (simpleRoot ((u ++ v).get x)) hbTake
      exact simpleRoot_apply_of_ne hbLabel
    rw [hRootEq]
    exact hPositiveQ x
  · have hxGe : u.length ≤ x.val := Nat.le_of_not_gt hxU
    let k : ℕ := x.val - u.length
    have hkV : k < v.length := by
      have hxLen := x.isLt
      simp only [List.length_append] at hxLen
      dsimp only [k]
      omega
    let xv : Fin v.length := ⟨k, hkV⟩
    let j : L := v[xv]
    have hLabel : (u ++ v)[x] = j := by
      change (u ++ v)[x.val] = v[k]
      exact List.getElem_append_right hxGe
    have hTake : (u ++ v).take x.val = u ++ v.take k := by
      rw [List.take_append]
      rw [List.take_of_length_le hxGe]
    have haTake : a ∉ v.take k := by
      intro ha
      apply haV
      exact List.mem_of_mem_take ha
    have haLabel : a ≠ j := by
      intro h
      apply haV
      rw [h]
      exact List.getElem_mem hkV
    let gamma : RootLattice L :=
      actWord G (v.take k) (simpleRoot j)
    have hGammaPositive : IsPositive gamma := by
      have h := hPositiveV xv
      rw [inversionRoot_eq_actWord] at h
      change IsPositive gamma at h
      exact h
    have hSplit := actWord_deleteEdge_split
      G a b u (v.take k) (simpleRoot j)
      hbU haTake (simpleRoot_apply_of_ne haLabel)
    have hDeletedRoot :
        inversionRoot (deleteEdge G a b) (u ++ v) x =
          actWord (deleteEdge G a b) (u ++ v.take k)
            (simpleRoot j) := by
      rw [inversionRoot_eq_actWord, hTake, hLabel]
    have hOriginalRoot :
        inversionRoot G (u ++ v) x =
          actWord G (u ++ v.take k) (simpleRoot j) := by
      rw [inversionRoot_eq_actWord, hTake, hLabel]
    by_cases hGammaB : gamma b = 0
    · have hEq :
          inversionRoot (deleteEdge G a b) (u ++ v) x =
            inversionRoot G (u ++ v) x := by
        rw [hDeletedRoot, hOriginalRoot]
        exact hSplit.2.1 hGammaB
      rw [hEq]
      exact hPositiveQ x
    · have hGammaBPos : 0 < gamma b :=
        lt_of_le_of_ne (hGammaPositive.1 b) (Ne.symm hGammaB)
      have hDeletedB :
          inversionRoot (deleteEdge G a b) (u ++ v) x b = gamma b := by
        rw [hDeletedRoot]
        exact hSplit.2.2
      rcases hSignCoherent (u ++ v) x with hNonnegative | hNonpositive
      · refine ⟨hNonnegative, ?_⟩
        intro hZero
        apply hGammaB
        rw [← hDeletedB]
        simpa using congrFun hZero b
      · exact False.elim (by
          have hle := hNonpositive b
          rw [hDeletedB] at hle
          exact (not_lt_of_ge hle) hGammaBPos)

/-- Symmetric form matching the manuscript: either ordering of the two
endpoint labels is accepted. -/
theorem isReduced_deleteEdge_of_separated
    (G : SimpleGraph L) (Q : List L) (a b : L)
    (hab : G.Adj a b)
    (hSeparated : AllOccurrencesBefore Q a b ∨
      AllOccurrencesBefore Q b a)
    (hReducedToPositive : ∀ R : List L,
      IsReduced G R → HasPositiveInversionRoots G R)
    (hPositiveToReduced : ∀ R : List L,
      HasPositiveInversionRoots (deleteEdge G a b) R →
        IsReduced (deleteEdge G a b) R)
    (hSignCoherent : ∀ (R : List L) (x : Fin R.length),
      IsNonnegative (inversionRoot (deleteEdge G a b) R x) ∨
        IsNonpositive (inversionRoot (deleteEdge G a b) R x))
    (hReduced : IsReduced G Q) :
    IsReduced (deleteEdge G a b) Q := by
  rcases hSeparated with hBefore | hBefore
  · exact isReduced_deleteEdge_of_allOccurrencesBefore G Q a b hab
      hBefore hReducedToPositive hPositiveToReduced hSignCoherent hReduced
  · have h := isReduced_deleteEdge_of_allOccurrencesBefore
      G Q b a hab.symm hBefore hReducedToPositive
      (fun R hR ↦ by
        rw [← deleteEdge_comm G a b]
        apply hPositiveToReduced R
        simpa only [deleteEdge_comm G a b] using hR)
      (fun R x ↦ by
        simpa only [deleteEdge_comm G a b] using hSignCoherent R x)
      hReduced
    simpa only [deleteEdge_comm G a b] using h

/-- The separated-edge theorem reduced to the smallest outstanding Tits
input: positivity of inversion roots for reduced words, once for the original
graph and once for the graph with the edge deleted.  The latter instance also
supplies the converse reducedness criterion and real-root sign coherence via
`SimpleGraphRootSignReduction`. -/
theorem isReduced_deleteEdge_of_separated_of_reducedWordsPositive
    (G : SimpleGraph L) (Q : List L) (a b : L)
    (hab : G.Adj a b)
    (hSeparated : AllOccurrencesBefore Q a b ∨
      AllOccurrencesBefore Q b a)
    (hPositiveG : ReducedWordsHavePositiveInversionRoots G)
    (hPositiveDeleted :
      ReducedWordsHavePositiveInversionRoots (deleteEdge G a b))
    (hReduced : IsReduced G Q) :
    IsReduced (deleteEdge G a b) Q := by
  apply isReduced_deleteEdge_of_separated G Q a b hab hSeparated
    hPositiveG
  · intro R hRoots
    exact
      (isReduced_iff_hasPositiveInversionRoots_of_rightDescentNegativity
        (deleteEdge G a b) R
        (rightDescentImpliesNegativeRoot_of_reducedWordsPositive
          (deleteEdge G a b) hPositiveDeleted)).2 hRoots
  · intro R x
    rcases
        hasRealRootSignDichotomy_of_reducedWordsPositive
          (deleteEdge G a b) hPositiveDeleted
          (prefixElement (deleteEdge G a b) R x) R[x] with hpos | hneg
    · exact Or.inl hpos.1
    · exact Or.inr hneg.1
  · exact hReduced

/-- Final unconditional form of the manuscript's separated-edge deletion
lemma.  The Tits root-sign theorem is now supplied for both the original and
edge-deleted graphs. -/
theorem isReduced_deleteEdge_of_separated_unconditional
    (G : SimpleGraph L) (Q : List L) (a b : L)
    (hab : G.Adj a b)
    (hSeparated : AllOccurrencesBefore Q a b ∨
      AllOccurrencesBefore Q b a)
    (hReduced : IsReduced G Q) :
    IsReduced (deleteEdge G a b) Q :=
  isReduced_deleteEdge_of_separated_of_reducedWordsPositive
    G Q a b hab hSeparated
      (reducedWordsHavePositiveInversionRoots G)
      (reducedWordsHavePositiveInversionRoots (deleteEdge G a b))
      hReduced

end QuotientSubmoduleEquidistribution.RepresentationDirected.SegmentReducedness
