import OpConjecture.RepresentationDirected.ARWordSelectedSegments
import OpConjecture.RepresentationDirected.ARWordSegmentSeparation
import OpConjecture.RepresentationDirected.CoxeterSeparatedEdgeReducedness

/-!
# Segment-word reducedness assembly

Integration of selected segments with the abstract Coxeter
comparison/deletion infrastructure.  The two remaining hypotheses
are deliberately visible: separatedness of each extra pullback edge, and the
one-edge reducedness theorem.
-/

noncomputable section

namespace OpConjecture.RepresentationDirected.SegmentReducedness

open OpConjecture.RepresentationDirected.SimpleGraphCoxeter
open OpConjecture.RepresentationDirected.ARWord.SelectedSegments
open OpConjecture.RepresentationDirected.RootSignStrategy

universe u

variable {L : Type u}

/-- The segment word is reduced in the manuscript's auxiliary graph
`hatDelta_C` as soon as its projected selected subword is reduced in the
original graph. -/
theorem segmentWord_isReduced_pullback
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hReduced : IsReduced G (selectedWord Q C)) :
    IsReduced (pullbackGraph G
      (projectLabel : SegmentLabel Q C → L)) (segmentWord Q C) := by
  apply isReduced_pullback_of_map_isReduced
  simpa only [map_projectLabel_segmentWord] using hReduced

/-- The natural segment graph is a spanning subgraph of the auxiliary
pullback graph. -/
theorem segmentGraph_le_pullback
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length)) :
    segmentGraph G Q C ≤
      pullbackGraph G (projectLabel : SegmentLabel Q C → L) := by
  intro A B hAB
  exact segmentGraph_adj_projectLabel hAB

/-- Exact conditional assembly of `prop:directed-segment-reduced`.

The first extra hypothesis is the representation-theoretic interval claim
from the two-orbit theorem: every auxiliary edge absent from the actual
segment graph has its endpoint segments separated in the segment word.  The
second is `lem:directed-delete-separated-edge`.  All remaining finite graph
and Coxeter bookkeeping is discharged here. -/
theorem segmentWord_isReduced_of_extraSeparated_of_oneEdge
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hProjectedReduced : IsReduced G (selectedWord Q C))
    (hExtraSeparated : ∀ A B : SegmentLabel Q C,
      (pullbackGraph G
        (projectLabel : SegmentLabel Q C → L)).Adj A B →
      ¬ (segmentGraph G Q C).Adj A B →
      AllOccurrencesBefore (segmentWord Q C) A B ∨
        AllOccurrencesBefore (segmentWord Q C) B A)
    (oneEdge : ∀ (K : SimpleGraph (SegmentLabel Q C))
      (A B : SegmentLabel Q C),
      K.Adj A B →
      (AllOccurrencesBefore (segmentWord Q C) A B ∨
        AllOccurrencesBefore (segmentWord Q C) B A) →
      IsReduced K (segmentWord Q C) →
      IsReduced (deleteEdge K A B) (segmentWord Q C)) :
    IsReduced (segmentGraph G Q C) (segmentWord Q C) := by
  apply isReduced_subgraph_of_all_extra_edges_separated
    (segmentWord Q C)
    (segmentGraph_le_pullback G Q C)
    hExtraSeparated oneEdge
  exact segmentWord_isReduced_pullback G Q C hProjectedReduced

/-- The exact selected-segment reducedness assembly after discharging the
extra-edge separation step from the boundary-run hypothesis.  The only
remaining input is the abstract one-edge separated-deletion theorem for the
intermediate graphs. -/
theorem segmentWord_isReduced_of_oneEdge
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (hProjectedReduced : IsReduced G (selectedWord Q C))
    (oneEdge : ∀ (K : SimpleGraph (SegmentLabel Q C))
      (A B : SegmentLabel Q C),
      K.Adj A B →
      (AllOccurrencesBefore (segmentWord Q C) A B ∨
        AllOccurrencesBefore (segmentWord Q C) B A) →
      IsReduced K (segmentWord Q C) →
      IsReduced (deleteEdge K A B) (segmentWord Q C)) :
    IsReduced (segmentGraph G Q C) (segmentWord Q C) := by
  apply segmentWord_isReduced_of_extraSeparated_of_oneEdge
    G Q C hProjectedReduced
  · intro A B hPull hNot
    exact allOccurrencesBefore_or_reverse_of_projected_adj_of_not_segmentGraph_adj
      hRuns A B ((pullbackGraph_adj G projectLabel A B).mp hPull) hNot
  · exact oneEdge

/-- The manuscript's selected-segment reducedness proposition reduced to the
single uniform Tits input that reduced words have positive inversion roots
for every graph on the finite segment-label type.  All segment, pullback,
separation, and finite edge-deletion bookkeeping is unconditional. -/
theorem segmentWord_isReduced_of_reducedWordsPositive
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (hProjectedReduced : IsReduced G (selectedWord Q C))
    (hRootPositive : ∀ K : SimpleGraph (SegmentLabel Q C),
      ReducedWordsHavePositiveInversionRoots K) :
    IsReduced (segmentGraph G Q C) (segmentWord Q C) := by
  apply segmentWord_isReduced_of_oneEdge G Q C hRuns hProjectedReduced
  intro K A B hAB hSeparated hReduced
  exact isReduced_deleteEdge_of_separated_of_reducedWordsPositive
    K (segmentWord Q C) A B hAB hSeparated
      (hRootPositive K) (hRootPositive (deleteEdge K A B)) hReduced

/-- Final unconditional form of `prop:directed-segment-reduced`: a reduced
selected subword, together with the boundary-run property of the ambient
word, gives a reduced word on its maximal selected segments. -/
theorem segmentWord_isReduced
    (G : SimpleGraph L) (Q : List L) (C : Finset (Fin Q.length))
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    (hProjectedReduced : IsReduced G (selectedWord Q C)) :
    IsReduced (segmentGraph G Q C) (segmentWord Q C) := by
  apply segmentWord_isReduced_of_reducedWordsPositive
    G Q C hRuns hProjectedReduced
  intro K
  exact reducedWordsHavePositiveInversionRoots K

end OpConjecture.RepresentationDirected.SegmentReducedness
