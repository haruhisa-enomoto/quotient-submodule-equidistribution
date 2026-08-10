import QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordInterface
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Reduced subwords of a fixed Coxeter word

This file develops the finite-candidate, lexicographic-minimum, and
word-reversal API needed by the representation-directed argument.  It does
not assume that the ambient word is reduced and does not depend on a global
Bruhat-order development.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords

open QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWord

universe uB uW

variable {B : Type uB} {W : Type uW}
variable [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

/-- Group elements admitting a reduced expression selected from `ambient`. -/
def FixedWordElement (ambient : List B) :=
  {w : W // ∃ positions : Finset (Fin ambient.length),
    IsReducedSubwordFor cs ambient w positions}

theorem fixedWordElement_set_finite (ambient : List B) :
    {w : W | ∃ positions : Finset (Fin ambient.length),
      IsReducedSubwordFor cs ambient w positions}.Finite := by
  let productAt : Finset (Fin ambient.length) → W :=
    fun positions => cs.wordProd (subwordAt ambient positions)
  apply (Set.finite_range productAt).subset
  intro w hw
  obtain ⟨positions, _hreduced, hprod⟩ := hw
  exact ⟨positions, hprod⟩

noncomputable instance fixedWordElementFintype (ambient : List B) :
    Fintype (FixedWordElement cs ambient) :=
  (fixedWordElement_set_finite cs ambient).fintype

/-- All reduced position witnesses for `w` inside `ambient`. -/
def reducedPositionCandidates
    (ambient : List B) (w : W) :
    Finset (Finset (Fin ambient.length)) := by
  classical
  exact Finset.univ.filter (IsReducedSubwordFor cs ambient w)

@[simp]
theorem mem_reducedPositionCandidates_iff
    (ambient : List B) (w : W)
    (positions : Finset (Fin ambient.length)) :
    positions ∈ reducedPositionCandidates cs ambient w ↔
      IsReducedSubwordFor cs ambient w positions := by
  simp [reducedPositionCandidates]

theorem reducedPositionCandidates_nonempty
    (ambient : List B) (w : FixedWordElement cs ambient) :
    (reducedPositionCandidates cs ambient w.1).Nonempty := by
  obtain ⟨positions, hpositions⟩ := w.property
  exact ⟨positions,
    (mem_reducedPositionCandidates_iff cs ambient w.1 positions).2 hpositions⟩

/-- Every element represented by a reduced subword has a lexicographically
leftmost reduced position witness. -/
theorem exists_leftmostReducedSubwordFor
    (ambient : List B) (w : FixedWordElement cs ambient) :
    ∃ positions : Finset (Fin ambient.length),
      IsLeftmostReducedSubwordFor cs ambient w.1 positions := by
  classical
  obtain ⟨positions, hpositions, hminimal⟩ :=
    Finset.exists_min_image
      (reducedPositionCandidates cs ambient w.1)
      (fun positions => positions.sort (· ≤ ·))
      (reducedPositionCandidates_nonempty cs ambient w)
  refine ⟨positions,
    (mem_reducedPositionCandidates_iff cs ambient w.1 positions).1 hpositions,
    ?_⟩
  intro other hother hlex
  have hle := hminimal other
    ((mem_reducedPositionCandidates_iff cs ambient w.1 other).2 hother)
  have hlt : other.sort (· ≤ ·) < positions.sort (· ≤ ·) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact (not_lt_of_ge hle) hlt

/-- A chosen lexicographically first reduced position set. -/
def lexFirstPositions
    (ambient : List B) (w : FixedWordElement cs ambient) :
    Finset (Fin ambient.length) :=
  (exists_leftmostReducedSubwordFor cs ambient w).choose

theorem lexFirstPositions_spec
    (ambient : List B) (w : FixedWordElement cs ambient) :
    IsLeftmostReducedSubwordFor cs ambient w.1
      (lexFirstPositions cs ambient w) :=
  (exists_leftmostReducedSubwordFor cs ambient w).choose_spec

/-! ## Reversal with a fixed index length -/

/-- Reverse a set of positions in `Fin n`. -/
def reversePositions {n : ℕ} (positions : Finset (Fin n)) :
    Finset (Fin n) :=
  positions.map Fin.revPerm.toEmbedding

@[simp]
theorem mem_reversePositions_iff {n : ℕ}
    (positions : Finset (Fin n)) (i : Fin n) :
    i ∈ reversePositions positions ↔ i.rev ∈ positions := by
  simp [reversePositions]

@[simp]
theorem card_reversePositions {n : ℕ}
    (positions : Finset (Fin n)) :
    (reversePositions positions).card = positions.card := by
  simp [reversePositions]

@[simp]
theorem reversePositions_reversePositions {n : ℕ}
    (positions : Finset (Fin n)) :
    reversePositions (reversePositions positions) = positions := by
  ext i
  simp

/-- Select positions from an `n`-indexed word.  This cast-free variant is the
convenient core for proving reversal identities. -/
def subwordAtFn {n : ℕ}
    (word : Fin n → B) (positions : Finset (Fin n)) : List B :=
  (positions.sort (· ≤ ·)).map word

/-- Reversing both an indexed word and its selected positions reverses the
selected subword. -/
theorem subwordAtFn_reverse {n : ℕ}
    (word : Fin n → B) (positions : Finset (Fin n)) :
    subwordAtFn (word ∘ Fin.rev) (reversePositions positions) =
      (subwordAtFn word positions).reverse := by
  have hdescending :
      ((positions.sort (· ≤ ·)).map Fin.rev).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_map]
    exact positions.sortedLT_sort.pairwise.imp
      fun hij => Fin.rev_lt_rev.mpr hij
  have hmembership :
      ∀ i : Fin n,
        i ∈ (positions.sort (· ≤ ·)).map Fin.rev ↔
          i ∈ (reversePositions positions).sort (· ≤ ·) := by
    intro i
    simp only [List.mem_map, Finset.mem_sort,
      mem_reversePositions_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hi
      exact ⟨i.rev, hi, Fin.rev_rev i⟩
  have hmapped :
      (positions.sort (· ≤ ·)).map Fin.rev =
        ((reversePositions positions).sort (· ≤ ·)).reverse :=
    hdescending.eq_reverse_of_mem_iff_of_sortedLT
      hmembership (reversePositions positions).sortedLT_sort
  have hsorted :
      (reversePositions positions).sort (· ≤ ·) =
        ((positions.sort (· ≤ ·)).map Fin.rev).reverse := by
    simpa using congrArg List.reverse hmapped.symm
  simp [subwordAtFn, hsorted, List.map_reverse, Function.comp_def]

@[simp]
theorem subwordAtFn_get
    (word : List B) (positions : Finset (Fin word.length)) :
    subwordAtFn word.get positions = subwordAt word positions :=
  rfl

/-! ## Reversal for the repository's list-indexed `subwordAt` -/

/-- The order-reversing equivalence from positions of `word` to positions of
`word.reverse`.  The final cast only transports across `length_reverse`. -/
def reverseIndexEquiv (word : List B) :
    Fin word.length ≃ Fin word.reverse.length :=
  Fin.revPerm.trans
    (Fin.castOrderIso (by simp)).toEquiv

@[simp]
theorem reverseIndexEquiv_apply_val
    (word : List B) (i : Fin word.length) :
    (reverseIndexEquiv word i).val = i.rev.val := by
  rfl

theorem reverseIndexEquiv_strictAnti
    (word : List B) :
    StrictAnti (reverseIndexEquiv word) := by
  intro i j hij
  simpa [reverseIndexEquiv] using Fin.rev_lt_rev.mpr hij

@[simp]
theorem get_reverse_reverseIndexEquiv
    (word : List B) (i : Fin word.length) :
    word.reverse.get (reverseIndexEquiv word i) = word.get i := by
  change word.reverse[(reverseIndexEquiv word i).val] = word[i.val]
  rw [List.getElem_reverse]
  congr
  simp [reverseIndexEquiv, Fin.rev]
  omega

/-- Reverse selected positions while changing from `word` to `word.reverse`. -/
def reversePositionsIn
    (word : List B) (positions : Finset (Fin word.length)) :
    Finset (Fin word.reverse.length) :=
  positions.map (reverseIndexEquiv word).toEmbedding

@[simp]
theorem card_reversePositionsIn
    (word : List B) (positions : Finset (Fin word.length)) :
    (reversePositionsIn word positions).card = positions.card := by
  simp [reversePositionsIn]

/-- Literal list form: selecting the reversed positions from the reversed
ambient word gives the reverse selected subword. -/
theorem subwordAt_reverse
    (word : List B) (positions : Finset (Fin word.length)) :
    subwordAt word.reverse (reversePositionsIn word positions) =
      (subwordAt word positions).reverse := by
  have hdescending :
      ((positions.sort (· ≤ ·)).map
        (reverseIndexEquiv word)).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_map]
    exact positions.sortedLT_sort.pairwise.imp
      fun hij => reverseIndexEquiv_strictAnti word hij
  have hmembership :
      ∀ i : Fin word.reverse.length,
        i ∈ (positions.sort (· ≤ ·)).map
            (reverseIndexEquiv word) ↔
          i ∈ (reversePositionsIn word positions).sort (· ≤ ·) := by
    intro i
    simp only [List.mem_map, Finset.mem_sort,
      reversePositionsIn, Finset.mem_map, Equiv.coe_toEmbedding]
  have hmapped :
      (positions.sort (· ≤ ·)).map (reverseIndexEquiv word) =
        ((reversePositionsIn word positions).sort (· ≤ ·)).reverse :=
    hdescending.eq_reverse_of_mem_iff_of_sortedLT
      hmembership (reversePositionsIn word positions).sortedLT_sort
  have hsorted :
      (reversePositionsIn word positions).sort (· ≤ ·) =
        ((positions.sort (· ≤ ·)).map
          (reverseIndexEquiv word)).reverse := by
    simpa using congrArg List.reverse hmapped.symm
  have hget :
      word.reverse.get ∘ reverseIndexEquiv word = word.get := by
    funext i
    exact get_reverse_reverseIndexEquiv word i
  simp only [subwordAt, hsorted, List.map_reverse, List.map_map]
  rw [hget]

/-- Reversal transports a reduced subword witness for `w` to one for
`w⁻¹` in the reversed ambient word. -/
@[simp]
theorem isReducedSubwordFor_reverse_iff
    (word : List B) (w : W)
    (positions : Finset (Fin word.length)) :
    IsReducedSubwordFor cs word.reverse w⁻¹
        (reversePositionsIn word positions) ↔
      IsReducedSubwordFor cs word w positions := by
  simp [IsReducedSubwordFor, subwordAt_reverse]

end QuotientSubmoduleEquidistribution.RepresentationDirected.FixedWordSubwords
