import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordCombinatorics
import QuotientSubmoduleEquidistribution.RepresentationDirected.SimpleGraphWordRoots
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-!
# Root-mesh identities for graph words

The word-root telescoping identities in `eq:directed-root-mesh`.  This file
deliberately depends only on the graph
geometric action and finite-word combinatorics, not on reducedness or root
signs.
-/

noncomputable section

open scoped BigOperators

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.WordRootProcess

open SimpleGraphCoxeter

universe u

variable {L : Type u} [Fintype L]

/-- The fixed simple root `alpha_i`, transported by the first `n` letters. -/
def transportedSimpleRoot (G : SimpleGraph L) (Q : List L) (i : L)
    (n : ℕ) : RootLattice L :=
  geometricRepresentation G (prefixElement G Q n) (simpleRoot i)

/-- The contribution made at position `n` when its label is adjacent to `i`.
It is defined as zero outside the word so that interval sums have a
nondependent summand. -/
def adjacentContribution (G : SimpleGraph L) (Q : List L) (i : L)
    (n : ℕ) : RootLattice L := by
  classical
  exact if hn : n < Q.length then
    if G.Adj (Q.get ⟨n, hn⟩) i then
      inversionRoot G Q ⟨n, hn⟩
    else 0
  else 0

@[simp]
theorem transportedSimpleRoot_zero (G : SimpleGraph L) (Q : List L) (i : L) :
    transportedSimpleRoot G Q i 0 = simpleRoot i := by
  simp [transportedSimpleRoot]

theorem adjacentContribution_of_adj
    (G : SimpleGraph L) (Q : List L) (i : L)
    {n : ℕ} (hn : n < Q.length) (hadj : G.Adj (Q.get ⟨n, hn⟩) i) :
    adjacentContribution G Q i n = inversionRoot G Q ⟨n, hn⟩ := by
  classical
  unfold adjacentContribution
  split
  · rename_i hn'
    have heq : (⟨n, hn'⟩ : Fin Q.length) = ⟨n, hn⟩ := Fin.ext rfl
    simp [heq]
  · rename_i hn'
    exact False.elim (hn' hn)

theorem adjacentContribution_of_not_adj
    (G : SimpleGraph L) (Q : List L) (i : L)
    {n : ℕ} (hn : n < Q.length) (hadj : ¬ G.Adj (Q.get ⟨n, hn⟩) i) :
    adjacentContribution G Q i n = 0 := by
  classical
  unfold adjacentContribution
  split
  · rename_i hn'
    rfl
  · rfl

/-- Away from occurrences of `i`, one prefix step either fixes the transported
root or adds the inversion root at that step, according to adjacency. -/
theorem transportedSimpleRoot_succ_of_ne
    (G : SimpleGraph L) (Q : List L) (i : L)
    {n : ℕ} (hn : n < Q.length)
    (hne : Q.get ⟨n, hn⟩ ≠ i) :
    transportedSimpleRoot G Q i (n + 1) =
      transportedSimpleRoot G Q i n + adjacentContribution G Q i n := by
  classical
  rw [transportedSimpleRoot, geometricRepresentation_prefix_succ G Q hn]
  change
    geometricRepresentation G (prefixElement G Q n)
        (simpleReflection G (Q.get ⟨n, hn⟩) (simpleRoot i)) =
      transportedSimpleRoot G Q i n + adjacentContribution G Q i n
  by_cases hadj : G.Adj (Q.get ⟨n, hn⟩) i
  · rw [adjacentContribution_of_adj G Q i hn hadj,
      simpleReflection_simpleRoot_of_adj G hadj]
    simp [map_add, transportedSimpleRoot, inversionRoot]
  · rw [adjacentContribution_of_not_adj G Q i hn hadj,
      simpleReflection_simpleRoot_of_ne_of_not_adj G hne hadj]
    simp [transportedSimpleRoot]

/-- Telescoping over a half-open interval on which the label `i` does not
occur. -/
theorem transportedSimpleRoot_eq_add_sum_Ico
    (G : SimpleGraph L) (Q : List L) (i : L)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Q.length)
    (hne : ∀ n, (hn : n < Q.length) → a ≤ n → n < b →
      Q.get ⟨n, hn⟩ ≠ i) :
    transportedSimpleRoot G Q i b =
      transportedSimpleRoot G Q i a +
        ∑ n ∈ Finset.Ico a b, adjacentContribution G Q i n := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hbLt : b < Q.length := by omega
      have hstep := transportedSimpleRoot_succ_of_ne G Q i hbLt
        (hne b hbLt hab (Nat.lt_succ_self b))
      rw [hstep, ih (by omega)
        (fun n hn han hnb => hne n hn han (by omega))]
      rw [Finset.sum_Ico_succ_top hab]
      simp only [add_assoc]

/-- Transporting through an occurrence of `i` negates the inversion root at
that occurrence. -/
theorem transportedSimpleRoot_succ_of_label_eq
    (G : SimpleGraph L) (Q : List L) (i : L)
    {n : ℕ} (hn : n < Q.length)
    (heq : Q.get ⟨n, hn⟩ = i) :
    transportedSimpleRoot G Q i (n + 1) =
      -inversionRoot G Q ⟨n, hn⟩ := by
  rw [transportedSimpleRoot, geometricRepresentation_prefix_succ G Q hn]
  change
    geometricRepresentation G (prefixElement G Q n)
        (simpleReflection G (Q.get ⟨n, hn⟩) (simpleRoot i)) =
      -inversionRoot G Q ⟨n, hn⟩
  subst i
  rw [simpleReflection_simpleRoot_self]
  simp [inversionRoot]

omit [Fintype L] in
/-- At a repeated position, the middle positions are exactly the adjacent
positions strictly between it and its predecessor.  The only combinatorial
input is the local interior-alternation consequence of the boundary-run
hypothesis. -/
theorem isMiddle_iff_between_previous_and_endpoint
    {G : SimpleGraph L} {Q : List L}
    (hAlt : ARWord.HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x)
    (y : Fin Q.length) :
    ARWord.IsMiddle G Q y x ↔
      p < y ∧ y < x ∧ G.Adj (ARWord.label Q y) (ARWord.label Q x) := by
  constructor
  · intro hy
    exact ⟨hy.2.2.1 p hpx, hy.2.1, hy.1⟩
  · rintro ⟨hpy, hyx, hadj⟩
    have hpAdj : G.Adj (ARWord.label Q p) (ARWord.label Q y) := by
      rw [hpx.2.1]
      exact hadj.symm
    refine ⟨hadj, hyx, ?_, ?_⟩
    · intro q hqx
      rw [ARWord.isPrevious_unique hqx hpx]
      exact hpy
    · intro z hyz hzx hzLabel
      have heq := hAlt hpx hpAdj hpy hyx (hpy.trans hyz) hzx hzLabel
      exact hyz.ne heq.symm

/-- The literal contribution of a middle position, zero elsewhere. -/
def middleContribution (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) (n : ℕ) : RootLattice L := by
  classical
  exact if hn : n < Q.length then
    if ARWord.IsMiddle G Q ⟨n, hn⟩ x then
      inversionRoot G Q ⟨n, hn⟩
    else 0
  else 0

/-- The sum over the literal middle positions of `x`, expressed over natural
position indices to interface with interval telescoping. -/
def middleRootSum (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) : RootLattice L :=
  ∑ n ∈ Finset.range Q.length, middleContribution G Q x n

/-- The natural-index implementation is definitionally the finite sum over
the literal subtype of `IsMiddle` positions. -/
def filteredMiddleRootSum
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) : RootLattice L := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y : Fin Q.length ↦
    ARWord.IsMiddle G Q y x), inversionRoot G Q y

theorem middleRootSum_eq_sum_filter
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    middleRootSum G Q x = filteredMiddleRootSum G Q x := by
  classical
  unfold filteredMiddleRootSum
  rw [Finset.sum_filter]
  unfold middleRootSum
  calc
    (∑ n ∈ Finset.range Q.length, middleContribution G Q x n) =
        ∑ y : Fin Q.length, middleContribution G Q x y.val :=
      (Fin.sum_univ_eq_sum_range
        (fun n ↦ middleContribution G Q x n) Q.length).symm
    _ = ∑ y : Fin Q.length,
        if ARWord.IsMiddle G Q y x then inversionRoot G Q y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp [middleContribution, y.isLt]

theorem middleContribution_of_isMiddle
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length)
    {n : ℕ} (hn : n < Q.length)
    (hmiddle : ARWord.IsMiddle G Q ⟨n, hn⟩ x) :
    middleContribution G Q x n = inversionRoot G Q ⟨n, hn⟩ := by
  classical
  unfold middleContribution
  split
  · rename_i hn'
    have heq : (⟨n, hn'⟩ : Fin Q.length) = ⟨n, hn⟩ := Fin.ext rfl
    simp [heq]
  · rename_i hn'
    exact False.elim (hn' hn)

theorem middleContribution_of_not_isMiddle
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length)
    {n : ℕ} (hn : n < Q.length)
    (hmiddle : ¬ ARWord.IsMiddle G Q ⟨n, hn⟩ x) :
    middleContribution G Q x n = 0 := by
  classical
  unfold middleContribution
  split
  · rfl
  · rfl

/-- On the predecessor--endpoint interval, adjacent-root contributions are
exactly literal middle-position contributions. -/
theorem adjacentContribution_eq_middleContribution
    {G : SimpleGraph L} {Q : List L}
    (hAlt : ARWord.HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x)
    {n : ℕ} (hnLower : p.val + 1 ≤ n) (hnUpper : n < x.val) :
    adjacentContribution G Q (ARWord.label Q x) n =
      middleContribution G Q x n := by
  have hn : n < Q.length := hnUpper.trans x.isLt
  have hpn : p < (⟨n, hn⟩ : Fin Q.length) := by
    exact_mod_cast (show p.val < n by omega)
  have hnx : (⟨n, hn⟩ : Fin Q.length) < x := by
    exact_mod_cast hnUpper
  by_cases hadj : G.Adj (Q.get ⟨n, hn⟩) (ARWord.label Q x)
  · have hmiddle : ARWord.IsMiddle G Q ⟨n, hn⟩ x :=
      (isMiddle_iff_between_previous_and_endpoint hAlt hpx ⟨n, hn⟩).2
        ⟨hpn, hnx, hadj⟩
    rw [adjacentContribution_of_adj G Q (ARWord.label Q x) hn hadj,
      middleContribution_of_isMiddle G Q x hn hmiddle]
  · have hmiddle : ¬ ARWord.IsMiddle G Q ⟨n, hn⟩ x := by
      intro h
      exact hadj h.1
    rw [adjacentContribution_of_not_adj G Q (ARWord.label Q x) hn hadj,
      middleContribution_of_not_isMiddle G Q x hn hmiddle]

/-- The natural-index interval sum of middle contributions is the literal
sum over all middle positions. -/
theorem sum_Ico_middleContribution_eq_middleRootSum
    {G : SimpleGraph L} {Q : List L}
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x) :
    (∑ n ∈ Finset.Ico (p.val + 1) x.val, middleContribution G Q x n) =
      middleRootSum G Q x := by
  unfold middleRootSum
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ico] at hn
    exact Finset.mem_range.mpr (hn.2.trans x.isLt)
  · intro n hnRange hnIco
    have hn : n < Q.length := Finset.mem_range.mp hnRange
    by_cases hmiddle : ARWord.IsMiddle G Q ⟨n, hn⟩ x
    · apply False.elim
      apply hnIco
      rw [Finset.mem_Ico]
      have hpn : p < (⟨n, hn⟩ : Fin Q.length) :=
        hmiddle.2.2.1 p hpx
      have hpnNat : p.val < n := hpn
      have hnxNat : n < x.val := hmiddle.2.1
      exact ⟨Nat.succ_le_iff.mpr hpnNat, hnxNat⟩
    · exact middleContribution_of_not_isMiddle G Q x hn hmiddle

/-- First equality in `eq:directed-root-mesh`, before identifying the
adjacent interval positions with the middle positions. -/
theorem inversionRoot_add_inversionRoot_eq_sum_adjacent_between
    {G : SimpleGraph L} {Q : List L}
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x) :
    inversionRoot G Q p + inversionRoot G Q x =
      ∑ n ∈ Finset.Ico (p.val + 1) x.val,
        adjacentContribution G Q (ARWord.label Q x) n := by
  have htel := transportedSimpleRoot_eq_add_sum_Ico G Q
    (ARWord.label Q x) (a := p.val + 1) (b := x.val)
    (Nat.succ_le_iff.mpr hpx.1) (Nat.le_of_lt x.isLt)
    (fun n hn hpn hnx => by
      have hpnFin : p < (⟨n, hn⟩ : Fin Q.length) := by
        change p.val < n
        omega
      have hnxFin : (⟨n, hn⟩ : Fin Q.length) < x := by
        change n < x.val
        exact hnx
      exact hpx.2.2 ⟨n, hn⟩ hpnFin hnxFin)
  have hpStep := transportedSimpleRoot_succ_of_label_eq G Q
    (ARWord.label Q x) p.isLt hpx.2.1
  change inversionRoot G Q x = _ at htel
  rw [hpStep] at htel
  rw [htel]
  simp

/-- Literal repeated-position root mesh identity from the manuscript. -/
theorem inversionRoot_add_inversionRoot_eq_middleRootSum
    {G : SimpleGraph L} {Q : List L}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x) :
    inversionRoot G Q p + inversionRoot G Q x = middleRootSum G Q x := by
  rw [inversionRoot_add_inversionRoot_eq_sum_adjacent_between hpx]
  calc
    (∑ n ∈ Finset.Ico (p.val + 1) x.val,
        adjacentContribution G Q (ARWord.label Q x) n) =
        ∑ n ∈ Finset.Ico (p.val + 1) x.val,
          middleContribution G Q x n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_Ico] at hn
      exact adjacentContribution_eq_middleContribution
        hRuns.hasInteriorAlternation hpx (by omega) hn.2
    _ = middleRootSum G Q x :=
      sum_Ico_middleContribution_eq_middleRootSum hpx

/-- Paper-facing repeated-position identity with the right side written as
the literal finite sum over `IsMiddle` positions. -/
theorem inversionRoot_add_inversionRoot_eq_sum_isMiddle
    {G : SimpleGraph L} {Q : List L}
    (hRuns : ARWord.HasOnlyBoundaryRepeatedRuns G Q)
    {p x : Fin Q.length} (hpx : ARWord.IsPrevious Q p x) :
    inversionRoot G Q p + inversionRoot G Q x =
      filteredMiddleRootSum G Q x := by
  rw [inversionRoot_add_inversionRoot_eq_middleRootSum hRuns hpx,
    middleRootSum_eq_sum_filter]

/-- An earlier position is adjacent to `x` but is not the final earlier
occurrence of its own label.  This is the literal index predicate in the
first-occurrence defect formula. -/
def IsEarlierNonLastAdjacent (G : SimpleGraph L) (Q : List L)
    (y x : Fin Q.length) : Prop :=
  G.Adj (ARWord.label Q y) (ARWord.label Q x) ∧ y < x ∧
    ∃ z : Fin Q.length,
      y < z ∧ z < x ∧ ARWord.label Q z = ARWord.label Q y

/-- The inversion-root contribution of an earlier nonlast adjacent position,
zero at all other natural indices. -/
def earlierNonLastAdjacentContribution
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) (n : ℕ) :
    RootLattice L := by
  classical
  exact if hn : n < Q.length then
    if IsEarlierNonLastAdjacent G Q ⟨n, hn⟩ x then
      inversionRoot G Q ⟨n, hn⟩
    else 0
  else 0

/-- The literal sum in the first-occurrence mesh defect. -/
def earlierNonLastAdjacentRootSum
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) : RootLattice L :=
  ∑ n ∈ Finset.range Q.length,
    earlierNonLastAdjacentContribution G Q x n

/-- The natural-index implementation of the defect sum is exactly the finite
sum over positions satisfying the manuscript's literal predicate. -/
def filteredEarlierNonLastAdjacentRootSum
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) : RootLattice L := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y : Fin Q.length ↦
    IsEarlierNonLastAdjacent G Q y x), inversionRoot G Q y

theorem earlierNonLastAdjacentRootSum_eq_sum_filter
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    earlierNonLastAdjacentRootSum G Q x =
      filteredEarlierNonLastAdjacentRootSum G Q x := by
  classical
  unfold filteredEarlierNonLastAdjacentRootSum
  rw [Finset.sum_filter]
  unfold earlierNonLastAdjacentRootSum
  calc
    (∑ n ∈ Finset.range Q.length,
        earlierNonLastAdjacentContribution G Q x n) =
        ∑ y : Fin Q.length,
          earlierNonLastAdjacentContribution G Q x y.val :=
      (Fin.sum_univ_eq_sum_range
        (fun n ↦ earlierNonLastAdjacentContribution G Q x n) Q.length).symm
    _ = ∑ y : Fin Q.length,
        if IsEarlierNonLastAdjacent G Q y x then
          inversionRoot G Q y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp [earlierNonLastAdjacentContribution, y.isLt]

theorem earlierNonLastAdjacentContribution_of_property
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length)
    {n : ℕ} (hn : n < Q.length)
    (hprop : IsEarlierNonLastAdjacent G Q ⟨n, hn⟩ x) :
    earlierNonLastAdjacentContribution G Q x n =
      inversionRoot G Q ⟨n, hn⟩ := by
  classical
  unfold earlierNonLastAdjacentContribution
  split
  · rename_i hn'
    have heq : (⟨n, hn'⟩ : Fin Q.length) = ⟨n, hn⟩ := Fin.ext rfl
    simp [heq]
  · rename_i hn'
    exact False.elim (hn' hn)

theorem earlierNonLastAdjacentContribution_of_not_property
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length)
    {n : ℕ} (hn : n < Q.length)
    (hprop : ¬ IsEarlierNonLastAdjacent G Q ⟨n, hn⟩ x) :
    earlierNonLastAdjacentContribution G Q x n = 0 := by
  classical
  unfold earlierNonLastAdjacentContribution
  split <;> rfl

omit [Fintype L] in
/-- At a first occurrence, a middle position is precisely an earlier adjacent
position with no later occurrence of the same label before the endpoint. -/
theorem isMiddle_iff_earlier_adjacent_and_last
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length}
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x)
    (y : Fin Q.length) :
    ARWord.IsMiddle G Q y x ↔
      G.Adj (ARWord.label Q y) (ARWord.label Q x) ∧ y < x ∧
        ¬ ∃ z : Fin Q.length,
          y < z ∧ z < x ∧ ARWord.label Q z = ARWord.label Q y := by
  constructor
  · intro hy
    refine ⟨hy.1, hy.2.1, ?_⟩
    rintro ⟨z, hyz, hzx, hzLabel⟩
    exact hy.2.2.2 z hyz hzx hzLabel
  · rintro ⟨hadj, hyx, hlast⟩
    refine ⟨hadj, hyx, ?_, ?_⟩
    · intro p hpx
      exact False.elim (hfirst ⟨p, hpx⟩)
    · intro z hyz hzx hzLabel
      exact hlast ⟨z, hyz, hzx, hzLabel⟩

/-- Before a first occurrence, each adjacent contribution belongs exactly to
one of the literal middle and nonlast-earlier sums. -/
theorem adjacentContribution_eq_middle_add_nonLast
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length}
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x)
    {n : ℕ} (hnUpper : n < x.val) :
    adjacentContribution G Q (ARWord.label Q x) n =
      middleContribution G Q x n +
        earlierNonLastAdjacentContribution G Q x n := by
  have hn : n < Q.length := hnUpper.trans x.isLt
  let y : Fin Q.length := ⟨n, hn⟩
  have hyx : y < x := hnUpper
  by_cases hadj : G.Adj (ARWord.label Q y) (ARWord.label Q x)
  · by_cases hnonlast : ∃ z : Fin Q.length,
        y < z ∧ z < x ∧ ARWord.label Q z = ARWord.label Q y
    · have hprop : IsEarlierNonLastAdjacent G Q y x :=
        ⟨hadj, hyx, hnonlast⟩
      have hnotMiddle : ¬ ARWord.IsMiddle G Q y x := by
        intro hmiddle
        exact hnonlast.elim fun z hz => hmiddle.2.2.2 z hz.1 hz.2.1 hz.2.2
      rw [adjacentContribution_of_adj G Q (ARWord.label Q x) hn hadj,
        middleContribution_of_not_isMiddle G Q x hn hnotMiddle,
        earlierNonLastAdjacentContribution_of_property G Q x hn hprop]
      simp
    · have hmiddle : ARWord.IsMiddle G Q y x :=
        (isMiddle_iff_earlier_adjacent_and_last hfirst y).2
          ⟨hadj, hyx, hnonlast⟩
      have hnotProp : ¬ IsEarlierNonLastAdjacent G Q y x := by
        intro hprop
        exact hnonlast hprop.2.2
      rw [adjacentContribution_of_adj G Q (ARWord.label Q x) hn hadj,
        middleContribution_of_isMiddle G Q x hn hmiddle,
        earlierNonLastAdjacentContribution_of_not_property G Q x hn hnotProp]
      simp
  · have hnotMiddle : ¬ ARWord.IsMiddle G Q y x := fun h => hadj h.1
    have hnotProp : ¬ IsEarlierNonLastAdjacent G Q y x := fun h => hadj h.1
    rw [adjacentContribution_of_not_adj G Q (ARWord.label Q x) hn hadj,
      middleContribution_of_not_isMiddle G Q x hn hnotMiddle,
      earlierNonLastAdjacentContribution_of_not_property G Q x hn hnotProp]
    simp

/-- Summing middle contributions before `x` already gives the literal
all-position middle sum. -/
theorem sum_Ico_zero_middleContribution_eq_middleRootSum
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length} :
    (∑ n ∈ Finset.Ico 0 x.val, middleContribution G Q x n) =
      middleRootSum G Q x := by
  unfold middleRootSum
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ico] at hn
    exact Finset.mem_range.mpr (hn.2.trans x.isLt)
  · intro n hnRange hnIco
    have hn : n < Q.length := Finset.mem_range.mp hnRange
    by_cases hmiddle : ARWord.IsMiddle G Q ⟨n, hn⟩ x
    · apply False.elim
      apply hnIco
      exact Finset.mem_Ico.mpr ⟨Nat.zero_le n, hmiddle.2.1⟩
    · exact middleContribution_of_not_isMiddle G Q x hn hmiddle

/-- The interval sum of nonlast-earlier contributions equals its literal
all-position sum, since its defining predicate already forces `n < x`. -/
theorem sum_Ico_zero_nonLastContribution_eq_rootSum
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length} :
    (∑ n ∈ Finset.Ico 0 x.val,
      earlierNonLastAdjacentContribution G Q x n) =
      earlierNonLastAdjacentRootSum G Q x := by
  unfold earlierNonLastAdjacentRootSum
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ico] at hn
    exact Finset.mem_range.mpr (hn.2.trans x.isLt)
  · intro n hnRange hnIco
    have hn : n < Q.length := Finset.mem_range.mp hnRange
    by_cases hprop : IsEarlierNonLastAdjacent G Q ⟨n, hn⟩ x
    · apply False.elim
      apply hnIco
      exact Finset.mem_Ico.mpr ⟨Nat.zero_le n, hprop.2.1⟩
    · exact earlierNonLastAdjacentContribution_of_not_property G Q x hn hprop

/-- The adjacent-prefix sum at a first occurrence splits into the literal
middle sum and the literal nonlast-earlier defect sum. -/
theorem sum_adjacent_before_eq_middle_add_nonLast
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length}
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    (∑ n ∈ Finset.Ico 0 x.val,
      adjacentContribution G Q (ARWord.label Q x) n) =
      middleRootSum G Q x + earlierNonLastAdjacentRootSum G Q x := by
  calc
    (∑ n ∈ Finset.Ico 0 x.val,
      adjacentContribution G Q (ARWord.label Q x) n) =
        ∑ n ∈ Finset.Ico 0 x.val,
          (middleContribution G Q x n +
            earlierNonLastAdjacentContribution G Q x n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact adjacentContribution_eq_middle_add_nonLast hfirst
        (Finset.mem_Ico.mp hn).2
    _ = (∑ n ∈ Finset.Ico 0 x.val, middleContribution G Q x n) +
        ∑ n ∈ Finset.Ico 0 x.val,
          earlierNonLastAdjacentContribution G Q x n := by
      rw [Finset.sum_add_distrib]
    _ = middleRootSum G Q x + earlierNonLastAdjacentRootSum G Q x := by
      rw [sum_Ico_zero_middleContribution_eq_middleRootSum,
        sum_Ico_zero_nonLastContribution_eq_rootSum]

/-- Literal first-occurrence defect formula from the manuscript. -/
theorem inversionRoot_sub_middleRootSum_eq_first_defect
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length}
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    inversionRoot G Q x - middleRootSum G Q x =
      simpleRoot (ARWord.label Q x) +
        earlierNonLastAdjacentRootSum G Q x := by
  have htel := transportedSimpleRoot_eq_add_sum_Ico G Q
    (ARWord.label Q x) (a := 0) (b := x.val)
    (Nat.zero_le _) (Nat.le_of_lt x.isLt) (fun n hn _ hnx => by
      intro hlabel
      apply hfirst
      rw [ARWord.exists_isPrevious_iff_exists_lt_label_eq]
      refine ⟨⟨n, hn⟩, ?_, hlabel⟩
      exact hnx)
  change inversionRoot G Q x = _ at htel
  simp only [transportedSimpleRoot_zero] at htel
  rw [htel, sum_adjacent_before_eq_middle_add_nonLast hfirst]
  abel

/-- Paper-facing first-occurrence defect identity with both sums interpreted
as literal filtered sums over word positions. -/
theorem inversionRoot_sub_sum_isMiddle_eq_sum_earlierNonLast
    {G : SimpleGraph L} {Q : List L} {x : Fin Q.length}
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    inversionRoot G Q x - filteredMiddleRootSum G Q x =
      simpleRoot (ARWord.label Q x) +
        filteredEarlierNonLastAdjacentRootSum G Q x := by
  rw [← middleRootSum_eq_sum_filter,
    inversionRoot_sub_middleRootSum_eq_first_defect hfirst,
    earlierNonLastAdjacentRootSum_eq_sum_filter]

end QuotientSubmoduleEquidistribution.RepresentationDirected.WordRootProcess
