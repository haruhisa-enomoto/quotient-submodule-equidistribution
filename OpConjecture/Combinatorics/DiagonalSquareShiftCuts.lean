import Mathlib

/-!
# Diagonal cuts in a finite square-shift strip

The diagonal `M₄` count in the four-vertex argument only reads equality
occurrences on two actual cuts of a labelled sequence.  This file proves
their equality directly.  Possible square-shift components which meet only
the ambient boundary are absent from both cut types by construction.
-/

set_option autoImplicit false
noncomputable section

namespace OpConjecture.DiagonalSquareShiftCuts

/-- The integer positions from `2` through `L - 2`. -/
abbrev CutIndex (L : ℕ) := {e : ℕ // 2 ≤ e ∧ e ≤ L - 2}

/-- Coordinate the cut interval by `Fin (L - 3)`. -/
def finEquivCutIndex (L : ℕ) : Fin (L - 3) ≃ CutIndex L where
  toFun e := ⟨e.1 + 2, by
    constructor
    · omega
    · have he := e.2
      omega⟩
  invFun e := ⟨e.1 - 2, by
    have he := e.2
    omega⟩
  left_inv e := by
    apply Fin.ext
    have he := e.2
    simp only
    omega
  right_inv e := by
    apply Subtype.ext
    have he := e.2
    simp only
    omega

noncomputable instance cutIndexFintype (L : ℕ) : Fintype (CutIndex L) :=
  Fintype.ofEquiv (Fin (L - 3)) (finEquivCutIndex L)

variable {Label : Type*} [DecidableEq Label]

/-- Equality occurrences on the cut based at position `2`. -/
abbrev FirstCut (L : ℕ) (x : ℕ → Label) :=
  {e : CutIndex L // x 2 = x e.1}

/-- Equality occurrences on the cut based at position `L - 2`. -/
abbrev LastCut (L : ℕ) (x : ℕ → Label) :=
  {e : CutIndex L // x (L - 2) = x e.1}

omit [DecidableEq Label] in
/-- Equality can be shifted backward through any prescribed number of
simultaneous two-step moves. -/
theorem iterate_shift_iff
    {L i j : ℕ} (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (k : ℕ) (hi : i + 2 * k ≤ L) (hj : j + 2 * k ≤ L) :
    x (i + 2 * k) = x (j + 2 * k) ↔ x i = x j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show i + 2 * (k + 1) = (i + 2 * k) + 2 by omega,
        show j + 2 * (k + 1) = (j + 2 * k) + 2 by omega,
        hshift (i + 2 * k) (j + 2 * k) (by omega) (by omega),
        ih (by omega) (by omega)]

omit [DecidableEq Label] in
/-- A last-cut equality away from the diagonal has an even second index.
Otherwise shifting it to the left boundary would repeat the distinguished
position `1`. -/
theorem lastCut_index_even
    {L : ℕ} (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hfirst : ∀ j, 2 ≤ j → j ≤ L → x 1 ≠ x j)
    (q : LastCut L x) (hne : q.1.1 ≠ L - 2) :
    Even q.1.1 := by
  by_contra hnot
  have hodd : Odd q.1.1 := Nat.not_even_iff_odd.mp hnot
  rcases hodd with ⟨k, hk⟩
  have heLower := q.1.2.1
  have heUpper := q.1.2.2
  have heStrict : q.1.1 < L - 2 := lt_of_le_of_ne heUpper hne
  let j := L - q.1.1 - 1
  have hjLower : 2 ≤ j := by
    dsimp [j]
    omega
  have hbase : x 1 = x j := by
    apply (iterate_shift_iff x hshift k (i := 1) (j := j)
      (by omega) (by
        dsimp [j]
        omega)).1
    rw [show 1 + 2 * k = q.1.1 by omega,
      show j + 2 * k = L - 2 by
        dsimp [j]
        omega]
    exact q.2.symm
  exact hfirst j hjLower (by omega) hbase

omit [DecidableEq Label] in
/-- A first-cut equality away from the diagonal has even distance from
the right endpoint.  Otherwise shifting it to the right boundary would
repeat the distinguished position `L - 1`. -/
theorem firstCut_distance_even
    {L : ℕ} (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hlast : ∀ j, j ≤ L - 2 → x (L - 1) ≠ x j)
    (q : FirstCut L x) (hne : q.1.1 ≠ 2) :
    Even (L - q.1.1) := by
  by_contra hnot
  have hodd : Odd (L - q.1.1) := Nat.not_even_iff_odd.mp hnot
  rcases hodd with ⟨k, hk⟩
  have heLower := q.1.2.1
  have heUpper := q.1.2.2
  have heStrict : 2 < q.1.1 := lt_of_le_of_ne heLower (Ne.symm hne)
  let j := L - q.1.1 + 1
  have hjUpper : j ≤ L - 2 := by
    dsimp [j]
    omega
  have hboundary : x j = x (L - 1) := by
    rw [show j = 2 + 2 * k by
        dsimp [j]
        omega,
      show L - 1 = q.1.1 + 2 * k by omega]
    exact (iterate_shift_iff x hshift k (i := 2) (j := q.1.1)
      (by omega) (by omega)).2 q.2
  exact hlast j hjUpper hboundary.symm

/-- Reflect a last-cut occurrence into the first cut. -/
def lastToFirst
    {L : ℕ} (hL : 5 ≤ L) (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hfirst : ∀ j, 2 ≤ j → j ≤ L → x 1 ≠ x j)
    (q : LastCut L x) : FirstCut L x := by
  let e := q.1.1
  have heLower : 2 ≤ e := q.1.2.1
  have heUpper : e ≤ L - 2 := q.1.2.2
  let d := L - e
  have hdLower : 2 ≤ d := by dsimp [d]; omega
  have hdUpper : d ≤ L - 2 := by dsimp [d]; omega
  refine ⟨⟨d, hdLower, hdUpper⟩, ?_⟩
  change x 2 = x d
  by_cases hdiag : e = L - 2
  · have hd : d = 2 := by dsimp [d]; omega
    simp [hd]
  · have heEven := lastCut_index_even x hshift hfirst q hdiag
    rcases (even_iff_exists_two_mul.mp heEven) with ⟨k, hk⟩
    have hkPos : 0 < k := by omega
    apply (iterate_shift_iff x hshift (k - 1) (i := 2) (j := d)
      (by omega) (by
        dsimp [d]
        omega)).1
    rw [show 2 + 2 * (k - 1) = e by omega,
      show d + 2 * (k - 1) = L - 2 by
        dsimp [d]
        omega]
    exact q.2.symm

/-- Reflect a first-cut occurrence into the last cut. -/
def firstToLast
    {L : ℕ} (hL : 5 ≤ L) (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hlast : ∀ j, j ≤ L - 2 → x (L - 1) ≠ x j)
    (q : FirstCut L x) : LastCut L x := by
  let e := q.1.1
  have heLower : 2 ≤ e := q.1.2.1
  have heUpper : e ≤ L - 2 := q.1.2.2
  let d := L - e
  have hdLower : 2 ≤ d := by dsimp [d]; omega
  have hdUpper : d ≤ L - 2 := by dsimp [d]; omega
  refine ⟨⟨d, hdLower, hdUpper⟩, ?_⟩
  change x (L - 2) = x d
  by_cases hdiag : e = 2
  · have hd : d = L - 2 := by dsimp [d]; omega
    simp [hd]
  · have hdEven := firstCut_distance_even x hshift hlast q hdiag
    rcases (even_iff_exists_two_mul.mp hdEven) with ⟨k, hk⟩
    have hkPos : 0 < k := by omega
    have hs := (iterate_shift_iff x hshift (k - 1)
      (i := 2) (j := e) (by omega) (by omega)).2 q.2
    calc
      x (L - 2) = x (e + 2 * (k - 1)) := by
        congr 1
        omega
      _ = x (2 + 2 * (k - 1)) := hs.symm
      _ = x d := by
        congr 1
        dsimp [d]
        omega

/-- The two actual diagonal cuts are exactly equivalent.  The map is the
index reflection `e ↦ L-e`; the injective- and projective-boundary
nonrepetition hypotheses eliminate the two wrong-parity cases. -/
def firstCutEquivLastCut
    {L : ℕ} (hL : 5 ≤ L) (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hfirst : ∀ j, 2 ≤ j → j ≤ L → x 1 ≠ x j)
    (hlast : ∀ j, j ≤ L - 2 → x (L - 1) ≠ x j) :
    FirstCut L x ≃ LastCut L x where
  toFun := firstToLast hL x hshift hlast
  invFun := lastToFirst hL x hshift hfirst
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    change L - (L - q.1.1) = q.1.1
    have hq := q.1.2
    omega
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    change L - (L - q.1.1) = q.1.1
    have hq := q.1.2
    omega

/-- Cardinal form of the corrected diagonal-cut count. -/
theorem firstCut_card_eq_lastCut_card
    {L : ℕ} (hL : 5 ≤ L) (x : ℕ → Label)
    (hshift : ∀ i j, i + 2 ≤ L → j + 2 ≤ L →
      (x (i + 2) = x (j + 2) ↔ x i = x j))
    (hfirst : ∀ j, 2 ≤ j → j ≤ L → x 1 ≠ x j)
    (hlast : ∀ j, j ≤ L - 2 → x (L - 1) ≠ x j) :
    Fintype.card (FirstCut L x) = Fintype.card (LastCut L x) :=
  Fintype.card_congr (firstCutEquivLastCut hL x hshift hfirst hlast)

end OpConjecture.DiagonalSquareShiftCuts
