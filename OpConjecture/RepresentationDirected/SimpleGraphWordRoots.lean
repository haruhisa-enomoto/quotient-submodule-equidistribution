import OpConjecture.RepresentationDirected.SimpleGraphGeometricRepresentation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.TakeDrop

/-!
# Root signs and word-prefix roots for the graph geometric representation

This file fixes the orientation conventions needed
for the representation-directed word arguments.  Since the geometric
representation is a left action, applying reflections in increasing list
order realizes the inverse of the listed Coxeter product.
-/

noncomputable section

open scoped BigOperators

namespace OpConjecture.RepresentationDirected.WordRootProcess

open SimpleGraphCoxeter

universe u

variable {L : Type u} [Fintype L]

/-- The basis vector indexed by `i`. -/
def simpleRoot (i : L) : RootLattice L := by
  classical
  exact fun j => if j = i then 1 else 0

omit [Fintype L] in
@[simp]
theorem simpleRoot_apply_self (i : L) : simpleRoot i i = 1 := by
  classical
  simp [simpleRoot]

omit [Fintype L] in
@[simp]
theorem simpleRoot_apply_of_ne {i j : L} (hji : j ≠ i) :
    simpleRoot i j = 0 := by
  classical
  simp [simpleRoot, hji]

/-- Coordinatewise nonnegativity. -/
def IsNonnegative (z : RootLattice L) : Prop := ∀ i, 0 ≤ z i

/-- Positivity in the root convention: coordinatewise nonnegative and nonzero. -/
def IsPositive (z : RootLattice L) : Prop := IsNonnegative z ∧ z ≠ 0

/-- Coordinatewise nonpositivity. -/
def IsNonpositive (z : RootLattice L) : Prop := ∀ i, z i ≤ 0

/-- Negativity in the root convention: coordinatewise nonpositive and nonzero. -/
def IsNegative (z : RootLattice L) : Prop := IsNonpositive z ∧ z ≠ 0

/-- The sum of the simple-root coordinates. -/
def height (z : RootLattice L) : ℤ := ∑ i, z i

omit [Fintype L] in
theorem simpleRoot_ne_zero (i : L) : simpleRoot i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp at hi

omit [Fintype L] in
theorem simpleRoot_isNonnegative (i : L) : IsNonnegative (simpleRoot i) := by
  intro j
  classical
  by_cases hji : j = i <;> simp [simpleRoot, hji]

omit [Fintype L] in
theorem simpleRoot_isPositive (i : L) : IsPositive (simpleRoot i) :=
  ⟨simpleRoot_isNonnegative i, simpleRoot_ne_zero i⟩

@[simp]
theorem height_simpleRoot (i : L) : height (simpleRoot i) = 1 := by
  classical
  simp [height, simpleRoot]

theorem IsNonnegative.height_nonnegative {z : RootLattice L}
    (hz : IsNonnegative z) : 0 ≤ height z := by
  exact Finset.sum_nonneg fun i _ => hz i

theorem IsPositive.height_positive {z : RootLattice L}
    (hz : IsPositive z) : 0 < height z := by
  have hex : ∃ i, 0 < z i := by
    by_contra h
    push Not at h
    apply hz.2
    funext i
    exact le_antisymm (h i) (hz.1 i)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => hz.1 j) ⟨i, Finset.mem_univ i, hi⟩

omit [Fintype L] in
theorem isNonnegative_neg_iff (z : RootLattice L) :
    IsNonnegative (-z) ↔ IsNonpositive z := by
  constructor <;> intro h i
  · simpa using h i
  · simpa using h i

omit [Fintype L] in
theorem isNonpositive_neg_iff (z : RootLattice L) :
    IsNonpositive (-z) ↔ IsNonnegative z := by
  constructor <;> intro h i
  · simpa using h i
  · simpa using h i

omit [Fintype L] in
theorem IsPositive.neg {z : RootLattice L} (hz : IsPositive z) :
    IsNegative (-z) := by
  refine ⟨(isNonpositive_neg_iff z).2 hz.1, ?_⟩
  simpa using hz.2

omit [Fintype L] in
theorem IsNegative.neg {z : RootLattice L} (hz : IsNegative z) :
    IsPositive (-z) := by
  refine ⟨(isNonnegative_neg_iff z).2 hz.1, ?_⟩
  simpa using hz.2

omit [Fintype L] in
/-- A nonzero vector cannot be both coordinatewise positive and negative. -/
theorem IsPositive.not_isNegative {z : RootLattice L} (hz : IsPositive z) :
    ¬ IsNegative z := by
  intro hn
  apply hz.2
  funext i
  exact le_antisymm (hn.1 i) (hz.1 i)

@[simp]
theorem height_neg (z : RootLattice L) : height (-z) = -height z := by
  simp [height]

private theorem neighborSum_simpleRoot_self_eq_zero
    (G : SimpleGraph L) (i : L) : neighborSum G i (simpleRoot i) = 0 := by
  classical
  unfold neighborSum
  apply Finset.sum_eq_zero
  intro j hj
  rw [simpleRoot_apply_of_ne]
  exact (G.ne_of_adj ((G.mem_neighborFinset i j).mp hj)).symm

/-- A simple reflection sends its own simple root to its negative. -/
theorem simpleReflection_simpleRoot_self (G : SimpleGraph L) (i : L) :
    simpleReflection G i (simpleRoot i) = -simpleRoot i := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [simpleReflection_apply_self,
      neighborSum_simpleRoot_self_eq_zero]
    simp
  · rw [simpleReflection_apply_of_ne G hji]
    simp [simpleRoot_apply_of_ne hji]

private theorem neighborSum_simpleRoot_of_adj
    (G : SimpleGraph L) {i j : L} (hij : G.Adj i j) :
    neighborSum G i (simpleRoot j) = 1 := by
  classical
  unfold neighborSum
  calc
    (∑ h ∈ G.neighborFinset i, simpleRoot j h) = simpleRoot j j := by
      apply Finset.sum_eq_single j
      · intro b hb hbj
        exact simpleRoot_apply_of_ne hbj
      · intro hj
        exact False.elim (hj ((G.mem_neighborFinset i j).mpr hij))
    _ = 1 := simpleRoot_apply_self j

/-- At adjacent vertices, `s_i(α_j) = α_j + α_i`. -/
theorem simpleReflection_simpleRoot_of_adj
    (G : SimpleGraph L) {i j : L} (hij : G.Adj i j) :
    simpleReflection G i (simpleRoot j) = simpleRoot j + simpleRoot i := by
  funext h
  by_cases hhi : h = i
  · subst h
    rw [simpleReflection_apply_self, neighborSum_simpleRoot_of_adj G hij]
    simp only [Pi.add_apply, simpleRoot_apply_of_ne hij.ne,
      simpleRoot_apply_self, neg_zero, zero_add]
  · rw [simpleReflection_apply_of_ne G hhi]
    simp [simpleRoot_apply_of_ne hhi]

private theorem neighborSum_simpleRoot_of_not_adj
    (G : SimpleGraph L) {i j : L} (hij : ¬ G.Adj i j) :
    neighborSum G i (simpleRoot j) = 0 := by
  classical
  unfold neighborSum
  apply Finset.sum_eq_zero
  intro h hh
  rw [simpleRoot_apply_of_ne]
  intro heq
  subst h
  exact hij ((G.mem_neighborFinset i j).mp hh)

/-- Distinct nonadjacent generators fix one another's simple roots. -/
theorem simpleReflection_simpleRoot_of_ne_of_not_adj
    (G : SimpleGraph L) {i j : L} (hne : i ≠ j) (hij : ¬ G.Adj i j) :
    simpleReflection G i (simpleRoot j) = simpleRoot j := by
  funext h
  by_cases hhi : h = i
  · subst h
    rw [simpleReflection_apply_self, neighborSum_simpleRoot_of_not_adj G hij]
    simp only [simpleRoot_apply_of_ne hne, neg_zero, zero_add]
  · rw [simpleReflection_apply_of_ne G hhi]

/-- The Coxeter element represented by the first `n` letters of `Q`. -/
def prefixElement (G : SimpleGraph L) (Q : List L) (n : ℕ) : Group G :=
  (system G).wordProd (Q.take n)

omit [Fintype L] in
@[simp]
theorem prefixElement_zero (G : SimpleGraph L) (Q : List L) :
    prefixElement G Q 0 = 1 := by
  simp [prefixElement]

omit [Fintype L] in
@[simp]
theorem prefixElement_length (G : SimpleGraph L) (Q : List L) :
    prefixElement G Q Q.length = wordProd G Q := by
  simp [prefixElement, wordProd]

omit [Fintype L] in
/-- Appending the next letter multiplies the prefix element on the right. -/
theorem prefixElement_succ (G : SimpleGraph L) (Q : List L)
    {n : ℕ} (hn : n < Q.length) :
    prefixElement G Q (n + 1) =
      prefixElement G Q n * (system G).simple Q[n] := by
  unfold prefixElement
  rw [← List.take_concat_get' Q n hn, (system G).wordProd_append]
  simp

/-- The action recursion for a prefix extended on the right. -/
theorem geometricRepresentation_prefix_succ
    (G : SimpleGraph L) (Q : List L) {n : ℕ} (hn : n < Q.length)
    (z : RootLattice L) :
    geometricRepresentation G (prefixElement G Q (n + 1)) z =
      geometricRepresentation G (prefixElement G Q n)
        (simpleReflection G Q[n] z) := by
  rw [prefixElement_succ G Q hn, map_mul, LinearEquiv.mul_apply,
    geometricRepresentation_simple]
  rfl

/-- The standard prefix (or inversion) root at a word position. -/
def inversionRoot (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    RootLattice L :=
  geometricRepresentation G (prefixElement G Q x) (simpleRoot Q[x])

/-- Every inversion root is nonzero because the geometric action is by
linear equivalences. -/
theorem inversionRoot_ne_zero (G : SimpleGraph L) (Q : List L)
    (x : Fin Q.length) : inversionRoot G Q x ≠ 0 := by
  intro h
  apply simpleRoot_ne_zero Q[x]
  apply (geometricRepresentation G (prefixElement G Q x)).injective
  simpa [inversionRoot] using h

/-- On inversion roots, the explicit nonzero clause in `IsPositive` is
automatic, so positivity is exactly coordinatewise nonnegativity as in the
manuscript. -/
theorem inversionRoot_isPositive_iff_isNonnegative
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    IsPositive (inversionRoot G Q x) ↔
      IsNonnegative (inversionRoot G Q x) := by
  exact and_iff_left (inversionRoot_ne_zero G Q x)

@[simp]
theorem inversionRoot_cons_zero (G : SimpleGraph L) (i : L) (Q : List L) :
    inversionRoot G (i :: Q) ⟨0, by simp⟩ = simpleRoot i := by
  simp [inversionRoot, prefixElement]

/-- Removing the first letter from a word removes its outermost action on
all later inversion roots. -/
theorem inversionRoot_cons_succ (G : SimpleGraph L) (i : L) (Q : List L)
    (x : Fin Q.length) :
    inversionRoot G (i :: Q) ⟨x + 1, by simp [x.isLt]⟩ =
      simpleReflection G i (inversionRoot G Q x) := by
  simp only [inversionRoot, prefixElement, List.take_succ_cons,
    CoxeterSystem.wordProd_cons, map_mul,
    LinearEquiv.mul_apply]
  rw [geometricRepresentation_simple]
  rfl

/-- The final inversion root after appending one letter is the full old word
acting on that letter's simple root. -/
theorem inversionRoot_concat_last (G : SimpleGraph L) (Q : List L) (i : L) :
    inversionRoot G (Q.concat i) ⟨Q.length, by simp⟩ =
      geometricRepresentation G (wordProd G Q) (simpleRoot i) := by
  simp [inversionRoot, prefixElement, wordProd, List.concat_eq_append]

/-- Every prefix root of `Q` is positive. -/
def HasPositiveInversionRoots (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ x : Fin Q.length, IsPositive (inversionRoot G Q x)

/-- The real-root sign-coherence assertion for the inversion roots of a
word: every such root is positive or negative in simple-root coordinates. -/
def HasCoherentInversionRootSigns (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ x : Fin Q.length,
    IsPositive (inversionRoot G Q x) ∨
      IsNegative (inversionRoot G Q x)

/-- No next letter is a right descent of the product of the earlier letters. -/
def HasNoPrefixRightDescents (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ n, (hn : n < Q.length) →
    ¬ (system G).IsRightDescent (prefixElement G Q n) Q[n]

omit [Fintype L] in
/-- Pure Coxeter length theory reduces word reducedness to the absence of a
right descent at every prefix extension. -/
theorem isReduced_iff_hasNoPrefixRightDescents
    (G : SimpleGraph L) (Q : List L) :
    IsReduced G Q ↔ HasNoPrefixRightDescents G Q := by
  constructor
  · intro hred n hn
    rw [(system G).not_isRightDescent_iff]
    rw [← prefixElement_succ G Q hn]
    have hnext := hred.take (n + 1)
    have hprev := hred.take n
    change (system G).length (prefixElement G Q (n + 1)) =
      (system G).length (prefixElement G Q n) + 1
    simp only [prefixElement]
    rw [hnext.eq, hprev.eq]
    rw [List.length_take_of_le (by omega),
      List.length_take_of_le (by omega)]
  · intro hprefix
    have hall : ∀ n, n ≤ Q.length → (system G).IsReduced (Q.take n) := by
      intro n hn
      induction n with
      | zero => simp [CoxeterSystem.IsReduced]
      | succ n ih =>
          have hnlt : n < Q.length := by omega
          have hprev := ih (by omega)
          have hstep :=
            ((system G).not_isRightDescent_iff (w := prefixElement G Q n)
              (i := Q[n])).mp (hprefix n hnlt)
          rw [← prefixElement_succ G Q hnlt] at hstep
          unfold CoxeterSystem.IsReduced
          change (system G).length (prefixElement G Q (n + 1)) =
            (Q.take (n + 1)).length
          rw [hstep]
          simp only [prefixElement]
          rw [hprev.eq]
          rw [List.length_take_of_le (by omega),
            List.length_take_of_le (by omega)]
    simpa [SimpleGraphCoxeter.IsReduced, prefixElement,
      SimpleGraphCoxeter.wordProd] using hall Q.length le_rfl

/-- The exact geometric input absent from the pinned Coxeter library: the
prefix root is positive exactly when the next generator is not a right
descent. -/
def HasPrefixRootSignCompatibility (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ x : Fin Q.length,
    IsPositive (inversionRoot G Q x) ↔
      ¬ (system G).IsRightDescent (prefixElement G Q x) Q[x]

/-- Descent/sign compatibility together with real-root sign coherence gives
the complementary negative-root criterion used by the cancellation proof. -/
theorem inversionRoot_isNegative_iff_isRightDescent
    (G : SimpleGraph L) (Q : List L)
    (hcompat : HasPrefixRootSignCompatibility G Q)
    (hcoherent : HasCoherentInversionRootSigns G Q)
    (x : Fin Q.length) :
    IsNegative (inversionRoot G Q x) ↔
      (system G).IsRightDescent (prefixElement G Q x) Q[x] := by
  constructor
  · intro hneg
    by_contra hdescent
    exact ((hcompat x).2 hdescent).not_isNegative hneg
  · intro hdescent
    rcases hcoherent x with hpos | hneg
    · exact False.elim ((hcompat x).1 hpos hdescent)
    · exact hneg

/-- Once the missing descent/sign compatibility is supplied, the familiar
reduced-word criterion by positive inversion roots is formal. -/
theorem isReduced_iff_hasPositiveInversionRoots
    (G : SimpleGraph L) (Q : List L)
    (hsign : HasPrefixRootSignCompatibility G Q) :
    IsReduced G Q ↔ HasPositiveInversionRoots G Q := by
  rw [isReduced_iff_hasNoPrefixRightDescents]
  constructor
  · intro h x
    exact (hsign x).2 (h x x.isLt)
  · intro h n hn
    exact (hsign ⟨n, hn⟩).1 (h ⟨n, hn⟩)

/-- Apply the listed reflections operationally from left to right. -/
def reflectInIncreasingOrder (G : SimpleGraph L) (Q : List L)
    (z : RootLattice L) : RootLattice L :=
  Q.foldl (fun z i => simpleReflection G i z) z

@[simp]
theorem reflectInIncreasingOrder_nil (G : SimpleGraph L) (z : RootLattice L) :
    reflectInIncreasingOrder G [] z = z := rfl

@[simp]
theorem reflectInIncreasingOrder_cons (G : SimpleGraph L) (i : L)
    (Q : List L) (z : RootLattice L) :
    reflectInIncreasingOrder G (i :: Q) z =
      reflectInIncreasingOrder G Q (simpleReflection G i z) := rfl

theorem reflectInIncreasingOrder_append (G : SimpleGraph L) (Q R : List L)
    (z : RootLattice L) :
    reflectInIncreasingOrder G (Q ++ R) z =
      reflectInIncreasingOrder G R (reflectInIncreasingOrder G Q z) := by
  simp [reflectInIncreasingOrder, List.foldl_append]

/-- Operational processing in increasing order uses the reversed word. -/
theorem reflectInIncreasingOrder_eq_reverse_word_action
    (G : SimpleGraph L) (Q : List L) (z : RootLattice L) :
    reflectInIncreasingOrder G Q z =
      geometricRepresentation G ((system G).wordProd Q.reverse) z := by
  induction Q generalizing z with
  | nil => simp [reflectInIncreasingOrder]
  | cons i Q ih =>
      rw [reflectInIncreasingOrder_cons, ih]
      rw [List.reverse_cons, (system G).wordProd_append,
        (system G).wordProd_singleton, map_mul, LinearEquiv.mul_apply]
      rw [geometricRepresentation_simple]
      rfl

/-- Orientation theorem: operational processing in increasing list order is
the action of the inverse of the listed Coxeter product. -/
theorem reflectInIncreasingOrder_eq_inverse_word_action
    (G : SimpleGraph L) (Q : List L) (z : RootLattice L) :
    reflectInIncreasingOrder G Q z =
      geometricRepresentation G ((system G).wordProd Q)⁻¹ z := by
  rw [reflectInIncreasingOrder_eq_reverse_word_action,
    (system G).wordProd_reverse]

/-- Processing an initial segment in increasing order acts by the inverse
prefix element. -/
theorem reflectInIncreasingOrder_take_eq_inverse_prefix_action
    (G : SimpleGraph L) (Q : List L) (n : ℕ) (z : RootLattice L) :
    reflectInIncreasingOrder G (Q.take n) z =
      geometricRepresentation G (prefixElement G Q n)⁻¹ z := by
  exact reflectInIncreasingOrder_eq_inverse_word_action G (Q.take n) z

/-- The standard inversion root is obtained operationally by processing its
earlier letters in *decreasing* position order. -/
theorem inversionRoot_eq_reverse_prefix_process
    (G : SimpleGraph L) (Q : List L) (x : Fin Q.length) :
    inversionRoot G Q x =
      reflectInIncreasingOrder G (Q.take x).reverse (simpleRoot Q[x]) := by
  rw [reflectInIncreasingOrder_eq_inverse_word_action,
    (system G).wordProd_reverse, inv_inv]
  rfl

end OpConjecture.RepresentationDirected.WordRootProcess
