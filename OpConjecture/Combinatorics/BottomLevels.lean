import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import OpConjecture.ConvexGeometry.BottomLevels

/-!
# Generic combinatorics for the first four levels

This file contains only generic finite deductions: the cardinality of the five
formal level-three shape families, finite joint-fiber stratification over a
possibly infinite ambient index type, minimal faithful-core consequences, and
the simultaneous induction pattern for the annihilator recurrence.

It does not classify module supports, construct Gabriel arrows or faithful
cores, or prove the manuscript’s bottom-three or bottom-four propositions.
-/

noncomputable section

namespace OpConjecture.BottomLevels

/-! ## Pure combinatorics of the five level-three families -/

namespace BottomThreeShape

variable {V E U : Type*}
  [Fintype V]
  [Fintype E]
  [Fintype U]

/-- The arrows with prescribed source. -/
abbrev OutFiber (source : E → V) (x : V) :=
  {e : E // source e = x}

/-- The arrows with prescribed target. -/
abbrev InFiber (target : E → V) (x : V) :=
  {e : E // target e = x}

/-- The cardinality of one source fiber. -/
def outDegree (source : E → V) (x : V) : ℕ :=
  Nat.card (OutFiber source x)

/-- The cardinality of one target fiber. -/
def inDegree (target : E → V) (x : V) : ℕ :=
  Nat.card (InFiber target x)

/--
The five purely formal families occurring in the proposed level-three
classification:

1. three vertices;
2. an edge and a further vertex different from its source;
3. two edges with a common source;
4. one element of the supplied fourth family `U`;
5. two edges with a common target.

No assertion is made here that actual quotient-closed supports are classified
by this type.
-/
def Shape (source target : E → V) :=
  {s : Finset V // s.card = 3} ⊕
    (Σ e : E, {x : V // x ≠ source e}) ⊕
      (Σ x : V, {s : Finset (OutFiber source x) // s.card = 2}) ⊕
        U ⊕
          (Σ x : V, {s : Finset (InFiber target x) // s.card = 2})

/-- The numerical expression obtained by counting the five formal families. -/
def formula (source target : E → V) : ℕ :=
  Nat.choose (Fintype.card V) 3 +
    Fintype.card E * (Fintype.card V - 1) +
      (∑ x : V, Nat.choose (outDegree source x) 2) +
        Fintype.card U +
          ∑ x : V, Nat.choose (inDegree target x) 2

/-- The five formal families have the displayed cardinality. -/
theorem card (source target : E → V) :
    Nat.card (Shape (U := U) source target) =
      formula (U := U) source target := by
  classical
  simp [Shape, formula, Nat.card_eq_fintype_card,
    Fintype.card_finset_len, outDegree, inDegree]
  ac_rfl

/-- Swapping source and target leaves the formal counting expression fixed. -/
theorem formula_swap (source target : E → V) :
    formula (U := U) source target =
      formula (U := U) target source := by
  unfold formula outDegree inDegree
  simp only [OutFiber, InFiber]
  ac_rfl

/-- The two source/target-swapped formal shape types have equal cardinality. -/
theorem card_swap (source target : E → V) :
    Nat.card (Shape (U := U) source target) =
      Nat.card (Shape (U := U) target source) := by
  rw [card, card, formula_swap]

end BottomThreeShape

/-! ## Minimal faithful cores inside an actual closure system -/

namespace MinimalFaithfulCore

open Set

variable {E : Type*} [Finite E]

/-- Faithful closed sets at one cardinality level. -/
def faithfulLevel
    (c : OpConjecture.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) :
    Set c.Closeds :=
  {C | Faithful (C : Set E) ∧ (C : Set E).ncard = n}

/-- The number of faithful closed sets at one level. -/
def faithfulLevelCount
    (c : OpConjecture.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) : ℕ :=
  (faithfulLevel c Faithful n).ncard

/--
A supplied minimal faithful closed core.  The core is already an element of
`c.Closeds`; `core_le` is its containment in every faithful closed set.
-/
structure Data
    (c : OpConjecture.SetClosure E)
    (Faithful : Set E → Prop) where
  core : c.Closeds
  core_faithful : Faithful (core : Set E)
  core_le :
    ∀ C : c.Closeds, Faithful (C : Set E) →
      (core : Set E) ⊆ (C : Set E)

/--
If faithfulness of closed sets is exactly containment of a fixed seed set,
then the closure of those seeds is the minimal faithful core.
-/
def Data.of_closed_iff_contains
    (c : OpConjecture.SetClosure E)
    (Faithful : Set E → Prop)
    (Seeds : Set E)
    (hFaithful :
      ∀ C : c.Closeds,
        Faithful (C : Set E) ↔ Seeds ⊆ (C : Set E)) :
    Data c Faithful where
  core := ⟨c Seeds, c.isClosed_closure Seeds⟩
  core_faithful :=
    (hFaithful ⟨c Seeds, c.isClosed_closure Seeds⟩).2
      (c.le_closure Seeds)
  core_le := by
    intro C hC
    exact c.closure_min ((hFaithful C).1 hC) C.property

/-- The special case in which faithfulness is defined as containing seeds. -/
def Data.of_contains
    (c : OpConjecture.SetClosure E)
    (Seeds : Set E) :
    Data c (fun C ↦ Seeds ⊆ C) :=
  Data.of_closed_iff_contains c (fun C ↦ Seeds ⊆ C) Seeds
    (fun _ ↦ Iff.rfl)

omit [Finite E] in
/--
For an upward-closed faithfulness predicate, a closed set is faithful exactly
when it contains the supplied minimal faithful core.
-/
theorem Data.faithful_iff_core_subset
    {c : OpConjecture.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful)
    (hFaithful : Monotone Faithful)
    (C : c.Closeds) :
    Faithful (C : Set E) ↔
      (D.core : Set E) ⊆ (C : Set E) := by
  constructor
  · exact D.core_le C
  · exact fun h ↦ hFaithful h D.core_faithful

/-- The faithful count is bounded by the full closure-system level count. -/
theorem faithfulLevelCount_le_levelCount
    (c : OpConjecture.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) :
    faithfulLevelCount c Faithful n ≤ c.levelCount n := by
  classical
  letI : Fintype c.Closeds := Fintype.ofFinite c.Closeds
  unfold faithfulLevelCount faithfulLevel
  unfold OpConjecture.SetClosure.levelCount
  exact Set.ncard_le_ncard
    (fun _ hC ↦ hC.2)
    (Set.toFinite _)

/-- No faithful closed set lies below the cardinality of its minimal core. -/
theorem faithfulLevelCount_eq_zero_of_lt_core
    {c : OpConjecture.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful) {n : ℕ}
    (hn : n < (D.core : Set E).ncard) :
    faithfulLevelCount c Faithful n = 0 := by
  classical
  have hlevel : faithfulLevel c Faithful n = ∅ := by
    ext C
    constructor
    · intro hC
      change
        Faithful (C : Set E) ∧ (C : Set E).ncard = n
        at hC
      have hle :
          (D.core : Set E).ncard ≤ (C : Set E).ncard :=
        Set.ncard_le_ncard (D.core_le C hC.1)
      omega
    · simp
  rw [faithfulLevelCount, hlevel]
  simp

/-- At the core's cardinality, the core is the unique faithful closed set. -/
theorem faithfulLevelCount_eq_one_of_eq_core
    {c : OpConjecture.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful) {n : ℕ}
    (hn : n = (D.core : Set E).ncard) :
    faithfulLevelCount c Faithful n = 1 := by
  classical
  have hlevel : faithfulLevel c Faithful n = {D.core} := by
    ext C
    constructor
    · intro hC
      change
        Faithful (C : Set E) ∧ (C : Set E).ncard = n
        at hC
      have hsets :
          (D.core : Set E) = (C : Set E) :=
        Set.eq_of_subset_of_ncard_le
          (D.core_le C hC.1)
          (by rw [hC.2, hn])
      exact Set.mem_singleton_iff.mpr (Subtype.ext hsets.symm)
    · intro hC
      have hCeq : C = D.core := Set.mem_singleton_iff.mp hC
      subst C
      exact ⟨D.core_faithful, hn.symm⟩
  rw [faithfulLevelCount, hlevel]
  simp

/--
Equal core cardinalities force equality of faithful level counts at and below
the two cores.  Taking `n = 4` gives precisely the formal `d > 4` and `d = 4`
deduction, once the two module-theoretic cores have been constructed.
-/
theorem faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
    {cQ cS : OpConjecture.SetClosure E}
    {FaithfulQ FaithfulS : Set E → Prop}
    (Q : Data cQ FaithfulQ) (S : Data cS FaithfulS)
    (hcard :
      (Q.core : Set E).ncard = (S.core : Set E).ncard)
    {n : ℕ} (hn : n ≤ (Q.core : Set E).ncard) :
    faithfulLevelCount cQ FaithfulQ n =
      faithfulLevelCount cS FaithfulS n := by
  rcases hn.eq_or_lt with hn | hn
  · rw [faithfulLevelCount_eq_one_of_eq_core Q hn,
      faithfulLevelCount_eq_one_of_eq_core S (hn.trans hcard)]
  · rw [faithfulLevelCount_eq_zero_of_lt_core Q hn,
      faithfulLevelCount_eq_zero_of_lt_core S (hcard ▸ hn)]

end MinimalFaithfulCore

/-! ## Finite support for a joint stratification -/

namespace FiniteJointStratification

variable {L R I : Type*} [Fintype L] [Fintype R]

/--
The finite union of the values actually realized by two finite types.  The
ambient index type `I` need not be finite.
-/
def JointRange (left : L → I) (right : R → I) :=
  {i : I // i ∈ Set.range left ∪ Set.range right}

instance jointRangeFinite (left : L → I) (right : R → I) :
    Finite (JointRange left right) :=
  ((Set.finite_range left).union (Set.finite_range right)).to_subtype

noncomputable instance jointRangeFintype
    (left : L → I) (right : R → I) :
    Fintype (JointRange left right) :=
  Fintype.ofFinite (JointRange left right)

/-- Lift the left indexing map to the finite joint range. -/
def toJointLeft
    (left : L → I) (right : R → I) (x : L) :
    JointRange left right :=
  ⟨left x, Set.mem_union_left _ ⟨x, rfl⟩⟩

/-- Lift the right indexing map to the finite joint range. -/
def toJointRight
    (left : L → I) (right : R → I) (x : R) :
    JointRange left right :=
  ⟨right x, Set.mem_union_right _ ⟨x, rfl⟩⟩

/-- One left fiber over the finite joint range. -/
def LeftFiber
    (left : L → I) (right : R → I)
    (i : JointRange left right) :=
  {x : L // toJointLeft left right x = i}

instance leftFiberFinite
    (left : L → I) (right : R → I)
    (i : JointRange left right) :
    Finite (LeftFiber left right i) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- One right fiber over the finite joint range. -/
def RightFiber
    (left : L → I) (right : R → I)
    (i : JointRange left right) :=
  {x : R // toJointRight left right x = i}

instance rightFiberFinite
    (left : L → I) (right : R → I)
    (i : JointRange left right) :
    Finite (RightFiber left right i) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Exact finite partition of the left type by its realized index. -/
theorem card_eq_sum_leftFibers
    (left : L → I) (right : R → I) :
    Fintype.card L =
      ∑ i : JointRange left right,
        Nat.card (LeftFiber left right i) := by
  classical
  calc
    Fintype.card L = Nat.card L :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card
        (Σ i : JointRange left right, LeftFiber left right i) :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv (toJointLeft left right)).symm
    _ = ∑ i : JointRange left right,
        Nat.card (LeftFiber left right i) :=
      Nat.card_sigma

/-- Exact finite partition of the right type by its realized index. -/
theorem card_eq_sum_rightFibers
    (left : L → I) (right : R → I) :
    Fintype.card R =
      ∑ i : JointRange left right,
        Nat.card (RightFiber left right i) := by
  classical
  calc
    Fintype.card R = Nat.card R :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card
        (Σ i : JointRange left right, RightFiber left right i) :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv (toJointRight left right)).symm
    _ = ∑ i : JointRange left right,
        Nat.card (RightFiber left right i) :=
      Nat.card_sigma

/-- Fiberwise equality on the joint range implies equality of total sizes. -/
theorem card_eq_of_fiber_card_eq
    (left : L → I) (right : R → I)
    (h : ∀ i : JointRange left right,
      Nat.card (LeftFiber left right i) =
        Nat.card (RightFiber left right i)) :
    Fintype.card L = Fintype.card R := by
  rw [card_eq_sum_leftFibers left right,
    card_eq_sum_rightFibers left right]
  exact Finset.sum_congr rfl fun i _ ↦ h i

end FiniteJointStratification

/-! ## Simultaneous total/faithful induction for annihilator strata -/

namespace AnnihilatorInduction

variable {B : Type*}
  (measure : B → ℕ)
  (totalQ totalS faithfulQ faithfulS : B → ℕ)
  (ProperFactor : B → Type*)
  [∀ b : B, Fintype (ProperFactor b)]
  (factor : ∀ b : B, ProperFactor b → B)
  (Connected : B → Prop)

/--
The simultaneous induction pattern matching the manuscript's annihilator
decomposition.

The recurrences use the faithful counts of proper factors:

`total(b) = faithful(b) + sum_I faithful(factor(b,I))`.

At a connected object, the representation-theoretic branch supplies equality
of the current faithful counts.  At a disconnected object, product
decomposition supplies equality of the current total counts from smaller
total equalities.  The recurrence and the smaller faithful equalities recover
the other equality in either branch.
-/
theorem total_and_faithful_eq_of_recurrence
    (hsmaller :
      ∀ (b : B) (I : ProperFactor b),
        measure (factor b I) < measure b)
    (hQ :
      ∀ b : B,
        totalQ b =
          faithfulQ b +
            ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS :
      ∀ b : B,
        totalS b =
          faithfulS b +
            ∑ I : ProperFactor b, faithfulS (factor b I))
    (hconnected :
      ∀ b : B, Connected b →
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b' ∧
            faithfulQ b' = faithfulS b') →
        faithfulQ b = faithfulS b)
    (hdisconnected :
      ∀ b : B, ¬ Connected b →
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b') →
        totalQ b = totalS b)
    (b : B) :
    totalQ b = totalS b ∧
      faithfulQ b = faithfulS b := by
  classical
  induction hμ : measure b using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have ihPair :
          ∀ b' : B, measure b' < measure b →
            totalQ b' = totalS b' ∧
              faithfulQ b' = faithfulS b' := by
        intro b' hb'
        exact ih (measure b') (by simpa [hμ] using hb') b' rfl
      have hfactor :
          ∀ I : ProperFactor b,
            faithfulQ (factor b I) =
              faithfulS (factor b I) := by
        intro I
        exact (ihPair (factor b I) (hsmaller b I)).2
      have hsum :
          (∑ I : ProperFactor b, faithfulQ (factor b I)) =
            ∑ I : ProperFactor b, faithfulS (factor b I) := by
        apply Finset.sum_congr rfl
        intro I _
        exact hfactor I
      by_cases hb : Connected b
      · have hf : faithfulQ b = faithfulS b :=
          hconnected b hb ihPair
        have ht : totalQ b = totalS b := by
          rw [hQ b, hS b, hf, hsum]
        exact ⟨ht, hf⟩
      · have ht : totalQ b = totalS b :=
          hdisconnected b hb fun b' hb' ↦ (ihPair b' hb').1
        have hadd :
            faithfulQ b +
                ∑ I : ProperFactor b, faithfulQ (factor b I) =
              faithfulS b +
                ∑ I : ProperFactor b, faithfulS (factor b I) := by
          rw [← hQ b, ← hS b, ht]
        rw [hsum] at hadd
        exact ⟨ht, Nat.add_right_cancel hadd⟩

/-- In a simultaneous annihilator induction, either equality of the
current faithful counts or equality of the current total counts is enough;
the recurrence and smaller faithful equalities recover the other one. -/
theorem total_and_faithful_eq_of_recurrence_of_local_either
    (hsmaller :
      ∀ (b : B) (I : ProperFactor b),
        measure (factor b I) < measure b)
    (hQ :
      ∀ b : B,
        totalQ b =
          faithfulQ b +
            ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS :
      ∀ b : B,
        totalS b =
          faithfulS b +
            ∑ I : ProperFactor b, faithfulS (factor b I))
    (hlocal :
      ∀ b : B,
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b' ∧
            faithfulQ b' = faithfulS b') →
        faithfulQ b = faithfulS b ∨ totalQ b = totalS b)
    (b : B) :
    totalQ b = totalS b ∧ faithfulQ b = faithfulS b := by
  classical
  induction hμ : measure b using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have ihPair :
          ∀ b' : B, measure b' < measure b →
            totalQ b' = totalS b' ∧
              faithfulQ b' = faithfulS b' := by
        intro b' hb'
        exact ih (measure b') (by simpa [hμ] using hb') b' rfl
      have hsum :
          (∑ I : ProperFactor b, faithfulQ (factor b I)) =
            ∑ I : ProperFactor b, faithfulS (factor b I) := by
        apply Finset.sum_congr rfl
        intro I _
        exact (ihPair (factor b I) (hsmaller b I)).2
      rcases hlocal b ihPair with hf | ht
      · have ht : totalQ b = totalS b := by
          rw [hQ b, hS b, hf, hsum]
        exact ⟨ht, hf⟩
      · have hadd :
            faithfulQ b +
                ∑ I : ProperFactor b, faithfulQ (factor b I) =
              faithfulS b +
                ∑ I : ProperFactor b, faithfulS (factor b I) := by
          rw [← hQ b, ← hS b, ht]
        rw [hsum] at hadd
        exact ⟨ht, Nat.add_right_cancel hadd⟩

end AnnihilatorInduction

end OpConjecture.BottomLevels
