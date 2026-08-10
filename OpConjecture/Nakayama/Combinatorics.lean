import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card.Arithmetic
import OpConjecture.ConvexGeometry.LevelPolynomial

/-!
# Product-of-chains combinatorics for the Nakayama formula

This file formalizes the finite combinatorial tail of the Nakayama
formula.  No module-theoretic classification is assumed.

A capacity function `c : ι → ℕ` determines a product of chains
`∏ i, [0, c i]`.  Its grading is the sum of the coordinates.  The main
theorem identifies the grading enumerator with the product of the
corresponding finite geometric sums.
-/

namespace OpConjecture.NakayamaCombinatorics

open Finset Polynomial Set
open scoped BigOperators

universe u v

/-- The finite product of chains with coordinate `i` ranging from
`0` through `c i`. -/
abbrev CapacityVector {ι : Type u} (c : ι → ℕ) :=
  ∀ i, Fin (c i + 1)

/-- The natural rank/size statistic on a product of chains. -/
def capacityWeight {ι : Type u} [Fintype ι]
    {c : ι → ℕ} (x : CapacityVector c) : ℕ :=
  ∑ i, (x i : ℕ)

/-- The cardinality generating polynomial of a product of chains. -/
noncomputable def capacityPolynomial
    {ι : Type u} [Fintype ι] (c : ι → ℕ) : ℕ[X] :=
  by
    classical
    exact ∑ x : CapacityVector c, X ^ capacityWeight x

/-- The factor contributed by one chain of capacity `n`. -/
noncomputable def chainPolynomial (n : ℕ) : ℕ[X] :=
  by
    classical
    exact ∑ k ∈ Finset.range (n + 1), X ^ k

/-- A one-chain factor is the usual finite geometric sum. -/
theorem chainPolynomial_eq_sum_range (n : ℕ) :
    chainPolynomial n = ∑ k ∈ Finset.range (n + 1), X ^ k :=
  rfl

/-- Main product-of-chains generating-polynomial formula. -/
theorem capacityPolynomial_eq_prod_chainPolynomial
    {ι : Type u} [Fintype ι] (c : ι → ℕ) :
    capacityPolynomial c = ∏ i, chainPolynomial (c i) := by
  classical
  calc
    capacityPolynomial c =
        ∑ x : CapacityVector c, ∏ i, X ^ (x i : ℕ) := by
      unfold capacityPolynomial capacityWeight
      congr 1
      funext x
      rw [Finset.prod_pow_eq_pow_sum]
    _ = ∏ i, ∑ k : Fin (c i + 1), X ^ (k : ℕ) :=
      (Fintype.prod_sum fun i (k : Fin (c i + 1)) ↦ X ^ (k : ℕ)).symm
    _ = ∏ i, chainPolynomial (c i) := by
      apply Fintype.prod_congr
      intro i
      rw [chainPolynomial, Fin.sum_univ_eq_sum_range]

/-- The ungraded cardinality of the product is the product of the chain
cardinalities. -/
theorem natCard_capacityVector
    {ι : Type u} [Fintype ι] (c : ι → ℕ) :
    Nat.card (CapacityVector c) = ∏ i, (c i + 1) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp

/-- Reindexing the capacities preserves the grading polynomial. -/
theorem capacityPolynomial_eq_of_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ) (e : ι ≃ κ)
    (h : ∀ i, c i = d (e i)) :
    capacityPolynomial c = capacityPolynomial d := by
  rw [capacityPolynomial_eq_prod_chainPolynomial,
    capacityPolynomial_eq_prod_chainPolynomial]
  exact Fintype.prod_equiv e _ _ fun i ↦ by rw [h i]

/-- The multiset of capacities, retaining multiplicities. -/
def capacityMultiset {ι : Type u} [Fintype ι] (c : ι → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset ι).val.map c

/-- Equality of capacity multisets can be realized by an equivalence of
coordinate types which preserves every capacity. -/
noncomputable def capacityEquivOfMultisetEq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d) : ι ≃ κ := by
  classical
  apply Equiv.ofFiberEquiv (f := c) (g := d)
  intro n
  apply Fintype.equivOfCardEq
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa [capacityMultiset, Multiset.count_map, eq_comm,
    ← Finset.filter_val] using congrArg (Multiset.count n) h

theorem capacityEquivOfMultisetEq_capacity
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d) (i : ι) :
    d (capacityEquivOfMultisetEq c d h i) = c i := by
  classical
  unfold capacityEquivOfMultisetEq
  exact Equiv.ofFiberEquiv_map _ _

/-- Existential form: equal capacity multisets admit a coordinate matching
which preserves the chain lengths. -/
theorem exists_capacityEquiv_of_capacityMultiset_eq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d) :
    ∃ e : ι ≃ κ, ∀ i, c i = d (e i) := by
  exact ⟨capacityEquivOfMultisetEq c d h,
    fun i ↦ (capacityEquivOfMultisetEq_capacity c d h i).symm⟩

/-- Coordinate reindexing along a capacity-preserving equivalence is an
order isomorphism of the corresponding products of chains. -/
noncomputable def capacityVectorOrderIsoOfEquiv
    {ι : Type u} {κ : Type v}
    (c : ι → ℕ) (d : κ → ℕ) (e : ι ≃ κ)
    (h : ∀ i, d (e i) = c i) :
    CapacityVector c ≃o CapacityVector d where
  toEquiv :=
    { toFun := fun x j =>
        Fin.cast (by
          congr 1
          rw [← h (e.symm j), e.apply_symm_apply])
          (x (e.symm j))
      invFun := fun y i =>
        Fin.cast (by congr 1; exact h i) (y (e i))
      left_inv := by
        intro x
        funext i
        apply Fin.ext
        change (x (e.symm (e i))).val = (x i).val
        rw [e.symm_apply_apply]
      right_inv := by
        intro y
        funext j
        apply Fin.ext
        change (y (e (e.symm j))).val = (y j).val
        rw [e.apply_symm_apply] }
  map_rel_iff' := by
    intro x y
    constructor
    · intro hxy i
      have hcoordinate := hxy (e i)
      change x (e.symm (e i)) ≤ y (e.symm (e i)) at hcoordinate
      rw [e.symm_apply_apply] at hcoordinate
      exact hcoordinate
    · intro hxy j
      exact hxy (e.symm j)

/-- Equality of the multisets of chain capacities determines the entire
product-of-chains poset, not only its rank polynomial. -/
noncomputable def capacityVectorOrderIsoOfMultisetEq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d) :
    CapacityVector c ≃o CapacityVector d :=
  capacityVectorOrderIsoOfEquiv c d
    (capacityEquivOfMultisetEq c d h)
    (capacityEquivOfMultisetEq_capacity c d h)

/-- Coordinate reindexing preserves the sum-of-coordinates grading. -/
theorem capacityWeight_capacityVectorOrderIsoOfEquiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ) (e : ι ≃ κ)
    (h : ∀ i, d (e i) = c i) (x : CapacityVector c) :
    capacityWeight (capacityVectorOrderIsoOfEquiv c d e h x) =
      capacityWeight x := by
  classical
  unfold capacityWeight
  apply Fintype.sum_equiv e.symm
  intro j
  rfl

/-- The order isomorphism selected from equal capacity multisets preserves
the sum-of-coordinates grading. -/
theorem capacityWeight_capacityVectorOrderIsoOfMultisetEq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d)
    (x : CapacityVector c) :
    capacityWeight (capacityVectorOrderIsoOfMultisetEq c d h x) =
      capacityWeight x :=
  capacityWeight_capacityVectorOrderIsoOfEquiv c d
    (capacityEquivOfMultisetEq c d h)
    (capacityEquivOfMultisetEq_capacity c d h) x

/-- The product formula depends only on the multiset of capacities. -/
theorem capacityPolynomial_eq_of_capacityMultiset_eq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (h : capacityMultiset c = capacityMultiset d) :
    capacityPolynomial c = capacityPolynomial d := by
  rw [capacityPolynomial_eq_prod_chainPolynomial,
    capacityPolynomial_eq_prod_chainPolynomial]
  have hmapped :
      (capacityMultiset c).map chainPolynomial =
        (capacityMultiset d).map chainPolynomial :=
    congrArg (Multiset.map chainPolynomial) h
  simpa [capacityMultiset] using congrArg Multiset.prod hmapped

/-! ## Recovering capacities from composition-length counts -/

/-- The number of chains whose capacity is at least `n`.  In the
Nakayama application this is the number of indecomposables of
composition length `n`. -/
def capacityAtLeastCount {ι : Type u} [Fintype ι]
    (c : ι → ℕ) (n : ℕ) : ℕ :=
  (capacityMultiset c).countP fun m ↦ n ≤ m

private theorem count_add_countP_succ_eq_countP
    (s : Multiset ℕ) (n : ℕ) :
    s.count n + s.countP (fun m ↦ n < m) =
      s.countP (fun m ↦ n ≤ m) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      by_cases han : a = n
      · subst a
        simp only [Multiset.count_cons, Multiset.countP_cons]
        simp only [if_pos (Nat.le_refl n),
          if_neg (Nat.lt_irrefl n)]
        calc
          (s.count n + 1) +
                s.countP (fun m ↦ n < m) =
              (s.count n +
                s.countP (fun m ↦ n < m)) + 1 := by
            ac_rfl
          _ = s.countP (fun m ↦ n ≤ m) + 1 := by
            rw [ih]
      · by_cases hge : n + 1 ≤ a
        · have hle : n ≤ a := by omega
          have hlt : n < a := by omega
          have hne : n ≠ a := Ne.symm han
          simp only [Multiset.count_cons, Multiset.countP_cons,
            if_neg hne, if_pos hlt, if_pos hle]
          have ih' := congrArg (fun k ↦ k + 1) ih
          omega
        · have hnotle : ¬n ≤ a := by omega
          have hnotlt : ¬n < a := fun h ↦ hnotle h.le
          have hne : n ≠ a := Ne.symm han
          simp only [Multiset.count_cons, Multiset.countP_cons,
            if_neg hne, if_neg hnotlt, if_neg hnotle]
          exact ih

/-- Equality of all composition-length counts determines the multiset of
chain capacities, including multiplicities of zero capacities. -/
theorem capacityMultiset_eq_of_atLeastCount_eq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (hcount : ∀ n, capacityAtLeastCount c n =
      capacityAtLeastCount d n) :
    capacityMultiset c = capacityMultiset d := by
  apply Multiset.ext.mpr
  intro n
  have hc :
      (capacityMultiset c).count n +
          capacityAtLeastCount c (n + 1) =
        capacityAtLeastCount c n := by
    simpa [capacityAtLeastCount] using
      count_add_countP_succ_eq_countP
        (capacityMultiset c) n
  have hd :
      (capacityMultiset d).count n +
          capacityAtLeastCount d (n + 1) =
        capacityAtLeastCount d n := by
    simpa [capacityAtLeastCount] using
      count_add_countP_succ_eq_countP
        (capacityMultiset d) n
  have hn := hcount n
  have hsucc := hcount (n + 1)
  omega

/-- The product-of-chains polynomials agree as soon as all
composition-length counts agree. -/
theorem capacityPolynomial_eq_of_atLeastCount_eq
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (c : ι → ℕ) (d : κ → ℕ)
    (hcount : ∀ n, capacityAtLeastCount c n =
      capacityAtLeastCount d n) :
    capacityPolynomial c = capacityPolynomial d :=
  capacityPolynomial_eq_of_capacityMultiset_eq c d
    (capacityMultiset_eq_of_atLeastCount_eq c d hcount)

/-! ## Explicit fixed-top-chain supports -/

/-- The disjoint union of the `c i` actual points in the fixed-top chains.
The additional `+1` in `CapacityVector c` accounts for choosing the empty
initial segment. -/
abbrev ChainPoint {ι : Type u} (c : ι → ℕ) :=
  Σ i, Fin (c i)

/-- The union of the initial segments selected by a capacity vector. -/
def initialSegment {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) : Set (ChainPoint c) :=
  {p | (p.2 : ℕ) < (x p.1 : ℕ)}

/-- The subtype of a selected initial segment is explicitly the sigma type
whose `i`-th fiber has size `x i`. -/
def selectedPointEquiv {ι : Type u} {c : ι → ℕ}
    (x : CapacityVector c) :
    (Σ i, Fin (x i : ℕ)) ≃ ↥(initialSegment x) where
  toFun p := by
    refine ⟨⟨p.1, ⟨p.2, ?_⟩⟩, p.2.isLt⟩
    have hx := (x p.1).isLt
    omega
  invFun p :=
    ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  left_inv p := rfl
  right_inv p := rfl

/-- The selected support has cardinality equal to the sum of the chosen
initial-segment lengths. -/
theorem ncard_initialSegment
    {ι : Type u} [Fintype ι] {c : ι → ℕ}
    (x : CapacityVector c) :
    (initialSegment x).ncard = capacityWeight x := by
  classical
  calc
    (initialSegment x).ncard = Nat.card ↥(initialSegment x) := by
      rw [Nat.card_coe_set_eq]
    _ = Nat.card (Σ i, Fin (x i : ℕ)) :=
      Nat.card_congr (selectedPointEquiv x).symm
    _ = ∑ i, (x i : ℕ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    _ = capacityWeight x := rfl

/-! ## Closure-system interface -/

/-- An explicit fixed-top-chain parametrization of a finite closure system.

The order isomorphism says that closed sets form the product of chains.
The carrier equation records that coordinate `x i` selects exactly the
first `x i` points in the `i`-th chain.
-/
structure FixedTopChainParametrization
    {ι : Type u} [Fintype ι] {E : Type v} [Finite E]
    (cl : OpConjecture.SetClosure E) (c : ι → ℕ) where
  pointEquiv : ChainPoint c ≃ E
  closedOrderIso : CapacityVector c ≃o cl.Closeds
  carrier_closedOrderIso (x : CapacityVector c) :
    (((closedOrderIso x : cl.Closeds) : Set E)) =
      pointEquiv '' initialSegment x

namespace FixedTopChainParametrization

variable {ι : Type u} [Fintype ι] {E : Type v} [Finite E]
  {cl : OpConjecture.SetClosure E} {c : ι → ℕ}
  (p : FixedTopChainParametrization cl c)

/-- The closed set corresponding to `x` has size equal to the sum of its
chain coordinates. -/
theorem ncard_closedOrderIso (x : CapacityVector c) :
    (((p.closedOrderIso x : cl.Closeds) : Set E)).ncard =
      capacityWeight x := by
  rw [p.carrier_closedOrderIso x,
    Set.ncard_image_of_injective _ p.pointEquiv.injective,
    ncard_initialSegment]

/-- Any closure system with an explicit fixed-top-chain parametrization has
the product-of-geometric-sums level polynomial. -/
theorem levelPolynomial_eq_prod_chainPolynomial
    (p : FixedTopChainParametrization cl c) :
    cl.levelPolynomial = ∏ i, chainPolynomial (c i) := by
  classical
  let e : CapacityVector c ≃ cl.Closeds := p.closedOrderIso.toEquiv
  rw [OpConjecture.SetClosure.levelPolynomial_eq_sum_stat
    cl e capacityWeight (ncard_closedOrderIso p)]
  exact capacityPolynomial_eq_prod_chainPolynomial c

end FixedTopChainParametrization


end OpConjecture.NakayamaCombinatorics
