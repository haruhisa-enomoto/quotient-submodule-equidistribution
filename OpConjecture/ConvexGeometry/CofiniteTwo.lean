import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import OpConjecture.ConvexGeometry.Basic

/-!
# Two-point complements in a convex geometry

This file isolates the closure-theoretic core of the manuscript's
cofinite-two argument.  It does not identify the mixed boundary term with
irreducible maps; that requires Auslander--Reiten theory absent from the
current package.
-/

noncomputable section

open Set

namespace OpConjecture.SetClosure

universe u

variable {E : Type u} (c : SetClosure E)

/-- A point whose deletion from the top closed set remains closed. -/
def IsTopExtreme (x : E) : Prop :=
  x ∈ c.extremePoints Set.univ

/-- A point is top extreme exactly when deleting just that point leaves a
closed set. -/
theorem isTopExtreme_iff_isClosed_compl_singleton (x : E) :
    c.IsTopExtreme x ↔ c.IsClosed ({x} : Set E)ᶜ := by
  calc
    c.IsTopExtreme x ↔
        c.IsClosed (Set.univ \ ({x} : Set E)) :=
      mem_extremePoints_iff_isClosed_sdiff_singleton
        c.isClosed_top (Set.mem_univ x)
    _ ↔ c.IsClosed ({x} : Set E)ᶜ := by
      have hset :
          Set.univ \ ({x} : Set E) = ({x} : Set E)ᶜ := by
        ext y
        simp
      rw [hset]

/-- Complements of arbitrary sets of top extreme points are closed. -/
theorem isClosed_compl_of_subset_topExtreme
    {D : Set E} (hD : ∀ x ∈ D, c.IsTopExtreme x) :
    c.IsClosed Dᶜ := by
  rw [ClosureOperator.isClosed_iff]
  apply Set.Subset.antisymm
  · intro z hz
    rw [Set.mem_compl_iff]
    intro hzD
    have hzextreme : z ∈ c.extremePoints Set.univ :=
      hD z hzD
    have hzclosed : c.IsClosed (Set.univ \ {z}) :=
      (mem_extremePoints_iff_isClosed_sdiff_singleton
        (c.isClosed_top) (Set.mem_univ z)).1 hzextreme
    have hsubset : Dᶜ ⊆ Set.univ \ {z} := by
      intro y hy
      refine ⟨Set.mem_univ y, ?_⟩
      intro hyz
      exact hy (hyz ▸ hzD)
    have hzdel : z ∈ Set.univ \ {z} :=
      c.closure_min hsubset hzclosed hz
    exact hzdel.2 (Set.mem_singleton z)
  · exact c.le_closure Dᶜ

/-- If deleting two distinct points leaves a closed set in an
anti-exchange closure, at least one deleted point is top extreme. -/
theorem isTopExtreme_or_isTopExtreme_of_isClosed_compl_pair
    (hae : c.IsAntiExchange) {x y : E} (hxy : x ≠ y)
    (hclosed : c.IsClosed ({x, y} : Set E)ᶜ) :
    c.IsTopExtreme x ∨ c.IsTopExtreme y := by
  by_contra h
  push Not at h
  obtain ⟨hxnot, hynot⟩ := h
  have hxgen : x ∈ c (Set.univ \ {x}) := by
    rw [IsTopExtreme, mem_extremePoints] at hxnot
    push Not at hxnot
    exact hxnot (Set.mem_univ x)
  have hygen : y ∈ c (Set.univ \ {y}) := by
    rw [IsTopExtreme, mem_extremePoints] at hynot
    push Not at hynot
    exact hynot (Set.mem_univ y)
  let K : Set E := ({x, y} : Set E)ᶜ
  have hxK : x ∉ K := by simp [K]
  have hyK : y ∉ K := by simp [K]
  have hxavail : x ∈ c (insert y K) := by
    apply c.monotone ?_ hxgen
    intro z hz
    by_cases hzy : z = y
    · exact hzy ▸ Set.mem_insert y K
    · exact Set.mem_insert_of_mem y (by
        simp only [K, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact fun hzpair ↦ hzpair.elim hz.2 hzy)
  have hyavail : y ∈ c (insert x K) := by
    apply c.monotone ?_ hygen
    intro z hz
    by_cases hzx : z = x
    · exact hzx ▸ Set.mem_insert x K
    · exact Set.mem_insert_of_mem x (by
        simp only [K, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        exact fun hzpair ↦ hzpair.elim hzx hz.2)
  exact
    (hae (by simpa only [K] using hclosed)
      hxK hyK hxy hxavail) hyavail

section Finite

variable [Fintype E] [DecidableEq E]

/-- The finite set of top extreme points. -/
def topExtremeFinset : Finset E :=
  by
    classical
    exact Finset.univ.filter c.IsTopExtreme

omit [DecidableEq E] in
@[simp]
theorem mem_topExtremeFinset {x : E} :
    x ∈ c.topExtremeFinset ↔ c.IsTopExtreme x := by
  classical
  simp [topExtremeFinset]

/-- All unordered two-point deletion sets. -/
def twoDeletions : Finset (Finset E) :=
  by
    classical
    exact Finset.univ.powersetCard 2

omit [DecidableEq E] in
@[simp]
theorem mem_twoDeletions {D : Finset E} :
    D ∈ twoDeletions (E := E) ↔ D.card = 2 := by
  classical
  simp [twoDeletions]

/-- Two-point deletions whose complements are closed. -/
def cofiniteTwoDeletions : Finset (Finset E) :=
  by
    classical
    exact (twoDeletions (E := E)).filter fun D ↦
      c.IsClosed ((D : Set E)ᶜ)

omit [DecidableEq E] in
@[simp]
theorem mem_cofiniteTwoDeletions {D : Finset E} :
    D ∈ c.cofiniteTwoDeletions ↔
      D.card = 2 ∧ c.IsClosed ((D : Set E)ᶜ) := by
  classical
  simp [cofiniteTwoDeletions]

/-- Unordered pairs of top extreme points. -/
def topExtremePairs : Finset (Finset E) :=
  by
    classical
    exact c.topExtremeFinset.powersetCard 2

omit [DecidableEq E] in
@[simp]
theorem mem_topExtremePairs {D : Finset E} :
    D ∈ c.topExtremePairs ↔
      D.card = 2 ∧ ∀ x ∈ D, c.IsTopExtreme x := by
  classical
  rw [topExtremePairs, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact
      ⟨hcard, fun x hx ↦
        (mem_topExtremeFinset (c := c)).1 (hsub hx)⟩
  · rintro ⟨hcard, hmem⟩
    exact
      ⟨fun x hx ↦
        (mem_topExtremeFinset (c := c)).2 (hmem x hx),
        hcard⟩

/-- The top-extreme part of a finite deletion set. -/
def topExtremePart (D : Finset E) : Finset E :=
  by
    classical
    exact D.filter c.IsTopExtreme

omit [Fintype E] [DecidableEq E] in
@[simp]
theorem mem_topExtremePart {D : Finset E} {x : E} :
    x ∈ c.topExtremePart D ↔ x ∈ D ∧ c.IsTopExtreme x := by
  classical
  simp [topExtremePart]

/-- The mixed boundary term: allowed two-point deletions containing
exactly one top extreme point. -/
def mixedBoundaryDeletions : Finset (Finset E) :=
  by
    classical
    exact c.cofiniteTwoDeletions.filter fun D ↦
      (c.topExtremePart D).card = 1

omit [DecidableEq E] in
@[simp]
theorem mem_mixedBoundaryDeletions {D : Finset E} :
    D ∈ c.mixedBoundaryDeletions ↔
      D.card = 2 ∧ c.IsClosed ((D : Set E)ᶜ) ∧
        (c.topExtremePart D).card = 1 := by
  classical
  simp [mixedBoundaryDeletions, and_assoc]

/-- The number of allowed unordered two-point deletion sets. -/
def cofiniteTwoCount : ℕ :=
  c.cofiniteTwoDeletions.card

/-- The closure-theoretic boundary count. -/
def mixedBoundaryCount : ℕ :=
  c.mixedBoundaryDeletions.card

/-- An allowed mixed deletion, oriented with its unique top extreme point
first. -/
def MixedBoundaryPair :=
  {p : E × E //
    c.IsTopExtreme p.1 ∧ ¬ c.IsTopExtreme p.2 ∧
      c.IsClosed ({p.1, p.2} : Set E)ᶜ}

namespace MixedBoundaryPair

omit [Fintype E] [DecidableEq E] in
/-- The two entries of an oriented mixed boundary pair are distinct. -/
theorem ne (p : c.MixedBoundaryPair) : p.1.1 ≠ p.1.2 := by
  intro h
  exact p.2.2.1 (h ▸ p.2.1)

end MixedBoundaryPair

omit [Fintype E] in
private theorem mixedBoundaryPair_eq_of_pair_eq
    (p q : c.MixedBoundaryPair)
    (h : ({p.1.1, p.1.2} : Finset E) = {q.1.1, q.1.2}) :
    p = q := by
  apply Subtype.ext
  apply Prod.ext
  · have hmem : q.1.1 ∈ ({p.1.1, p.1.2} : Finset E) := by
      rw [h]
      simp
    rcases (by simpa using hmem) with hqp | hqp
    · exact hqp.symm
    · exact (p.2.2.1 (hqp ▸ q.2.1)).elim
  · have hmem : q.1.2 ∈ ({p.1.1, p.1.2} : Finset E) := by
      rw [h]
      simp
    rcases (by simpa using hmem) with hqp | hqp
    · exact (q.2.2.1 (hqp ▸ p.2.1)).elim
    · exact hqp.symm

private theorem mixedBoundaryPair_mem (p : c.MixedBoundaryPair) :
    ({p.1.1, p.1.2} : Finset E) ∈ c.mixedBoundaryDeletions := by
  rw [mem_mixedBoundaryDeletions]
  refine ⟨by simp [p.ne], by simpa using p.2.2.2, ?_⟩
  have hpart :
      c.topExtremePart ({p.1.1, p.1.2} : Finset E) = {p.1.1} := by
    ext x
    simp only [mem_topExtremePart, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hxp | hxn, hxext⟩
      · exact hxp
      · subst x
        exact (p.2.2.1 hxext).elim
    · intro hxp
      subst x
      exact ⟨Or.inl rfl, p.2.1⟩
  rw [hpart]
  simp

private theorem exists_mixedBoundaryPair
    (D : {D : Finset E // D ∈ c.mixedBoundaryDeletions}) :
    ∃ p : c.MixedBoundaryPair,
      D.1 = {p.1.1, p.1.2} := by
  have hdata := (mem_mixedBoundaryDeletions (c := c)).1 D.2
  obtain ⟨x, y, hxy, hD⟩ := Finset.card_eq_two.mp hdata.1
  have hclosed : c.IsClosed ({x, y} : Set E)ᶜ := by
    simpa [hD] using hdata.2.1
  by_cases hx : c.IsTopExtreme x
  · have hy : ¬ c.IsTopExtreme y := by
      intro hy
      have hpart : c.topExtremePart D.1 = D.1 := by
        ext z
        simp only [mem_topExtremePart, and_iff_left_iff_imp]
        intro hz
        rw [hD] at hz
        rcases Finset.mem_insert.mp hz with hzx | hzy
        · exact hzx ▸ hx
        · exact (Finset.mem_singleton.mp hzy) ▸ hy
      have hcard := hdata.2.2
      rw [hpart, hdata.1] at hcard
      omega
    exact ⟨⟨(x, y), hx, hy, hclosed⟩, hD⟩
  · have hy : c.IsTopExtreme y := by
      by_contra hy
      have hpart : c.topExtremePart D.1 = ∅ := by
        ext z
        simp only [mem_topExtremePart]
        constructor
        · rintro ⟨hz, hzext⟩
          rw [hD] at hz
          rcases Finset.mem_insert.mp hz with hzx | hzy
          · exact (hx (hzx ▸ hzext)).elim
          · exact (hy ((Finset.mem_singleton.mp hzy) ▸ hzext)).elim
        · simp
      have hcard := hdata.2.2
      rw [hpart] at hcard
      simp at hcard
    have hclosed' : c.IsClosed ({y, x} : Set E)ᶜ := by
      simpa [Set.pair_comm] using hclosed
    refine ⟨⟨(y, x), hy, hx, hclosed'⟩, ?_⟩
    simpa [Finset.pair_comm] using hD

/-- Mixed deletions are canonically oriented by putting their unique top
extreme point first. -/
noncomputable def mixedBoundaryDeletionEquivMixedBoundaryPair :
    {D : Finset E // D ∈ c.mixedBoundaryDeletions} ≃
      c.MixedBoundaryPair where
  toFun D := Classical.choose (exists_mixedBoundaryPair c D)
  invFun p := ⟨{p.1.1, p.1.2}, mixedBoundaryPair_mem c p⟩
  left_inv D := by
    apply Subtype.ext
    exact (Classical.choose_spec (exists_mixedBoundaryPair c D)).symm
  right_inv p := by
    apply mixedBoundaryPair_eq_of_pair_eq c
    exact (Classical.choose_spec
      (exists_mixedBoundaryPair c
        ⟨{p.1.1, p.1.2}, mixedBoundaryPair_mem c p⟩)).symm

/-- The mixed-boundary count is the natural cardinality of the canonically
oriented mixed pairs. -/
theorem mixedBoundaryCount_eq_natCard_mixedBoundaryPair :
    c.mixedBoundaryCount = Nat.card c.MixedBoundaryPair := by
  unfold mixedBoundaryCount
  rw [← Fintype.card_coe]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mixedBoundaryDeletionEquivMixedBoundaryPair c)

omit [DecidableEq E] in
/-- Every pair of top extreme points is an allowed deletion. -/
theorem topExtremePairs_subset_cofiniteTwoDeletions :
    c.topExtremePairs ⊆ c.cofiniteTwoDeletions := by
  classical
  intro D hD
  rw [mem_cofiniteTwoDeletions]
  have hpair := (mem_topExtremePairs (c := c)).1 hD
  refine ⟨hpair.1, ?_⟩
  exact
    isClosed_compl_of_subset_topExtreme c fun x hxD ↦
      hpair.2 x hxD

/-- The exact two-deletion partition: an allowed pair consists either of
two top extreme points or of exactly one top extreme point. -/
theorem cofiniteTwoDeletions_eq_topExtremePairs_union_mixedBoundary
    (hae : c.IsAntiExchange) :
    c.cofiniteTwoDeletions =
      c.topExtremePairs ∪ c.mixedBoundaryDeletions := by
  classical
  ext D
  constructor
  · intro hD
    have hdata := (mem_cofiniteTwoDeletions (c := c)).1 hD
    obtain ⟨x, y, hxy, rfl⟩ :=
      Finset.card_eq_two.mp hdata.1
    have hclosed :
        c.IsClosed ((({x, y} : Finset E) : Set E)ᶜ) :=
      hdata.2
    have hextreme :=
      isTopExtreme_or_isTopExtreme_of_isClosed_compl_pair
        c hae hxy (by simpa using hclosed)
    rcases hextreme with hx | hy
    · by_cases hy' : c.IsTopExtreme y
      · apply Finset.mem_union_left
        simp [hxy, hx, hy']
      · apply Finset.mem_union_right
        rw [mem_mixedBoundaryDeletions]
        refine ⟨by simp [hxy], by simpa using hclosed, ?_⟩
        have hpart :
            c.topExtremePart ({x, y} : Finset E) = {x} := by
          ext z
          simp only [mem_topExtremePart, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hzx | hzy, hzext⟩
            · exact hzx
            · subst z
              exact (hy' hzext).elim
          · intro hzx
            subst z
            exact ⟨Or.inl rfl, hx⟩
        rw [hpart]
        simp
    · by_cases hx' : c.IsTopExtreme x
      · apply Finset.mem_union_left
        simp [hxy, hx', hy]
      · apply Finset.mem_union_right
        rw [mem_mixedBoundaryDeletions]
        refine ⟨by simp [hxy], by simpa using hclosed, ?_⟩
        have hpart :
            c.topExtremePart ({x, y} : Finset E) = {y} := by
          ext z
          simp only [mem_topExtremePart, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨hzx | hzy, hzext⟩
            · subst z
              exact (hx' hzext).elim
            · exact hzy
          · intro hzy
            subst z
            exact ⟨Or.inr rfl, hy⟩
        rw [hpart]
        simp
  · intro hD
    rcases Finset.mem_union.mp hD with htop | hmixed
    · exact topExtremePairs_subset_cofiniteTwoDeletions c htop
    · have hmixed' :=
        (mem_mixedBoundaryDeletions (c := c)).1 hmixed
      exact
        (mem_cofiniteTwoDeletions (c := c)).2
          ⟨hmixed'.1, hmixed'.2.1⟩

omit [DecidableEq E] in
/-- The two parts of the partition are disjoint. -/
theorem disjoint_topExtremePairs_mixedBoundary :
    Disjoint c.topExtremePairs c.mixedBoundaryDeletions := by
  classical
  rw [Finset.disjoint_left]
  intro D htop hmixed
  have htop' := (mem_topExtremePairs (c := c)).1 htop
  have hmixed' := (mem_mixedBoundaryDeletions (c := c)).1 hmixed
  have hpart : c.topExtremePart D = D := by
    apply Finset.ext
    intro x
    simp only [mem_topExtremePart, and_iff_left_iff_imp]
    exact htop'.2 x
  rw [hpart, htop'.1] at hmixed'
  omega

/-- Abstract cofinite-two formula.  In the module-theoretic application,
top extreme points are indecomposable projectives; identifying the mixed
term with irreducible projective-to-nonprojective arrows is a separate
Auslander--Reiten theorem. -/
theorem cofiniteTwoCount_eq_choose_add_mixedBoundaryCount
    (hae : c.IsAntiExchange) :
    c.cofiniteTwoCount =
      Nat.choose c.topExtremeFinset.card 2 +
        c.mixedBoundaryCount := by
  classical
  rw [cofiniteTwoCount, mixedBoundaryCount,
    cofiniteTwoDeletions_eq_topExtremePairs_union_mixedBoundary c hae,
    Finset.card_union_of_disjoint
      (disjoint_topExtremePairs_mixedBoundary c),
    topExtremePairs, Finset.card_powersetCard]

end Finite

end OpConjecture.SetClosure
