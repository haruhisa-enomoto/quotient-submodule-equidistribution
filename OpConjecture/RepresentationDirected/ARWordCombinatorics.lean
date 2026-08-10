import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max

/-!
# Local combinatorics of an Auslander--Reiten word

This file isolates the word-theoretic translation step used in the
representation-directed argument.  Positions carry labels in a simple graph.
For a position `x`, a previous position is the immediately preceding occurrence
of the same label.  A middle position is the last occurrence of a neighboring
label in the window following that predecessor (or in the whole prefix when
there is no predecessor).

The manuscript assumes that the projection to every adjacent pair of labels
alternates away from its two boundary runs.  Its exact local consequence is
`HasInteriorAlternation`: between consecutive occurrences of one label there
is at most one occurrence of any fixed neighboring label.  Under this
hypothesis, a middle arrow `y -> x` at a repeated position rotates to the
middle arrow `p -> y`, where `p` is the previous occurrence of `x`.
-/

namespace OpConjecture.RepresentationDirected.ARWord

universe u

variable {L : Type u}

/-- The label carried by a position of a finite word. -/
abbrev label (Q : List L) (x : Fin Q.length) : L := Q.get x

/-- `p` is the immediately preceding occurrence of the label at `x`. -/
def IsPrevious (Q : List L) (p x : Fin Q.length) : Prop :=
  p < x ∧ label Q p = label Q x ∧
    ∀ z : Fin Q.length, p < z → z < x → label Q z ≠ label Q x

/-- A position has a previous occurrence exactly when its label has occurred
strictly earlier in the word. -/
theorem exists_isPrevious_iff_exists_lt_label_eq
    {Q : List L} {x : Fin Q.length} :
    (∃ p : Fin Q.length, IsPrevious Q p x) ↔
      ∃ p : Fin Q.length, p < x ∧ label Q p = label Q x := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hp.1, hp.2.1⟩
  · classical
    rintro ⟨q, hqx, hqLabel⟩
    let S : Finset (Fin Q.length) :=
      Finset.univ.filter fun p ↦ p < x ∧ label Q p = label Q x
    have hS : S.Nonempty := by
      refine ⟨q, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ q, hqx, hqLabel⟩
    let p : Fin Q.length := S.max' hS
    have hpS : p ∈ S := S.max'_mem hS
    have hpData : p < x ∧ label Q p = label Q x := by
      simpa [S] using hpS
    refine ⟨p, hpData.1, hpData.2, ?_⟩
    intro z hpz hzx hzLabel
    have hzS : z ∈ S := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ z, hzx, hzLabel⟩
    exact (not_le_of_gt hpz) (S.le_max' z hzS)

/-- A previous occurrence, when it exists, is unique. -/
theorem isPrevious_unique
    {Q : List L} {p q x : Fin Q.length}
    (hp : IsPrevious Q p x) (hq : IsPrevious Q q x) :
    p = q := by
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · exact False.elim (hp.2.2 q hpq hq.1 hq.2.1)
  · exact hpq
  · exact False.elim (hq.2.2 p hqp hp.1 hp.2.1)

/-- `y` is the middle position of its label at `x`: its label is adjacent to
the label of `x`, it lies after the predecessor of `x` when one exists, and
it is the last occurrence of its own label before `x`. -/
def IsMiddle (G : SimpleGraph L) (Q : List L)
    (y x : Fin Q.length) : Prop :=
  G.Adj (label Q y) (label Q x) ∧
    y < x ∧
    (∀ p : Fin Q.length, IsPrevious Q p x → p < y) ∧
    ∀ z : Fin Q.length, y < z → z < x → label Q z ≠ label Q y

/-- At most one middle position with a fixed label can occur at an endpoint. -/
theorem isMiddle_unique_of_label_eq
    {G : SimpleGraph L} {Q : List L} {x y z : Fin Q.length}
    (hy : IsMiddle G Q y x) (hz : IsMiddle G Q z x)
    (hlabel : label Q y = label Q z) :
    y = z := by
  rcases lt_trichotomy y z with hyz | hyz | hzy
  · exact False.elim (hy.2.2.2 z hyz hz.2.1 hlabel.symm)
  · exact hyz
  · exact False.elim (hz.2.2.2 y hzy hy.2.1 hlabel)

/-- Local form of the adjacent-label alternation property: between two
consecutive occurrences of one label, there is at most one occurrence of any
fixed neighboring label. -/
def HasInteriorAlternation (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ ⦃p x y z : Fin Q.length⦄,
    IsPrevious Q p x →
      G.Adj (label Q p) (label Q y) →
      p < y → y < x → p < z → z < x →
      label Q z = label Q y → z = y

/-- A witness that the projection to `a` and `b` has an interior `a`-run of
length at least two.  Other labels are irrelevant because they disappear
under the two-letter projection. -/
def IsInteriorRepeatedRun (Q : List L) (a b : L) : Prop :=
  ∃ x y : Fin Q.length,
    x < y ∧
      label Q x = a ∧
      label Q y = a ∧
      (∀ z : Fin Q.length, x < z → z < y → label Q z ≠ b) ∧
      (∃ z : Fin Q.length, z < x ∧ label Q z = b) ∧
      ∃ z : Fin Q.length, y < z ∧ label Q z = b

/-- In every adjacent two-letter projection, repeated runs can occur only at
the two boundaries.  Equivalently, every maximal non-boundary run has length
one. -/
def HasOnlyBoundaryRepeatedRuns (G : SimpleGraph L) (Q : List L) : Prop :=
  ∀ ⦃a b : L⦄, G.Adj a b → ¬ IsInteriorRepeatedRun Q a b

/-- Pointwise form of `HasOnlyBoundaryRepeatedRuns`. -/
theorem hasOnlyBoundaryRepeatedRuns_iff
    {G : SimpleGraph L} {Q : List L} :
    HasOnlyBoundaryRepeatedRuns G Q ↔
      ∀ ⦃a b : L⦄, G.Adj a b →
        ∀ ⦃x y : Fin Q.length⦄,
          x < y → label Q x = a → label Q y = a →
          (∀ z : Fin Q.length, x < z → z < y → label Q z ≠ b) →
          (∀ z : Fin Q.length, z < x → label Q z ≠ b) ∨
            ∀ z : Fin Q.length, y < z → label Q z ≠ b := by
  constructor
  · intro h a b hab x y hxy hxa hya hbetween
    by_contra hboundary
    push Not at hboundary
    exact h hab ⟨x, y, hxy, hxa, hya, hbetween,
      hboundary.1, hboundary.2⟩
  · intro h a b hab hbad
    rcases hbad with
      ⟨x, y, hxy, hxa, hya, hbetween, ⟨z, hzx, hzb⟩,
        ⟨w, hyw, hwb⟩⟩
    rcases h hab hxy hxa hya hbetween with hbefore | hafter
    · exact hbefore z hzx hzb
    · exact hafter w hyw hwb

/-- The literal boundary-run property implies the local
interior-alternation condition used by the word-rotation API. -/
theorem HasOnlyBoundaryRepeatedRuns.hasInteriorAlternation
    {G : SimpleGraph L} {Q : List L}
    (hRuns : HasOnlyBoundaryRepeatedRuns G Q) :
    HasInteriorAlternation G Q := by
  intro p x y z hpx hadj hpy hyx hpz hzx hzLabel
  rcases lt_trichotomy y z with hyz | hyz | hzy
  · exact False.elim (hRuns hadj.symm ⟨y, z, hyz, rfl, hzLabel, by
      intro q hyq hqz hqp
      exact hpx.2.2 q (hpy.trans hyq) (hqz.trans hzx)
        (hqp.trans hpx.2.1),
      ⟨p, hpy, rfl⟩, ⟨x, hzx, hpx.2.1.symm⟩⟩)
  · exact hyz.symm
  · exact False.elim (hRuns hadj.symm ⟨z, y, hzy, hzLabel, rfl, by
      intro q hzq hqy hqp
      exact hpx.2.2 q (hpz.trans hzq) (hqy.trans hyx)
        (hqp.trans hpx.2.1),
      ⟨p, hpz, rfl⟩, ⟨x, hyx, hpx.2.1.symm⟩⟩)

/-- The abstract word-translation lemma.  If `p` is the previous occurrence
of `x`, then `y -> x` is a middle arrow exactly when `p -> y` is a middle
arrow.  In particular, the two families of mesh arrows are paired by the
identity on their intermediate positions. -/
theorem isMiddle_iff_previous_isMiddle
    {G : SimpleGraph L} {Q : List L}
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x)
    (y : Fin Q.length) :
    IsMiddle G Q y x ↔ IsMiddle G Q p y := by
  constructor
  · rintro ⟨hyxAdj, hyx, hafter, hlast⟩
    have hpy : p < y := hafter p hpx
    have hpAdj : G.Adj (label Q p) (label Q y) := by
      rw [hpx.2.1]
      exact hyxAdj.symm
    refine ⟨?_, hpy, ?_, ?_⟩
    · exact hpAdj
    · intro q hqy
      rcases lt_trichotomy q p with hqp | hqp | hpq
      · exact hqp
      · subst q
        exact False.elim
          (hyxAdj.ne (hqy.2.1.symm.trans hpx.2.1))
      · have hqy' : q = y :=
          hAlt hpx hpAdj
            hpy hyx hpq (hqy.1.trans hyx) hqy.2.1
        exact False.elim (hqy.1.ne hqy')
    · intro z hpz hzy
      have hzx : z < x := hzy.trans hyx
      intro hzp
      exact hpx.2.2 z hpz hzx (hzp.trans hpx.2.1)
  · rintro ⟨hpyAdj, hpy, hbefore, hlast⟩
    have hyx : y < x := by
      rcases lt_trichotomy y x with hyx | hyx | hxy
      · exact hyx
      · subst y
        exact False.elim (hpyAdj.ne hpx.2.1)
      · exact False.elim (hlast x hpx.1 hxy hpx.2.1.symm)
    refine ⟨?_, hyx, ?_, ?_⟩
    · rw [← hpx.2.1]
      exact hpyAdj.symm
    · intro q hqx
      rw [isPrevious_unique hqx hpx]
      exact hpy
    · intro z hyz hzx hzy
      have hzp : p < z := hpy.trans hyz
      have hEq : z = y :=
        hAlt hpx hpyAdj hpy hyx hzp hzx hzy
      exact hyz.ne hEq.symm

/-- Paper-facing one-way form: every middle arrow into a repeated position
rotates across its predecessor. -/
theorem previous_isMiddle_of_isMiddle
    {G : SimpleGraph L} {Q : List L}
    (hAlt : HasInteriorAlternation G Q)
    {p x y : Fin Q.length}
    (hpx : IsPrevious Q p x) (hyx : IsMiddle G Q y x) :
    IsMiddle G Q p y :=
  (isMiddle_iff_previous_isMiddle hAlt hpx y).1 hyx

/-- The literal bijection between the incoming middle arrows at `x` and the
outgoing middle arrows at its previous occurrence `p`. -/
def middleRotationEquiv
    {G : SimpleGraph L} {Q : List L}
    (hAlt : HasInteriorAlternation G Q)
    {p x : Fin Q.length} (hpx : IsPrevious Q p x) :
    {y : Fin Q.length // IsMiddle G Q y x} ≃
      {y : Fin Q.length // IsMiddle G Q p y} where
  toFun y :=
    ⟨y.1, (isMiddle_iff_previous_isMiddle hAlt hpx y.1).1 y.2⟩
  invFun y :=
    ⟨y.1, (isMiddle_iff_previous_isMiddle hAlt hpx y.1).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end OpConjecture.RepresentationDirected.ARWord
