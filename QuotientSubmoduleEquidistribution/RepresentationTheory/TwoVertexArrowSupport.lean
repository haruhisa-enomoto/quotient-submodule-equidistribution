import Mathlib.Tactic.FinCases

/-!
# Arrow supports on two vertices

This file contains the finite combinatorics used after the exceptional
faithful-core reduction has identified the simple vertices with `Fin 2`.
It separates the support-shape argument from the missing theorem realizing
Ext-Gabriel arrows by concrete cyclic ideals.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.TwoVertexArrowSupport

universe u

/-- An arrow type with source and target in the fixed two-vertex set.  The
pair-injectivity field says there is at most one arrow for each ordered pair
of endpoints. -/
structure Data (Arrow : Type u) where
  source : Arrow → Fin 2
  target : Arrow → Fin 2
  pair_injective : Function.Injective fun a ↦ (source a, target a)

namespace Data

variable {Arrow : Type u} (D : Data Arrow)

private theorem finTwo_eq_of_ne_common {i j k : Fin 2}
    (hi : i ≠ k) (hj : j ≠ k) : i = j := by
  omega

/-- The arrow support relation. -/
def HasArrow (i j : Fin 2) : Prop :=
  ∃ a : Arrow, D.source a = i ∧ D.target a = j

/-- A loop occurs at `i`. -/
abbrev HasLoopAt (i : Fin 2) : Prop := D.HasArrow i i

/-- There are no loops. -/
def NoLoops : Prop := ∀ i, ¬ D.HasLoopAt i

/-- For two vertices, connectedness of the underlying unoriented support is
exactly the existence of at least one cross-arrow. -/
def UnderlyingConnected : Prop :=
  D.HasArrow 0 1 ∨ D.HasArrow 1 0

/-- Loops do not occur at both vertices. -/
def LoopsAtMostOneVertex : Prop :=
  ¬ (D.HasLoopAt 0 ∧ D.HasLoopAt 1)

/-- The loop-free two-vertex support has at most one outgoing arrow from
each vertex. -/
theorem source_injective_of_noLoops (hNoLoops : D.NoLoops) :
    Function.Injective D.source := by
  intro a b hab
  apply D.pair_injective
  apply Prod.ext hab
  have ha : D.target a ≠ D.source a := by
    intro ha
    exact hNoLoops (D.source a) ⟨a, rfl, ha⟩
  have hb : D.target b ≠ D.source a := by
    intro hb
    apply hNoLoops (D.source b)
    refine ⟨b, rfl, ?_⟩
    exact hb.trans hab
  exact finTwo_eq_of_ne_common ha hb

/-- Dually, the loop-free two-vertex support has at most one incoming arrow
at each vertex. -/
theorem target_injective_of_noLoops (hNoLoops : D.NoLoops) :
    Function.Injective D.target := by
  intro a b hab
  apply D.pair_injective
  apply Prod.ext
  · have ha : D.source a ≠ D.target a := by
      intro ha
      exact hNoLoops (D.source a) ⟨a, rfl, ha.symm⟩
    have hb : D.source b ≠ D.target a := by
      intro hb
      apply hNoLoops (D.source b)
      refine ⟨b, rfl, ?_⟩
      exact (hb.trans hab).symm
    exact finTwo_eq_of_ne_common ha hb
  · exact hab

/-- A one-way lollipop support: one loop vertex and exactly one orientation
of cross-arrow. -/
def IsOneWayLollipopAt (loopVertex other : Fin 2) : Prop :=
  loopVertex ≠ other ∧
    D.HasLoopAt loopVertex ∧ ¬ D.HasLoopAt other ∧
      ((D.HasArrow loopVertex other ∧
          ¬ D.HasArrow other loopVertex) ∨
        (¬ D.HasArrow loopVertex other ∧
          D.HasArrow other loopVertex))

/-- The excluded support shape in the manuscript: one loop together with
both arrows of a two-cycle. -/
def IsLoopTwoCycleAt (loopVertex other : Fin 2) : Prop :=
  loopVertex ≠ other ∧
    D.HasLoopAt loopVertex ∧ ¬ D.HasLoopAt other ∧
      D.HasArrow loopVertex other ∧ D.HasArrow other loopVertex

/-- Exhaustive two-vertex support classification after loop uniqueness:
the support is loop-free, a one-way lollipop, or a loop plus two-cycle. -/
theorem noLoops_or_oneWayLollipop_or_loopTwoCycle
    (hConnected : D.UnderlyingConnected)
    (hLoopUnique : D.LoopsAtMostOneVertex) :
    D.NoLoops ∨
      (∃ i j, D.IsOneWayLollipopAt i j) ∨
        ∃ i j, D.IsLoopTwoCycleAt i j := by
  classical
  by_cases hNoLoops : D.NoLoops
  · exact Or.inl hNoLoops
  · right
    have hLoop : ∃ i, D.HasLoopAt i := by
      simpa only [NoLoops, not_forall, not_not] using hNoLoops
    obtain ⟨i, hi⟩ := hLoop
    have hi_cases : i = 0 ∨ i = 1 := by omega
    rcases hi_cases with rfl | rfl
    · have hNotOther : ¬ D.HasLoopAt 1 := by
        intro hOther
        exact hLoopUnique ⟨hi, hOther⟩
      by_cases hForward : D.HasArrow 0 1
      · by_cases hBackward : D.HasArrow 1 0
        · exact Or.inr ⟨0, 1, by
            exact ⟨by decide, hi, hNotOther, hForward, hBackward⟩⟩
        · exact Or.inl ⟨0, 1, by
            exact ⟨by decide, hi, hNotOther,
              Or.inl ⟨hForward, hBackward⟩⟩⟩
      · have hBackward : D.HasArrow 1 0 :=
          hConnected.resolve_left hForward
        exact Or.inl ⟨0, 1, by
          exact ⟨by decide, hi, hNotOther,
            Or.inr ⟨hForward, hBackward⟩⟩⟩
    · have hNotOther : ¬ D.HasLoopAt 0 := by
        intro hOther
        exact hLoopUnique ⟨hOther, hi⟩
      by_cases hForward : D.HasArrow 0 1
      · by_cases hBackward : D.HasArrow 1 0
        · exact Or.inr ⟨1, 0, by
            exact ⟨by decide, hi, hNotOther, hBackward, hForward⟩⟩
        · exact Or.inl ⟨1, 0, by
            exact ⟨by decide, hi, hNotOther,
              Or.inr ⟨hBackward, hForward⟩⟩⟩
      · have hBackward : D.HasArrow 1 0 :=
          hConnected.resolve_left hForward
        exact Or.inl ⟨1, 0, by
          exact ⟨by decide, hi, hNotOther,
            Or.inl ⟨hBackward, hForward⟩⟩⟩

end Data

end QuotientSubmoduleEquidistribution.TwoVertexArrowSupport
