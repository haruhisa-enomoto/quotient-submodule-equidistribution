import OpConjecture.Combinatorics.CyclicBinaryTransitions
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Packet assembly for the four-vertex ladder count

The four-support lemma classifies a killed ladder either by a hook
occurrence, a fixed packet, or a triangle packet.  A double hook is counted
twice by hook occurrences, so it appears once on the opposite side of the
classification.  This file records that classification as a finite
equivalence and proves the final arithmetic assembly used by the manuscript.

The representation-theoretic work is therefore cleanly separated from the
counting: it must construct the two packet decompositions and prove the strip
and fixed-packet balances under reversal.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OpConjecture.FourVertexLadderPackets

universe u v w x

/-- A proof-relevant form of the four-support packet classification.

`Hook` counts hook occurrences rather than supports.  Consequently a
double-hook support occurs once in `Killed` and twice in `Hook`, which is
encoded by placing `Double` on the right-hand side. -/
structure Decomposition
    (Killed : Type u)
    (Hook Double Fixed Triangle : Type v) where
  classify : (Hook ⊕ Fixed ⊕ Triangle) ≃ (Killed ⊕ Double)

namespace Decomposition

variable {Killed : Type u}
  {Hook Double Fixed Triangle : Type v}
  [Fintype Killed] [Fintype Hook] [Fintype Double]
  [Fintype Fixed] [Fintype Triangle]

/-- Cardinal form of `K = W - B + F + T`, without truncated subtraction. -/
theorem card_killed_add_card_double
    (D : Decomposition Killed Hook Double Fixed Triangle) :
    Fintype.card Killed + Fintype.card Double =
      Fintype.card Hook + Fintype.card Fixed + Fintype.card Triangle := by
  have h := Fintype.card_congr D.classify
  simp only [Fintype.card_sum] at h
  omega

end Decomposition

section FiberClassification

variable {Base : Type u} [Fintype Base]
  (Hook : Base → Type u) [∀ b, Fintype (Hook b)]
  (Bad Fixed Triangle : Base → Prop)

/-- Cardinality of a finite predicate subtype as a sum of indicators over
the ambient finite type. -/
private theorem card_subtype_eq_sum_indicator
    (P : Base → Prop) [DecidablePred P] [Fintype {b // P b}] :
    Fintype.card {b // P b} = ∑ b : Base, (if P b then 1 else 0) := by
  classical
  rw [Fintype.card_subtype]
  symm
  exact (Finset.sum_boole P Finset.univ :
    (∑ b ∈ Finset.univ, if P b then 1 else 0) =
      (Finset.univ.filter P).card)

/-- A supportwise hook/fixed/triangle classification gives the exact
proof-relevant packet decomposition.  Hook fibers may have cardinality two;
the corresponding base point is then counted once by `Double` on the other
side.  The resulting equivalence is chosen from the proved cardinality
identity, so no arbitrary ordering of the two hook occurrences is needed. -/
noncomputable def decompositionOfFiberClassification
    (hook_card_le_two : ∀ b, Fintype.card (Hook b) ≤ 2)
    (classify : ∀ b,
      Bad b ↔ Nonempty (Hook b) ∨ Fixed b ∨ Triangle b)
    (fixed_hookless : ∀ b, Fixed b → IsEmpty (Hook b))
    (triangle_hookless : ∀ b, Triangle b → IsEmpty (Hook b))
    (fixed_triangle_disjoint : ∀ b, Fixed b → Triangle b → False) :
    Decomposition
      {b // Bad b}
      (Σ b, Hook b)
      {b // Nontrivial (Hook b)}
      {b // Fixed b}
      {b // Triangle b} := by
  classical
  letI : Fintype {b // Bad b} := Fintype.ofFinite _
  letI : Fintype {b // Nontrivial (Hook b)} := Fintype.ofFinite _
  letI : Fintype {b // Fixed b} := Fintype.ofFinite _
  letI : Fintype {b // Triangle b} := Fintype.ofFinite _
  have hpoint : ∀ b : Base,
      (if Bad b then 1 else 0) +
          (if Nontrivial (Hook b) then 1 else 0) =
        Fintype.card (Hook b) +
          (if Fixed b then 1 else 0) +
          (if Triangle b then 1 else 0) := by
    intro b
    by_cases hh : Nonempty (Hook b)
    · have hbad : Bad b := (classify b).2 (Or.inl hh)
      have hfixed : ¬ Fixed b := by
        intro hf
        letI : IsEmpty (Hook b) := fixed_hookless b hf
        exact hh.elim isEmptyElim
      have htriangle : ¬ Triangle b := by
        intro ht
        letI : IsEmpty (Hook b) := triangle_hookless b ht
        exact hh.elim isEmptyElim
      have hpos : 0 < Fintype.card (Hook b) :=
        Fintype.card_pos_iff.2 hh
      by_cases hd : Nontrivial (Hook b)
      · have htwo : Fintype.card (Hook b) = 2 := by
          have hlt : 1 < Fintype.card (Hook b) :=
            Fintype.one_lt_card_iff_nontrivial.2 hd
          have hle := hook_card_le_two b
          omega
        simp [hbad, hd, hfixed, htriangle, htwo]
      · have hone : Fintype.card (Hook b) = 1 := by
          have hle : Fintype.card (Hook b) ≤ 1 := by
            by_contra hnot
            apply hd
            apply Fintype.one_lt_card_iff_nontrivial.1
            omega
          have hle2 := hook_card_le_two b
          omega
        simp [hbad, hd, hfixed, htriangle, hone]
    · have hi : IsEmpty (Hook b) := not_nonempty_iff.mp hh
      have hdouble : ¬ Nontrivial (Hook b) := by
        intro hd
        letI : Nontrivial (Hook b) := hd
        exact hh inferInstance
      by_cases hf : Fixed b
      · have ht : ¬ Triangle b := fixed_triangle_disjoint b hf
        have hb : Bad b := (classify b).2 (Or.inr (Or.inl hf))
        simp [hb, hdouble, hf, ht]
      · by_cases ht : Triangle b
        · have hb : Bad b := (classify b).2 (Or.inr (Or.inr ht))
          simp [hb, hdouble, hf, ht]
        · have hb : ¬ Bad b := by
            intro hb
            rcases (classify b).1 hb with h | h | h
            · exact hh h
            · exact hf h
            · exact ht h
          simp [hb, hdouble, hf, ht]
  have hsum := Fintype.sum_congr
    (fun b : Base ↦
      (if Bad b then 1 else 0) +
        (if Nontrivial (Hook b) then 1 else 0))
    (fun b : Base ↦
      Fintype.card (Hook b) +
        (if Fixed b then 1 else 0) +
        (if Triangle b then 1 else 0)) hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at hsum
  have hcard :
      Fintype.card {b // Bad b} +
          Fintype.card {b // Nontrivial (Hook b)} =
        Fintype.card (Σ b, Hook b) +
          Fintype.card {b // Fixed b} +
          Fintype.card {b // Triangle b} := by
    rw [card_subtype_eq_sum_indicator Bad,
      card_subtype_eq_sum_indicator (fun b ↦ Nontrivial (Hook b)),
      Fintype.card_sigma,
      card_subtype_eq_sum_indicator Fixed,
      card_subtype_eq_sum_indicator Triangle]
    exact hsum
  refine ⟨Fintype.equivOfCardEq ?_⟩
  simp only [Fintype.card_sum]
  omega

end FiberClassification

/-- The two numerical reversal statements left after packet classification.

The strip equality is the subtraction-free form of
`(W - B + T)_q = (W - B + T)_s`; the fixed equality is
`F_q = F_s`. -/
structure ReversalBalance
    (QHook QDouble QFixed QTriangle : Type u)
    (SHook SDouble SFixed STriangle : Type v)
    [Fintype QHook] [Fintype QDouble] [Fintype QFixed]
    [Fintype QTriangle] [Fintype SHook] [Fintype SDouble]
    [Fintype SFixed] [Fintype STriangle] : Prop where
  strip :
    Fintype.card QHook + Fintype.card QTriangle + Fintype.card SDouble =
      Fintype.card SHook + Fintype.card STriangle + Fintype.card QDouble
  fixed : Fintype.card QFixed = Fintype.card SFixed

/-- Four-support packet classification plus strip and fixed-strip reversal
balance gives equality of the quotient and submodule killed-ladder counts. -/
theorem killed_card_eq_of_reversalBalance
    {QKilled : Type u} {QHook QDouble QFixed QTriangle : Type v}
    {SKilled : Type w} {SHook SDouble SFixed STriangle : Type x}
    [Fintype QKilled] [Fintype QHook] [Fintype QDouble]
    [Fintype QFixed] [Fintype QTriangle]
    [Fintype SKilled] [Fintype SHook] [Fintype SDouble]
    [Fintype SFixed] [Fintype STriangle]
    (Q : Decomposition QKilled QHook QDouble QFixed QTriangle)
    (S : Decomposition SKilled SHook SDouble SFixed STriangle)
    (R : ReversalBalance QHook QDouble QFixed QTriangle
      SHook SDouble SFixed STriangle) :
    Fintype.card QKilled = Fintype.card SKilled := by
  have hQ := Q.card_killed_add_card_double
  have hS := S.card_killed_add_card_double
  have hstrip := R.strip
  have hfixed := R.fixed
  omega

end OpConjecture.FourVertexLadderPackets
