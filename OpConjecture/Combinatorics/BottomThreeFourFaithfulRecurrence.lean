import OpConjecture.Combinatorics.BottomLevels

/-!
# Repairing bottom levels three and four by faithful-core recurrence

This file deliberately does not use the formal five-family shape count.
-/

noncomputable section

open Set

namespace OpConjecture.BottomLevels.BottomThreeFourFaithfulRecurrence

universe u v w

variable {B : Type u}
  (Index : B → Type v)
  [∀ b : B, Finite (Index b)]
  (cQ cS : ∀ b : B, OpConjecture.SetClosure (Index b))
  (FaithfulQ FaithfulS : ∀ b : B, Set (Index b) → Prop)
  (QCore : ∀ b : B,
    MinimalFaithfulCore.Data (cQ b) (FaithfulQ b))
  (SCore : ∀ b : B,
    MinimalFaithfulCore.Data (cS b) (FaithfulS b))
  (measure : B → ℕ)
  (ProperFactor : B → Type w)
  [∀ b : B, Fintype (ProperFactor b)]
  (factor : ∀ b : B, ProperFactor b → B)
  (Connected : B → Prop)

/-- The faithful count of the quotient-side closure system at one level. -/
abbrev faithfulQCount (b : B) (n : ℕ) : ℕ :=
  MinimalFaithfulCore.faithfulLevelCount
    (cQ b) (FaithfulQ b) n

/-- The faithful count of the submodule-side closure system at one level. -/
abbrev faithfulSCount (b : B) (n : ℕ) : ℕ :=
  MinimalFaithfulCore.faithfulLevelCount
    (cS b) (FaithfulS b) n

/-- At a fixed level, equal minimal-core sizes reduce the connected faithful
comparison exactly to the genuinely exceptional case in which the common
core size is strictly smaller than the level.  The maintained annihilator
induction theorem then proves both total and faithful equality. -/
theorem total_and_faithful_eq_at_level_of_core_control
    (n : ℕ)
    (hfactorSmaller :
      ∀ (b : B) (I : ProperFactor b),
        measure (factor b I) < measure b)
    (hcoreCard :
      ∀ b : B,
        ((QCore b).core : Set (Index b)).ncard =
          ((SCore b).core : Set (Index b)).ncard)
    (hrecurrenceQ :
      ∀ b : B,
        (cQ b).levelCount n =
          faithfulQCount Index cQ FaithfulQ b n +
            ∑ I : ProperFactor b,
              faithfulQCount Index cQ FaithfulQ (factor b I) n)
    (hrecurrenceS :
      ∀ b : B,
        (cS b).levelCount n =
          faithfulSCount Index cS FaithfulS b n +
            ∑ I : ProperFactor b,
              faithfulSCount Index cS FaithfulS (factor b I) n)
    (hsmallCore :
      ∀ b : B, Connected b →
        ((QCore b).core : Set (Index b)).ncard < n →
        faithfulQCount Index cQ FaithfulQ b n =
          faithfulSCount Index cS FaithfulS b n)
    (hdisconnected :
      ∀ b : B, ¬ Connected b →
        (∀ b' : B, measure b' < measure b →
          (cQ b').levelCount n = (cS b').levelCount n) →
        (cQ b).levelCount n = (cS b).levelCount n)
    (b : B) :
    (cQ b).levelCount n = (cS b).levelCount n ∧
      faithfulQCount Index cQ FaithfulQ b n =
        faithfulSCount Index cS FaithfulS b n := by
  apply AnnihilatorInduction.total_and_faithful_eq_of_recurrence
    (measure := measure)
    (totalQ := fun b ↦ (cQ b).levelCount n)
    (totalS := fun b ↦ (cS b).levelCount n)
    (faithfulQ := fun b ↦
      faithfulQCount Index cQ FaithfulQ b n)
    (faithfulS := fun b ↦
      faithfulSCount Index cS FaithfulS b n)
    (ProperFactor := ProperFactor)
    (factor := factor)
    (Connected := Connected)
    hfactorSmaller hrecurrenceQ hrecurrenceS
  · intro b hb _
    by_cases hsmall :
        ((QCore b).core : Set (Index b)).ncard < n
    · exact hsmallCore b hb hsmall
    · exact
        MinimalFaithfulCore.faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
          (QCore b) (SCore b) (hcoreCard b) (Nat.le_of_not_gt hsmall)
  · exact hdisconnected

/-- The exact abstract input package for replacing the invalid five-family
classification at levels three and four.

The only connected cases not settled formally by equal minimal-core sizes
are the `core size < level` cases recorded in `smallCore`.  That field may
supply either faithful equality directly (as in an explicit core-extension
count) or total equality (as in the Dynkin and Nakayama polynomial
theorems); the recurrence recovers the other equality.  `recurrenceQ` and
`recurrenceS` are the annihilator-stratum formulas, while `disconnected` is
the block-product step. -/
structure ThreeFourCoreRecurrenceData where
  factorSmaller :
    ∀ (b : B) (I : ProperFactor b),
      measure (factor b I) < measure b
  coreCard :
    ∀ b : B,
      ((QCore b).core : Set (Index b)).ncard =
        ((SCore b).core : Set (Index b)).ncard
  recurrenceQ :
    ∀ (b : B) (n : ℕ), n = 3 ∨ n = 4 →
      (cQ b).levelCount n =
        faithfulQCount Index cQ FaithfulQ b n +
          ∑ I : ProperFactor b,
            faithfulQCount Index cQ FaithfulQ (factor b I) n
  recurrenceS :
    ∀ (b : B) (n : ℕ), n = 3 ∨ n = 4 →
      (cS b).levelCount n =
        faithfulSCount Index cS FaithfulS b n +
          ∑ I : ProperFactor b,
            faithfulSCount Index cS FaithfulS (factor b I) n
  smallCore :
    ∀ (b : B) (n : ℕ), n = 3 ∨ n = 4 → Connected b →
      ((QCore b).core : Set (Index b)).ncard < n →
      (faithfulQCount Index cQ FaithfulQ b n =
          faithfulSCount Index cS FaithfulS b n) ∨
        (cQ b).levelCount n = (cS b).levelCount n
  disconnected :
    ∀ b : B, ¬ Connected b →
      (∀ b' : B, measure b' < measure b →
        (cQ b').levelCount 3 = (cS b').levelCount 3 ∧
          (cQ b').levelCount 4 = (cS b').levelCount 4) →
      (cQ b).levelCount 3 = (cS b).levelCount 3 ∧
        (cQ b).levelCount 4 = (cS b).levelCount 4

/-- Simultaneous repaired bottom-level endpoint.  Under precisely the
minimal-core, exceptional faithful, annihilator recurrence, and block-product
inputs above, both total and faithful counts agree at levels three and four.
No shape classification occurs in the proof. -/
theorem total_and_faithful_eq_three_and_four
    (D : ThreeFourCoreRecurrenceData Index cQ cS FaithfulQ FaithfulS
      QCore SCore measure ProperFactor factor Connected)
    (b : B) :
    ((cQ b).levelCount 3 = (cS b).levelCount 3 ∧
      faithfulQCount Index cQ FaithfulQ b 3 =
        faithfulSCount Index cS FaithfulS b 3) ∧
    ((cQ b).levelCount 4 = (cS b).levelCount 4 ∧
      faithfulQCount Index cQ FaithfulQ b 4 =
        faithfulSCount Index cS FaithfulS b 4) := by
  classical
  induction hμ : measure b using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have ihAll :
          ∀ b' : B, measure b' < measure b →
            ((cQ b').levelCount 3 = (cS b').levelCount 3 ∧
              faithfulQCount Index cQ FaithfulQ b' 3 =
                faithfulSCount Index cS FaithfulS b' 3) ∧
            ((cQ b').levelCount 4 = (cS b').levelCount 4 ∧
              faithfulQCount Index cQ FaithfulQ b' 4 =
                faithfulSCount Index cS FaithfulS b' 4) := by
        intro b' hb'
        exact ih (measure b') (by simpa [hμ] using hb') b' rfl
      have hsumThree :
          (∑ I : ProperFactor b,
              faithfulQCount Index cQ FaithfulQ (factor b I) 3) =
            ∑ I : ProperFactor b,
              faithfulSCount Index cS FaithfulS (factor b I) 3 := by
        apply Finset.sum_congr rfl
        intro I _
        exact (ihAll (factor b I) (D.factorSmaller b I)).1.2
      have hsumFour :
          (∑ I : ProperFactor b,
              faithfulQCount Index cQ FaithfulQ (factor b I) 4) =
            ∑ I : ProperFactor b,
              faithfulSCount Index cS FaithfulS (factor b I) 4 := by
        apply Finset.sum_congr rfl
        intro I _
        exact (ihAll (factor b I) (D.factorSmaller b I)).2.2
      by_cases hb : Connected b
      · have hfaithfulThree :
            faithfulQCount Index cQ FaithfulQ b 3 =
              faithfulSCount Index cS FaithfulS b 3 := by
          by_cases hsmall :
              ((QCore b).core : Set (Index b)).ncard < 3
          · rcases D.smallCore b 3 (Or.inl rfl) hb hsmall with hf | ht
            · exact hf
            · have hadd :
                  faithfulQCount Index cQ FaithfulQ b 3 +
                        ∑ I : ProperFactor b,
                          faithfulQCount Index cQ FaithfulQ (factor b I) 3 =
                    faithfulSCount Index cS FaithfulS b 3 +
                        ∑ I : ProperFactor b,
                          faithfulSCount Index cS FaithfulS (factor b I) 3 := by
                rw [← D.recurrenceQ b 3 (Or.inl rfl),
                  ← D.recurrenceS b 3 (Or.inl rfl), ht]
              rw [hsumThree] at hadd
              exact Nat.add_right_cancel hadd
          · exact
              MinimalFaithfulCore.faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
                (QCore b) (SCore b) (D.coreCard b)
                (Nat.le_of_not_gt hsmall)
        have hfaithfulFour :
            faithfulQCount Index cQ FaithfulQ b 4 =
              faithfulSCount Index cS FaithfulS b 4 := by
          by_cases hsmall :
              ((QCore b).core : Set (Index b)).ncard < 4
          · rcases D.smallCore b 4 (Or.inr rfl) hb hsmall with hf | ht
            · exact hf
            · have hadd :
                  faithfulQCount Index cQ FaithfulQ b 4 +
                        ∑ I : ProperFactor b,
                          faithfulQCount Index cQ FaithfulQ (factor b I) 4 =
                    faithfulSCount Index cS FaithfulS b 4 +
                        ∑ I : ProperFactor b,
                          faithfulSCount Index cS FaithfulS (factor b I) 4 := by
                rw [← D.recurrenceQ b 4 (Or.inr rfl),
                  ← D.recurrenceS b 4 (Or.inr rfl), ht]
              rw [hsumFour] at hadd
              exact Nat.add_right_cancel hadd
          · exact
              MinimalFaithfulCore.faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
                (QCore b) (SCore b) (D.coreCard b)
                (Nat.le_of_not_gt hsmall)
        have htotalThree :
            (cQ b).levelCount 3 = (cS b).levelCount 3 := by
          rw [D.recurrenceQ b 3 (Or.inl rfl),
            D.recurrenceS b 3 (Or.inl rfl),
            hfaithfulThree, hsumThree]
        have htotalFour :
            (cQ b).levelCount 4 = (cS b).levelCount 4 := by
          rw [D.recurrenceQ b 4 (Or.inr rfl),
            D.recurrenceS b 4 (Or.inr rfl),
            hfaithfulFour, hsumFour]
        exact
          ⟨⟨htotalThree, hfaithfulThree⟩,
            ⟨htotalFour, hfaithfulFour⟩⟩
      · have htotal := D.disconnected b hb fun b' hb' ↦
          ⟨(ihAll b' hb').1.1, (ihAll b' hb').2.1⟩
        have hfaithfulThree :
            faithfulQCount Index cQ FaithfulQ b 3 =
              faithfulSCount Index cS FaithfulS b 3 := by
          have hadd :
              faithfulQCount Index cQ FaithfulQ b 3 +
                    ∑ I : ProperFactor b,
                      faithfulQCount Index cQ FaithfulQ (factor b I) 3 =
                faithfulSCount Index cS FaithfulS b 3 +
                    ∑ I : ProperFactor b,
                      faithfulSCount Index cS FaithfulS (factor b I) 3 := by
            rw [← D.recurrenceQ b 3 (Or.inl rfl),
              ← D.recurrenceS b 3 (Or.inl rfl), htotal.1]
          rw [hsumThree] at hadd
          exact Nat.add_right_cancel hadd
        have hfaithfulFour :
            faithfulQCount Index cQ FaithfulQ b 4 =
              faithfulSCount Index cS FaithfulS b 4 := by
          have hadd :
              faithfulQCount Index cQ FaithfulQ b 4 +
                    ∑ I : ProperFactor b,
                      faithfulQCount Index cQ FaithfulQ (factor b I) 4 =
                faithfulSCount Index cS FaithfulS b 4 +
                    ∑ I : ProperFactor b,
                      faithfulSCount Index cS FaithfulS (factor b I) 4 := by
            rw [← D.recurrenceQ b 4 (Or.inr rfl),
              ← D.recurrenceS b 4 (Or.inr rfl), htotal.2]
          rw [hsumFour] at hadd
          exact Nat.add_right_cancel hadd
        exact
          ⟨⟨htotal.1, hfaithfulThree⟩,
            ⟨htotal.2, hfaithfulFour⟩⟩

/-- Coefficient-only form of the repaired endpoint. -/
theorem levelCount_three_and_four_eq
    (D : ThreeFourCoreRecurrenceData Index cQ cS FaithfulQ FaithfulS
      QCore SCore measure ProperFactor factor Connected)
    (b : B) :
    (cQ b).levelCount 3 = (cS b).levelCount 3 ∧
      (cQ b).levelCount 4 = (cS b).levelCount 4 := by
  have h := total_and_faithful_eq_three_and_four
    Index cQ cS FaithfulQ FaithfulS QCore SCore measure
      ProperFactor factor Connected D b
  exact ⟨h.1.1, h.2.1⟩

end OpConjecture.BottomLevels.BottomThreeFourFaithfulRecurrence
