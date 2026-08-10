import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Stable Hom--Ext pairings and right almost-split sequences

This file isolates the formal last step of the classical Auslander--Reiten
construction.  A nonzero `Ext¹` class whose pullback along every
nonretraction vanishes makes any short exact sequence representing it right
almost split.  Existence of a representing sequence remains a separate input.

A natural projective-stable Hom--`Ext¹` pairing, together with a distinguished
class detected by the stable identity and annihilating nonretractions,
produces exactly such a class.  The construction is abstract: no concrete
algebra, module classification, or existence theorem for the pairing is
assumed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution

universe uC vC uQ vQ w uOmega

variable {C : Type uC} [Category.{vC} C]

/-- If a composite `f ≫ g` is a retraction, then `g` is already a
retraction. -/
theorem isSplitEpi_right_of_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsSplitEpi (f ≫ g)) :
    IsSplitEpi g := by
  letI : IsSplitEpi (f ≫ g) := hfg
  exact IsSplitEpi.mk'
    { section_ := section_ (f ≫ g) ≫ f
      id := by
        rw [Category.assoc]
        exact IsSplitEpi.id (f ≫ g) }

variable [Abelian C] [HasExt.{w} C]

/-- A nonzero extension class annihilated by pullback along every
nonretraction makes any representing short exact sequence right almost
split. -/
theorem ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator
    {S : ShortComplex C} (hS : S.ShortExact)
    (hne : hS.extClass ≠ 0)
    (hannihilates :
      ∀ {Y : C} (g : Y ⟶ S.X₃),
        ¬ IsSplitEpi g →
          (Ext.mk₀ g).comp hS.extClass (zero_add 1) = 0) :
    IsRightAlmostSplit S.g := by
  constructor
  · intro hsplit
    letI : IsSplitEpi S.g := hsplit
    apply hne
    calc
      hS.extClass =
          (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := by
        simp
      _ = (Ext.mk₀ (section_ S.g ≫ S.g)).comp
            hS.extClass (zero_add 1) := by
        rw [IsSplitEpi.id S.g]
      _ = (Ext.mk₀ (section_ S.g)).comp
            ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1))
            (zero_add 1) := by
        rw [Ext.mk₀_comp_mk₀_assoc]
      _ = 0 := by simp
  · intro Y g hg
    obtain ⟨x₂, hx₂⟩ :=
      Ext.covariant_sequence_exact₃
        (X := Y) hS (Ext.mk₀ g)
        (rfl : 0 + 1 = 1) (hannihilates g hg)
    refine ⟨Ext.addEquiv₀ x₂, ?_⟩
    apply (Ext.mk₀_bijective Y S.X₃).1
    rw [← Ext.mk₀_comp_mk₀]
    simpa using hx₂

/-- The local output needed from a projective-stable Hom--`Ext¹` pairing.

`Q` is intended to be the quotient functor to the projective-stable category.
The distinguished class is detected by the stable identity and annihilates
the image of every nonretraction endomorphism. -/
structure StableHomExtSoclePairing
    {QCat : Type uQ} [Category.{vQ} QCat]
    (Q : C ⥤ QCat) (X T : C) (Omega : Type uOmega) [Zero Omega] where
  pair :
    ∀ Y : C, (Q.obj X ⟶ Q.obj Y) → Ext Y T 1 → Omega
  pair_zero :
    ∀ (Y : C) (a : Q.obj X ⟶ Q.obj Y), pair Y a 0 = 0
  pair_pullback :
    ∀ {Y Z : C} (a : Q.obj X ⟶ Q.obj Y)
      (g : Y ⟶ Z) (xi : Ext Z T 1),
      pair Y a ((Ext.mk₀ g).comp xi (zero_add 1)) =
        pair Z (a ≫ Q.map g) xi
  separates_ext :
    ∀ (Y : C) (xi : Ext Y T 1),
      (∀ a : Q.obj X ⟶ Q.obj Y, pair Y a xi = 0) → xi = 0
  socleClass : Ext X T 1
  pair_identity_ne_zero :
    pair X (𝟙 (Q.obj X)) socleClass ≠ 0
  pair_nonretraction_eq_zero :
    ∀ (r : X ⟶ X), ¬ IsSplitEpi r →
      pair X (Q.map r) socleClass = 0

namespace StableHomExtSoclePairing

variable
    {QCat : Type uQ} [Category.{vQ} QCat]
    {Q : C ⥤ QCat} {X T : C}
    {Omega : Type uOmega} [Zero Omega]
    (P : StableHomExtSoclePairing Q X T Omega)

/-- The distinguished socle class is nonzero. -/
theorem socleClass_ne_zero : P.socleClass ≠ 0 := by
  intro hzero
  apply P.pair_identity_ne_zero
  rw [hzero, P.pair_zero]

/-- Naturality, right separation, and nonretraction annihilation force every
nonretraction pullback of the distinguished class to vanish. -/
theorem pullback_socleClass_eq_zero_of_not_isSplitEpi
    [Q.Full]
    {Y : C} (g : Y ⟶ X) (hg : ¬ IsSplitEpi g) :
    (Ext.mk₀ g).comp P.socleClass (zero_add 1) = 0 := by
  apply P.separates_ext
  intro a
  rw [P.pair_pullback]
  have hcomp : ¬ IsSplitEpi (Q.preimage a ≫ g) := by
    intro hsplit
    exact hg (isSplitEpi_right_of_comp (Q.preimage a) g hsplit)
  rw [← Q.map_preimage a, ← Q.map_comp]
  exact P.pair_nonretraction_eq_zero (Q.preimage a ≫ g) hcomp

/-- Any short exact sequence realizing the distinguished class is right
almost split. -/
theorem isRightAlmostSplit_of_realizes_socleClass
    [Q.Full]
    {E : C} (f : T ⟶ E) (g : E ⟶ X) (zero : f ≫ g = 0)
    (hS : (ShortComplex.mk f g zero).ShortExact)
    (hrealizes : hS.extClass = P.socleClass) :
    IsRightAlmostSplit g := by
  apply ShortComplex.ShortExact.isRightAlmostSplit_of_extClass_annihilator hS
  · rw [hrealizes]
    exact P.socleClass_ne_zero
  · intro Y q hq
    rw [hrealizes]
    exact P.pullback_socleClass_eq_zero_of_not_isSplitEpi q hq

end StableHomExtSoclePairing

end QuotientSubmoduleEquidistribution
