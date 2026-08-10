import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedIndecomposable
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedTrace

/-!
# Simple sources do not contribute to nonsimple top trace

For a square-zero module whose separated datum is kernel-free, every map from
a module with zero Jacobson radical induces the zero map on tops.  Indeed, the
compatibility square puts the image of the top map in the common kernel of the
target action.  This is the mechanism by which selected simple modules drop
out of nonsimple generation in the radical-square-zero closure argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedTrace

open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedData
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedCorrespondence
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedIndecomposable
open QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedModuleFunctor

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- A map from a semisimple source to a kernel-free square-zero target is zero
on module tops. -/
theorem moduleTopMapS_eq_zero_of_source_jacobson_eq_bot_of_target_kernelFree
    [IsSemisimpleRing S]
    (X Y : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : Module.jacobson (TrivSqZeroExt S J) X = ⊥)
    (hY : IsKernelFree
      (moduleSeparatedData (S := S) (J := J) Y))
    (f : X ⟶ Y) :
    moduleTopMapS f = 0 := by
  have sourceRadical_eq_zero
      (z : Module.jacobson (TrivSqZeroExt S J) X) : z = 0 := by
    apply Subtype.ext
    have hz : (z.val : X) ∈ (⊥ :
        Submodule (TrivSqZeroExt S J) X) := by
      rw [← hX]
      exact z.property
    exact hz
  let DX := moduleSeparatedData (S := S) (J := J) X
  let DY := moduleSeparatedData (S := S) (J := J) Y
  let p : DX ⟶ DY := moduleSeparatedDataMap f
  ext t
  have hsourceAction (j : J) : DX.action j t = 0 := by
    exact sourceRadical_eq_zero (DX.action j t)
  have hkernel : p.val.1 t ∈ commonKernel DY := by
    intro j
    have hp := p.property j t
    rw [hsourceAction j, map_zero] at hp
    exact hp.symm
  rw [hY] at hkernel
  exact hkernel

/-- Consequently the one-source top trace of a semisimple source in a
kernel-free target is zero. -/
theorem moduleTopTrace_eq_bot_of_source_jacobson_eq_bot_of_target_kernelFree
    [IsSemisimpleRing S]
    (X Y : ModuleCat.{w} (TrivSqZeroExt S J))
    (hX : Module.jacobson (TrivSqZeroExt S J) X = ⊥)
    (hY : IsKernelFree
      (moduleSeparatedData (S := S) (J := J) Y)) :
    moduleTopTrace X Y = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro f
  rw [moduleTopMapS_eq_zero_of_source_jacobson_eq_bot_of_target_kernelFree
    X Y hX hY f]
  simp

/-- In particular, a semisimple source contributes nothing to the top trace
of an indecomposable target with nonzero radical.  Simple sources are the
paper-facing special case. -/
theorem moduleTopTrace_eq_bot_of_semisimple_source_of_indecomposable_target
    [IsSemisimpleRing S]
    (X Y : ModuleCat.{w} (TrivSqZeroExt S J))
    [IsSemisimpleModule (TrivSqZeroExt S J) X]
    (hY : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (TrivSqZeroExt S J) Y)
    [Nontrivial (Module.jacobson (TrivSqZeroExt S J) Y)] :
    moduleTopTrace X Y = ⊥ := by
  apply
    moduleTopTrace_eq_bot_of_source_jacobson_eq_bot_of_target_kernelFree
      X Y
  · exact IsSemisimpleModule.jacobson_eq_bot _ _
  · exact moduleSeparatedData_isKernelFree_of_indecomposable Y hY

/-- If every source in the right half of a disjoint family has zero top
trace, deleting that half does not change the family top trace. -/
theorem moduleFamilyTopTrace_sum_eq_left_of_right_eq_bot
    {A B : Type*}
    (X : A → ModuleCat.{w} (TrivSqZeroExt S J))
    (Z : B → ModuleCat.{w} (TrivSqZeroExt S J))
    (Y : ModuleCat.{w} (TrivSqZeroExt S J))
    (hZ : ∀ b, moduleTopTrace (Z b) Y = ⊥) :
    moduleFamilyTopTrace (Sum.elim X Z) Y =
      moduleFamilyTopTrace X Y := by
  rw [moduleFamilyTopTrace_sum]
  have hright : moduleFamilyTopTrace Z Y = ⊥ := by
    apply bot_unique
    apply iSup_le
    intro b
    rw [hZ b]
  rw [hright, sup_bot_eq]

/-- Split a selected family on a sum of labels and delete its right half when
that half has zero target top trace. -/
theorem moduleFamilyTopTrace_selected_sum_eq_left
    {N V : Type*}
    (X : N → ModuleCat.{w} (TrivSqZeroExt S J))
    (Z : V → ModuleCat.{w} (TrivSqZeroExt S J))
    (T : Set (N ⊕ V))
    (Y : ModuleCat.{w} (TrivSqZeroExt S J))
    (hZ : ∀ b : {v : V // Sum.inr v ∈ T},
      moduleTopTrace (Z b.1) Y = ⊥) :
    moduleFamilyTopTrace
        (fun i : {z : N ⊕ V // z ∈ T} ↦
          Sum.elim X Z i.1) Y =
      moduleFamilyTopTrace
        (fun i : {n : N // Sum.inl n ∈ T} ↦ X i.1) Y := by
  let XL : {n : N // Sum.inl n ∈ T} →
      ModuleCat.{w} (TrivSqZeroExt S J) := fun i ↦ X i.1
  let ZR : {v : V // Sum.inr v ∈ T} →
      ModuleCat.{w} (TrivSqZeroExt S J) := fun i ↦ Z i.1
  calc
    moduleFamilyTopTrace
        (fun i : {z : N ⊕ V // z ∈ T} ↦
          Sum.elim X Z i.1) Y =
        moduleFamilyTopTrace (Sum.elim XL ZR) Y := by
      have hfun :
          (fun i : {z : N ⊕ V // z ∈ T} ↦
            Sum.elim X Z i.1) =
            fun i ↦ (Sum.elim XL ZR)
              (Equiv.subtypeSum
                (p := fun z : N ⊕ V ↦ z ∈ T) i) := by
        funext i
        rcases i with ⟨a | b, h⟩ <;> rfl
      rw [hfun]
      exact moduleFamilyTopTrace_reindex
        (Equiv.subtypeSum (p := fun z : N ⊕ V ↦ z ∈ T))
        (Sum.elim XL ZR) Y
    _ = moduleFamilyTopTrace XL Y :=
      moduleFamilyTopTrace_sum_eq_left_of_right_eq_bot XL ZR Y hZ
    _ = _ := rfl

/-- For an indecomposable nonsimple square-zero target, any selected simple
(more generally semisimple) source half may be deleted from the top trace. -/
theorem moduleFamilyTopTrace_selected_sum_eq_left_of_semisimple_right
    [IsSemisimpleRing S]
    {N V : Type*}
    (X : N → ModuleCat.{w} (TrivSqZeroExt S J))
    (Z : V → ModuleCat.{w} (TrivSqZeroExt S J))
    [∀ v, IsSemisimpleModule (TrivSqZeroExt S J) (Z v)]
    (T : Set (N ⊕ V))
    (Y : ModuleCat.{w} (TrivSqZeroExt S J))
    (hY : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      (TrivSqZeroExt S J) Y)
    [Nontrivial (Module.jacobson (TrivSqZeroExt S J) Y)] :
    moduleFamilyTopTrace
        (fun i : {z : N ⊕ V // z ∈ T} ↦
          Sum.elim X Z i.1) Y =
      moduleFamilyTopTrace
        (fun i : {n : N // Sum.inl n ∈ T} ↦ X i.1) Y := by
  apply moduleFamilyTopTrace_selected_sum_eq_left X Z T Y
  intro b
  exact
    moduleTopTrace_eq_bot_of_semisimple_source_of_indecomposable_target
      (Z b.1) Y hY

end QuotientSubmoduleEquidistribution.TrivSqZeroExtSeparatedTrace
