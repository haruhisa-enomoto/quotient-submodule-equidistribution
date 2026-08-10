import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Ideal.Maps

/-!
# Embedding the regular module in a finite power of a faithful module

This file formalizes the finite-basis argument used in the faithful-core
proof.  Evaluation on a vector-space basis embeds the regular module into a
finite power of a faithful module.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.FaithfulRegularEmbedding

universe uK uR uM

variable (K : Type uK) (R : Type uR) (M : Type uM)
  [Field K] [Ring R]
  [AddCommGroup M] [Module K M] [Module R M]
  [SMulCommClass R K M]
  [Module.Free K M] [Module.Finite K M]

/-- Evaluate the regular module on a finite basis of a faithful module. -/
def regularToBasisProduct :
    R →ₗ[R] (Fin (Module.finrank K M) → M) where
  toFun r i := r • Module.finBasis K M i
  map_add' r s := by
    ext i
    exact add_smul r s (Module.finBasis K M i)
  map_smul' r s := by
    ext i
    exact mul_smul r s (Module.finBasis K M i)

/-- Evaluation on a finite basis embeds the regular module when the action
is faithful. -/
theorem regularToBasisProduct_injective
    [FaithfulSMul R M] :
    Function.Injective (regularToBasisProduct K R M) := by
  intro r s hrs
  apply FaithfulSMul.eq_of_smul_eq_smul (M := R) (α := M)
  intro m
  let b := Module.finBasis K M
  rw [← b.sum_repr m]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm r, smul_comm s]
  congr 1
  exact congr_fun hrs i

/-- Annihilator-zero form of the faithful regular embedding. -/
theorem regularToBasisProduct_injective_of_annihilator_eq_bot
    (hM : Module.annihilator R M = ⊥) :
    Function.Injective (regularToBasisProduct K R M) := by
  letI : FaithfulSMul R M :=
    Module.annihilator_eq_bot.mp hM
  exact regularToBasisProduct_injective K R M

end QuotientSubmoduleEquidistribution.FaithfulRegularEmbedding
