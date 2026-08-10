import Mathlib.Algebra.Module.Submodule.Range

/-!
# Trace comparison modulo a radical subspace

This file isolates the linear-algebra step in the separated-representation
argument.  A surjective comparison of two families of maps into the same
target, whose pointwise discrepancies lie in a fixed subspace, gives the same
trace after adjoining that subspace.
-/

set_option autoImplicit false

noncomputable section

namespace OpConjecture.RadicalSquareZero.HomKernelTrace

universe u v w x

variable {K : Type u} [Field K]
  {M : Type v} {N : Type w}
  [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- The trace of a family of linear maps is the sum of their ranges. -/
def familyTrace {A : Type x} (f : A → M →ₗ[K] N) : Submodule K N :=
  ⨆ a, LinearMap.range (f a)

/-- A surjective comparison of map families which agrees modulo `R`
preserves trace modulo `R`.

For separated representations, `R` is the radical of the target module and
the two indexing types are the original and separated Hom spaces. -/
theorem familyTrace_sup_eq_of_surjective_mod
    {A : Type x} {B : Type*}
    (f : A → M →ₗ[K] N) (g : B → M →ₗ[K] N)
    (R : Submodule K N) (φ : A → B)
    (hφ : Function.Surjective φ)
    (hmod : ∀ (a : A) (m : M), f a m - g (φ a) m ∈ R) :
    familyTrace f ⊔ R = familyTrace g ⊔ R := by
  apply le_antisymm
  · apply sup_le
    · apply iSup_le
      intro a
      rintro n ⟨m, rfl⟩
      have hf : g (φ a) m ∈ familyTrace g := by
        exact (le_iSup (fun b ↦ LinearMap.range (g b)) (φ a)) ⟨m, rfl⟩
      have hdiff := hmod a m
      have heq : f a m = g (φ a) m + (f a m - g (φ a) m) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm]
      have hf' : g (φ a) m ∈ familyTrace g ⊔ R :=
        (show familyTrace g ≤ familyTrace g ⊔ R from le_sup_left) hf
      have hdiff' : f a m - g (φ a) m ∈ familyTrace g ⊔ R :=
        (show R ≤ familyTrace g ⊔ R from le_sup_right) hdiff
      rw [heq]
      exact (familyTrace g ⊔ R).add_mem hf' hdiff'
    · exact le_sup_right
  · apply sup_le
    · apply iSup_le
      intro b
      obtain ⟨a, rfl⟩ := hφ b
      rintro n ⟨m, rfl⟩
      have hf : f a m ∈ familyTrace f := by
        exact (le_iSup (fun a ↦ LinearMap.range (f a)) a) ⟨m, rfl⟩
      have hdiff := hmod a m
      have heq : g (φ a) m = f a m - (f a m - g (φ a) m) := by
        simp [sub_eq_add_neg]
      have hf' : f a m ∈ familyTrace f ⊔ R :=
        (show familyTrace f ≤ familyTrace f ⊔ R from le_sup_left) hf
      have hdiff' : f a m - g (φ a) m ∈ familyTrace f ⊔ R :=
        (show R ≤ familyTrace f ⊔ R from le_sup_right) hdiff
      rw [heq]
      exact (familyTrace f ⊔ R).sub_mem hf' hdiff'
    · exact le_sup_right

end OpConjecture.RadicalSquareZero.HomKernelTrace
