import OpConjecture.RepresentationTheory.BottomTwoModules

/-!
# Length-three quotient and submodule reductions

This file isolates the first length-theoretic reduction needed by the
module-side classification of three-point quotient- and submodule-closed
supports.  It deliberately makes no collective finite-biproduct closure
claim.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Composition length does not increase under an epimorphism between chosen
indecomposable representatives. -/
theorem compositionLength_le_of_epi
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Epi f] :
    σ.compositionLength j ≤ σ.compositionLength i := by
  have hsurj : Function.Surjective f.hom.hom :=
    (fg_epi_iff_surjective f).mp inferInstance
  apply ENat.coe_le_coe.mp
  rw [σ.coe_compositionLength j,
    σ.coe_compositionLength i]
  exact Module.length_le_of_surjective f.hom.hom hsurj

/-- Composition length does not decrease under a monomorphism between chosen
indecomposable representatives. -/
theorem compositionLength_le_of_mono
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Mono f] :
    σ.compositionLength i ≤ σ.compositionLength j := by
  have hinj : Function.Injective f.hom.hom :=
    (fg_mono_iff_injective f).mp inferInstance
  apply ENat.coe_le_coe.mp
  rw [σ.coe_compositionLength i,
    σ.coe_compositionLength j]
  exact Module.length_le_of_injective f.hom.hom hinj

/-- An indecomposable quotient of a length-three representative is simple,
has composition length two, or is isomorphic to the source representative. -/
theorem simple_or_lengthTwo_or_isIso_of_epi_of_compositionLength_eq_three
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Epi f]
    (hi : σ.compositionLength i = 3) :
    Simple (σ.obj j) ∨
      σ.compositionLength j = 2 ∨
        IsIso f := by
  have hle :
      σ.compositionLength j ≤
        σ.compositionLength i :=
    σ.compositionLength_le_of_epi f
  have hjpos := σ.compositionLength_pos j
  have hj :
      σ.compositionLength j = 1 ∨
        σ.compositionLength j = 2 ∨
          σ.compositionLength j = 3 := by
    omega
  rcases hj with hj | hj | hj
  · exact Or.inl
      ((σ.compositionLength_eq_one_iff_simple j).mp hj)
  · exact Or.inr (Or.inl hj)
  · exact Or.inr (Or.inr
      (σ.isIso_of_epi_of_compositionLength_eq f
        (hi.trans hj.symm)))

/-- An indecomposable submodule of a length-three representative is simple,
has composition length two, or is isomorphic to the target representative. -/
theorem simple_or_lengthTwo_or_isIso_of_mono_of_compositionLength_eq_three
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Mono f]
    (hj : σ.compositionLength j = 3) :
    Simple (σ.obj i) ∨
      σ.compositionLength i = 2 ∨
        IsIso f := by
  have hle :
      σ.compositionLength i ≤
        σ.compositionLength j :=
    σ.compositionLength_le_of_mono f
  have hipos := σ.compositionLength_pos i
  have hi :
      σ.compositionLength i = 1 ∨
        σ.compositionLength i = 2 ∨
          σ.compositionLength i = 3 := by
    omega
  rcases hi with hi | hi | hi
  · exact Or.inl
      ((σ.compositionLength_eq_one_iff_simple i).mp hi)
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr
      (σ.isIso_of_mono_of_compositionLength_eq f
        (hi.trans hj.symm)))

end OpConjecture.IndecomposableSkeleton
