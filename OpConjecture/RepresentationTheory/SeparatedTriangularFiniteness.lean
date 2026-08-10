import OpConjecture.RepresentationTheory.SeparatedTriangularAlgebra
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finiteness of the separated triangular algebra

If the radical bimodule is finite over the left semisimple coordinate ring,
then the triangular algebra `(S × S) ⋉ J` is module-finite over `S × S`.
In particular it is Artinian, hence Noetherian, when `S` is Artinian.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions

namespace OpConjecture.SeparatedTriangularAlgebra

universe u v

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]

/-- The separated ideal is finite over the two-copy coordinate algebra as
soon as `J` is finite for its left `S`-action. -/
instance separatedIdealFinite [Module.Finite S J] :
    Module.Finite (S × S) (SeparatedIdeal S J) := by
  let f : SeparatedIdeal S J →ₛₗ[(RingHom.fst S S)] J :=
    { toFun := SeparatedIdeal.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : RingHomSurjective (RingHom.fst S S) :=
    ⟨fun s ↦ ⟨(s, 0), rfl⟩⟩
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_injective f
  · intro x y hxy
    exact SeparatedIdeal.ext hxy
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr]
    · exact Module.Finite.fg_top
    · intro x
      exact ⟨SeparatedIdeal.mk x, rfl⟩

/-- The triangular algebra is finite as a module over its semisimple
two-copy coordinate subalgebra. -/
instance algebraModuleFinite [Module.Finite S J] :
    Module.Finite (S × S) (Algebra S J) := by
  change Module.Finite (S × S) ((S × S) × SeparatedIdeal S J)
  infer_instance

/-- A separated triangular algebra over an Artinian coordinate ring is
Artinian. -/
instance algebraIsArtinian [Module.Finite S J] [IsArtinianRing S] :
    IsArtinianRing (Algebra S J) := by
  letI : IsScalarTower (S × S) (Algebra S J) (Algebra S J) :=
    ⟨fun r x y ↦ by
      apply TrivSqZeroExt.ext
      · exact mul_assoc _ _ _
      · change
          (r * x.fst) • y.snd + (r • x.snd) <• y.fst =
            r • (x.fst • y.snd + x.snd <• y.fst)
        rw [smul_add, mul_smul]
        congr 1
        exact (SMulCommClass.smul_comm r
          (MulOpposite.op y.fst) x.snd).symm⟩
  exact IsArtinianRing.of_finite (S × S) (Algebra S J)

end OpConjecture.SeparatedTriangularAlgebra
