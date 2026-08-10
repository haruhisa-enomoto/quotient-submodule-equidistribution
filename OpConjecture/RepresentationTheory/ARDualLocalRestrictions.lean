import OpConjecture.RepresentationTheory.ARDualTranslation
import OpConjecture.RepresentationTheory.ARLocalRestrictions

/-!
# Dual local restrictions for finite AR quivers

The source-coordinate fixed-strip argument needs the dual clause of the
local two-cycle lemma: an injective vertex in an opposite-arrow pair is also
projective.  It follows by transporting the pair to the aligned dual
skeleton and applying the already proved projective clause there.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

include k D in
omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- The injective member of an opposite-arrow pair is projective. -/
theorem projective_of_injective_two_cycle
    (ARτ : τ.FiniteARTranslationData)
    (i z : ι) (hi : Injective (σ.obj i))
    (hiz : HasIrreducibleMorphism (σ.obj i) (σ.obj z))
    (hzi : HasIrreducibleMorphism (σ.obj z) (σ.obj i)) :
    Projective (σ.obj i) := by
  let ei := D.forward.labelEquiv i
  let ez := D.forward.labelEquiv z
  have heiP : Projective (τ.obj ei) := by
    simpa [ei] using
      (D.forward.injective_iff_projective_image σ τ i).1 hi
  have hei_ez : HasIrreducibleMorphism (τ.obj ei) (τ.obj ez) := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := z) (y := i)).2 hzi
  have hez_ei : HasIrreducibleMorphism (τ.obj ez) (τ.obj ei) := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := i) (y := z)).2 hiz
  have heiI : Injective (τ.obj ei) :=
    ARτ.injective_of_projective_two_cycle
      (K := k) τ ei ez heiP hei_ez hez_ei
  exact (D.forward.projective_iff_injective_image σ τ i).2 (by
    simpa [ei] using heiI)

include k D in
omit [Algebra k R] [FiniteDimensional k R] [Fintype ι] in
/-- A nonprojective vertex in an opposite-arrow pair is noninjective. -/
theorem noninjective_of_nonprojective_two_cycle
    (ARτ : τ.FiniteARTranslationData)
    (x z : ι) (hx : ¬ Projective (σ.obj x))
    (hxz : HasIrreducibleMorphism (σ.obj x) (σ.obj z))
    (hzx : HasIrreducibleMorphism (σ.obj z) (σ.obj x)) :
    ¬ Injective (σ.obj x) := by
  intro hxi
  exact hx (D.projective_of_injective_two_cycle
    (k := k) σ τ ARτ x z hxi hxz hzx)

end AlignedBiduality

end OpConjecture.IndecomposableSkeleton
