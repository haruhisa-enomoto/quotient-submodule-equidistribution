import OpConjecture.RepresentationTheory.EquivalenceTransport
import OpConjecture.RepresentationTheory.SimpleLevels

/-!
# Simple representatives under an aligned equivalence

An equivalence of module categories preserves simple objects.  Hence an
aligned equivalence of complete indecomposable skeletons restricts its label
bijection to their simple representatives.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.AlignedEquivalence

universe uR uS vR vS wR wS

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
variable {S : Type uS} [Ring S] [IsNoetherianRing S]
variable {iota : Type vR} {kappa : Type vS}
variable
  {sigma : IndecomposableSkeleton.{uR, vR, wR} R iota}
  {tau : IndecomposableSkeleton.{uS, vS, wS} S kappa}

/-- An aligned equivalence restricts its label bijection to the simple
indecomposable representatives. -/
def simpleIndexEquiv (E : AlignedEquivalence sigma tau) :
    sigma.SimpleIndex ≃ tau.SimpleIndex where
  toFun i := ⟨E.labelEquiv i.1, by
    letI : Simple (sigma.obj i.1) := i.2
    have hiMap : Simple
        (E.categoryEquiv.functor.obj (sigma.obj i.1)) :=
      CategoryTheory.simple_obj E.categoryEquiv.functor (sigma.obj i.1)
    exact (Simple.iff_of_iso (E.objIso i.1)).mp hiMap⟩
  invFun j := ⟨E.labelEquiv.symm j.1, by
    letI : Simple (tau.obj j.1) := j.2
    have hjMap : Simple
        (E.categoryEquiv.functor.obj
          (sigma.obj (E.labelEquiv.symm j.1))) :=
      (Simple.iff_of_iso (E.objIso (E.labelEquiv.symm j.1))).mpr <| by
        simpa using j.2
    exact (CategoryTheory.simple_obj_iff E.categoryEquiv.functor
      (sigma.obj (E.labelEquiv.symm j.1))).mp hjMap⟩
  left_inv i := by
    apply Subtype.ext
    exact E.labelEquiv.symm_apply_apply i.1
  right_inv j := by
    apply Subtype.ext
    exact E.labelEquiv.apply_symm_apply j.1

/-- In particular, aligned equivalent finite skeletons have the same number
of simple representatives. -/
theorem natCard_simpleIndex_eq (E : AlignedEquivalence sigma tau) :
    Nat.card sigma.SimpleIndex = Nat.card tau.SimpleIndex :=
  Nat.card_congr E.simpleIndexEquiv

end OpConjecture.IndecomposableSkeleton.AlignedEquivalence
