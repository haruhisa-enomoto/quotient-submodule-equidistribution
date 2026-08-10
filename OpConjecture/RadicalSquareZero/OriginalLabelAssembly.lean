import OpConjecture.RadicalSquareZero.OriginalNonsimpleClosure
import OpConjecture.RepresentationTheory.SimpleNonsimpleRelabeling

/-!
# Construct the original nonsimple/simple labeling

For an arbitrary finite-length indecomposable skeleton over a semisimple-base
trivial square-zero extension, the canonical nonsimple/simple partition
supplies the exact original-side label data used by the separated-quiver
argument.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace OpConjecture.RadicalSquareZero

universe u v w x

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsNoetherianRing (TrivSqZeroExt S J)]
variable {ι : Type x}

namespace OriginalNonsimpleLabelData

/-- The canonical nonsimple/simple relabeling of the original skeleton
carries the exact objectwise properties required by the closure argument. -/
theorem ofSkeleton
    (sigma : IndecomposableSkeleton.{max u v, x, w}
      (TrivSqZeroExt S J) ι) :
    OriginalNonsimpleLabelData
      (IndecomposableSkeleton.NonsimpleIndex sigma)
      (IndecomposableSkeleton.SimpleIndex sigma)
      sigma.nonsimpleSimpleSkeleton where
  simple_simple i := by
    simpa using i.2
  nonsimple_radical_nontrivial i := by
    apply Submodule.nontrivial_iff_ne_bot.mpr
    intro hrad
    letI : IsArtinian (TrivSqZeroExt S J) (sigma.obj i.1) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (sigma.finiteLength i.1)).2
    letI : IsSemisimpleModule (TrivSqZeroExt S J) (sigma.obj i.1) :=
      (IsArtinian.isSemisimpleModule_iff_jacobson
        (TrivSqZeroExt S J) (sigma.obj i.1)).2 hrad
    have hsimpleModule :
        IsSimpleModule (TrivSqZeroExt S J) (sigma.obj i.1) :=
      IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
        (sigma.indecomposable i.1)
    exact i.2
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (sigma.obj i.1)).2 hsimpleModule)

end OriginalNonsimpleLabelData

end OpConjecture.RadicalSquareZero
