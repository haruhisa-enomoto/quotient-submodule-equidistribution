import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitExtNonvanishing
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalTwoSidedAlmostSplit

/-!
# Ext nonvanishing and intrinsic AR translation over a field

Finite-dimensional field algebras automatically supply the right
almost-split family and projective--injective boundary data.  This file
specializes the abstract almost-split Ext-detection theorem to that data on
an arbitrary complete indecomposable skeleton.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u uIota

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

local instance : HasExt.{u} (FGModuleCat.{u} R) :=
  hasExt_of_enoughProjectives.{u} (FGModuleCat.{u} R)

/-- The right-family part of the automatic finite-dimensional two-sided
local AR data. -/
def finiteDimensionalARTranslationData : sigma.FiniteARTranslationData :=
  (sigma.finiteDimensionalTwoSidedLocalARData K R).toFiniteARTranslationData

include K in
/-- For every finite-dimensional algebra over a field, a nonzero
`Ext¹(X,Z)` class produces a nonzero map `Z -> tau X`, where `tau X` is the
chosen skeleton representative of the kernel of a minimal right almost-split
map ending at the nonprojective indecomposable `X`.

No finite-skeleton or representation-finiteness hypothesis is used. -/
theorem finiteDimensional_exists_ne_zero_hom_to_arTranslation_of_ext_ne_zero
    (x : sigma.NonprojectiveLabel)
    (Z : FGModuleCat.{u} R) (xi : Ext (sigma.obj x.1) Z 1)
    (hxi : xi ≠ 0) :
    ∃ a : Z ⟶ sigma.obj
        (FiniteARTranslationData.arTranslation sigma
          (sigma.finiteDimensionalARTranslationData K R) x).1,
      a ≠ 0 :=
  (sigma.finiteDimensionalARTranslationData K R).exists_ne_zero_hom_to_arTranslation_of_ext_ne_zero
    sigma x Z xi hxi

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
