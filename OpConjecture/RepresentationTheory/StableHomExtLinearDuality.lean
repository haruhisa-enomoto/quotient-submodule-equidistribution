import OpConjecture.RepresentationTheory.StableEndResidue
import OpConjecture.RepresentationTheory.StableHomExtAlmostSplit
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Scalar-linear stable Hom--Ext duality

This file packages the exact scalar-enriched interface needed between a
stable Auslander--Reiten formula and `StableHomExtSoclePairing`.  For fixed
objects `X` and `T`, the interface identifies `Ext¹(Y,T)` naturally with the
`k`-linear dual of stable `Hom(X,Y)`.

An identity-detecting stable functional is constructed additively elsewhere.
To use it in the scalar dual, one must separately exhibit a linear map with
that underlying additive homomorphism.  Evaluation then selects a
distinguished extension class and constructs the abstract socle pairing.

The declarations here do not construct the linear duality or its scalar
lift, identify `T` with `DTr X` or an Auslander--Reiten translate, or construct
an almost-split sequence.  They are classification-free and contain no
concrete algebra or module example.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace OpConjecture

universe uk uC vC uQ vQ w uE

namespace StableEndIdentityFunctional

variable
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    [Linear k QCat]
    {Q : C ⥤ QCat} {X : C}
    {E : Type uE} [AddCommGroup E] [Module k E]

/-- Evidence that an additive stable-endomorphism functional belongs to the
selected `k`-linear dual.  An arbitrary additive functional need not possess
such a lift. -/
structure ScalarLift (L : StableEndIdentityFunctional Q X E) where
  linear : (Q.obj X ⟶ Q.obj X) →ₗ[k] E
  toAddMonoidHom_eq : linear.toAddMonoidHom = L.functional

end StableEndIdentityFunctional

variable
    {k : Type uk} [CommRing k]
    {C : Type uC} [Category.{vC} C] [Abelian C] [Linear k C]
    [HasExt.{w} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    [Linear k QCat]
    (Q : C ⥤ QCat) (X T : C)
    (E : Type uE) [AddCommGroup E] [Module k E]

/-- A scalar-linear form of the local stable Auslander--Reiten formula for
fixed `X` and `T`.  It is contravariantly natural in the variable `Y`.

The coefficient module `E` is arbitrary at this interface.  In the intended
Artin-algebra application it will come from a Matlis dualizing module, but no
Artinianity, injective-cogenerator, `DTr`, or biduality datum is asserted by
this structure. -/
structure StableHomExtLinearDuality where
  equiv :
    ∀ Y : C,
      Ext Y T 1 ≃ₗ[k] ((Q.obj X ⟶ Q.obj Y) →ₗ[k] E)
  naturality :
    ∀ {Y Z : C} (a : Q.obj X ⟶ Q.obj Y)
      (g : Y ⟶ Z) (xi : Ext Z T 1),
      equiv Y ((Ext.mk₀ g).comp xi (zero_add 1)) a =
        equiv Z xi (a ≫ Q.map g)

namespace StableHomExtLinearDuality

variable {Q X T E}

/-- A scalar-admissible identity functional selects the distinguished
extension class and supplies the abstract stable Hom--Ext socle pairing. -/
def toSoclePairing
    (D : StableHomExtLinearDuality (k := k) Q X T E)
    (L : StableEndIdentityFunctional Q X E)
    (hL : StableEndIdentityFunctional.ScalarLift (k := k) L) :
    StableHomExtSoclePairing Q X T E where
  pair Y a xi := D.equiv Y xi a
  pair_zero := by
    intro Y a
    simp
  pair_pullback := by
    intro Y Z a g xi
    exact D.naturality a g xi
  separates_ext := by
    intro Y xi hxi
    apply (D.equiv Y).injective
    apply LinearMap.ext
    intro a
    simpa using hxi a
  socleClass := (D.equiv X).symm hL.linear
  pair_identity_ne_zero := by
    rw [LinearEquiv.apply_symm_apply]
    change hL.linear.toAddMonoidHom (𝟙 (Q.obj X)) ≠ 0
    rw [hL.toAddMonoidHom_eq]
    exact L.identity_ne_zero
  pair_nonretraction_eq_zero := by
    intro r hr
    rw [LinearEquiv.apply_symm_apply]
    change hL.linear.toAddMonoidHom (Q.map r) = 0
    rw [hL.toAddMonoidHom_eq]
    exact L.nonretraction_eq_zero r hr

end StableHomExtLinearDuality

end OpConjecture
