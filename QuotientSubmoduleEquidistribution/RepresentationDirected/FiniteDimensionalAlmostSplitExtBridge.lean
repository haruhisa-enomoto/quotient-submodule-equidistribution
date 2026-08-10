import QuotientSubmoduleEquidistribution.RepresentationDirected.AlmostSplitExtBridge
import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedOrder
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalARNonvanishing

/-!
# Automatic directed almost-split lifting over a field

Finite-dimensional field algebras supply the intrinsic AR-translation data
used by the abstract directed Hom--Ext contradiction.  This file removes that
remaining AR-existence/duality input from the local nonprojective lifting
substep; the directed Hom order and the short exact sequence under
consideration remain explicit.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

local instance : HasExt.{u} (FGModuleCat.{u} R) :=
  hasExt_of_enoughProjectives.{u} (FGModuleCat.{u} R)

namespace DirectedHomOrder

include K in
/-- Finite-dimensional-field specialization of the exact almost-split
lifting step used in the manuscript's representation-directed induction.

If `X -> Z` is nonzero, then every map from the nonprojective indecomposable
`X` to the quotient of a short exact sequence starting at `Z` lifts through
its middle term.  No finite-skeleton hypothesis is needed. -/
theorem finiteDimensional_exists_lift_of_nonzero_kernel_hom
    [Preorder Iota]
    (H : DirectedHomOrder sigma)
    (x : sigma.NonprojectiveLabel) (z : Iota)
    (g : sigma.obj x.1 ⟶ sigma.obj z) (hg : g ≠ 0)
    {V W : FGModuleCat.{u} R}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (a : sigma.obj x.1 ⟶ W) :
    ∃ b : sigma.obj x.1 ⟶ V, b ≫ p = a :=
  H.exists_lift_of_nonzero_kernel_hom
    (D := sigma.finiteDimensionalARTranslationData K R)
    x z g hg hS a

include K in
/-- Under the cycle-free part of representation-directedness, the chosen
linear extension and the finite-dimensional almost-split data together make
the local nonprojective lifting statement automatic. -/
theorem finiteDimensional_exists_lift_of_acyclicNonzeroNonisomorphisms
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (x : sigma.NonprojectiveLabel) (z : Iota)
    (g : sigma.obj x.1 ⟶ sigma.obj z) (hg : g ≠ 0)
    {V W : FGModuleCat.{u} R}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (a : sigma.obj x.1 ⟶ W) :
    ∃ b : sigma.obj x.1 ⟶ V, b ≫ p = a := by
  letI := directedLinearOrder sigma H
  exact finiteDimensional_exists_lift_of_nonzero_kernel_hom
    K R sigma (of_acyclicNonzeroNonisomorphisms sigma H)
      x z g hg hS a

end DirectedHomOrder

end QuotientSubmoduleEquidistribution.RepresentationDirected
