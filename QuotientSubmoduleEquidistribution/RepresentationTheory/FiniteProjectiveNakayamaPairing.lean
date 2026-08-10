import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteProjectiveCounit
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-!
# The finite-projective Nakayama pairing over a field

Using the counit pairing between a finite projective module `P` and its
regular Hom-dual `Q`, this file constructs the rank-one maps
`P ⟶ Y` determined by `q : Q` and `y : Y`.  Their evaluations define the
canonical map from the coefficient dual of `Hom(P,Y)` to `Hom(Y,DQ)`.

The construction is global in the finite projective `P` and the variable
finite module `Y`; it contains no algebra-specific examples.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation

open QuotientSubmoduleEquidistribution.RingelStable

universe u

namespace FiniteProjectiveNakayama

variable (K R : Type u) [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R]

variable [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]

variable (P : FGProjectives (R := R))

def rankOne
    (Y : FGModuleCat.{u} R)
    (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    P.obj →ₗ[R] Y where
  toFun p := MulOpposite.unop (counitEvaluation (R := R) P p q) • y
  map_add' p p' := by simp [add_smul]
  map_smul' r p := by
    change
      MulOpposite.unop (counitEvaluation (R := R) P (r • p) q) • y =
        r • MulOpposite.unop (counitEvaluation (R := R) P p q) • y
    rw [counitEvaluation_smul]
    simp [smul_smul]

omit [IsNoetherianRing R] in
@[simp]
theorem rankOne_add_left
    (Y : FGModuleCat.{u} R)
    (q q' : (projectiveHomDual (R := R) P).obj) (y : Y) :
    rankOne (R := R) P Y (q + q') y =
      rankOne (R := R) P Y q y + rankOne (R := R) P Y q' y := by
  ext p
  simp [rankOne, add_smul]

omit [IsNoetherianRing R] in
@[simp]
theorem rankOne_add_right
    (Y : FGModuleCat.{u} R)
    (q : (projectiveHomDual (R := R) P).obj) (y y' : Y) :
    rankOne (R := R) P Y q (y + y') =
      rankOne (R := R) P Y q y + rankOne (R := R) P Y q y' := by
  ext p
  simp [rankOne, smul_add]

omit [IsNoetherianRing R] in
@[simp]
theorem rankOne_balance
    (Y : FGModuleCat.{u} R)
    (r : R) (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    rankOne (R := R) P Y q (r • y) =
      rankOne (R := R) P Y (MulOpposite.op r • q) y := by
  ext p
  simp [rankOne, smul_smul]

omit [FiniteDimensional K R] [IsNoetherianRing R] in
@[simp]
theorem rankOne_smul_left
    (Y : FGModuleCat.{u} R)
    (k : K) (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    rankOne (R := R) P Y (k • q) y =
      k • rankOne (R := R) P Y q y := by
  rw [← IsScalarTower.algebraMap_smul Rᵐᵒᵖ k q]
  change
    rankOne (R := R) P Y
        (MulOpposite.op (algebraMap K R k) • q) y = _
  rw [← rankOne_balance]
  rw [IsScalarTower.algebraMap_smul R k y]
  ext p
  change
    MulOpposite.unop (counitEvaluation (R := R) P p q) • k • y =
      k • MulOpposite.unop (counitEvaluation (R := R) P p q) • y
  exact smul_comm _ _ _

omit [FiniteDimensional K R] [IsNoetherianRing R] in
@[simp]
theorem rankOne_smul_right
    (Y : FGModuleCat.{u} R)
    (k : K) (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    rankOne (R := R) P Y q (k • y) =
      k • rankOne (R := R) P Y q y := by
  ext p
  simp only [rankOne, LinearMap.coe_mk, AddHom.coe_mk]
  exact smul_comm _ _ _

abbrev projectiveNakayama :=
  (QuotientSubmoduleEquidistribution.Contragredient.reverseDualFunctor K R).obj
    (Opposite.op (projectiveHomDual (R := R) P).obj)

def nakayamaHomValue
    (Y : FGModuleCat.{u} R)
    (ell : Module.Dual K (P.obj →ₗ[R] Y)) (y : Y) :
    projectiveNakayama (K := K) (R := R) P := by
  change Module.Dual K (projectiveHomDual (R := R) P).obj
  exact
    { toFun := fun q ↦ ell (rankOne (R := R) P Y q y)
      map_add' := fun q q' ↦ by
        rw [rankOne_add_left, map_add]
      map_smul' := fun k q ↦ by
        rw [rankOne_smul_left, map_smul]
        rfl }

def nakayamaHomRLinear
    (Y : FGModuleCat.{u} R)
    (ell : Module.Dual K (P.obj →ₗ[R] Y)) :
    Y →ₗ[R] projectiveNakayama (K := K) (R := R) P where
  toFun := nakayamaHomValue (K := K) (R := R) P Y ell
  map_add' y y' := by
    apply LinearMap.ext
    intro q
    change
      ell (rankOne (R := R) P Y q (y + y')) =
        ell (rankOne (R := R) P Y q y) +
          ell (rankOne (R := R) P Y q y')
    rw [rankOne_add_right, map_add]
  map_smul' r y := by
    apply LinearMap.ext
    intro q
    change
      ell (rankOne (R := R) P Y q (r • y)) =
        ell (rankOne (R := R) P Y (MulOpposite.op r • q) y)
    rw [rankOne_balance]

def nakayamaHomLinearMap
    (Y : FGModuleCat.{u} R) :
    Module.Dual K (P.obj →ₗ[R] Y) →ₗ[K]
      (Y →ₗ[R] projectiveNakayama (K := K) (R := R) P) where
  toFun := nakayamaHomRLinear (K := K) (R := R) P Y
  map_add' ell mu := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro q
    change
      (ell + mu) (rankOne (R := R) P Y q y) =
        ell (rankOne (R := R) P Y q y) +
          mu (rankOne (R := R) P Y q y)
    rw [LinearMap.add_apply]
  map_smul' k ell := by
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro q
    change
      k * ell (rankOne (R := R) P Y q y) =
        ell (rankOne (R := R) P Y
          (MulOpposite.op (algebraMap K R k) • q) y)
    rw [show MulOpposite.op (algebraMap K R k) =
      algebraMap K Rᵐᵒᵖ k by rfl]
    rw [IsScalarTower.algebraMap_smul Rᵐᵒᵖ k q]
    rw [rankOne_smul_left, map_smul]
    rfl

def projectiveHomDualMap
    {P' P : FGProjectives (R := R)} (d : P' ⟶ P) :
    (projectiveHomDual (R := R) P).obj ⟶ (projectiveHomDual (R := R) P').obj :=
  ((fgProjectiveHomDuality (R := R)).functor.map d.op).hom

omit [IsNoetherianRing R] in
theorem counitEvaluation_naturality
    {P' P : FGProjectives (R := R)} (d : P' ⟶ P)
    (p : P'.obj) (q : (projectiveHomDual (R := R) P).obj) :
    counitEvaluation (R := R) P' p
        ((projectiveHomDualMap (R := R) d).hom.hom q) =
      counitEvaluation (R := R) P (d.hom.hom.hom p) q := by
  let df : finiteProjectiveObject (R := R) P' ⟶
      finiteProjectiveObject (R := R) P :=
    (fgProjectivesEquivFiniteProjectives (R := R)).functor.map d
  have hn := (regularHomDuality R).counitIso.inv.naturality df
  have hp := congrArg (fun f ↦ f.hom.hom p) hn
  have hq := congrArg (fun f ↦ f.unop.hom q) hp
  exact hq.symm

omit [IsNoetherianRing R] in
theorem rankOne_naturality
    {P' P : FGProjectives (R := R)} (d : P' ⟶ P)
    (Y : FGModuleCat.{u} R)
    (q : (projectiveHomDual (R := R) P).obj) (y : Y) :
    (rankOne (R := R) P Y q y).comp d.hom.hom.hom =
      rankOne (R := R) P' Y ((projectiveHomDualMap (R := R) d).hom.hom q) y := by
  ext p
  change
    MulOpposite.unop
        (counitEvaluation (R := R) P (d.hom.hom.hom p) q) • y =
      MulOpposite.unop
        (counitEvaluation (R := R) P' p
          ((projectiveHomDualMap (R := R) d).hom.hom q)) • y
  rw [counitEvaluation_naturality]

end FiniteProjectiveNakayama

end QuotientSubmoduleEquidistribution.AuslanderTranspose.TwoStepProjectivePresentation
