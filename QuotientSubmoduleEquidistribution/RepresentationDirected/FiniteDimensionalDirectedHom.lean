import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.LinearAlgebra.Matrix.Block
import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedOrder
import QuotientSubmoduleEquidistribution.RepresentationTheory.NoParallelExtOne

/-!
# Finite-dimensional directed Hom spaces

For a cycle-free indecomposable skeleton over a finite-dimensional algebra,
the chosen directed order makes the Hom-dimension matrix upper triangular.
Algebraic closedness and the cycle condition make its diagonal entries one.
These are the numerical prerequisites for the manuscript's mixed-coordinate
construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

omit [IsAlgClosed K] in
/-- Hom spaces from a chosen indecomposable to any finite module over a
finite-dimensional algebra are finite-dimensional over the ground field. -/
theorem finiteDimensional_hom_from_obj (i : Iota) (Y : FGModuleCat.{u} R) :
    FiniteDimensional K (sigma.obj i ⟶ Y) := by
  letI : Module K (sigma.obj i) := Module.restrictScalars K R (sigma.obj i)
  letI : Module K Y := Module.restrictScalars K R Y
  letI : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  letI : IsScalarTower K R Y := IsScalarTower.restrictScalars K R Y
  letI : FiniteDimensional K (sigma.obj i) := Module.Finite.trans R (sigma.obj i)
  letI : FiniteDimensional K Y := Module.Finite.trans R Y
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  letI : FiniteDimensional K
      (U.obj (sigma.obj i) ⟶ U.obj Y) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := R) (M := sigma.obj i) (N := Y)
  let forgetHom :
      (sigma.obj i ⟶ Y) →ₗ[K]
        (U.obj (sigma.obj i) ⟶ U.obj Y) :=
    { toFun := fun f => f.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective forgetHom (Functor.map_injective U)

omit [IsAlgClosed K] in
/-- Hom spaces between two chosen indecomposables are finite-dimensional. -/
theorem finiteDimensional_hom_obj (i j : Iota) :
    FiniteDimensional K (sigma.obj i ⟶ sigma.obj j) :=
  finiteDimensional_hom_from_obj K R sigma i (sigma.obj j)

/-- Cycle-freeness and algebraic closedness make each indecomposable
endomorphism space one-dimensional. -/
theorem HasAcyclicNonzeroNonisomorphisms.finrank_endomorphism_eq_one
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (i : Iota) :
    Module.finrank K (sigma.obj i ⟶ sigma.obj i) = 1 := by
  letI : FiniteDimensional K (sigma.obj i ⟶ sigma.obj i) :=
    finiteDimensional_hom_obj K R sigma i i
  apply CategoryTheory.finrank_endomorphism_eq_one K
  intro f
  constructor
  · intro hfiso
    letI : IsIso f := hfiso
    intro hfzero
    have hzero : IsZero (sigma.obj i) := IsZero.of_mono_eq_zero f hfzero
    let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    have hzero' : IsZero (U.obj (sigma.obj i)) := U.map_isZero hzero
    have hsub : Subsingleton (sigma.obj i) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero'
    exact not_nontrivial_iff_subsingleton.mpr hsub
      (sigma.indecomposable i).nontrivial
  · exact H.isIso_of_ne_zero_endomorphism sigma i f

/-- Constructive form of the directed Schur conclusion: every endomorphism
of a chosen indecomposable is a scalar multiple of the identity. -/
theorem HasAcyclicNonzeroNonisomorphisms.endomorphism_eq_smul_id
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (i : Iota)
    (f : sigma.obj i ⟶ sigma.obj i) :
    ∃ c : K, c • 𝟙 (sigma.obj i) = f := by
  letI : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  letI : FiniteDimensional K (sigma.obj i ⟶ sigma.obj i) :=
    finiteDimensional_hom_obj K R sigma i i
  have hid : (𝟙 (sigma.obj i) : sigma.obj i ⟶ sigma.obj i) ≠ 0 := by
    intro hzero
    have hz : IsZero (sigma.obj i) :=
      IsZero.of_mono_eq_zero (𝟙 (sigma.obj i)) hzero
    let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    have hz' : IsZero (U.obj (sigma.obj i)) := U.map_isZero hz
    have hs : Subsingleton (sigma.obj i) :=
      ModuleCat.isZero_iff_subsingleton.mp hz'
    exact not_nontrivial_iff_subsingleton.mpr hs
      (sigma.indecomposable i).nontrivial
  exact
    ((finrank_eq_one_iff_of_nonzero' (𝟙 (sigma.obj i)) hid).mp
      (H.finrank_endomorphism_eq_one K R sigma i)) f

/-- In the chosen directed linear order, there are no maps strictly
backwards. -/
theorem hom_eq_zero_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    letI := directedLinearOrder sigma H
    ∀ {i j : Iota}, j < i → ∀ f : sigma.obj i ⟶ sigma.obj j, f = 0 := by
  letI := directedLinearOrder sigma H
  intro i j hji f
  by_contra hf
  have hne : i ≠ j := by
    intro hij
    subst j
    exact (lt_irrefl i) hji
  have hij := (directedLinearOrder_homOrderProperty sigma H) f hf hne
  exact (asymm hij hji).elim

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- Consequently every strictly lower-triangular Hom dimension vanishes. -/
theorem finrank_hom_eq_zero_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    letI := directedLinearOrder sigma H
    ∀ {i j : Iota}, j < i →
      Module.finrank K (sigma.obj i ⟶ sigma.obj j) = 0 := by
  letI := directedLinearOrder sigma H
  intro i j hji
  haveI : Subsingleton (sigma.obj i ⟶ sigma.obj j) :=
    ⟨fun f g => by
      rw [hom_eq_zero_of_lt R sigma H hji f,
        hom_eq_zero_of_lt R sigma H hji g]⟩
  exact Module.finrank_zero_of_subsingleton

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- The integral Hom-finrank matrix of the chosen indecomposable
representatives.  Under the finite-dimensional-algebra hypotheses used below,
these finranks are the actual finite Hom dimensions. -/
def homFinrankMatrix : Matrix Iota Iota ℤ :=
  fun i j => (Module.finrank K (sigma.obj i ⟶ sigma.obj j) : ℤ)

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- In the directed linear extension, the Hom-dimension matrix is upper
triangular. -/
theorem HasAcyclicNonzeroNonisomorphisms.homFinrankMatrix_blockTriangular
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    letI := directedLinearOrder sigma H
    (homFinrankMatrix K R sigma).BlockTriangular id := by
  letI := directedLinearOrder sigma H
  intro i j hji
  change j < i at hji
  change (Module.finrank K (sigma.obj i ⟶ sigma.obj j) : ℤ) = 0
  exact_mod_cast finrank_hom_eq_zero_of_lt K R sigma H hji

/-- Over an algebraically closed field, the Hom-dimension matrix has diagonal
entries one. -/
theorem HasAcyclicNonzeroNonisomorphisms.homFinrankMatrix_diagonal
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (i : Iota) :
    homFinrankMatrix K R sigma i i = 1 := by
  simp [homFinrankMatrix, H.finrank_endomorphism_eq_one K R sigma i]

end QuotientSubmoduleEquidistribution.RepresentationDirected
