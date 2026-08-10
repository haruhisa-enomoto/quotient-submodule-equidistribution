import QuotientSubmoduleEquidistribution.RepresentationTheory.PiRingModule
import Mathlib.Algebra.Module.BigOperators

/-!
# Coordinate-idempotent decomposition of product-ring modules

For finite `V`, every module over `V → K` is the product of the subspaces
fixed by the coordinate idempotents.  This proves essential surjectivity of
`PiRingModule.totalFunctor` and hence the expected category equivalence.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.PiRingModule

universe uK uV w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V]

omit [Fintype V] in
@[simp]
theorem coordinateIdempotent_mul_self (i : V) :
    coordinateIdempotent K V i * coordinateIdempotent K V i =
      coordinateIdempotent K V i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

omit [Fintype V] in
theorem coordinateIdempotent_mul_eq_zero {i j : V} (h : i ≠ j) :
    coordinateIdempotent K V i * coordinateIdempotent K V j = 0 := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [coordinateIdempotent, h]
  · simp [coordinateIdempotent, hi]

@[simp]
theorem sum_coordinateIdempotent :
    ∑ i : V, coordinateIdempotent K V i = 1 := by
  funext j
  simp [coordinateIdempotent]

omit [Fintype V] in
theorem mul_coordinateIdempotent (s : V → K) (i : V) :
    s * coordinateIdempotent K V i =
      algebraMap K (V → K) (s i) * coordinateIdempotent K V i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

/-- A tagged copy of the underlying additive group, used to register scalar
restriction along the diagonal map `K → V → K` without identifying two
different bundled `ModuleCat` carriers by definitional equality. -/
structure ScalarCarrier
    (X : ModuleCat.{max uV w} (V → K)) where
  val : X

namespace ScalarCarrier

/-- Forget the scalar-restriction tag. -/
def equiv (X : ModuleCat.{max uV w} (V → K)) : ScalarCarrier K V X ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] in
@[ext]
theorem ext {X : ModuleCat.{max uV w} (V → K)}
    {x y : ScalarCarrier K V X} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance (X : ModuleCat.{max uV w} (V → K)) :
    AddCommGroup (ScalarCarrier K V X) :=
  (equiv K V X).addCommGroup

instance (X : ModuleCat.{max uV w} (V → K)) :
    Module K (ScalarCarrier K V X) := by
  letI : Module K X := Module.compHom X (algebraMap K (V → K))
  exact (equiv K V X).module K

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem smul_val (X : ModuleCat.{max uV w} (V → K)) (k : K)
    (x : ScalarCarrier K V X) :
    (k • x).val = algebraMap K (V → K) k • x.val := rfl

end ScalarCarrier

/-- The subspace fixed by the coordinate idempotent at `i`. -/
def coordinateSubmodule
    (X : ModuleCat.{max uV w} (V → K)) (i : V) :
    Submodule K (ScalarCarrier K V X) where
  carrier := {x | coordinateIdempotent K V i • x.val = x.val}
  zero_mem' := by
    change coordinateIdempotent K V i • (0 : X) = 0
    exact smul_zero _
  add_mem' := by
    intro x y hx hy
    change coordinateIdempotent K V i • (x.val + y.val) = x.val + y.val
    change coordinateIdempotent K V i • x.val = x.val at hx
    change coordinateIdempotent K V i • y.val = y.val at hy
    rw [smul_add, hx, hy]
  smul_mem' := by
    intro k x hx
    change coordinateIdempotent K V i •
        ((algebraMap K (V → K) k) • x.val) =
      (algebraMap K (V → K) k) • x.val
    change coordinateIdempotent K V i • x.val = x.val at hx
    rw [← mul_smul, mul_comm, mul_smul, hx]

omit [Fintype V] in
@[simp]
theorem coordinateSubmodule_fixed
    (X : ModuleCat.{max uV w} (V → K)) (i : V)
    (x : coordinateSubmodule K V X i) :
    coordinateIdempotent K V i • x.val.val = x.val.val := by
  have h := x.property
  change coordinateIdempotent K V i • x.val.val = x.val.val at h
  exact h

/-- The family of coordinate subspaces of a product-ring module. -/
abbrev coordinateFamily
    (X : ModuleCat.{max uV w} (V → K)) : Family.{uK, uV, max uV w} K V :=
  fun i ↦ ModuleCat.of K (coordinateSubmodule K V X i)

omit [Fintype V] in
theorem scalar_smul_coordinate
    (X : ModuleCat.{max uV w} (V → K)) (s : V → K) (i : V)
    (x : coordinateSubmodule K V X i) :
    s • x.val.val =
      algebraMap K (V → K) (s i) • x.val.val := by
  calc
    s • x.val.val =
        s • (coordinateIdempotent K V i • x.val.val) := by
      rw [coordinateSubmodule_fixed]
    _ = (s * coordinateIdempotent K V i) • x.val.val := by
      rw [mul_smul]
    _ = (algebraMap K (V → K) (s i) *
          coordinateIdempotent K V i) • x.val.val := by
      rw [mul_coordinateIdempotent]
    _ = algebraMap K (V → K) (s i) •
        (coordinateIdempotent K V i • x.val.val) := by
      rw [mul_smul]
    _ = algebraMap K (V → K) (s i) • x.val.val := by
      rw [coordinateSubmodule_fixed]

omit [Fintype V] in
theorem coordinateIdempotent_smul_coordinate
    (X : ModuleCat.{max uV w} (V → K)) (i j : V)
    (x : coordinateSubmodule K V X i) :
    coordinateIdempotent K V j • x.val.val =
      if j = i then x.val.val else 0 := by
  by_cases h : j = i
  · subst j
    rw [coordinateSubmodule_fixed]
    simp
  · rw [← coordinateSubmodule_fixed K V X i x, ← mul_smul,
      coordinateIdempotent_mul_eq_zero K V h, zero_smul]
    simp [h]

/-- Sum the coordinate subspaces inside the original module. -/
def coordinateSumLinearMap
    (X : ModuleCat.{max uV w} (V → K)) :
    Total K V (coordinateFamily K V X) →ₗ[V → K] X where
  toFun x := ∑ i, (x i).val.val
  map_add' := by
    intro x y
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  map_smul' := by
    intro s x
    change (∑ i, algebraMap K (V → K) (s i) • (x i).val.val) =
      s • ∑ i, (x i).val.val
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (scalar_smul_coordinate K V X s i (x i)).symm

@[simp]
theorem coordinateSumLinearMap_apply
    (X : ModuleCat.{max uV w} (V → K))
    (x : Total K V (coordinateFamily K V X)) :
    coordinateSumLinearMap K V X x =
      ∑ i, (x i).val.val := rfl

/-- Projection onto one coordinate idempotent, as an endomorphism of the
product-ring module. -/
def coordinateProjection
    (X : ModuleCat.{max uV w} (V → K)) (j : V) : X →ₗ[V → K] X :=
  LinearMap.lsmul (V → K) X (coordinateIdempotent K V j)

omit [Fintype V] in
@[simp]
theorem coordinateProjection_apply
    (X : ModuleCat.{max uV w} (V → K)) (j : V) (x : X) :
    coordinateProjection K V X j x = coordinateIdempotent K V j • x := rfl

/-- The coordinate summation map is bijective. -/
theorem coordinateSumLinearMap_bijective
    (X : ModuleCat.{max uV w} (V → K)) :
    Function.Bijective (coordinateSumLinearMap K V X) := by
  constructor
  · intro x y h
    rw [coordinateSumLinearMap_apply, coordinateSumLinearMap_apply] at h
    funext j
    apply Subtype.ext
    apply ScalarCarrier.ext
    have hj := congrArg (coordinateProjection K V X j) h
    rw [map_sum, map_sum] at hj
    have hxproj :
        (∑ i, coordinateProjection K V X j
          (x i).val.val) = (x j).val.val := by
      rw [Finset.sum_eq_single j]
      · rw [coordinateProjection_apply, coordinateSubmodule_fixed]
      · intro i _ hij
        rw [coordinateProjection_apply,
          coordinateIdempotent_smul_coordinate]
        simp [hij.symm]
      · simp
    have hyproj :
        (∑ i, coordinateProjection K V X j
          (y i).val.val) = (y j).val.val := by
      rw [Finset.sum_eq_single j]
      · rw [coordinateProjection_apply, coordinateSubmodule_fixed]
      · intro i _ hij
        rw [coordinateProjection_apply,
          coordinateIdempotent_smul_coordinate]
        simp [hij.symm]
      · simp
    rw [hxproj, hyproj] at hj
    exact hj
  · intro x
    let y : Total K V (coordinateFamily K V X) := fun i ↦
      ⟨⟨coordinateIdempotent K V i • x⟩, by
        change coordinateIdempotent K V i •
            (coordinateIdempotent K V i • x) =
          coordinateIdempotent K V i • x
        rw [← mul_smul, coordinateIdempotent_mul_self]⟩
    refine ⟨y, ?_⟩
    rw [coordinateSumLinearMap_apply]
    change (∑ i, coordinateIdempotent K V i • x) = x
    rw [← Finset.sum_smul, sum_coordinateIdempotent, one_smul]

/-- The total space of the coordinate family recovers the original module. -/
def totalCoordinateIso
    (X : ModuleCat.{max uV w} (V → K)) :
    (totalFunctor K V).obj (coordinateFamily K V X) ≅ X :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective (coordinateSumLinearMap K V X)
      (coordinateSumLinearMap_bijective K V X))

instance totalFunctor_essSurj :
    (totalFunctor.{uK, uV, uV} K V).EssSurj where
  mem_essImage X :=
    ⟨coordinateFamily K V X, ⟨totalCoordinateIso K V X⟩⟩

instance totalFunctor_isEquivalence :
    (totalFunctor.{uK, uV, uV} K V).IsEquivalence where

/-- Modules over `V → K` are equivalent to `V`-indexed families of
`K`-modules. -/
def moduleEquivalence :
    Family.{uK, uV, uV} K V ≌ ModuleCat.{uV} (V → K) :=
  (totalFunctor.{uK, uV, uV} K V).asEquivalence

end QuotientSubmoduleEquidistribution.PiRingModule
