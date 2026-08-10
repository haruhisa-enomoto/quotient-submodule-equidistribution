import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finsupp.Single

/-!
# Modules over a finite product of copies of a field

For a finite type `V`, modules over the function ring `V → K` are equivalent
to `V`-indexed families of `K`-modules.  This file constructs the forward
total-space functor and proves it full and faithful.  The inverse object
construction by coordinate idempotents is supplied in the companion file.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.PiRingModule

universe uK uV w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V]

/-- A family of vector spaces indexed by the primitive coordinates. -/
abbrev Family := V → ModuleCat.{w} K

/-- The product of a family, with the pointwise action of `V → K`. -/
abbrev Total (D : Family.{uK, uV, w} K V) := ∀ i, D i

/-- The product family as a module over the coordinate ring. -/
abbrev totalModuleCat (D : Family.{uK, uV, w} K V) :
    ModuleCat.{max uV w} (V → K) :=
  ModuleCat.of (V → K) (Total K V D)

/-- A pointwise family of linear maps induces a linear map of product-ring
modules. -/
def mapTotal {D E : Family.{uK, uV, w} K V} (f : D ⟶ E) :
    Total K V D →ₗ[V → K] Total K V E where
  toFun x i := f i (x i)
  map_add' x y := by
    funext i
    exact (f i).hom.map_add (x i) (y i)
  map_smul' s x := by
    funext i
    exact (f i).hom.map_smul (s i) (x i)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem mapTotal_apply {D E : Family.{uK, uV, w} K V} (f : D ⟶ E)
    (x : Total K V D) (i : V) :
    mapTotal (K := K) (V := V) f x i = f i (x i) := rfl

/-- Assemble a family of vector spaces into a module over `V → K`. -/
def totalFunctor :
    CategoryTheory.Functor (Family.{uK, uV, w} K V)
      (ModuleCat.{max uV w} (V → K)) where
  obj := totalModuleCat K V
  map f := ModuleCat.ofHom (mapTotal (K := K) (V := V) f)
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

/-- The coordinate idempotent at `i`. -/
def coordinateIdempotent (i : V) : V → K :=
  Pi.single i 1

omit [Fintype V] in
@[simp]
theorem coordinateIdempotent_apply_self (i : V) :
    coordinateIdempotent K V i i = 1 := by
  simp [coordinateIdempotent]

omit [Fintype V] in
theorem coordinateIdempotent_smul_total
    (D : Family.{uK, uV, w} K V) (i : V)
    (x : Total K V D) :
    coordinateIdempotent K V i • x = Pi.single i (x i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [coordinateIdempotent]
  · simp [coordinateIdempotent, h]

/-- The total-space functor remembers every component map. -/
instance totalFunctor_faithful : (totalFunctor K V).Faithful where
  map_injective := by
    intro D E f g h
    ext i x
    have h' := congrArg ModuleCat.Hom.hom h
    change mapTotal (K := K) (V := V) f =
      mapTotal (K := K) (V := V) g at h'
    have hx := DFunLike.congr_fun h'
      (Pi.single i x)
    simpa only [mapTotal_apply, Pi.single_eq_same] using congrFun hx i

/-- Every product-ring-linear map between total spaces is pointwise. -/
instance totalFunctor_full : (totalFunctor K V).Full where
  map_surjective := by
    intro D E f
    let F : Total K V D →ₗ[V → K] Total K V E := f.hom
    let component (i : V) : D i →ₗ[K] E i :=
      { toFun := fun x ↦ (F (Pi.single i x)) i
        map_add' := by
          intro x y
          calc
            (F (Pi.single i (x + y))) i =
                (F ((Pi.single i x : Total K V D) + Pi.single i y)) i := by
              rw [Pi.single_add]
            _ = (F (Pi.single i x)) i + (F (Pi.single i y)) i := by
              simpa only [Pi.add_apply] using congrFun
                (F.map_add (Pi.single i x) (Pi.single i y)) i
        map_smul' := by
          intro k x
          have h := congrFun
            (F.map_smul (fun _ ↦ k) (Pi.single i x)) i
          have hs : (fun _ : V ↦ k) •
                (Pi.single i x : Total K V D) =
              (Pi.single i (k • x) : Total K V D) := by
            funext j
            by_cases hj : j = i
            · subst j
              simp
            · simp [hj]
          rw [hs] at h
          change F (Pi.single i (k • x)) i =
            (RingHom.id K) k • F (Pi.single i x) i
          calc
            F (Pi.single i (k • x)) i =
                ((fun _ : V ↦ k) • F (Pi.single i x)) i := h
            _ = (RingHom.id K) k • F (Pi.single i x) i := rfl }
    let g : D ⟶ E := fun i ↦ ModuleCat.ofHom (component i)
    refine ⟨g, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change (F (Pi.single i (x i))) i = F x i
    have h := congrFun
      (F.map_smul (coordinateIdempotent K V i) x) i
    rw [coordinateIdempotent_smul_total] at h
    simpa [coordinateIdempotent] using h

end QuotientSubmoduleEquidistribution.PiRingModule
