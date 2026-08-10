import OpConjecture.RepresentationTheory.PiRingModule
import OpConjecture.RepresentationTheory.SeparatedQuiverRepresentation
import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedData
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.MinimalAxioms

/-!
# The arrow bimodule of a finite quiver

For a finite quiver on `V`, let `S = V → K`.  Its arrow bimodule has one
copy of `K` for every arrow `e : i ⟶ j`.  The left action of `S` reads the
target coordinate `j`, while the right action reads the source coordinate
`i`.  Consequently, a balanced action of this bimodule from a product of
source spaces to a product of target spaces is precisely the aggregate of
the individual arrow maps.

This file constructs the resulting functor from literal separated-quiver
coordinate representations to abstract separated top/radical data and proves
that it is full and faithful.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.SeparatedQuiverArrowBimodule

open OpConjecture.SeparatedQuiver
open OpConjecture.TrivSqZeroExtSeparatedData

universe uK uV v w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V] [Quiver.{v} V]
variable [∀ i j : V, Fintype (i ⟶ j)] [∀ i j : V, DecidableEq (i ⟶ j)]

/-- The vector space with one coordinate for every arrow of the quiver. -/
abbrev ArrowBimodule := ∀ i j : V, (i ⟶ j) → K

instance : AddCommGroup (ArrowBimodule K V) :=
  inferInstanceAs (AddCommGroup (∀ i j : V, (i ⟶ j) → K))

/-- The coordinate ring acts from the left through arrow targets. -/
instance targetSMul : SMul (V → K) (ArrowBimodule K V) where
  smul s a := fun _ j e ↦ s j * a _ j e

/-- The target action makes the arrow space a left module over `V → K`. -/
instance targetModule : Module (V → K) (ArrowBimodule K V) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      funext i j e
      exact mul_add (r j) (x i j e) (y i j e))
    (by
      intro r s x
      funext i j e
      exact add_mul (r j) (s j) (x i j e))
    (by
      intro r s x
      funext i j e
      exact mul_assoc (r j) (s j) (x i j e))
    (by
      intro x
      funext i j e
      exact one_mul (x i j e))

/-- The coordinate ring acts from the right through arrow sources. -/
instance sourceSMul : SMul (V → K)ᵐᵒᵖ (ArrowBimodule K V) where
  smul s a := fun i _ e ↦ a i _ e * (MulOpposite.unop s) i

/-- The source action makes the arrow space a right module over `V → K`. -/
instance sourceModule : Module (V → K)ᵐᵒᵖ (ArrowBimodule K V) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      funext i j e
      exact add_mul (x i j e) (y i j e) ((MulOpposite.unop r) i))
    (by
      intro r s x
      funext i j e
      exact mul_add (x i j e) ((MulOpposite.unop r) i)
        ((MulOpposite.unop s) i))
    (by
      intro r s x
      funext i j e
      change x i j e * ((MulOpposite.unop s) i * (MulOpposite.unop r) i) =
        (x i j e * (MulOpposite.unop s) i) * (MulOpposite.unop r) i
      exact (mul_assoc _ _ _).symm)
    (by
      intro x
      funext i j e
      exact mul_one (x i j e))

instance : SMulCommClass (V → K) (V → K)ᵐᵒᵖ
    (ArrowBimodule K V) where
  smul_comm s t a := by
    funext i j e
    change s j * (a i j e * (MulOpposite.unop t) i) =
      (s j * a i j e) * (MulOpposite.unop t) i
    exact (mul_assoc _ _ _).symm

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem target_smul_apply (s : V → K) (a : ArrowBimodule K V)
    (i j : V) (e : i ⟶ j) :
    (s • a) i j e = s j * a i j e := rfl

omit [Fintype V] [DecidableEq V] [∀ i j : V, Fintype (i ⟶ j)]
    [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem source_smul_apply (a : ArrowBimodule K V) (s : V → K)
    (i j : V) (e : i ⟶ j) :
    (a <• s) i j e = a i j e * s i := rfl

/-- The arrow-basis vector belonging to `e : i ⟶ j`. -/
def singleArrow {i j : V} (e : i ⟶ j) : ArrowBimodule K V :=
  Pi.single i (Pi.single j (Pi.single e 1))

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem singleArrow_apply_self {i j : V} (e : i ⟶ j) :
    singleArrow K V e i j e = 1 := by
  simp [singleArrow]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem coordinateIdempotent_target_smul_singleArrow
    {i j : V} (e : i ⟶ j) :
    PiRingModule.coordinateIdempotent K V j • singleArrow K V e =
      singleArrow K V e := by
  funext i' j' e'
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      by_cases he : e' = e
      · subst e'
        simp [PiRingModule.coordinateIdempotent, singleArrow]
      · simp [PiRingModule.coordinateIdempotent, singleArrow, he]
    · simp [PiRingModule.coordinateIdempotent, singleArrow, hj]
  · simp [singleArrow, hi]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
theorem coordinateIdempotent_target_smul_singleArrow_eq_zero
    {i j k : V} (e : i ⟶ j) (h : k ≠ j) :
    PiRingModule.coordinateIdempotent K V k • singleArrow K V e = 0 := by
  funext i' j' e'
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      simp [PiRingModule.coordinateIdempotent, singleArrow, h]
    · simp [PiRingModule.coordinateIdempotent, singleArrow, hj]
  · simp [singleArrow, hi]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
@[simp]
theorem singleArrow_source_smul_coordinateIdempotent
    {i j : V} (e : i ⟶ j) :
    singleArrow K V e <• PiRingModule.coordinateIdempotent K V i =
      singleArrow K V e := by
  funext i' j' e'
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      by_cases he : e' = e
      · subst e'
        simp [PiRingModule.coordinateIdempotent, singleArrow]
      · simp [PiRingModule.coordinateIdempotent, singleArrow, he]
    · simp [singleArrow, hj]
  · simp [PiRingModule.coordinateIdempotent, singleArrow, hi]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
theorem singleArrow_source_smul_coordinateIdempotent_eq_zero
    {i j k : V} (e : i ⟶ j) (h : k ≠ i) :
    singleArrow K V e <• PiRingModule.coordinateIdempotent K V k = 0 := by
  funext i' j' e'
  by_cases hi : i' = i
  · subst i'
    simp [PiRingModule.coordinateIdempotent, singleArrow, h]
  · simp [PiRingModule.coordinateIdempotent, singleArrow, hi]

omit [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] in
theorem singleArrow_source_constant_eq_target_constant
    {i j : V} (e : i ⟶ j) (k : K) :
    singleArrow K V e <• (fun _ : V ↦ k) =
      (fun _ : V ↦ k) • singleArrow K V e := by
  funext i' j' e'
  change singleArrow K V e i' j' e' * k =
    k * singleArrow K V e i' j' e'
  exact mul_comm _ _

/-- Restricting an arrow vector to one source coordinate is its finite
expansion in the arrow basis with that source. -/
theorem sourceSlice_eq_sum
    (a : ArrowBimodule K V) (i : V) :
    a <• PiRingModule.coordinateIdempotent K V i =
      ∑ j : V, ∑ e : i ⟶ j,
        (fun _ : V ↦ a i j e) • singleArrow K V e := by
  change (fun i' j' e' ↦
      a i' j' e' * (Pi.single i (1 : K) : V → K) i') =
    ∑ j : V, ∑ e : i ⟶ j,
      (fun _ : V ↦ a i j e) • singleArrow K V e
  apply funext
  intro i'
  rw [Finset.sum_apply]
  apply funext
  intro j'
  simp_rw [Finset.sum_apply]
  apply funext
  intro e'
  simp_rw [Finset.sum_apply]
  simp only [target_smul_apply]
  by_cases hi : i' = i
  · subst i'
    rw [Pi.single_eq_same, mul_one, Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single e']
      · simp [singleArrow]
      · intro e _ he
        simp [singleArrow, he]
      · simp
    · intro j _ hj
      simp [singleArrow, hj]
    · simp
  · simp [singleArrow, hi]

/-- Aggregate the arrow maps of a separated-quiver representation. -/
def aggregateAction
    (D : RepresentationData.{uK, uV, v, w} K V)
    (a : ArrowBimodule K V) (t : PiRingModule.Total K V D.plus) :
    PiRingModule.Total K V D.minus :=
  fun j ↦ ∑ i : V, ∑ e : i ⟶ j, a i j e • D.arrow e (t i)

@[simp]
theorem aggregateAction_singleArrow_singleTop
    (D : RepresentationData.{uK, uV, v, w} K V)
    {i j : V} (e : i ⟶ j) (x : D.plus i) :
    aggregateAction K V D (singleArrow K V e) (Pi.single i x) =
      Pi.single j (D.arrow e x) := by
  funext k
  by_cases hk : k = j
  · subst k
    simp only [aggregateAction, Pi.single_eq_same]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single e]
      · simp [singleArrow]
      · intro e' _ he'
        simp [singleArrow, he']
      · simp
    · intro i' _ hi'
      simp [singleArrow, hi']
    · simp
  · simp only [aggregateAction]
    rw [Pi.single_eq_of_ne hk]
    apply Finset.sum_eq_zero
    intro i' _
    by_cases hi' : i' = i
    · subst i'
      simp [singleArrow, hk]
    · simp [singleArrow, hi']

omit [DecidableEq V] [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem aggregateAction_add_arrow
    (D : RepresentationData.{uK, uV, v, w} K V)
    (a b : ArrowBimodule K V) (t : PiRingModule.Total K V D.plus) :
    aggregateAction K V D (a + b) t =
      aggregateAction K V D a t + aggregateAction K V D b t := by
  funext j
  change (∑ i : V, ∑ e : i ⟶ j,
      (a i j e + b i j e) • D.arrow e (t i)) =
    (∑ i : V, ∑ e : i ⟶ j, a i j e • D.arrow e (t i)) +
      ∑ i : V, ∑ e : i ⟶ j, b i j e • D.arrow e (t i)
  simp only [add_smul, Finset.sum_add_distrib]

omit [DecidableEq V] [∀ i j : V, DecidableEq (i ⟶ j)] in
@[simp]
theorem aggregateAction_add_top
    (D : RepresentationData.{uK, uV, v, w} K V)
    (a : ArrowBimodule K V) (t u : PiRingModule.Total K V D.plus) :
    aggregateAction K V D a (t + u) =
      aggregateAction K V D a t + aggregateAction K V D a u := by
  funext j
  simp only [aggregateAction, Pi.add_apply, map_add, smul_add,
    Finset.sum_add_distrib]

/-- The aggregate arrow action, additive in both the arrow and top inputs. -/
def aggregateActionHom
    (D : RepresentationData.{uK, uV, v, w} K V) :
    ArrowBimodule K V →+
      (PiRingModule.Total K V D.plus →+
        PiRingModule.Total K V D.minus) where
  toFun a :=
    { toFun := aggregateAction K V D a
      map_zero' := by
        funext j
        simp [aggregateAction]
      map_add' := aggregateAction_add_top K V D a }
  map_zero' := by
    apply AddMonoidHom.ext
    intro t
    funext j
    change (∑ i : V, ∑ e : i ⟶ j,
      (0 : K) • D.arrow e (t i)) = 0
    simp
  map_add' a b := by
    apply AddMonoidHom.ext
    intro t
    exact aggregateAction_add_arrow K V D a b t

omit [DecidableEq V] [∀ i j : V, DecidableEq (i ⟶ j)] in
theorem aggregateAction_left_smul
    (D : RepresentationData.{uK, uV, v, w} K V)
    (s : V → K) (a : ArrowBimodule K V)
    (t : PiRingModule.Total K V D.plus) :
    aggregateActionHom K V D (s • a) t =
      s • aggregateActionHom K V D a t := by
  funext j
  change (∑ i : V, ∑ e : i ⟶ j,
      (s j * a i j e) • D.arrow e (t i)) =
    s j • ∑ i : V, ∑ e : i ⟶ j,
      a i j e • D.arrow e (t i)
  simp only [mul_smul, Finset.smul_sum]

omit [DecidableEq V] [∀ i j : V, DecidableEq (i ⟶ j)] in
theorem aggregateAction_right_smul
    (D : RepresentationData.{uK, uV, v, w} K V)
    (a : ArrowBimodule K V) (s : V → K)
    (t : PiRingModule.Total K V D.plus) :
    aggregateActionHom K V D (a <• s) t =
      aggregateActionHom K V D a (s • t) := by
  funext j
  change (∑ i : V, ∑ e : i ⟶ j,
      (a i j e * s i) • D.arrow e (t i)) =
    ∑ i : V, ∑ e : i ⟶ j,
      a i j e • D.arrow e (s i • t i)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro e _
  rw [mul_smul, map_smul]

/-- Literal separated-quiver coordinates as balanced separated data over the
vertex ring and arrow bimodule. -/
def toSeparatedData
    (D : RepresentationData.{uK, uV, v, w} K V) :
    SeparatedData (S := V → K) (J := ArrowBimodule K V) where
  top := PiRingModule.totalModuleCat K V D.plus
  radical := PiRingModule.totalModuleCat K V D.minus
  action := aggregateActionHom K V D
  action_left_smul := aggregateAction_left_smul K V D
  action_right_smul := aggregateAction_right_smul K V D

/-- A morphism of literal coordinate representations acts componentwise on
the aggregated top and radical spaces. -/
def toSeparatedDataMap
    {D E : RepresentationData.{uK, uV, v, w} K V} (f : D ⟶ E) :
    toSeparatedData K V D ⟶ toSeparatedData K V E :=
  ⟨(PiRingModule.mapTotal (K := K) (V := V) f.plus,
      PiRingModule.mapTotal (K := K) (V := V) f.minus), by
    intro a t
    funext j
    change f.minus j
        (∑ i : V, ∑ e : i ⟶ j, a i j e • D.arrow e (t i)) =
      ∑ i : V, ∑ e : i ⟶ j,
        a i j e • E.arrow e (f.plus i (t i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [map_smul]
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.comm e)) (t i)
    exact congrArg (fun x ↦ a i j e • x) h⟩

/-- The functor from literal separated-quiver coordinates to balanced arrow
bimodule actions. -/
def toSeparatedDataFunctor :
    CategoryTheory.Functor
      (RepresentationData.{uK, uV, v, w} K V)
      (SeparatedData (S := V → K) (J := ArrowBimodule K V)) where
  obj := toSeparatedData K V
  map := toSeparatedDataMap K V
  map_id _ := by rfl
  map_comp _ _ := by rfl

/-- The aggregation functor remembers every component map. -/
instance toSeparatedDataFunctor_faithful :
    (toSeparatedDataFunctor (K := K) (V := V)).Faithful where
  map_injective := by
    intro D E f g h
    apply RepresentationData.Hom.ext
    · apply (PiRingModule.totalFunctor K V).map_injective
      exact congrArg (fun q ↦ ModuleCat.ofHom q.val.1) h
    · apply (PiRingModule.totalFunctor K V).map_injective
      exact congrArg (fun q ↦ ModuleCat.ofHom q.val.2) h

/-- Every morphism between aggregated separated data is componentwise. -/
instance toSeparatedDataFunctor_full :
    (toSeparatedDataFunctor (K := K) (V := V)).Full where
  map_surjective := by
    intro D E f
    let F := PiRingModule.totalFunctor K V
    let fPlus : D.plus ⟶ E.plus := F.preimage (ModuleCat.ofHom f.val.1)
    let fMinus : D.minus ⟶ E.minus := F.preimage (ModuleCat.ofHom f.val.2)
    have hPlus : ModuleCat.ofHom (PiRingModule.mapTotal (K := K) (V := V) fPlus) =
        ModuleCat.ofHom f.val.1 := F.map_preimage _
    have hMinus : ModuleCat.ofHom (PiRingModule.mapTotal (K := K) (V := V) fMinus) =
        ModuleCat.ofHom f.val.2 := F.map_preimage _
    let g : D ⟶ E :=
      { plus := fPlus
        minus := fMinus
        comm := by
          intro i j e
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          have h := congrFun (f.property (singleArrow K V e) (Pi.single i x)) j
          have hPlusHom := congrArg ModuleCat.Hom.hom hPlus
          have hMinusHom := congrArg ModuleCat.Hom.hom hMinus
          change PiRingModule.mapTotal (K := K) (V := V) fPlus = f.val.1 at hPlusHom
          change PiRingModule.mapTotal (K := K) (V := V) fMinus = f.val.2 at hMinusHom
          rw [← hPlusHom, ← hMinusHom] at h
          change (PiRingModule.mapTotal (K := K) (V := V) fMinus
              (aggregateAction K V D (singleArrow K V e) (Pi.single i x))) j =
            aggregateAction K V E (singleArrow K V e)
              (PiRingModule.mapTotal (K := K) (V := V) fPlus (Pi.single i x)) j at h
          have hMap :
              PiRingModule.mapTotal (K := K) (V := V) fPlus (Pi.single i x) =
                Pi.single i (fPlus i x) := by
            funext k
            by_cases hk : k = i
            · subst k
              simp
            · simp [hk]
          rw [aggregateAction_singleArrow_singleTop, hMap,
            aggregateAction_singleArrow_singleTop] at h
          simp only [PiRingModule.mapTotal_apply, Pi.single_eq_same] at h
          change fMinus j (D.arrow e x) = E.arrow e (fPlus i x)
          exact h }
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg ModuleCat.Hom.hom hPlus
    · exact congrArg ModuleCat.Hom.hom hMinus

end OpConjecture.SeparatedQuiverArrowBimodule
