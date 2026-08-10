import OpConjecture.RepresentationTheory.PiRingModuleEquivalence
import OpConjecture.RepresentationTheory.SeparatedQuiverArrowBimodule

/-!
# Extracting separated-quiver arrows from a balanced action

The coordinate idempotents of `V → K` split an arbitrary top module and
radical module into vertex spaces.  Applying a balanced arrow-bimodule action
to an arrow basis vector then gives the corresponding map from the source top
coordinate to the target radical coordinate.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.SeparatedQuiverArrowExtraction

open OpConjecture.SeparatedQuiver
open OpConjecture.SeparatedQuiverArrowBimodule
open OpConjecture.TrivSqZeroExtSeparatedData

universe uK uV v

variable (K : Type uK) (V : Type uV)
variable [Field K] [Fintype V] [DecidableEq V] [Quiver.{v} V]
variable [∀ i j : V, Fintype (i ⟶ j)] [∀ i j : V, DecidableEq (i ⟶ j)]

abbrev CoordinatedSeparatedData :=
  SeparatedData.{max uK uV, max uK uV v, uV}
    (S := V → K) (J := ArrowBimodule K V)

/-- The map attached to an arrow after splitting the top and radical by
coordinate idempotents. -/
def coordinateArrowMap
    (D : CoordinatedSeparatedData.{uK, uV, v} K V)
    {i j : V} (e : i ⟶ j) :
    PiRingModule.coordinateSubmodule K V D.top i →ₗ[K]
      PiRingModule.coordinateSubmodule K V D.radical j where
  toFun x :=
    ⟨⟨D.action (singleArrow K V e) x.val.val⟩, by
      change PiRingModule.coordinateIdempotent K V j •
          D.action (singleArrow K V e) x.val.val =
        D.action (singleArrow K V e) x.val.val
      rw [← D.action_left_smul,
        coordinateIdempotent_target_smul_singleArrow]⟩
  map_add' x y := by
    apply Subtype.ext
    apply PiRingModule.ScalarCarrier.ext
    exact map_add (D.action (singleArrow K V e)) x.val.val y.val.val
  map_smul' k x := by
    apply Subtype.ext
    apply PiRingModule.ScalarCarrier.ext
    change D.action (singleArrow K V e)
        (algebraMap K (V → K) k • x.val.val) =
      algebraMap K (V → K) k •
        D.action (singleArrow K V e) x.val.val
    rw [← D.action_right_smul]
    have hconst : algebraMap K (V → K) k = (fun _ : V ↦ k) := rfl
    rw [hconst, singleArrow_source_constant_eq_target_constant,
      D.action_left_smul]

/-- Every balanced arrow action determines literal separated-quiver
coordinate data on its vertex-idempotent summands. -/
def ofSeparatedData
    (D : CoordinatedSeparatedData.{uK, uV, v} K V) :
    RepresentationData.{uK, uV, v, uV} K V where
  plus := PiRingModule.coordinateFamily K V D.top
  minus := PiRingModule.coordinateFamily K V D.radical
  arrow e := ModuleCat.ofHom (coordinateArrowMap K V D e)

/-- On one top coordinate, a balanced action is the sum of the individual
arrow-basis actions with that source. -/
theorem action_on_coordinate_eq_sum
    (D : CoordinatedSeparatedData.{uK, uV, v} K V)
    (a : ArrowBimodule K V) (i : V)
    (x : PiRingModule.coordinateSubmodule K V D.top i) :
    D.action a x.val.val =
      ∑ j : V, ∑ e : i ⟶ j,
        (fun _ : V ↦ a i j e) •
          D.action (singleArrow K V e) x.val.val := by
  calc
    D.action a x.val.val =
        D.action a
          (PiRingModule.coordinateIdempotent K V i • x.val.val) := by
      rw [PiRingModule.coordinateSubmodule_fixed]
    _ = D.action
        (a <• PiRingModule.coordinateIdempotent K V i) x.val.val :=
      (D.action_right_smul a
        (PiRingModule.coordinateIdempotent K V i) x.val.val).symm
    _ = D.action
        (∑ j : V, ∑ e : i ⟶ j,
          (fun _ : V ↦ a i j e) • singleArrow K V e) x.val.val := by
      rw [sourceSlice_eq_sum]
    _ = ∑ j : V, ∑ e : i ⟶ j,
        (fun _ : V ↦ a i j e) •
          D.action (singleArrow K V e) x.val.val := by
      simp only [map_sum]
      simp only [AddMonoidHom.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro e _
      exact D.action_left_smul (fun _ : V ↦ a i j e)
        (singleArrow K V e) x.val.val

/-- Forget a coordinate-submodule tag. -/
def coordinateInclusion
    (X : ModuleCat.{uV} (V → K)) (i : V) :
    PiRingModule.coordinateSubmodule K V X i →+ X where
  toFun x := x.val.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The underlying vector of one aggregate target coordinate is the expected
sum of the extracted arrow-basis actions. -/
theorem aggregateAction_coordinate_val
    (D : CoordinatedSeparatedData.{uK, uV, v} K V)
    (a : ArrowBimodule K V)
    (x : PiRingModule.Total K V
      (PiRingModule.coordinateFamily K V D.top)) (j : V) :
    (aggregateAction K V (ofSeparatedData K V D) a x j).val.val =
      ∑ i : V, ∑ e : i ⟶ j,
        (fun _ : V ↦ a i j e) •
          D.action (singleArrow K V e) (x i).val.val := by
  change coordinateInclusion K V D.radical j
      (∑ i : V, ∑ e : i ⟶ j,
        a i j e • coordinateArrowMap K V D e (x i)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rfl

/-- Summing the extracted target coordinates intertwines the aggregate
literal arrow action with the original balanced action. -/
theorem coordinateSum_aggregateAction
    (D : CoordinatedSeparatedData.{uK, uV, v} K V)
    (a : ArrowBimodule K V)
    (x : PiRingModule.Total K V
      (PiRingModule.coordinateFamily K V D.top)) :
    PiRingModule.coordinateSumLinearMap K V D.radical
        (aggregateAction K V (ofSeparatedData K V D) a x) =
      D.action a (PiRingModule.coordinateSumLinearMap K V D.top x) := by
  rw [PiRingModule.coordinateSumLinearMap_apply,
    PiRingModule.coordinateSumLinearMap_apply]
  apply Eq.trans (Finset.sum_congr rfl (fun j _ ↦
    aggregateAction_coordinate_val K V D a x j))
  rw [map_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (action_on_coordinate_eq_sum K V D a i (x i)).symm

/-- The aggregate action reconstructed from the extracted arrow maps is
isomorphic to the original balanced separated datum. -/
def extractedIso
    (D : CoordinatedSeparatedData.{uK, uV, v} K V) :
    toSeparatedData K V (ofSeparatedData K V D) ≅ D := by
  let topIso := PiRingModule.totalCoordinateIso K V D.top
  let radicalIso := PiRingModule.totalCoordinateIso K V D.radical
  refine
    { hom := ⟨(topIso.hom.hom, radicalIso.hom.hom), ?_⟩
      inv := ⟨(topIso.inv.hom, radicalIso.inv.hom), ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro a x
    exact coordinateSum_aggregateAction K V D a x
  · intro a t
    have hRadicalInjective : Function.Injective radicalIso.hom.hom := by
      apply Function.LeftInverse.injective (g := radicalIso.inv.hom)
      intro y
      have h := congrArg ModuleCat.Hom.hom radicalIso.hom_inv_id
      change radicalIso.inv.hom.comp radicalIso.hom.hom = LinearMap.id at h
      exact DFunLike.congr_fun h y
    apply hRadicalInjective
    change radicalIso.hom.hom
        (radicalIso.inv.hom (D.action a t)) =
      radicalIso.hom.hom
        (aggregateAction K V (ofSeparatedData K V D) a
          (topIso.inv.hom t))
    have hAction := coordinateSum_aggregateAction K V D a
      (topIso.inv.hom t)
    change radicalIso.hom.hom
        (aggregateAction K V (ofSeparatedData K V D) a
          (topIso.inv.hom t)) =
      D.action a (topIso.hom.hom (topIso.inv.hom t)) at hAction
    rw [hAction]
    have hRadical := congrArg ModuleCat.Hom.hom radicalIso.inv_hom_id
    have hTop := congrArg ModuleCat.Hom.hom topIso.inv_hom_id
    change radicalIso.hom.hom.comp radicalIso.inv.hom =
      LinearMap.id at hRadical
    change topIso.hom.hom.comp topIso.inv.hom = LinearMap.id at hTop
    have hRadicalApply := DFunLike.congr_fun hRadical (D.action a t)
    have hTopApply := DFunLike.congr_fun hTop t
    change radicalIso.hom.hom (radicalIso.inv.hom (D.action a t)) =
      D.action a t at hRadicalApply
    change topIso.hom.hom (topIso.inv.hom t) = t at hTopApply
    rw [hRadicalApply, hTopApply]
  · apply Subtype.ext
    apply Prod.ext
    · exact congrArg ModuleCat.Hom.hom topIso.hom_inv_id
    · exact congrArg ModuleCat.Hom.hom radicalIso.hom_inv_id
  · apply Subtype.ext
    apply Prod.ext
    · exact congrArg ModuleCat.Hom.hom topIso.inv_hom_id
    · exact congrArg ModuleCat.Hom.hom radicalIso.inv_hom_id

instance toSeparatedDataFunctor_essSurj :
    (toSeparatedDataFunctor.{uK, uV, v, uV} (K := K) (V := V)).EssSurj where
  mem_essImage D :=
    ⟨ofSeparatedData K V D, ⟨extractedIso K V D⟩⟩

instance toSeparatedDataFunctor_isEquivalence :
    (toSeparatedDataFunctor.{uK, uV, v, uV} (K := K) (V := V)).IsEquivalence where

/-- Literal separated-quiver coordinate data are equivalent to balanced
actions of the finite quiver-arrow bimodule. -/
def arrowActionEquivalence :
    CategoryTheory.Equivalence
      (RepresentationData.{uK, uV, v, uV} K V)
      (CoordinatedSeparatedData.{uK, uV, v} K V) :=
  (toSeparatedDataFunctor.{uK, uV, v, uV} (K := K) (V := V)).asEquivalence

end OpConjecture.SeparatedQuiverArrowExtraction
