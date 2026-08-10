import OpConjecture.CategoryTheory.IyamaNakayamaExtraction
import OpConjecture.CategoryTheory.IyamaKrullSchmidtWeight
import OpConjecture.RepresentationDirected.IyamaMeshStrictness

/-!
# The categorical Nakayama bridge for Iyama strictness

This file connects the abstract finite-ladder Nakayama extraction theorem to
the numerical sign argument used for strict word meshes.  Its realization
structure contains only pre-strict categorical data and weight alignments: it
does not assume monicity or the endpoint-weight equality which strictness
requires.

No concrete algebra, quiver presentation, module enumeration, or module
classification is used here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected.IyamaMesh

open OpConjecture.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteAdmissibleTranslationQuiver

/-- Copies of labels prescribed by a valued right mesh. -/
abbrev MiddleIndex (Q : FiniteAdmissibleTranslationQuiver Ind)
    (x : Ind) := Σ y : Ind, Fin (Q.valuation y x)

/-- The finite biproduct prescribed by the valuation at a right mesh. -/
def middleObject (Q : FiniteAdmissibleTranslationQuiver Ind)
    (T : FiniteTauCategoryData C Ind) (x : Ind) : C :=
  ⨁ fun i : Q.MiddleIndex x ↦ T.obj i.1

/-- The canonical lift of a label weight evaluates on the prescribed middle
object as the numerical valuation sum. -/
theorem weight_middleObject
    (Q : FiniteAdmissibleTranslationQuiver Ind)
    (T : FiniteTauCategoryData C Ind)
    (weight : Ind → ℤ) (x : Ind) :
    (T.additiveObjectWeightOfLabelWeight weight).weight
        (Q.middleObject T x) =
      Q.thetaWeight weight x := by
  unfold middleObject
  rw [AdditiveObjectWeight.weight_biproduct]
  unfold thetaWeight
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y hy
  simp [T.additiveObjectWeightOfLabelWeight_obj]

end FiniteAdmissibleTranslationQuiver

/-- Pre-strict categorical data aligning a finite translation quiver with
the chosen indecomposable meshes of a finite tau-category.  No monicity or
endpoint-weight equality is assumed. -/
structure NakayamaStrictnessRealization
    (T : FiniteTauCategoryData C Ind)
    (Q : FiniteAdmissibleTranslationQuiver Ind) where
  projective_iff :
    ∀ x : Ind, x ∈ Q.projective ↔ T.IsProjective x
  tau_alignment :
    ∀ (x : T.Nonprojective) (hx : x.1 ∉ Q.projective),
      T.tauPlus x = Q.tauVertex x.1 hx
  middle_iso :
    ∀ x : Ind, Nonempty (T.thetaPlus x ≅ Q.middleObject T x)

namespace NakayamaStrictnessRealization

variable {T : FiniteTauCategoryData C Ind}
variable {Q : FiniteAdmissibleTranslationQuiver Ind}

/-- A quiver-nonprojective vertex gives the corresponding categorical
nonprojective label. -/
def nonprojective (R : NakayamaStrictnessRealization T Q)
    (x : Ind) (hx : x ∉ Q.projective) : T.Nonprojective :=
  ⟨x, fun h ↦ hx ((R.projective_iff x).mpr h)⟩

/-- The structural middle-term isomorphism gives the required numerical
weight alignment for every label weight. -/
theorem middle_weight
    (R : NakayamaStrictnessRealization T Q)
    (weight : Ind → ℤ) (x : Ind) :
    (T.additiveObjectWeightOfLabelWeight weight).weight (T.thetaPlus x) =
      Q.thetaWeight weight x := by
  calc
    (T.additiveObjectWeightOfLabelWeight weight).weight (T.thetaPlus x) =
        (T.additiveObjectWeightOfLabelWeight weight).weight
          (Q.middleObject T x) :=
      (T.additiveObjectWeightOfLabelWeight weight).iso_invariant
        (R.middle_iso x)
    _ = Q.thetaWeight weight x := Q.weight_middleObject T weight x

/-- Right additivity and the object/middle alignments imply the complete
off-projective Euler property. -/
theorem liftWeight_euler_offProjectives
    (R : NakayamaStrictnessRealization T Q)
    (weight : Ind → ℤ) (hadd : Q.IsPositiveRightAdditive weight)
    : (T.additiveObjectWeightOfLabelWeight weight).IsRightMeshEulerOffProjectives T := by
  let W := T.additiveObjectWeightOfLabelWeight weight
  apply W.isRightMeshEulerOffProjectives_of_obj
  intro x hx
  have hxQ : x ∉ Q.projective := fun h ↦
    hx ((R.projective_iff x).mp h)
  let X : T.Nonprojective := R.nonprojective x hxQ
  have htau : T.tauPlus X = Q.tauVertex x hxQ := by
    simpa only [X, nonprojective] using R.tau_alignment X hxQ
  have hleft :
      W.weight (T.rightMesh (T.obj x)).X₁ =
        W.weight (T.obj (T.tauPlus X)) :=
    W.iso_invariant ⟨T.tauPlusIso X⟩
  have hright :
      W.weight (T.rightMesh (T.obj x)).X₃ = W.weight (T.obj x) :=
    W.iso_invariant ⟨T.rightTermIso (T.obj x)⟩
  dsimp only [AdditiveObjectWeight.IsRightMeshEulerAt]
  rw [hleft, hright, T.additiveObjectWeightOfLabelWeight_obj,
    R.middle_weight weight, htau,
    T.additiveObjectWeightOfLabelWeight_obj]
  have h := hadd.2.1 x hxQ
  omega

/-- The numerical first-map weight is the categorical source-minus-target
weight of the compatible left mesh map at the translated label. -/
theorem nuWeight_eq_morphismWeight_muMinus
    (R : NakayamaStrictnessRealization T Q)
    (weight : Ind → ℤ)
    (x : Ind) (hx : x ∉ Q.projective) :
    Q.nuWeight weight x hx =
      (T.additiveObjectWeightOfLabelWeight weight).morphismWeight
        (T.muMinus (Q.tauVertex x hx)) := by
  let X : T.Nonprojective := R.nonprojective x hx
  let W : AdditiveObjectWeight C :=
    T.additiveObjectWeightOfLabelWeight weight
  have htau : T.tauPlus X = Q.tauVertex x hx := by
    simpa only [X, nonprojective] using R.tau_alignment X hx
  have hleft :
      W.weight (T.rightMesh (T.obj x)).X₁ =
        W.weight (T.obj (T.tauPlus X)) :=
    W.iso_invariant ⟨T.tauPlusIso X⟩
  have harrow :
      W.morphismWeight (T.nuPlus x) =
        W.morphismWeight (T.muMinus (T.tauPlus X)) :=
    W.morphismWeight_eq_of_arrowIso (T.firstMapIso X)
  calc
    Q.nuWeight weight x hx =
        weight (Q.tauVertex x hx) - Q.thetaWeight weight x := rfl
    _ = W.weight (T.obj (T.tauPlus X)) - W.weight (T.thetaPlus x) := by
      rw [htau, T.additiveObjectWeightOfLabelWeight_obj,
        R.middle_weight weight]
    _ = W.weight (T.rightMesh (T.obj x)).X₁ -
        W.weight (T.thetaPlus x) := by rw [hleft]
    _ = W.morphismWeight (T.nuPlus x) := rfl
    _ = W.morphismWeight (T.muMinus (T.tauPlus X)) := harrow
    _ = W.morphismWeight (T.muMinus (Q.tauVertex x hx)) := by
      rw [htau]

/-- The numerical second-map weight is the categorical source-minus-target
weight of the chosen right mesh map. -/
theorem muWeight_eq_morphismWeight_muPlus
    (R : NakayamaStrictnessRealization T Q)
    (weight : Ind → ℤ)
    (y : Ind) :
    Q.muWeight weight y =
      (T.additiveObjectWeightOfLabelWeight weight).morphismWeight
        (T.muPlus y) := by
  let W : AdditiveObjectWeight C :=
    T.additiveObjectWeightOfLabelWeight weight
  have hright :
      W.weight (T.rightMesh (T.obj y)).X₃ = W.weight (T.obj y) :=
    W.iso_invariant ⟨T.rightTermIso (T.obj y)⟩
  simp only [FiniteAdmissibleTranslationQuiver.muWeight,
    AdditiveObjectWeight.morphismWeight]
  rw [R.middle_weight weight, hright,
    T.additiveObjectWeightOfLabelWeight_obj]

/-- The pre-strict realization and the proved finite-ladder extraction
construct the exact numerical bridge consumed by Iyama's sign argument. -/
def toNakayamaStrictnessBridge
    (R : NakayamaStrictnessRealization T Q) :
    Q.NakayamaStrictnessBridge (fun x ↦ Mono (T.nuPlus x)) where
  nakayamaPair := T.NakayamaPair
  pair_of_not_monic := by
    intro x hx hmono
    let X : T.Nonprojective := R.nonprojective x hx
    have htau : T.tauPlus X = Q.tauVertex x hx := by
      simpa only [X, nonprojective] using R.tau_alignment X hx
    obtain ⟨y, hy, hpair⟩ :=
      T.exists_nakayamaPair_of_not_mono_nuPlus
        T.NakayamaPair T.hasMuMinusNakayamaExtraction X
        (T.not_isZero_thetaPlus X) hmono
    refine ⟨y, ?_, ?_⟩
    · intro hyQ
      exact hy ((R.projective_iff y).mp hyQ)
    · simpa only [htau] using hpair
  endpoint_weight_eq := by
    intro weight hadd x hx y hpair
    rw [R.nuWeight_eq_morphismWeight_muMinus weight x hx,
      R.muWeight_eq_morphismWeight_muPlus weight y]
    exact
      AdditiveObjectWeight.morphismWeight_muMinus_eq_muPlus_of_nakayamaPair_offProjectives
        (T.additiveObjectWeightOfLabelWeight weight)
        (R.liftWeight_euler_offProjectives weight hadd)
        NakayamaLadder.hasNonprojectiveRightSupport hpair

end NakayamaStrictnessRealization

end OpConjecture.RepresentationDirected.IyamaMesh
