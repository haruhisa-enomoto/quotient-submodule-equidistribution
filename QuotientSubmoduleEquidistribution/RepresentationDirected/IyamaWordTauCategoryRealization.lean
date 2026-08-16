import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordSelectedSegments
import QuotientSubmoduleEquidistribution.RepresentationDirected.HomBiproductFinrank
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaTauCategoryRepresentableMesh

/-!
# Word presentations of finite tau-categories

This file connects a literal finite tau-category to the word-mesh numerical
interface.  Its hypotheses are only the structural identifications of the
left and middle terms with the predecessor and middle positions of the word.
The resulting mesh-exactness data records the actual Hom dimensions of the
given category.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh

open QuotientSubmoduleEquidistribution.Iyama
open QuotientSubmoduleEquidistribution.RepresentationDirected
open QuotientSubmoduleEquidistribution.RepresentationDirected.PrincipalPositivity
open QuotientSubmoduleEquidistribution.RepresentationDirected.MeshExactness

universe uK v u w uL

variable {K : Type uK} [Field K]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind] [DecidableEq Ind]
variable {L : Type uL}

/-- A word-indexed presentation of the chosen right meshes in a literal
finite tau-category. -/
structure WordTauCategoryRealization
    (T : FiniteTauCategoryData C Ind)
    (G : SimpleGraph L) (Q : List L)
    (label : Fin Q.length ≃ Ind) where
  projective_iff :
    ∀ x : Fin Q.length,
      T.IsProjective (label x) ↔ ¬ ∃ p, ARWord.IsPrevious Q p x
  left_iso :
    ∀ x : Fin Q.length,
      (T.rightMesh (T.obj (label x))).X₁ ≅
        ⨁ fun p : {p : Fin Q.length // ARWord.IsPrevious Q p x} ↦
          T.obj (label p.1)
  middle_iso :
    ∀ x : Fin Q.length,
      T.thetaPlus (label x) ≅
        ⨁ fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
          T.obj (label y.1)

namespace WordTauCategoryRealization

variable {T : FiniteTauCategoryData C Ind}
variable {G : SimpleGraph L} {Q : List L}
variable {label : Fin Q.length ≃ Ind}

/-- Transport a word-position weight to the indecomposable labels of the
literal tau-category. -/
def labelWeight (_R : WordTauCategoryRealization T G Q label)
    (weight : Fin Q.length → ℤ) : Ind → ℤ :=
  fun i ↦ weight (label.symm i)

@[simp]
theorem labelWeight_label (weight : Fin Q.length → ℤ)
    (R : WordTauCategoryRealization T G Q label)
    (x : Fin Q.length) :
    R.labelWeight weight (label x) = weight x := by
  simp [labelWeight]

/-- The categorical middle-term weight is the word's scalar middle sum. -/
theorem middle_weight
    (R : WordTauCategoryRealization T G Q label)
    (weight : Fin Q.length → ℤ) (x : Fin Q.length) :
    (T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)).weight
        (T.thetaPlus (label x)) =
      scalarMiddleSum G Q weight x := by
  classical
  let W := T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)
  calc
    W.weight (T.thetaPlus (label x)) =
        W.weight
          (⨁ fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
            T.obj (label y.1)) :=
      W.iso_invariant ⟨R.middle_iso x⟩
    _ = ∑ y : {y : Fin Q.length // ARWord.IsMiddle G Q y x},
          W.weight (T.obj (label y.1)) := W.weight_biproduct _
    _ = ∑ y : {y : Fin Q.length // ARWord.IsMiddle G Q y x},
          weight y.1 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [T.additiveObjectWeightOfLabelWeight_obj]
      exact R.labelWeight_label weight y.1
    _ = scalarMiddleSum G Q weight x :=
      subtypeMiddleSum_eq_scalarMiddleSum G Q weight x

/-- At a repeated letter, the categorical left-term weight is the weight of
the unique predecessor. -/
theorem left_weight_of_previous
    (R : WordTauCategoryRealization T G Q label)
    (weight : Fin Q.length → ℤ)
    (p x : Fin Q.length) (hp : ARWord.IsPrevious Q p x) :
    (T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)).weight
        (T.rightMesh (T.obj (label x))).X₁ = weight p := by
  classical
  let W := T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)
  let p₀ : {q : Fin Q.length // ARWord.IsPrevious Q q x} := ⟨p, hp⟩
  calc
    W.weight (T.rightMesh (T.obj (label x))).X₁ =
        W.weight
          (⨁ fun q : {q : Fin Q.length // ARWord.IsPrevious Q q x} ↦
            T.obj (label q.1)) := W.iso_invariant ⟨R.left_iso x⟩
    _ = ∑ q : {q : Fin Q.length // ARWord.IsPrevious Q q x},
          W.weight (T.obj (label q.1)) := W.weight_biproduct _
    _ = ∑ q : {q : Fin Q.length // ARWord.IsPrevious Q q x},
          weight q.1 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [T.additiveObjectWeightOfLabelWeight_obj]
      exact R.labelWeight_label weight q.1
    _ = weight p := by
      apply Finset.sum_eq_single p₀
      · intro q _ hq
        exact (hq (Subtype.ext (ARWord.isPrevious_unique q.2 hp))).elim
      · intro hp₀
        exact (hp₀ (Finset.mem_univ p₀)).elim

/-- At a first letter, the categorical left-term weight vanishes. -/
theorem left_weight_of_first
    (R : WordTauCategoryRealization T G Q label)
    (weight : Fin Q.length → ℤ) (x : Fin Q.length)
    (hfirst : ¬ ∃ p, ARWord.IsPrevious Q p x) :
    (T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)).weight
        (T.rightMesh (T.obj (label x))).X₁ = 0 := by
  apply AdditiveObjectWeight.weight_eq_zero_of_isZero
    (T.additiveObjectWeightOfLabelWeight (R.labelWeight weight))
  exact (R.projective_iff x).2 hfirst

/-- A positive right-additive word weight is literally a positive
right-additive label weight on the realized tau-category. -/
theorem isPositiveRightAdditiveLabelWeight
    (R : WordTauCategoryRealization T G Q label)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.FiniteTauCategoryData.IsPositiveRightAdditiveLabelWeight
      T (R.labelWeight weight) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    simpa [labelWeight] using hweight.1 (label.symm i)
  · intro i
    let x := label.symm i
    have hi : label x = i := label.apply_symm_apply i
    rw [← hi]
    have hright :
        (T.additiveObjectWeightOfLabelWeight (R.labelWeight weight)).weight
            (T.rightMesh (T.obj (label x))).X₃ = weight x := by
      calc
        _ = (T.additiveObjectWeightOfLabelWeight
              (R.labelWeight weight)).weight (T.obj (label x)) :=
          (T.additiveObjectWeightOfLabelWeight
            (R.labelWeight weight)).iso_invariant
              ⟨T.rightTermIso (T.obj (label x))⟩
        _ = R.labelWeight weight (label x) :=
          T.additiveObjectWeightOfLabelWeight_obj _ _
        _ = weight x := R.labelWeight_label weight x
    rw [R.middle_weight weight x, hright]
    by_cases hprev : ∃ p, ARWord.IsPrevious Q p x
    · obtain ⟨p, hp⟩ := hprev
      rw [R.left_weight_of_previous weight p x hp]
      have heq := hweight.2.1 p x hp
      refine ⟨by linarith [heq], ?_⟩
      intro _
      linarith [heq]
    · rw [R.left_weight_of_first weight x hprev]
      have hpos := hweight.2.2 x hprev
      refine ⟨by linarith [hpos], ?_⟩
      intro hnonprojective
      exact (hnonprojective ((R.projective_iff x).2 hprev)).elim

/-- Relabel the standard diagonal simple fiber along an injective label
equivalence. -/
def simpleFiberLinearEquiv (a x : Fin Q.length) :
    SimpleRepresentableFiber K (label a) (label x) ≃ₗ[K]
      SimpleRepresentableFiber K a x :=
  LinearEquiv.ofFinrankEq (R := K) _ _ (by
    rw [finrank_simpleRepresentableFiber (K := K),
      finrank_simpleRepresentableFiber (K := K)]
    simp only [label.injective.eq_iff])

/-- Hom spaces into the categorical left mesh terms are finite-dimensional
whenever the vertex-to-vertex Hom spaces are. -/
theorem finite_leftHom
    (R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (a x : Fin Q.length) :
    Module.Finite K
      (T.obj (label a) ⟶ (T.rightMesh (T.obj (label x))).X₁) := by
  classical
  let eHom :
      (T.obj (label a) ⟶ (T.rightMesh (T.obj (label x))).X₁) ≃ₗ[K]
        (T.obj (label a) ⟶
          ⨁ fun p : {p : Fin Q.length // ARWord.IsPrevious Q p x} ↦
            T.obj (label p.1)) :=
    Linear.homCongr K (Iso.refl (T.obj (label a))) (R.left_iso x)
  letI : Module.Finite K
      (∀ p : {p : Fin Q.length // ARWord.IsPrevious Q p x},
        T.obj (label a) ⟶ T.obj (label p.1)) := inferInstance
  letI : Module.Finite K
      (T.obj (label a) ⟶
        ⨁ fun p : {p : Fin Q.length // ARWord.IsPrevious Q p x} ↦
          T.obj (label p.1)) :=
    Module.Finite.equiv
      (QuotientSubmoduleEquidistribution.RepresentationDirected.homLinearEquivBiproduct
        (T.obj (label a))
        (fun p : {p : Fin Q.length // ARWord.IsPrevious Q p x} ↦
          T.obj (label p.1))).symm
  exact Module.Finite.equiv eHom.symm

/-- Hom spaces into the categorical middle mesh terms are
finite-dimensional whenever the vertex-to-vertex Hom spaces are. -/
theorem finite_middleHom
    (R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (a x : Fin Q.length) :
    Module.Finite K (T.obj (label a) ⟶ T.thetaPlus (label x)) := by
  classical
  let eHom :
      (T.obj (label a) ⟶ T.thetaPlus (label x)) ≃ₗ[K]
        (T.obj (label a) ⟶
          ⨁ fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
            T.obj (label y.1)) :=
    Linear.homCongr K (Iso.refl (T.obj (label a))) (R.middle_iso x)
  letI : Module.Finite K
      (∀ y : {y : Fin Q.length // ARWord.IsMiddle G Q y x},
        T.obj (label a) ⟶ T.obj (label y.1)) := inferInstance
  letI : Module.Finite K
      (T.obj (label a) ⟶
        ⨁ fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
          T.obj (label y.1)) :=
    Module.Finite.equiv
      (QuotientSubmoduleEquidistribution.RepresentationDirected.homLinearEquivBiproduct
        (T.obj (label a))
        (fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
          T.obj (label y.1))).symm
  exact Module.Finite.equiv eHom.symm

/-- Pull the categorical representable mesh complex back along the word's
position-label equivalence. -/
def rightRepresentableMeshComplex
    (_R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈
          T.radicalHomSubmodule (K := K) x x) :
    RightRepresentableMeshComplex (K := K)
      (fun x ↦ T.obj (label x))
      (fun x ↦ (T.rightMesh (T.obj (label x))).X₁)
      (fun x ↦ T.thetaPlus (label x)) where
  nu x := T.nuPlus (label x)
  mu x := T.representableMeshMu (label x)
  simpleQuotient a x :=
    (simpleFiberLinearEquiv (K := K) (label := label) a x).toLinearMap.comp
      (T.categoricalSimpleQuotient (K := K) scalar_mod_radical
        (label a) (label x))
  exact_at_middle a x :=
    T.exact_at_representableMesh_middle (K := K) (label a) (label x)
  exact_at_right a x :=
    by
      intro f
      constructor
      · intro hf
        have hf' : T.categoricalSimpleQuotient (K := K)
            scalar_mod_radical (label a) (label x) f = 0 := by
          exact (simpleFiberLinearEquiv (K := K)
            (label := label) a x).injective (by simpa using hf)
        exact (T.exact_at_representableMesh_right (K := K)
          scalar_mod_radical (label a) (label x) f).mp hf'
      · rintro ⟨g, rfl⟩
        change (simpleFiberLinearEquiv (K := K) (label := label) a x)
          (T.categoricalSimpleQuotient (K := K) scalar_mod_radical
            (label a) (label x)
            (g ≫ T.representableMeshMu (label x))) = 0
        rw [(T.exact_at_representableMesh_right (K := K)
          scalar_mod_radical (label a) (label x)
          (g ≫ T.representableMeshMu (label x))).mpr ⟨g, rfl⟩,
          map_zero]
  simpleQuotient_surjective a x :=
    (simpleFiberLinearEquiv (K := K)
      (label := label) a x).surjective.comp
      (T.categoricalSimpleQuotient_surjective (K := K) scalar_mod_radical
        (label a) (label x))

/-- The word presentation turns the literal categorical mesh complexes into
the standard word realization. -/
def wordRightMeshRealization
    (R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈
          T.radicalHomSubmodule (K := K) x x) :
    WordRightMeshRealization (K := K) G Q
      (fun x ↦ T.obj (label x))
      (fun x ↦ (T.rightMesh (T.obj (label x))).X₁)
      (fun x ↦ T.thetaPlus (label x)) := by
  classical
  letI finiteLeft : ∀ a x : Fin Q.length,
      Module.Finite K
        (T.obj (label a) ⟶ (T.rightMesh (T.obj (label x))).X₁) :=
    fun a x ↦ R.finite_leftHom (K := K) a x
  letI finiteMiddle : ∀ a x : Fin Q.length,
      Module.Finite K
        (T.obj (label a) ⟶ T.thetaPlus (label x)) :=
    fun a x ↦ R.finite_middleHom (K := K) a x
  exact
    { toRightRepresentableMeshComplex :=
        R.rightRepresentableMeshComplex (K := K) scalar_mod_radical
      left_finrank_of_previous := by
        intro a p x hp
        exact (Linear.homCongr K (Iso.refl _) (R.left_iso x)).finrank_eq.trans <| by
          rw [(QuotientSubmoduleEquidistribution.RepresentationDirected.homLinearEquivBiproduct
            (T.obj (label a))
            (fun q : {q : Fin Q.length // ARWord.IsPrevious Q q x} ↦
              T.obj (label q.1))).finrank_eq,
            Module.finrank_pi_fintype K]
          let p₀ : {q : Fin Q.length // ARWord.IsPrevious Q q x} := ⟨p, hp⟩
          apply Finset.sum_eq_single p₀
          · intro q _ hq
            exact (hq (Subtype.ext (ARWord.isPrevious_unique q.2 hp))).elim
          · intro hp₀
            exact (hp₀ (Finset.mem_univ p₀)).elim
      left_isZero_of_first := by
        intro x hfirst
        exact (R.projective_iff x).2 hfirst
      middle_finrank := by
        intro a x
        calc
          Module.finrank K
              (T.obj (label a) ⟶ T.thetaPlus (label x)) =
              Module.finrank K
                (T.obj (label a) ⟶
                  ⨁ fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
                    T.obj (label y.1)) :=
            (Linear.homCongr K (Iso.refl _) (R.middle_iso x)).finrank_eq
          _ = ∑ y : {y : Fin Q.length // ARWord.IsMiddle G Q y x},
                Module.finrank K
                  (T.obj (label a) ⟶ T.obj (label y.1)) :=
            by
              rw [(QuotientSubmoduleEquidistribution.RepresentationDirected.homLinearEquivBiproduct
                (T.obj (label a))
                (fun y : {y : Fin Q.length // ARWord.IsMiddle G Q y x} ↦
                  T.obj (label y.1))).finrank_eq,
                Module.finrank_pi_fintype K]
          _ = wordMiddleFinrank G Q
                (fun b y ↦ Module.finrank K
                  (T.obj (label b) ⟶ T.obj (label y))) a x := by
            unfold wordMiddleFinrank
            symm
            apply Finset.sum_subtype
            intro y
            simp }

/-- A positive right-additive word weight produces exact mesh data whose
entries are the actual Hom dimensions of the realized tau-category. -/
def toRepresentableMeshExactnessData
    (R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈
          T.radicalHomSubmodule (K := K) x x)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight) :
    RepresentableMeshExactnessData G Q := by
  classical
  let E := R.wordRightMeshRealization (K := K) scalar_mod_radical
  let hcategorical := R.isPositiveRightAdditiveLabelWeight weight hweight
  have hmono : ∀ i : Ind, Mono (T.nuPlus i) :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.FiniteTauCategoryData.mono_nuPlus_of_isPositiveRightAdditiveLabelWeight
      T (R.labelWeight weight) hcategorical
  have hstrict : E.toRightRepresentableMeshComplex.IsStrict :=
    fun x ↦ hmono (label x)
  letI finiteLeft : ∀ a x : Fin Q.length,
      Module.Finite K
        (T.obj (label a) ⟶ (T.rightMesh (T.obj (label x))).X₁) :=
    fun a x ↦ R.finite_leftHom (K := K) a x
  letI finiteMiddle : ∀ a x : Fin Q.length,
      Module.Finite K
        (T.obj (label a) ⟶ T.thetaPlus (label x)) :=
    fun a x ↦ R.finite_middleHom (K := K) a x
  exact E.toRepresentableMeshExactnessData hstrict

@[simp]
theorem toRepresentableMeshExactnessData_homDimension
    (R : WordTauCategoryRealization T G Q label)
    [∀ a x : Ind, Module.Finite K (T.obj a ⟶ T.obj x)]
    (scalar_mod_radical : ∀ (x : Ind) (f : T.obj x ⟶ T.obj x),
      ∃ c : K,
        f - c • 𝟙 (T.obj x) ∈
          T.radicalHomSubmodule (K := K) x x)
    (weight : Fin Q.length → ℤ)
    (hweight : IsPositiveRightAdditive G Q weight)
    (a x : Fin Q.length) :
    (R.toRepresentableMeshExactnessData (K := K)
      scalar_mod_radical weight hweight).homDimension a x =
      Module.finrank K (T.obj (label a) ⟶ T.obj (label x)) :=
  rfl

end WordTauCategoryRealization

end QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh
