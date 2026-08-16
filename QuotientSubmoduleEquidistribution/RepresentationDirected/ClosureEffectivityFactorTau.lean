import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedHomRigidity
import QuotientSubmoduleEquidistribution.RepresentationDirected.EffectiveLifting
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderPositiveWeight
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderEventualVanishing

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

/-- Pairwise nonnegativity on the indecomposable skeleton extends to every
module and every mixed-coordinate row. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_nonnegative_of_obj_all'
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (M : FGModuleCat.{u} R) (a : Iota) :
    0 ≤ mixedMultiplicity K R sigma H D M a := by
  obtain ⟨n, j, ⟨e⟩⟩ := sigma.decomposes M
  rw [mixedMultiplicity_iso K R sigma H D e]
  rw [mixedMultiplicity_biproduct_finite K R sigma H D]
  change 0 ≤ (∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t))) a
  rw [show (∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t))) a =
      ∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t)) a by
    exact map_sum (Pi.evalAddMonoidHom (fun _ : Iota => ℤ) a)
      (fun t ↦ mixedMultiplicity K R sigma H D (sigma.obj (j t)))
      Finset.univ]
  exact Finset.sum_nonneg fun t _ ↦ hobj a (j t)

/-- Exact Hom-vector residual before separating retained and omitted rows. -/
theorem HasAcyclicNonzeroNonisomorphisms.homFinrankVector_mixedApproximationObject_sub
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (Y : FGModuleCat.{u} R) (a : Iota) :
    homFinrankVector K R sigma Y a =
      homFinrankVector K R sigma
          (mixedApproximationObject K R sigma H D Y) a +
        mixedMultiplicity K R sigma H D Y a -
          mixedMultiplicity K R sigma H D
            (mixedApproximationObject K R sigma H D Y) a := by
  letI := directedLinearOrder sigma H
  let T := mixedApproximationObject K R sigma H D Y
  have hnonnegative (b : Iota) :
      0 ≤ mixedMultiplicity K R sigma H D Y b :=
    H.mixedMultiplicity_nonnegative_of_obj_all' K R sigma D hobj Y b
  have hretained (b : Iota) (hb : b ∉ D) :
      mixedMultiplicity K R sigma H D Y b =
        mixedMultiplicity K R sigma H D T b := by
    have hT := mixedMultiplicity_mixedApproximationObject_of_not_mem
      K R sigma H D D Set.Subset.rfl Y hb
    change mixedMultiplicity K R sigma H D Y b = _
    rw [show ((mixedMultiplicity K R sigma H D Y b).toNat : ℤ) =
        mixedMultiplicity K R sigma H D Y b by
      exact Int.toNat_of_nonneg (hnonnegative b)] at hT
    exact hT.symm
  have homitted (b : Iota) (hb : b ∈ D) :
      mixedMultiplicity K R sigma H D T b = 0 :=
    mixedMultiplicity_mixedApproximationObject_eq_zero
      K R sigma H D D Set.Subset.rfl Y hb
  have hcoordinates : ∀ b, b ∉ insert a D →
      mixedMultiplicity K R sigma H D Y b =
        mixedMultiplicity K R sigma H D T b := by
    intro b hb
    exact hretained b (fun hbD ↦ hb (Finset.mem_insert_of_mem hbD))
  have hrow := UpperUnitriangular.value_eq_add_coordinate_sub
    (homFinrankMatrix K R sigma) D
    (H.homFinrankMatrix_blockTriangular K R sigma)
    (H.homFinrankMatrix_diagonal K R sigma)
    (homFinrankVector K R sigma Y) (homFinrankVector K R sigma T)
    (fun b hb ↦ by
      simpa only [mixedMultiplicity] using hcoordinates b hb)
  have hrow' :
      homFinrankVector K R sigma Y a =
        homFinrankVector K R sigma T a +
          mixedMultiplicity K R sigma H D Y a -
            mixedMultiplicity K R sigma H D T a := by
    simpa only [mixedMultiplicity] using hrow
  exact hrow'

theorem HasAcyclicNonzeroNonisomorphisms.homFinrankVector_mixedApproximationObject_residual_of_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∈ D) :
    homFinrankVector K R sigma Y a =
      homFinrankVector K R sigma
          (mixedApproximationObject K R sigma H D Y) a +
        mixedMultiplicity K R sigma H D Y a := by
  have h := H.homFinrankVector_mixedApproximationObject_sub
    K R sigma D hobj Y a
  rw [mixedMultiplicity_mixedApproximationObject_eq_zero
    K R sigma H D D Set.Subset.rfl Y ha, sub_zero] at h
  exact h

theorem HasAcyclicNonzeroNonisomorphisms.homFinrankVector_mixedApproximationObject_eq_of_not_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∉ D) :
    homFinrankVector K R sigma Y a =
      homFinrankVector K R sigma
        (mixedApproximationObject K R sigma H D Y) a := by
  have h := H.homFinrankVector_mixedApproximationObject_sub
    K R sigma D hobj Y a
  have hT := mixedMultiplicity_mixedApproximationObject_of_not_mem
    K R sigma H D D Set.Subset.rfl Y ha
  have hnonneg := H.mixedMultiplicity_nonnegative_of_obj_all'
    K R sigma D hobj Y a
  rw [show ((mixedMultiplicity K R sigma H D Y a).toNat : ℤ) =
      mixedMultiplicity K R sigma H D Y a by
    exact Int.toNat_of_nonneg hnonneg] at hT
  rw [← hT] at h
  omega

/-- The retained approximation contains no ordinary split copy of an
omitted indecomposable. -/
theorem splitCoordinate_mixedApproximationObject_eq_zero_of_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y : FGModuleCat.{u} R)
    {y : Iota} (hy : y ∈ D) :
    splitCoordinate K R sigma H
      (mixedApproximationObject K R sigma H D Y) y = 0 := by
  letI := directedLinearOrder sigma H
  change mixedMultiplicity K R sigma H ∅
    (mixedApproximationObject K R sigma H D Y) y = 0
  rw [mixedApproximationObject]
  rw [H.mixedMultiplicity_multiplicityBiproduct K R sigma ∅
    (Finset.univ \ D)
    (fun a ↦ (mixedMultiplicity K R sigma H D Y a).toNat)]
  · simp [hy]
  · intro a ha
    simp

/-- Sum of the omitted-projective mixed coordinates of a module. -/
def omittedProjectiveMeasure
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (M : FGModuleCat.{u} R) : ℤ := by
  classical
  exact ∑ p ∈ D, if Projective (sigma.obj p) then
    mixedMultiplicity K R sigma H D M p else 0

/-- Label form of the omitted-projective measure. -/
def omittedProjectiveWeight
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (y : Iota) : ℤ :=
  omittedProjectiveMeasure K R sigma H D (sigma.obj y)

theorem omittedProjectiveMeasure_iso
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {M N : FGModuleCat.{u} R} (e : M ≅ N) :
    omittedProjectiveMeasure K R sigma H D M =
      omittedProjectiveMeasure K R sigma H D N := by
  classical
  simp only [omittedProjectiveMeasure,
    mixedMultiplicity_iso K R sigma H D e]

theorem omittedProjectiveMeasure_biproduct
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {J : Type*} [Fintype J]
    (M : J → FGModuleCat.{u} R) :
    omittedProjectiveMeasure K R sigma H D (⨁ M) =
      ∑ j, omittedProjectiveMeasure K R sigma H D (M j) := by
  classical
  simp only [omittedProjectiveMeasure,
    mixedMultiplicity_biproduct_finite K R sigma H D,
    Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hP : Projective (sigma.obj j)
  · simp [hP]
  · simp [hP]

theorem omittedProjectiveWeight_eq_zero_of_not_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {y : Iota} (hy : y ∉ D) :
    omittedProjectiveWeight (K := K) (R := R) sigma H D y = 0 := by
  classical
  rw [omittedProjectiveWeight, omittedProjectiveMeasure]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hP : Projective (sigma.obj p)
  · rw [if_pos hP]
    exact H.mixedMultiplicity_obj_ne K R sigma D hy (by
      intro hpy
      subst p
      exact hy hp)
  · rw [if_neg hP]

theorem omittedProjectiveWeight_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (y : Iota) :
    0 ≤ omittedProjectiveWeight (K := K) (R := R) sigma H D y := by
  classical
  apply Finset.sum_nonneg
  intro p _
  by_cases hp : Projective (sigma.obj p)
  · rw [if_pos hp]
    exact hobj _ _
  · rw [if_neg hp]

theorem omittedProjectiveWeight_pos_of_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (A : sigma.FiniteARTranslationData)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    {y : Iota} (hy : y ∈ D) :
    0 < omittedProjectiveWeight (K := K) (R := R) sigma H D y := by
  classical
  let T := mixedApproximationObject K R sigma H D (sigma.obj y)
  have hle (a : Iota) :
      homFinrankVector K R sigma T a ≤
        homFinrankVector K R sigma (sigma.obj y) a := by
    have hnonneg := H.mixedMultiplicity_nonnegative_of_obj_all'
      K R sigma D hobj (sigma.obj y) a
    by_cases ha : a ∈ D
    · have heq := H.homFinrankVector_mixedApproximationObject_residual_of_mem
        K R sigma D hobj (sigma.obj y) ha
      change homFinrankVector K R sigma T a ≤ _
      change _ = homFinrankVector K R sigma T a + _ at heq
      omega
    · have heq := H.homFinrankVector_mixedApproximationObject_eq_of_not_mem
        K R sigma D hobj (sigma.obj y) ha
      change _ = homFinrankVector K R sigma T a at heq
      exact heq.ge
  have hno : splitCoordinate K R sigma H T y = 0 :=
    splitCoordinate_mixedApproximationObject_eq_zero_of_mem
      K R sigma H D (sigma.obj y) hy
  obtain ⟨p, hp, hpstrict⟩ :=
    exists_projective_obj_homFinrank_lt_of_le
      K R sigma H A y T hno hle
  have hpD : p ∈ D := by
    by_contra hpD
    have heq := H.homFinrankVector_mixedApproximationObject_eq_of_not_mem
      K R sigma D hobj (sigma.obj y) hpD
    change _ = homFinrankVector K R sigma T p at heq
    omega
  have hmupos : 0 < mixedMultiplicity K R sigma H D (sigma.obj y) p := by
    have heq := H.homFinrankVector_mixedApproximationObject_residual_of_mem
      K R sigma D hobj (sigma.obj y) hpD
    change _ = homFinrankVector K R sigma T p + _ at heq
    omega
  have hleterm : mixedMultiplicity K R sigma H D (sigma.obj y) p ≤
      omittedProjectiveWeight (K := K) (R := R) sigma H D y := by
    rw [omittedProjectiveWeight]
    calc
      mixedMultiplicity K R sigma H D (sigma.obj y) p =
          (if Projective (sigma.obj p) then
            mixedMultiplicity K R sigma H D (sigma.obj y) p else 0) := by
              simp [hp]
      _ ≤ ∑ q ∈ D, if Projective (sigma.obj q) then
            mixedMultiplicity K R sigma H D (sigma.obj y) q else 0 := by
        refine Finset.single_le_sum (s := D)
          (f := fun q ↦ if Projective (sigma.obj q) then
            mixedMultiplicity K R sigma H D (sigma.obj y) q else 0) ?_ hpD
        · intro q hq
          by_cases hqP : Projective (sigma.obj q)
          · rw [if_pos hqP]
            exact hobj _ _
          · rw [if_neg hqP]
  omega

end QuotientSubmoduleEquidistribution.RepresentationDirected

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

namespace FiniteARTranslationData

variable (A : sigma.FiniteARTranslationData)

attribute [local instance] FintypeCat.fintype

/-- Regrouping the deleted part of a right-AR middle decomposition by
labels.  Retained labels may be inserted because their weight is zero. -/
theorem weighted_deletedMiddleMultiplicity_eq_sum
    (S : Set Iota) [Fintype (DeletedLabel S)] (x : DeletedLabel S)
    (weight : Iota → ℤ) (hzero : ∀ i, i ∈ S → weight i = 0) :
    ∑ y : DeletedLabel S,
        A.deletedMiddleMultiplicity sigma S x y * weight y.1 =
      ∑ t : (A.factorLadderRightARAt sigma x.1).index,
        weight ((A.factorLadderRightARAt sigma x.1).label t) := by
  classical
  let AR := A.factorLadderRightARAt sigma x.1
  let g : Iota → ℤ := fun y ↦
    (((Finset.univ.filter fun t : AR.index ↦ AR.label t = y).card : ℕ) : ℤ) *
      weight y
  calc
    (∑ y : DeletedLabel S,
        A.deletedMiddleMultiplicity sigma S x y * weight y.1) =
        ∑ y : DeletedLabel S, g y.1 := by
      apply Finset.sum_congr rfl
      intro y _
      rfl
    _ = ∑ y ∈ Finset.univ.filter (fun y : Iota ↦ y ∉ S), g y := by
      symm
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ y : Iota, g y := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro y _ hy
      have hyS : y ∈ S := by simpa using hy
      simp [g, hzero y hyS]
    _ = ∑ y : Iota,
        ∑ t ∈ (Finset.univ.filter fun t : AR.index ↦ AR.label t = y),
          weight (AR.label t) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [g]
      calc
        (((Finset.univ.filter fun t : AR.index ↦ AR.label t = y).card : ℕ) : ℤ) *
            weight y =
            ∑ _t ∈ (Finset.univ.filter fun t : AR.index ↦ AR.label t = y),
              weight y := by simp
        _ = ∑ t ∈ (Finset.univ.filter fun t : AR.index ↦ AR.label t = y),
              weight (AR.label t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [(Finset.mem_filter.mp ht).2]
    _ = ∑ t : AR.index, weight (AR.label t) := by
      exact Finset.sum_fiberwise Finset.univ AR.label
        (fun t ↦ weight (AR.label t))

end FiniteARTranslationData
end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The retained support complementary to the omitted finset. -/
def retainedSupport (D : Finset Iota) : Set Iota :=
  {i | i ∉ D}

attribute [local instance] FintypeCat.fintype

noncomputable local instance retainedDeletedFintype (D : Finset Iota) :
    Fintype (DeletedLabel (retainedSupport D)) := Fintype.ofFinite _

theorem deletedLabel_mem_omitted
    (D : Finset Iota) (x : DeletedLabel (retainedSupport D)) :
    x.1 ∈ D := by
  classical
  simpa [retainedSupport] using x.2

/-- The positive label weight used on the literal factor category. -/
def factorBoundaryWeight
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (x : DeletedLabel (retainedSupport D)) : ℤ :=
  omittedProjectiveWeight (K := K) (R := R) sigma H D x.1

theorem weightedSum_factorTheta_basis_eq_measure_middle
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (x : DeletedLabel (retainedSupport D)) :
    let A := sigma.finiteDimensionalARTranslationData K R
    let L := sigma.finiteDimensionalFactorLadderData K R (retainedSupport D)
    FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
        (L.theta (FactorLadder.basis x)) =
      omittedProjectiveMeasure K R sigma H D
        (A.factorLadderRightARAt sigma x.1).middle := by
  classical
  let A := sigma.finiteDimensionalARTranslationData K R
  let S := retainedSupport D
  let L := sigma.finiteDimensionalFactorLadderData K R S
  letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
  have hzero (i : Iota) (hi : i ∈ S) :
      omittedProjectiveWeight (K := K) (R := R) sigma H D i = 0 :=
    omittedProjectiveWeight_eq_zero_of_not_mem K R sigma H D hi
  have hregroup := A.weighted_deletedMiddleMultiplicity_eq_sum sigma S x
    (omittedProjectiveWeight (K := K) (R := R) sigma H D) hzero
  have hmiddle := omittedProjectiveMeasure_iso K R sigma H D
    (A.factorLadderRightARAt sigma x.1).decomposition
  have hbip := omittedProjectiveMeasure_biproduct K R sigma H D
    (fun t : (A.factorLadderRightARAt sigma x.1).index ↦
      sigma.obj ((A.factorLadderRightARAt sigma x.1).label t))
  calc
    FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
        (L.theta (FactorLadder.basis x)) =
        ∑ y : DeletedLabel S,
          A.deletedMiddleMultiplicity sigma S x y *
            omittedProjectiveWeight (K := K) (R := R) sigma H D y.1 := by
      simp [FactorLadder.weightedSum, L,
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.finiteDimensionalFactorLadderData,
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData.factorLadderData_theta,
        QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData.factorLadderTheta_basis_apply,
        factorBoundaryWeight, A, S]
    _ = ∑ t : (A.factorLadderRightARAt sigma x.1).index,
          omittedProjectiveWeight (K := K) (R := R) sigma H D
            ((A.factorLadderRightARAt sigma x.1).label t) := hregroup
    _ = omittedProjectiveMeasure K R sigma H D
          (⨁ fun t : (A.factorLadderRightARAt sigma x.1).index ↦
            sigma.obj ((A.factorLadderRightARAt sigma x.1).label t)) := hbip.symm
    _ = omittedProjectiveMeasure K R sigma H D
          (A.factorLadderRightARAt sigma x.1).middle := hmiddle.symm

theorem omittedProjectiveMeasure_chosenRightAR_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (A : sigma.FiniteARTranslationData)
    (D : Finset Iota) (x : sigma.NonprojectiveLabel)
    (hxD : x.1 ∈ D) :
    omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 +
        omittedProjectiveWeight (K := K) (R := R) sigma H D
          (A.arTranslation sigma x).1 =
      omittedProjectiveMeasure K R sigma H D
        (A.chosenRightAR sigma x).middle := by
  classical
  rw [omittedProjectiveWeight, omittedProjectiveWeight]
  simp only [omittedProjectiveMeasure]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpD
  by_cases hp : Projective (sigma.obj p)
  · rw [if_pos hp, if_pos hp, if_pos hp]
    have hmesh := congrFun
      (chosenRightAR_mixedMultiplicity_mesh
        (K := K) (R := R) sigma H A D x hxD) p
    have hpx : p ≠ x.1 := by
      intro hpx
      subst p
      exact x.2 hp
    simp [directedSingle, Pi.single_apply, hpx] at hmesh
    exact hmesh
  · rw [if_neg hp, if_neg hp, if_neg hp]
    simp

/-- Away from the deleted-projective boundary, the positive boundary weight
has zero defect on the literal factor mesh. -/
theorem factorBoundaryWeight_meshDefect_eq_zero
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (x : DeletedLabel (retainedSupport D))
    (hxBoundary : x ∉ deletedProjectiveSet sigma (retainedSupport D)) :
    let L := sigma.finiteDimensionalFactorLadderData K R (retainedSupport D)
    FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (FactorLadder.basis x) -
        FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (L.theta (FactorLadder.basis x)) +
        FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (L.tau (FactorLadder.basis x)) = 0 := by
  classical
  let A := sigma.finiteDimensionalARTranslationData K R
  let S := retainedSupport D
  let L := sigma.finiteDimensionalFactorLadderData K R S
  letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
  have hx : ¬ Projective (sigma.obj x.1) := by
    simpa [deletedProjectiveSet] using hxBoundary
  let xnp : sigma.NonprojectiveLabel := ⟨x.1, hx⟩
  have hxD : x.1 ∈ D := deletedLabel_mem_omitted D x
  let tx : Iota := (A.arTranslation sigma xnp).1
  have hambient := omittedProjectiveMeasure_chosenRightAR_mesh
    K R sigma H A D xnp hxD
  have htheta := weightedSum_factorTheta_basis_eq_measure_middle
    K R sigma H D x
  have htheta' :
      FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (L.theta (FactorLadder.basis x)) =
        omittedProjectiveMeasure K R sigma H D
          (A.chosenRightAR sigma xnp).middle := by
    simpa [L, S, A,
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData.factorLadderRightARAt,
      hx, xnp] using htheta
  change FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (FactorLadder.basis x) -
        FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (L.theta (FactorLadder.basis x)) +
        FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
          (L.tau (FactorLadder.basis x)) = 0
  rw [FactorLadder.weightedSum_basis, htheta']
  change omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 - _ + _ = 0
  by_cases htxD : tx ∈ D
  · have htxS : tx ∉ S := by
      simpa [S, retainedSupport] using htxD
    let txdel : DeletedLabel S := ⟨tx, htxS⟩
    by_cases hmiddle :
        A.factorLadderTheta sigma S (FactorLadder.basis x) = 0
    · have hthetaZero :
          FactorLadder.weightedSum (factorBoundaryWeight K R sigma H D)
            (L.theta (FactorLadder.basis x)) = 0 := by
        rw [show L.theta = A.factorLadderTheta sigma S by rfl, hmiddle]
        exact FactorLadder.weightedSum_zero _
      rw [htheta'] at hthetaZero
      have hxpos := omittedProjectiveWeight_pos_of_mem
        K R sigma H A D hobj hxD
      have htxpos := omittedProjectiveWeight_pos_of_mem
        K R sigma H A D hobj htxD
      change omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 +
          omittedProjectiveWeight (K := K) (R := R) sigma H D tx =
        omittedProjectiveMeasure K R sigma H D
          (A.chosenRightAR sigma xnp).middle at hambient
      omega
    · have htgt : A.factorLadderTauTarget sigma S x = some txdel := by
        apply A.factorLadderTauTarget_eq_some sigma S x hx htxS hmiddle
      have htau : A.factorLadderTau sigma S (FactorLadder.basis x) =
          FactorLadder.basis txdel :=
        A.factorLadderTau_basis_eq_basis_of_target_eq_some
          sigma S x txdel htgt
      rw [show L.tau = A.factorLadderTau sigma S by rfl, htau,
        FactorLadder.weightedSum_basis]
      change omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 -
          omittedProjectiveMeasure K R sigma H D
            (A.chosenRightAR sigma xnp).middle +
          omittedProjectiveWeight (K := K) (R := R) sigma H D tx = 0
      change omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 +
          omittedProjectiveWeight (K := K) (R := R) sigma H D tx =
        omittedProjectiveMeasure K R sigma H D
          (A.chosenRightAR sigma xnp).middle at hambient
      omega
  · have htxS : tx ∈ S := by
      simpa [S, retainedSupport] using htxD
    have htgt : A.factorLadderTauTarget sigma S x = none :=
      A.factorLadderTauTarget_eq_none_of_translation_mem sigma S x hx htxS
    have htau : A.factorLadderTau sigma S (FactorLadder.basis x) = 0 :=
      A.factorLadderTau_basis_eq_zero_of_target_eq_none sigma S x htgt
    have htxzero : omittedProjectiveWeight (K := K) (R := R)
        sigma H D tx = 0 :=
      omittedProjectiveWeight_eq_zero_of_not_mem K R sigma H D htxD
    rw [show L.tau = A.factorLadderTau sigma S by rfl, htau,
      FactorLadder.weightedSum_zero]
    change omittedProjectiveWeight (K := K) (R := R) sigma H D x.1 +
        omittedProjectiveWeight (K := K) (R := R) sigma H D tx =
      omittedProjectiveMeasure K R sigma H D
        (A.chosenRightAR sigma xnp).middle at hambient
    omega

/-- Every deleted factor-ladder label reaches an omitted projective when all
mixed coordinates are nonnegative. -/
theorem factorLadder_reaches_projective_of_mixedMultiplicity_obj_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (x : DeletedLabel (retainedSupport D)) :
    (sigma.finiteDimensionalFactorLadderData K R (retainedSupport D)).ReachesBoundary
      (deletedProjectiveSet sigma (retainedSupport D)) x := by
  classical
  let A := sigma.finiteDimensionalARTranslationData K R
  let S := retainedSupport D
  let L := sigma.finiteDimensionalFactorLadderData K R S
  letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
  apply FactorLadder.Data.reachesBoundary_of_positiveWeight
    L (deletedProjectiveSet sigma S) x
      (factorBoundaryWeight K R sigma H D)
  · intro d
    exact omittedProjectiveWeight_pos_of_mem K R sigma H A D hobj
      (deletedLabel_mem_omitted D d)
  · intro n d
    exact A.factorLadderData_ladder_nonneg sigma S x n d
  · intro d hd
    exact factorBoundaryWeight_meshDefect_eq_zero
      K R sigma H D hobj d hd
  · exact sigma.finiteDimensionalFactorLadder_eventuallyZero
      (k := K) (R := R) S x

/-- Pairwise nonnegative mixed coordinates force quotient closure through the
literal factor category and the positive-weight factor-ladder argument. -/
theorem HasAcyclicNonzeroNonisomorphisms.qClosed_of_mixedMultiplicity_obj_nonnegative_via_factorTau
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a) :
    sigma.qClosure.IsClosed {a | a ∉ D} := by
  rw [qClosed_iff_generated_isClosedUnderQuotients]
  rw [sigma.finiteDimensional_generated_isClosedUnderQuotients_iff_factorLadder_reaches_projective
    (k := K) (R := R)]
  intro x
  exact factorLadder_reaches_projective_of_mixedMultiplicity_obj_nonnegative
    K R sigma H D hobj x

end QuotientSubmoduleEquidistribution.RepresentationDirected
