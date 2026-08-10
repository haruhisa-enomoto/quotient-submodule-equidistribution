import QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedMixedCoordinates
import QuotientSubmoduleEquidistribution.RepresentationDirected.FiniteDimensionalDirectedHom
import QuotientSubmoduleEquidistribution.RepresentationDirected.HomBiproductFinrank

/-!
# Mixed Hom coordinates for a representation-directed skeleton

The abstract integral coordinates are specialized to the Hom-dimension
vectors of modules over a finite-dimensional algebra.  This identifies the
matrix coordinates with the manuscript's mixed multiplicities, proves their
basic additivity and retained-column formulas, and packages one-step deletion
transport under the required Hom-vanishing hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

/-- The integral vector of Hom dimensions from the chosen indecomposables. -/
def homFinrankVector (Y : FGModuleCat.{u} R) : Iota → ℤ :=
  fun a => (Module.finrank K (sigma.obj a ⟶ Y) : ℤ)

/-- The manuscript's integral mixed multiplicities, defined without passing
through a functor-category Grothendieck group. -/
def mixedMultiplicity
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y : FGModuleCat.{u} R) : Iota → ℤ := by
  letI := directedLinearOrder sigma H
  exact UpperUnitriangular.coordinates
    (homFinrankMatrix K R sigma) D (homFinrankVector K R sigma Y)

/-- The mixed multiplicities reconstruct every Hom-dimension vector. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMatrix_mulVec_mixedMultiplicity
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y : FGModuleCat.{u} R) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.mixedMatrix (homFinrankMatrix K R sigma) D *ᵥ
      mixedMultiplicity K R sigma H D Y = homFinrankVector K R sigma Y := by
  letI := directedLinearOrder sigma H
  simpa [mixedMultiplicity] using
    UpperUnitriangular.mixedMatrix_mulVec_coordinates
      (homFinrankMatrix K R sigma) D
      (H.homFinrankMatrix_blockTriangular K R sigma)
      (H.homFinrankMatrix_diagonal K R sigma)
      (homFinrankVector K R sigma Y)

/-- A retained indecomposable has mixed multiplicity one at its own
position. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_obj_self
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {j : Iota} (hj : j ∉ D) :
    mixedMultiplicity K R sigma H D (sigma.obj j) j = 1 := by
  letI := directedLinearOrder sigma H
  have h := congrFun
    (UpperUnitriangular.coordinates_retained_column
      (homFinrankMatrix K R sigma) D
      (H.homFinrankMatrix_blockTriangular K R sigma)
      (H.homFinrankMatrix_diagonal K R sigma) hj) j
  have hv : homFinrankVector K R sigma (sigma.obj j) =
      (homFinrankMatrix K R sigma).col j := by
    rfl
  rw [mixedMultiplicity, hv]
  simpa [Pi.single_apply] using h

/-- A retained indecomposable has mixed multiplicity zero at every other
position. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_obj_ne
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {j a : Iota} (hj : j ∉ D) (haj : a ≠ j) :
    mixedMultiplicity K R sigma H D (sigma.obj j) a = 0 := by
  letI := directedLinearOrder sigma H
  have h := congrFun
    (UpperUnitriangular.coordinates_retained_column
      (homFinrankMatrix K R sigma) D
      (H.homFinrankMatrix_blockTriangular K R sigma)
      (H.homFinrankMatrix_diagonal K R sigma) hj) a
  have hv : homFinrankVector K R sigma (sigma.obj j) =
      (homFinrankMatrix K R sigma).col j := by
    rfl
  rw [mixedMultiplicity, hv]
  simpa [Pi.single_apply, haj] using h

omit [IsAlgClosed K] [Fintype Iota] in
/-- Hom-dimension vectors are additive on binary biproducts. -/
theorem homFinrankVector_biprod (Y Z : FGModuleCat.{u} R) :
    homFinrankVector K R sigma (Y ⊞ Z) =
      homFinrankVector K R sigma Y + homFinrankVector K R sigma Z := by
  funext a
  letI : FiniteDimensional K (sigma.obj a ⟶ Y) :=
    finiteDimensional_hom_from_obj K R sigma a Y
  letI : FiniteDimensional K (sigma.obj a ⟶ Z) :=
    finiteDimensional_hom_from_obj K R sigma a Z
  letI : FiniteDimensional K (sigma.obj a ⟶ Y ⊞ Z) :=
    finiteDimensional_hom_from_obj K R sigma a (Y ⊞ Z)
  change (Module.finrank K (sigma.obj a ⟶ Y ⊞ Z) : ℤ) =
    (Module.finrank K (sigma.obj a ⟶ Y) : ℤ) +
      (Module.finrank K (sigma.obj a ⟶ Z) : ℤ)
  exact_mod_cast finrank_hom_biprod (K := K) (sigma.obj a) Y Z

omit [IsAlgClosed K] in
/-- Mixed multiplicities are additive on binary biproducts. -/
theorem mixedMultiplicity_biprod
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y Z : FGModuleCat.{u} R) :
    mixedMultiplicity K R sigma H D (Y ⊞ Z) =
      mixedMultiplicity K R sigma H D Y +
        mixedMultiplicity K R sigma H D Z := by
  letI := directedLinearOrder sigma H
  simp only [mixedMultiplicity, homFinrankVector_biprod K R sigma Y Z,
    UpperUnitriangular.coordinates_add]

/-- A retained label is least in the directed linear extension. -/
def IsLeastRetained
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (i : Iota) : Prop := by
  letI := directedLinearOrder sigma H
  exact i ∉ D ∧ ∀ a, a ∉ D → i ≤ a

/-- Every nonempty finite retained set has a least label. -/
theorem HasAcyclicNonzeroNonisomorphisms.exists_isLeastRetained
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (hne : ∃ a, a ∉ D) :
    ∃ i, IsLeastRetained R sigma H D i := by
  letI := directedLinearOrder sigma H
  classical
  let S : Finset Iota := Finset.univ.filter (fun a => a ∉ D)
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, by simp [S, ha]⟩
  let i := S.min' hS
  refine ⟨i, ?_⟩
  change i ∉ D ∧ ∀ a, a ∉ D → i ≤ a
  constructor
  · have hi := Finset.min'_mem S hS
    simpa [i, S] using hi
  · intro a ha
    exact Finset.min'_le S a (by simp [S, ha])

omit [Fintype Iota] in
/-- A least retained object receives no nonzero map from the other retained
objects. -/
theorem HasAcyclicNonzeroNonisomorphisms.hom_eq_zero_of_isLeastRetained
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hleast : IsLeastRetained R sigma H D i)
    {a : Iota} (ha : a ∉ D.cons i hi)
    (f : sigma.obj a ⟶ sigma.obj i) : f = 0 := by
  letI := directedLinearOrder sigma H
  change i ∉ D ∧ ∀ b, b ∉ D → i ≤ b at hleast
  have haD : a ∉ D := by
    intro ha'
    exact ha (Finset.mem_cons.mpr (Or.inr ha'))
  have hai : i ≠ a := by
    intro hia
    subst a
    exact ha (Finset.mem_cons_self i D)
  have hia : i < a := lt_of_le_of_ne (hleast.2 a haD) hai
  exact hom_eq_zero_of_lt R sigma H hia f

/-- One-step deletion preserves all still-retained mixed multiplicities when
the newly deleted object receives no map from the remaining objects. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_cons_eq_of_hom_zero
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hzero : ∀ a, a ∉ D.cons i hi →
      ∀ f : sigma.obj a ⟶ sigma.obj i, f = 0)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∉ D.cons i hi) :
    mixedMultiplicity K R sigma H (D.cons i hi) Y a =
      mixedMultiplicity K R sigma H D Y a := by
  letI := directedLinearOrder sigma H
  have hzero' : ∀ b, b ∉ D.cons i hi →
      homFinrankMatrix K R sigma b i = 0 := by
    intro b hb
    change (Module.finrank K (sigma.obj b ⟶ sigma.obj i) : ℤ) = 0
    haveI : Subsingleton (sigma.obj b ⟶ sigma.obj i) :=
      ⟨fun f g => (hzero b hb f).trans (hzero b hb g).symm⟩
    exact_mod_cast (Module.finrank_zero_of_subsingleton :
      Module.finrank K (sigma.obj b ⟶ sigma.obj i) = 0)
  simpa [mixedMultiplicity] using
    UpperUnitriangular.coordinates_cons_eq_of_column_zero
      (homFinrankMatrix K R sigma) D
      (H.homFinrankMatrix_blockTriangular K R sigma)
      (H.homFinrankMatrix_diagonal K R sigma) hi hzero'
      (homFinrankVector K R sigma Y) ha

/-- For the least retained label, one-step mixed-coordinate transport is
automatic from directedness. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_cons_eq_of_isLeastRetained
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hleast : IsLeastRetained R sigma H D i)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∉ D.cons i hi) :
    mixedMultiplicity K R sigma H (D.cons i hi) Y a =
      mixedMultiplicity K R sigma H D Y a :=
  H.mixedMultiplicity_cons_eq_of_hom_zero K R sigma D hi
    (fun _ hb f =>
      H.hom_eq_zero_of_isLeastRetained R sigma D hi hleast hb f)
    Y ha

end QuotientSubmoduleEquidistribution.RepresentationDirected
