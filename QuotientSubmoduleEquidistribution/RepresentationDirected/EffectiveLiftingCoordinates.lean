import QuotientSubmoduleEquidistribution.RepresentationDirected.FiniteDimensionalMixedCoordinates

/-!
# Mixed-coordinate identities for directed effective lifting

This file supplies the finite-biproduct, multiplicity-object, and one-row
finrank comparisons used by the effective-lifting induction.  The proofs are
entirely abstract and use no concrete algebra or module classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota uJ

private theorem fintype_sum_apply
    {J I M : Type*} [Fintype J] [AddCommMonoid M]
    (f : J → I → M) (i : I) :
    (∑ j, f j) i = ∑ j, f j i := by
  exact map_sum (Pi.evalAddMonoidHom (fun _ : I => M) i) f Finset.univ

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

omit [IsAlgClosed K] [FiniteDimensional K R] [Fintype Iota] in
/-- Hom-finrank vectors are invariant under isomorphism of their target. -/
theorem homFinrankVector_iso {Y Z : FGModuleCat.{u} R} (e : Y ≅ Z) :
    homFinrankVector K R sigma Y = homFinrankVector K R sigma Z := by
  funext a
  change (Module.finrank K (sigma.obj a ⟶ Y) : ℤ) =
    (Module.finrank K (sigma.obj a ⟶ Z) : ℤ)
  exact_mod_cast (Linear.homCongr K (Iso.refl _) e).finrank_eq

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- Mixed multiplicities are invariant under isomorphism. -/
theorem mixedMultiplicity_iso
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {Y Z : FGModuleCat.{u} R} (e : Y ≅ Z) :
    mixedMultiplicity K R sigma H D Y =
      mixedMultiplicity K R sigma H D Z := by
  letI := directedLinearOrder sigma H
  simp only [mixedMultiplicity, homFinrankVector_iso K R sigma e]

omit [IsAlgClosed K] [Fintype Iota] in
/-- Hom-finrank vectors commute with arbitrary finite biproducts. -/
theorem homFinrankVector_biproduct_finite
    {J : Type uJ} [Fintype J] (Y : J → FGModuleCat.{u} R) :
    homFinrankVector K R sigma (⨁ Y) =
      ∑ j, homFinrankVector K R sigma (Y j) := by
  funext a
  letI : FiniteDimensional K (sigma.obj a ⟶ ⨁ Y) :=
    finiteDimensional_hom_from_obj K R sigma a (⨁ Y)
  letI (j : J) : FiniteDimensional K (sigma.obj a ⟶ Y j) :=
    finiteDimensional_hom_from_obj K R sigma a (Y j)
  calc
    homFinrankVector K R sigma (⨁ Y) a =
        (Module.finrank K (sigma.obj a ⟶ ⨁ Y) : ℤ) := rfl
    _ = ∑ j, (Module.finrank K (sigma.obj a ⟶ Y j) : ℤ) := by
      exact_mod_cast finrank_hom_biproduct (K := K) (sigma.obj a) Y
    _ = (∑ j, homFinrankVector K R sigma (Y j)) a := by
      simp [homFinrankVector]

omit [IsAlgClosed K] in
/-- Mixed multiplicities commute with arbitrary finite biproducts. -/
theorem mixedMultiplicity_biproduct_finite
    {J : Type uJ} [Fintype J]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y : J → FGModuleCat.{u} R) :
    mixedMultiplicity K R sigma H D (⨁ Y) =
      ∑ j, mixedMultiplicity K R sigma H D (Y j) := by
  letI := directedLinearOrder sigma H
  simp only [mixedMultiplicity,
    homFinrankVector_biproduct_finite K R sigma Y,
    UpperUnitriangular.coordinates_sum]

/-- A finite biproduct of retained indecomposables has exactly its displayed
natural multiplicities in the mixed coordinates. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_multiplicityBiproduct
    [DecidableEq Iota]
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D support : Finset Iota) (n : Iota → ℕ)
    (hretained : ∀ i, i ∈ support → i ∉ D) (a : Iota) :
    mixedMultiplicity K R sigma H D
        (multiplicityBiproduct sigma.obj support n) a =
      if a ∈ support then (n a : ℤ) else 0 := by
  classical
  rw [multiplicityBiproduct,
    mixedMultiplicity_biproduct_finite K R sigma H D]
  rw [fintype_sum_apply]
  change (∑ p : MultiplicityIndex support n,
      mixedMultiplicity K R sigma H D (sigma.obj p.1.1) a) = _
  have hcoordinate (p : MultiplicityIndex support n) :
      mixedMultiplicity K R sigma H D (sigma.obj p.1.1) a =
        if a = p.1.1 then 1 else 0 := by
    by_cases hap : a = p.1.1
    · subst a
      simp [H.mixedMultiplicity_obj_self K R sigma D
        (hretained p.1.1 p.1.2)]
    · simp [hap, H.mixedMultiplicity_obj_ne K R sigma D
        (hretained p.1.1 p.1.2) hap]
  simp_rw [hcoordinate]
  change (∑ p : Σ i : support, Fin (n i.1),
    if a = p.1.1 then (1 : ℤ) else 0) = _
  rw [Fintype.sum_sigma]
  have hinner (i : support) :
      (∑ _k : Fin (n i.1), if a = i.1 then (1 : ℤ) else 0) =
        if i.1 = a then (n i.1 : ℤ) else 0 := by
    by_cases hia : i.1 = a
    · subst a
      simp
    · have hai : a ≠ i.1 := Ne.symm hia
      simp [hia, hai]
  simp_rw [hinner]
  rw [← Finset.sum_subtype support (fun _ => Iff.rfl)
    (fun i => if i = a then (n i : ℤ) else 0)]
  exact Finset.sum_ite_eq' support a (fun i => (n i : ℤ))

/-- One-row dimension comparison used in effective lifting.  If `M` and
`T` have equal Hom dimensions on all labels remaining after deleting a
least retained `i`, and the old `i`-coordinate of `T` is zero, then the
Hom-dimension deficit at `i` is exactly the old mixed multiplicity of `M`. -/
theorem HasAcyclicNonzeroNonisomorphisms.homFinrankVector_eq_add_mixedMultiplicity
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hleast : IsLeastRetained R sigma H D i)
    (T M : FGModuleCat.{u} R)
    (hHom : ∀ a, a ∉ D.cons i hi →
      homFinrankVector K R sigma M a = homFinrankVector K R sigma T a)
    (hTi : mixedMultiplicity K R sigma H D T i = 0) :
    homFinrankVector K R sigma M i =
      homFinrankVector K R sigma T i +
        mixedMultiplicity K R sigma H D M i := by
  letI := directedLinearOrder sigma H
  have hcoordinates : ∀ a, a ∉ insert i D →
      mixedMultiplicity K R sigma H D M a =
        mixedMultiplicity K R sigma H D T a := by
    intro a ha
    have ha' : a ∉ D.cons i hi := by
      simpa only [Finset.cons_eq_insert] using ha
    have hnew :
        mixedMultiplicity K R sigma H (D.cons i hi) M a =
          mixedMultiplicity K R sigma H (D.cons i hi) T a := by
      have h := UpperUnitriangular.coordinates_eq_on_retained_of_eq_on_retained
        (homFinrankMatrix K R sigma) (D.cons i hi)
        (H.homFinrankMatrix_blockTriangular K R sigma)
        (H.homFinrankMatrix_diagonal K R sigma)
        (v := homFinrankVector K R sigma M)
        (w := homFinrankVector K R sigma T)
        hHom ha'
      simpa only [mixedMultiplicity] using h
    calc
      mixedMultiplicity K R sigma H D M a =
          mixedMultiplicity K R sigma H (D.cons i hi) M a :=
        (H.mixedMultiplicity_cons_eq_of_isLeastRetained
          K R sigma D hi hleast M ha').symm
      _ = mixedMultiplicity K R sigma H (D.cons i hi) T a := hnew
      _ = mixedMultiplicity K R sigma H D T a :=
        H.mixedMultiplicity_cons_eq_of_isLeastRetained
          K R sigma D hi hleast T ha'
  have hrow := UpperUnitriangular.value_eq_add_coordinate_sub
    (homFinrankMatrix K R sigma) D
    (H.homFinrankMatrix_blockTriangular K R sigma)
    (H.homFinrankMatrix_diagonal K R sigma)
    (homFinrankVector K R sigma M) (homFinrankVector K R sigma T)
    hcoordinates
  have hTi' : UpperUnitriangular.coordinates
      (homFinrankMatrix K R sigma) D (homFinrankVector K R sigma T) i = 0 := by
    simpa only [mixedMultiplicity] using hTi
  rw [hTi', sub_zero] at hrow
  simpa only [mixedMultiplicity] using hrow

omit [IsAlgClosed K] in
/-- Nonnegativity on all indecomposable representatives extends to every
finitely generated module.  This is the adapter from the paper's pairwise
definition of a nonnegative omitted set to the effective-lifting hypothesis. -/
theorem HasAcyclicNonzeroNonisomorphisms.mixedMultiplicity_nonnegative_of_obj
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (D : Finset Iota)
    (hobj : ∀ a, a ∉ D → ∀ j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (M : FGModuleCat.{u} R) (a : Iota) (ha : a ∉ D) :
    0 ≤ mixedMultiplicity K R sigma H D M a := by
  obtain ⟨n, j, ⟨e⟩⟩ := sigma.decomposes M
  rw [mixedMultiplicity_iso K R sigma H D e]
  rw [mixedMultiplicity_biproduct_finite K R sigma H D]
  change 0 ≤ (∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t))) a
  rw [show (∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t))) a =
      ∑ t, mixedMultiplicity K R sigma H D (sigma.obj (j t)) a by
    exact map_sum (Pi.evalAddMonoidHom (fun _ : Iota => ℤ) a)
      (fun t => mixedMultiplicity K R sigma H D (sigma.obj (j t))) Finset.univ]
  exact Finset.sum_nonneg fun t _ ↦ hobj a ha (j t)

end QuotientSubmoduleEquidistribution.RepresentationDirected
