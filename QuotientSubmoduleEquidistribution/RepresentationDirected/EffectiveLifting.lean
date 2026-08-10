import QuotientSubmoduleEquidistribution.RepresentationDirected.EffectiveLiftingKernelContradiction
import QuotientSubmoduleEquidistribution.RepresentationDirected.EffectiveLiftingAdditive
import QuotientSubmoduleEquidistribution.RepresentationDirected.MultiplicityBiproductReindex

/-!
# Directed effective lifting

For a finite representation-directed indecomposable skeleton and an omitted
set `D` with nonnegative retained mixed coordinates, this file constructs the
prescribed multiplicity biproduct and a map to any module which represents
the restricted contravariant Hom functor on the additive closure of the retained
objects.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u uIota

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type uIota} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, uIota, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The direct sum prescribed by the retained mixed multiplicities. -/
def mixedApproximationObject
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (Y : FGModuleCat.{u} R) : FGModuleCat.{u} R := by
  letI := directedLinearOrder sigma H
  exact multiplicityBiproduct sigma.obj (Finset.univ \ D)
    (fun a => (mixedMultiplicity K R sigma H D Y a).toNat)

/-- Splitting the least retained block from the prescribed direct sum. -/
def mixedApproximationObject_consIso
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {i : Iota} (hi : i ∉ D)
    (hleast : IsLeastRetained R sigma H D i)
    (Y : FGModuleCat.{u} R) :
    mixedApproximationObject K R sigma H D Y ≅
      (mixedApproximationObject K R sigma H (D.cons i hi) Y ⊞
        ⨁ fun _ : Fin (mixedMultiplicity K R sigma H D Y i).toNat =>
          sigma.obj i) := by
  letI := directedLinearOrder sigma H
  apply multiplicityBiproductConsIso sigma.obj D hi
    (fun a => (mixedMultiplicity K R sigma H D Y a).toNat)
    (fun a => (mixedMultiplicity K R sigma H (D.cons i hi) Y a).toNat)
  intro a ha
  exact congrArg Int.toNat
    (H.mixedMultiplicity_cons_eq_of_isLeastRetained
      K R sigma D hi hleast Y ha)

/-- At a label retained by `E`, the mixed coordinate of its prescribed
approximation object is the displayed natural multiplicity, even when the
coordinate is computed relative to a smaller omitted set. -/
theorem mixedMultiplicity_mixedApproximationObject_of_not_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D E : Finset Iota) (hDE : D ⊆ E)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∉ E) :
    mixedMultiplicity K R sigma H D
        (mixedApproximationObject K R sigma H E Y) a =
      ((mixedMultiplicity K R sigma H E Y a).toNat : ℤ) := by
  letI := directedLinearOrder sigma H
  rw [mixedApproximationObject]
  rw [H.mixedMultiplicity_multiplicityBiproduct K R sigma D
    (Finset.univ \ E)
    (fun b => (mixedMultiplicity K R sigma H E Y b).toNat)]
  · simp [ha]
  · intro b hb
    have hbE : b ∉ E := (Finset.mem_sdiff.mp hb).2
    exact fun hbD ↦ hbE (hDE hbD)

/-- A label already omitted from a prescribed approximation object has zero
mixed coordinate when computed with respect to any smaller omitted set. -/
theorem mixedMultiplicity_mixedApproximationObject_eq_zero
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D E : Finset Iota) (hDE : D ⊆ E)
    (Y : FGModuleCat.{u} R) {a : Iota} (ha : a ∈ E) :
    mixedMultiplicity K R sigma H D
        (mixedApproximationObject K R sigma H E Y) a = 0 := by
  letI := directedLinearOrder sigma H
  rw [mixedApproximationObject]
  rw [H.mixedMultiplicity_multiplicityBiproduct K R sigma D
    (Finset.univ \ E)
    (fun b => (mixedMultiplicity K R sigma H E Y b).toNat)]
  · simp [ha]
  · intro b hb
    have hbE : b ∉ E := (Finset.mem_sdiff.mp hb).2
    exact fun hbD ↦ hbE (hDE hbD)

private theorem finset_complement_strongInduction
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Finset I → Prop)
    (hbase : P Finset.univ)
    (hstep : ∀ D, D ≠ Finset.univ →
      (∀ i, ∀ hi : i ∉ D, P (D.cons i hi)) → P D) :
    ∀ D, P D := by
  intro D
  induction hcard : (Finset.univ \ D).card using Nat.strong_induction_on generalizing D with
  | h n ih =>
      by_cases hfull : D = Finset.univ
      · simpa [hfull] using hbase
      · apply hstep D hfull
        intro i hi
        apply ih ((Finset.univ \ D.cons i hi).card)
        · rw [Finset.cons_eq_insert, ← hcard]
          have himem : i ∈ Finset.univ \ D := by simp [hi]
          have hproper : Finset.univ \ insert i D ⊂ Finset.univ \ D := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro a ha
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
              exact fun haD ↦ ha (Finset.mem_insert_of_mem haD)
            · intro heq
              have : i ∈ Finset.univ \ insert i D := heq ▸ himem
              simp at this
          exact Finset.card_lt_card hproper
        · rfl

/-- Pointwise form of directed effective lifting on the indecomposable
skeleton. -/
theorem HasAcyclicNonzeroNonisomorphisms.exists_effectiveLifting_on_obj
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hnonnegative : ∀ (M : FGModuleCat.{u} R) a, a ∉ D →
      0 ≤ mixedMultiplicity K R sigma H D M a)
    (Y : FGModuleCat.{u} R) :
    ∃ ρ : mixedApproximationObject K R sigma H D Y ⟶ Y,
      ∀ a, a ∉ D → Function.Bijective
        (postcompLinearMap (K := K) (X := sigma.obj a) ρ) := by
  classical
  letI := directedLinearOrder sigma H
  let P : Finset Iota → Prop := fun E =>
    (∀ (M : FGModuleCat.{u} R) a, a ∉ E →
      0 ≤ mixedMultiplicity K R sigma H E M a) →
    ∀ Z : FGModuleCat.{u} R,
      ∃ ρ : mixedApproximationObject K R sigma H E Z ⟶ Z,
        ∀ a, a ∉ E → Function.Bijective
          (postcompLinearMap (K := K) (X := sigma.obj a) ρ)
  have hP : ∀ E, P E := finset_complement_strongInduction P (by
      intro _ Z
      refine ⟨0, ?_⟩
      intro a ha
      exact (ha (Finset.mem_univ a)).elim) (by
      intro E hEfull hrec hnonnegativeE Z
      have hex : ∃ a, a ∉ E := by
        by_contra hnone
        push Not at hnone
        apply hEfull
        ext a
        simp [hnone a]
      obtain ⟨i, hleast⟩ := H.exists_isLeastRetained R sigma E hex
      have hi : i ∉ E := hleast.1
      have hnonnegative' : ∀ (M : FGModuleCat.{u} R) a,
          a ∉ E.cons i hi →
          0 ≤ mixedMultiplicity K R sigma H (E.cons i hi) M a := by
        intro M a ha
        rw [H.mixedMultiplicity_cons_eq_of_isLeastRetained
          K R sigma E hi hleast M ha]
        apply hnonnegativeE M a
        exact fun haE ↦ ha (Finset.mem_cons.mpr (Or.inr haE))
      obtain ⟨f, hf⟩ := hrec i hi hnonnegative' Z
      let T := mixedApproximationObject K R sigma H (E.cons i hi) Z
      have hTi : mixedMultiplicity K R sigma H E T i = 0 := by
        change mixedMultiplicity K R sigma H E
          (mixedApproximationObject K R sigma H (E.cons i hi) Z) i = 0
        rw [mixedMultiplicity_mixedApproximationObject_eq_zero
          K R sigma H E (E.cons i hi)]
        · intro a ha
          exact Finset.mem_cons.mpr (Or.inr ha)
        · exact Finset.mem_cons_self i E
      have hfCore : ∀ a, a ∉ E.cons i hi →
          Function.Bijective (postcompose (U := sigma.obj a) f) := by
        intro a ha
        have hb := hf a ha
        constructor
        · intro x y hxy
          apply hb.1
          exact hxy
        · intro y
          obtain ⟨x, hx⟩ := hb.2 y
          exact ⟨x, hx⟩
      have hkernel : ∀ g : sigma.obj i ⟶ kernel f, g = 0 :=
        hom_kernel_eq_zero_of_recursive_bijective_of_nonnegative
          K R sigma H E hi hleast f hfCore hTi hnonnegativeE
      have hinjective : Function.Injective
          (postcompLinearMap (K := K) (X := sigma.obj i) f) :=
        postcompLinearMap_injective_of_kernel_orthogonal
          (K := K) f hkernel
      have hHom : ∀ a, a ∉ E.cons i hi →
          homFinrankVector K R sigma Z a =
            homFinrankVector K R sigma T a := by
        intro a ha
        letI : FiniteDimensional K (sigma.obj a ⟶ T) :=
          finiteDimensional_hom_from_obj K R sigma a T
        letI : FiniteDimensional K (sigma.obj a ⟶ Z) :=
          finiteDimensional_hom_from_obj K R sigma a Z
        have hfinrank :=
          (LinearEquiv.ofBijective
            (postcompLinearMap (K := K) (X := sigma.obj a) f)
            (hf a ha)).finrank_eq
        change (Module.finrank K (sigma.obj a ⟶ Z) : ℤ) =
          (Module.finrank K (sigma.obj a ⟶ T) : ℤ)
        exact_mod_cast hfinrank.symm
      have hrow := H.homFinrankVector_eq_add_mixedMultiplicity
        K R sigma E hi hleast T Z hHom hTi
      have hmu : 0 ≤ mixedMultiplicity K R sigma H E Z i :=
        hnonnegativeE Z i hi
      let n := (mixedMultiplicity K R sigma H E Z i).toNat
      have hmuNat : (n : ℤ) = mixedMultiplicity K R sigma H E Z i := by
        exact Int.toNat_of_nonneg hmu
      have hdim : Module.finrank K (sigma.obj i ⟶ Z) =
          Module.finrank K (sigma.obj i ⟶ T) + n := by
        change (Module.finrank K (sigma.obj i ⟶ Z) : ℤ) =
          (Module.finrank K (sigma.obj i ⟶ T) : ℤ) +
            mixedMultiplicity K R sigma H E Z i at hrow
        have hdimInt : (Module.finrank K (sigma.obj i ⟶ Z) : ℤ) =
            (Module.finrank K (sigma.obj i ⟶ T) : ℤ) + (n : ℤ) := by
          simpa only [hmuNat] using hrow
        exact_mod_cast hdimInt
      letI : FiniteDimensional K (sigma.obj i ⟶ T) :=
        finiteDimensional_hom_from_obj K R sigma i T
      letI : FiniteDimensional K (sigma.obj i ⟶ Z) :=
        finiteDimensional_hom_from_obj K R sigma i Z
      letI : FiniteDimensional K (sigma.obj i ⟶ sigma.obj i) :=
        finiteDimensional_hom_obj K R sigma i i
      obtain ⟨g, hg⟩ := exists_fin_copies_postcomp_bijective_of_finrank_eq_add
        (K := K) f hinjective (H.finrank_endomorphism_eq_one K R sigma i)
          n hdim
      let assembled :
          (T ⊞ ⨁ fun _ : Fin n => sigma.obj i) ⟶ Z :=
        biprod.desc f (biproduct.desc g)
      have hassembled : ∀ a, a ∉ E → Function.Bijective
          (postcompLinearMap (K := K) (X := sigma.obj a) assembled) := by
        intro a ha
        by_cases hai : a = i
        · subst a
          exact hg
        · have ha' : a ∉ E.cons i hi := by
            intro hmem
            rcases Finset.mem_cons.mp hmem with h | h
            · exact hai h
            · exact ha h
          apply postcompLinearMap_bijective_append_of_hom_zero
            (K := K) f g (hf a ha')
          intro q
          exact H.hom_eq_zero_of_isLeastRetained
            R sigma E hi hleast ha' q
      let e := mixedApproximationObject_consIso
        K R sigma H E hi hleast Z
      let ρ : mixedApproximationObject K R sigma H E Z ⟶ Z :=
        e.hom ≫ assembled
      refine ⟨ρ, ?_⟩
      intro a ha
      exact postcompLinearMap_bijective_comp_iso
        (K := K) (X := sigma.obj a) e assembled (hassembled a ha))
  exact hP D hnonnegative Y

/-- Literal additive-closure form of directed effective lifting. -/
theorem HasAcyclicNonzeroNonisomorphisms.exists_effectiveLifting
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hnonnegative : ∀ (M : FGModuleCat.{u} R) a, a ∉ D →
      0 ≤ mixedMultiplicity K R sigma H D M a)
    (Y : FGModuleCat.{u} R) :
    ∃ ρ : mixedApproximationObject K R sigma H D Y ⟶ Y,
      ∀ U, sigma.InAdd {a | a ∉ D} U → Function.Bijective
        (postcompLinearMap (K := K) (X := U) ρ) := by
  obtain ⟨ρ, hρ⟩ := H.exists_effectiveLifting_on_obj
    K R sigma D hnonnegative Y
  refine ⟨ρ, ?_⟩
  intro U hU
  apply postcompLinearMap_bijective_of_inAdd K R sigma ρ hU
  intro a ha
  exact hρ a ha

/-- Paper-facing form: pairwise nonnegativity on the indecomposable skeleton
implies the effective-lifting conclusion for every module. -/
theorem HasAcyclicNonzeroNonisomorphisms.exists_effectiveLifting_of_obj_nonnegative
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota)
    (hobj : ∀ a j,
      0 ≤ mixedMultiplicity K R sigma H D (sigma.obj j) a)
    (Y : FGModuleCat.{u} R) :
    ∃ ρ : mixedApproximationObject K R sigma H D Y ⟶ Y,
      ∀ U, sigma.InAdd {a | a ∉ D} U → Function.Bijective
        (postcompLinearMap (K := K) (X := U) ρ) := by
  apply H.exists_effectiveLifting K R sigma D _ Y
  intro M a ha
  exact H.mixedMultiplicity_nonnegative_of_obj K R sigma D
    (fun b _ j ↦ hobj b j) M a ha

end QuotientSubmoduleEquidistribution.RepresentationDirected
