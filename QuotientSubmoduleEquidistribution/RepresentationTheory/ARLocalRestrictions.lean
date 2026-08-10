import QuotientSubmoduleEquidistribution.RepresentationDirected.IrreducibleDimensionGrowth
import QuotientSubmoduleEquidistribution.Combinatorics.BoundaryTranslationChains
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderRooted
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteARTranslationData
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveBoundaryAlmostSplit

/-!
# Local restrictions in a finite Auslander--Reiten quiver

This file formalizes local translation-quiver exclusions used by the
four-vertex ladder classification.  The arguments use only mesh incidence,
finite-dimensional length inequalities, and the projective radical
boundary; they do not classify modules or algebras.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance] FintypeCat.fintype

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

include K in
/-- Every vertex of the finite AR quiver is reachable from a projective
vertex.  This is the full-support specialization of the already proved
factor-ladder rootedness theorem; it uses no representation-directedness
or classification of indecomposable modules. -/
theorem isProjectivelyRooted_univ :
    QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Finset.univ := by
  classical
  have hclosed :
      σ.qClosure.IsClosed (((Finset.univ : Finset ι) : Set ι)ᶜ) := by
    simpa using qClosure_isClosed_empty σ
  exact
    ((qClosure_isClosed_compl_iff_projectivelyRooted_and_not_factorLadderBad
      (k := K) (R := R) σ Finset.univ).1 hclosed).1

omit [Algebra K R] [FiniteDimensional K R] [Fintype ι] in
/-- No irreducible arrow has the form `tau X → X`.  Mesh incidence
would rotate such an arrow to an irreducible endomorphism of `tau X`. -/
theorem no_irreducible_arTranslation_to_endpoint
    (x : σ.NonprojectiveLabel) :
    ¬ HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ x).1) (σ.obj x.1) := by
  intro h
  have hloop := (AR.arTranslation_incidence σ x
    (AR.arTranslation σ x).1).1 h
  exact (σ.hasNoIrreducibleEndomorphism_obj
    (AR.arTranslation σ x).1) hloop

omit [Fintype ι] in
/-- One selected summand occurrence contributes at most the dimension of
the entire finite direct sum. -/
theorem groundFinrank_le_middle_of_occurrence
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t : A.index) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj (A.label t)) ≤
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) A.middle := by
  classical
  rw [QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_sum_of_iso_sumOver
    (K := K) σ A.middle A.index A.label A.decomposition]
  calc
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj (A.label t)) =
      ∑ s ∈ ({t} : Finset A.index),
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label s)) := by simp
    _ ≤ ∑ s : A.index,
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label s)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [Fintype ι] in
/-- Two distinct selected summand occurrences contribute their combined
dimension below the dimension of the entire finite direct sum. -/
theorem add_groundFinrank_le_middle_of_two_occurrences
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t₁ t₂ : A.index) (hne : t₁ ≠ t₂) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj (A.label t₁)) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj (A.label t₂)) ≤
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) A.middle := by
  classical
  rw [QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_sum_of_iso_sumOver
    (K := K) σ A.middle A.index A.label A.decomposition]
  calc
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₁)) +
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₂)) =
      ∑ s ∈ ({t₁, t₂} : Finset A.index),
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label s)) := by simp [hne]
    _ ≤ ∑ s : A.index,
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label s)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [Fintype ι] in
/-- Three pairwise distinct selected summand occurrences contribute their
combined dimension below the dimension of the entire finite direct sum. -/
theorem add_add_groundFinrank_le_middle_of_three_occurrences
    {z : ι} (A : σ.MinimalRightAlmostSplitDecomposition z)
    (t₁ t₂ t₃ : A.index)
    (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃) (h₂₃ : t₂ ≠ t₃) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₁)) +
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₂)) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₃)) ≤
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) A.middle := by
  classical
  rw [QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_sum_of_iso_sumOver
    (K := K) σ A.middle A.index A.label A.decomposition]
  calc
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₁)) +
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₂)) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label t₃)) =
        ∑ s ∈ ({t₁, t₂, t₃} : Finset A.index),
          QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj (A.label s)) := by
      simp [h₁₂, h₁₃, h₂₃, Nat.add_assoc]
    _ ≤ ∑ s : A.index,
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (A.label s)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [Fintype ι] in
/-- Every skeleton representative has positive ground-field dimension. -/
theorem groundFinrank_obj_pos (x : ι) :
    0 < QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj x) := by
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) :=
    Module.Finite.trans R (σ.obj x)
  letI : Nontrivial (σ.obj x) := (σ.indecomposable x).nontrivial
  exact Module.finrank_pos

omit [Fintype ι] in
/-- The Jacobson radical of a nonzero finite module has strictly smaller
ground-field dimension than the module. -/
theorem projectiveBoundaryRadical_groundFinrank_lt
    (p : ι) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.projectiveBoundaryRadical p) <
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj p) := by
  letI : Module K (σ.obj p) := Module.restrictScalars K R (σ.obj p)
  letI : IsScalarTower K R (σ.obj p) :=
    IsScalarTower.restrictScalars K R (σ.obj p)
  letI : FiniteDimensional K (σ.obj p) :=
    Module.Finite.trans R (σ.obj p)
  letI : Nontrivial (σ.obj p) := (σ.indecomposable p).nontrivial
  let J : Submodule K (σ.obj p) :=
    (Module.jacobson R (σ.obj p)).restrictScalars K
  have hJne : J ≠ ⊤ := by
    intro htop
    apply (Module.jacobson_lt_top R (σ.obj p)).ne
    apply SetLike.ext
    intro x
    have hx := SetLike.ext_iff.mp htop x
    simpa [J] using hx
  have hlt := Submodule.finrank_lt_finrank_of_lt
    (show J < ⊤ from lt_top_iff_ne_top.2 hJne)
  have htopdim : Module.finrank K (⊤ : Submodule K (σ.obj p)) =
      Module.finrank K (σ.obj p) :=
    Submodule.topEquiv.finrank_eq
  change Module.finrank K (σ.projectiveBoundaryRadical p) <
    Module.finrank K (σ.obj p)
  change Module.finrank K J < Module.finrank K (σ.obj p)
  exact hlt.trans_eq htopdim

omit [Fintype ι] in
/-- Ground-field dimension in the chosen AR sequence is the sum of its
translation and endpoint dimensions. -/
theorem arTranslation_add_endpoint_groundFinrank_eq_middle
    (x : σ.NonprojectiveLabel) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj (AR.arTranslation σ x).1) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj x.1) =
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (AR.chosenRightAR σ x).middle := by
  let A := AR.chosenRightAR σ x
  letI : Epi A.map :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      σ A.map A.rightAlmostSplit x.2
  let S := ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel A.map)
    mono_f := inferInstance
    epi_g := inferInstance }
  letI : Module K (kernel A.map : FGModuleCat.{u} R) :=
    Module.restrictScalars K R (kernel A.map : FGModuleCat.{u} R)
  letI : IsScalarTower K R (kernel A.map : FGModuleCat.{u} R) :=
    IsScalarTower.restrictScalars K R (kernel A.map : FGModuleCat.{u} R)
  letI : Module K A.middle := Module.restrictScalars K R A.middle
  letI : IsScalarTower K R A.middle :=
    IsScalarTower.restrictScalars K R A.middle
  letI : FiniteDimensional K A.middle := Module.Finite.trans R A.middle
  letI : Module K (σ.obj x.1) :=
    Module.restrictScalars K R (σ.obj x.1)
  letI : IsScalarTower K R (σ.obj x.1) :=
    IsScalarTower.restrictScalars K R (σ.obj x.1)
  have hdim :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.finrank_add_finrank_eq_of_shortExact
      (K := K) (R := R) S hS
  have hk := QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_of_iso
    (K := K) (AR.arTranslationKernelIso σ x)
  have hk' : QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (kernel A.map : FGModuleCat.{u} R) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj (AR.arTranslation σ x).1) := by
    simpa [A, FiniteARTranslationData.arTranslation] using hk
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj (AR.arTranslation σ x).1) +
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj x.1) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) A.middle
  rw [← hk']
  exact hdim

omit [Algebra K R] [FiniteDimensional K R] [Fintype ι] in
/-- Translating both members of an opposite-arrow pair again gives an
opposite-arrow pair, provided both members are nonprojective. -/
theorem arTranslation_two_cycle
    (y z : ι) (hy : ¬ Projective (σ.obj y))
    (hz : ¬ Projective (σ.obj z))
    (hyz : HasIrreducibleMorphism (σ.obj y) (σ.obj z))
    (hzy : HasIrreducibleMorphism (σ.obj z) (σ.obj y)) :
    HasIrreducibleMorphism
        (σ.obj (AR.arTranslation σ ⟨y, hy⟩).1)
        (σ.obj (AR.arTranslation σ ⟨z, hz⟩).1) ∧
      HasIrreducibleMorphism
        (σ.obj (AR.arTranslation σ ⟨z, hz⟩).1)
        (σ.obj (AR.arTranslation σ ⟨y, hy⟩).1) := by
  have hτz_y := (AR.arTranslation_incidence σ ⟨z, hz⟩ y).1 hyz
  have hτy_z := (AR.arTranslation_incidence σ ⟨y, hy⟩ z).1 hzy
  constructor
  · exact
      (AR.arTranslation_incidence σ ⟨y, hy⟩
        (AR.arTranslation σ ⟨z, hz⟩).1).1 hτz_y
  · exact
      (AR.arTranslation_incidence σ ⟨z, hz⟩
        (AR.arTranslation σ ⟨y, hy⟩).1).1 hτy_z

omit [Fintype ι] in
include K in
/-- If neither member of a nonprojective two-cycle is translation-fixed,
the only predecessors of the first member are the second member and the
translate of the second member.  The two opposite mesh inequalities force
equality, so a third predecessor would contribute a positive extra summand. -/
theorem predecessor_eq_or_eq_arTranslation_of_two_cycle
    (y z : ι) (hy : ¬ Projective (σ.obj y))
    (hz : ¬ Projective (σ.obj z))
    (hy_not_fixed : (AR.arTranslation σ ⟨y, hy⟩).1 ≠ y)
    (hz_not_fixed : (AR.arTranslation σ ⟨z, hz⟩).1 ≠ z)
    (hyz : HasIrreducibleMorphism (σ.obj y) (σ.obj z))
    (hzy : HasIrreducibleMorphism (σ.obj z) (σ.obj y))
    {x : ι} (hxy : HasIrreducibleMorphism (σ.obj x) (σ.obj y)) :
    x = z ∨ x = (AR.arTranslation σ ⟨z, hz⟩).1 := by
  let ty : ι := (AR.arTranslation σ ⟨y, hy⟩).1
  let tz : ι := (AR.arTranslation σ ⟨z, hz⟩).1
  let Ay := AR.chosenRightAR σ ⟨y, hy⟩
  let Az := AR.chosenRightAR σ ⟨z, hz⟩
  have htz_y : HasIrreducibleMorphism (σ.obj tz) (σ.obj y) := by
    exact (AR.arTranslation_incidence σ ⟨z, hz⟩ y).1 hyz
  have hty_z : HasIrreducibleMorphism (σ.obj ty) (σ.obj z) := by
    exact (AR.arTranslation_incidence σ ⟨y, hy⟩ z).1 hzy
  obtain ⟨tzy, htzy⟩ := (Ay.summandIrreducibleCorrespondence z).2 hzy
  obtain ⟨ttzy, httzy⟩ := (Ay.summandIrreducibleCorrespondence tz).2 htz_y
  obtain ⟨tyz, htyz⟩ := (Az.summandIrreducibleCorrespondence y).2 hyz
  obtain ⟨ttyz, httyz⟩ := (Az.summandIrreducibleCorrespondence ty).2 hty_z
  have htzy_ne : tzy ≠ ttzy := by
    intro h
    apply hz_not_fixed
    change tz = z
    rw [← htzy, ← httzy, h]
  have htyz_ne : tyz ≠ ttyz := by
    intro h
    apply hy_not_fixed
    change ty = y
    rw [← htyz, ← httyz, h]
  have hyPair := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ Ay tzy ttzy htzy_ne
  have hzPair := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ Az tyz ttyz htyz_ne
  rw [htzy, httzy] at hyPair
  rw [htyz, httyz] at hzPair
  have hyMesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ ⟨y, hy⟩
  have hzMesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ ⟨z, hz⟩
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj ty) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj y) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) Ay.middle at hyMesh
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj tz) +
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj z) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) Az.middle at hzMesh
  have hyMiddle :
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) Ay.middle =
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj z) +
          QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj tz) := by
    omega
  by_contra hcases
  rw [not_or] at hcases
  obtain ⟨txy, htxy⟩ := (Ay.summandIrreducibleCorrespondence x).2 hxy
  have htxy_tzy : txy ≠ tzy := by
    intro h
    exact hcases.1 (by rw [← htxy, ← htzy, h])
  have htxy_ttzy : txy ≠ ttzy := by
    intro h
    apply hcases.2
    change x = tz
    rw [← htxy, ← httzy, h]
  have hthree := add_add_groundFinrank_le_middle_of_three_occurrences
    (K := K) σ Ay txy tzy ttzy htxy_tzy htxy_ttzy htzy_ne
  rw [htxy, htzy, httzy, hyMiddle] at hthree
  have hxpos := groundFinrank_obj_pos (K := K) σ x
  omega

omit [Fintype ι] in
include K in
/-- If a projective vertex and another vertex are joined by arrows in both
directions, the other vertex is nonprojective and fixed by AR translation.
This is the first, dimension-theoretic part of the manuscript's local
two-cycle lemma. -/
theorem arTranslation_eq_self_of_projective_two_cycle
    (p z : ι) (hp : Projective (σ.obj p))
    (hpz : HasIrreducibleMorphism (σ.obj p) (σ.obj z))
    (hzp : HasIrreducibleMorphism (σ.obj z) (σ.obj p)) :
    ∃ hz : ¬ Projective (σ.obj z),
      (AR.arTranslation σ ⟨z, hz⟩).1 = z := by
  have hz : ¬ Projective (σ.obj z) := by
    intro hz
    let Aₚ := σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition p hp
    let Aᵢ := σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition z hz
    obtain ⟨tₚ, htₚ⟩ := (Aₚ.summandIrreducibleCorrespondence z).2 hzp
    obtain ⟨tᵢ, htᵢ⟩ := (Aᵢ.summandIrreducibleCorrespondence p).2 hpz
    have hzp_le := groundFinrank_le_middle_of_occurrence
      (K := K) σ Aₚ tₚ
    have hpz_le := groundFinrank_le_middle_of_occurrence
      (K := K) σ Aᵢ tᵢ
    have hradp := projectiveBoundaryRadical_groundFinrank_lt
      (K := K) σ p
    have hradz := projectiveBoundaryRadical_groundFinrank_lt
      (K := K) σ z
    rw [htₚ] at hzp_le
    change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj z) ≤
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.projectiveBoundaryRadical p) at hzp_le
    rw [htᵢ] at hpz_le
    change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj p) ≤
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.projectiveBoundaryRadical z) at hpz_le
    have hz_lt_p :
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj z) <
          QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj p) := by
      apply lt_of_le_of_lt hzp_le
      exact hradp
    have hp_lt_z :
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj p) <
          QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
            (K := K) (σ.obj z) := by
      apply lt_of_le_of_lt hpz_le
      exact hradz
    omega
  refine ⟨hz, ?_⟩
  let x : σ.NonprojectiveLabel := ⟨z, hz⟩
  by_contra hne
  let Aₚ := σ.projectiveBoundaryMinimalRightAlmostSplitDecomposition p hp
  let Aₓ := AR.chosenRightAR σ x
  have htaup : HasIrreducibleMorphism
      (σ.obj (AR.arTranslation σ x).1) (σ.obj p) :=
    (AR.arTranslation_incidence σ x p).1 hpz
  obtain ⟨tₓ, htₓ⟩ := (Aₚ.summandIrreducibleCorrespondence z).2 hzp
  obtain ⟨tₜ, htₜ⟩ :=
    (Aₚ.summandIrreducibleCorrespondence
      (AR.arTranslation σ x).1).2 htaup
  have htne : tₓ ≠ tₜ := by
    intro ht
    apply hne
    have hz_tau : z = (AR.arTranslation σ x).1 := by
      rw [← htₓ, ← htₜ, ht]
    exact hz_tau.symm
  have hpair := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ Aₚ tₓ tₜ htne
  rw [htₓ, htₜ] at hpair
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj z) +
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj (AR.arTranslation σ x).1) ≤
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.projectiveBoundaryRadical p) at hpair
  have hpair' :
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj z) +
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj (AR.arTranslation σ x).1) ≤
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.projectiveBoundaryRadical p) := by
    exact hpair
  have hradp := projectiveBoundaryRadical_groundFinrank_lt
    (K := K) σ p
  obtain ⟨tₚ, htₚ⟩ := (Aₓ.summandIrreducibleCorrespondence p).2 hpz
  have hp_le_middle := groundFinrank_le_middle_of_occurrence
    (K := K) σ Aₓ tₚ
  have hp_le_middle' :
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (σ.obj p) ≤
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) Aₓ.middle := by
    simpa [htₚ] using hp_le_middle
  have hmesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ x
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj (AR.arTranslation σ x).1) +
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj z) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) Aₓ.middle at hmesh
  omega

omit [Algebra K R] [FiniteDimensional K R] [Fintype ι] in
/-- A fixed point one AR-translation step later pulls back to a fixed point,
by injectivity of AR translation. -/
theorem arTranslation_eq_self_of_translated_eq_self
    (x : ι) (hx : ¬ Projective (σ.obj x))
    (htx : ¬ Projective
      (σ.obj (AR.arTranslation σ ⟨x, hx⟩).1))
    (hfixed :
      (AR.arTranslation σ
        ⟨(AR.arTranslation σ ⟨x, hx⟩).1, htx⟩).1 =
          (AR.arTranslation σ ⟨x, hx⟩).1) :
    (AR.arTranslation σ ⟨x, hx⟩).1 = x := by
  have hinputs :
      (⟨(AR.arTranslation σ ⟨x, hx⟩).1, htx⟩ :
          σ.NonprojectiveLabel) = ⟨x, hx⟩ := by
    apply AR.arTranslation_injective σ
    apply Subtype.ext
    simpa using hfixed
  exact congrArg Subtype.val hinputs

/-- An opposite-arrow pair with neither member projective or fixed. -/
@[ext]
structure NonfixedTwoCycle where
  left : ι
  right : ι
  left_nonprojective : ¬ Projective (σ.obj left)
  right_nonprojective : ¬ Projective (σ.obj right)
  left_to_right :
    HasIrreducibleMorphism (σ.obj left) (σ.obj right)
  right_to_left :
    HasIrreducibleMorphism (σ.obj right) (σ.obj left)
  left_not_fixed :
    (AR.arTranslation σ ⟨left, left_nonprojective⟩).1 ≠ left
  right_not_fixed :
    (AR.arTranslation σ ⟨right, right_nonprojective⟩).1 ≠ right

noncomputable instance nonfixedTwoCycleFinite [Finite ι] :
    Finite (AR.NonfixedTwoCycle σ) :=
  Finite.of_injective
    (fun Q ↦ (Q.left, Q.right)) (by
      intro Q₁ Q₂ h
      ext
      · exact congrArg (fun q ↦ q.1) h
      · exact congrArg (fun q ↦ q.2) h)

namespace NonfixedTwoCycle

variable {AR : σ.FiniteARTranslationData}

include K in
/-- Simultaneous AR translation preserves a nonfixed two-cycle.  If a
translated member were projective, the projective two-cycle theorem would
fix the other translated member, and translation injectivity would pull
that fixed point back. -/
def translate (Q : AR.NonfixedTwoCycle σ) : AR.NonfixedTwoCycle σ := by
  let l : ι := (AR.arTranslation σ ⟨Q.left, Q.left_nonprojective⟩).1
  let r : ι := (AR.arTranslation σ ⟨Q.right, Q.right_nonprojective⟩).1
  have hpair := AR.arTranslation_two_cycle σ Q.left Q.right
    Q.left_nonprojective Q.right_nonprojective
    Q.left_to_right Q.right_to_left
  have hlr : HasIrreducibleMorphism (σ.obj l) (σ.obj r) := by
    simpa [l, r] using hpair.1
  have hrl : HasIrreducibleMorphism (σ.obj r) (σ.obj l) := by
    simpa [l, r] using hpair.2
  have hl_nonprojective : ¬ Projective (σ.obj l) := by
    intro hl_projective
    obtain ⟨hr_nonprojective, hr_fixed⟩ :=
      AR.arTranslation_eq_self_of_projective_two_cycle
        (K := K) σ l r hl_projective hlr hrl
    apply Q.right_not_fixed
    exact AR.arTranslation_eq_self_of_translated_eq_self
      σ Q.right Q.right_nonprojective (by simpa [r] using hr_nonprojective)
        (by simpa [r] using hr_fixed)
  have hr_nonprojective : ¬ Projective (σ.obj r) := by
    intro hr_projective
    obtain ⟨hl_nonprojective', hl_fixed⟩ :=
      AR.arTranslation_eq_self_of_projective_two_cycle
        (K := K) σ r l hr_projective hrl hlr
    apply Q.left_not_fixed
    exact AR.arTranslation_eq_self_of_translated_eq_self
      σ Q.left Q.left_nonprojective (by simpa [l] using hl_nonprojective')
        (by simpa [l] using hl_fixed)
  have hl_not_fixed :
      (AR.arTranslation σ ⟨l, hl_nonprojective⟩).1 ≠ l := by
    intro hl_fixed
    apply Q.left_not_fixed
    exact AR.arTranslation_eq_self_of_translated_eq_self
      σ Q.left Q.left_nonprojective (by simpa [l] using hl_nonprojective)
        (by simpa [l] using hl_fixed)
  have hr_not_fixed :
      (AR.arTranslation σ ⟨r, hr_nonprojective⟩).1 ≠ r := by
    intro hr_fixed
    apply Q.right_not_fixed
    exact AR.arTranslation_eq_self_of_translated_eq_self
      σ Q.right Q.right_nonprojective (by simpa [r] using hr_nonprojective)
        (by simpa [r] using hr_fixed)
  exact {
    left := l
    right := r
    left_nonprojective := hl_nonprojective
    right_nonprojective := hr_nonprojective
    left_to_right := hlr
    right_to_left := hrl
    left_not_fixed := hl_not_fixed
    right_not_fixed := hr_not_fixed }

/-- All vertices occurring in simultaneous translation iterates of a
nonfixed two-cycle. -/
def translationOrbit (Q : AR.NonfixedTwoCycle σ) : Set ι :=
  {x | ∃ n : ℕ,
    x = ((fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q).left ∨
      x = ((fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q).right}

omit [Fintype ι] in
include K in
/-- The simultaneous translation orbit of a nonfixed two-cycle is closed
under irreducible predecessors. -/
theorem translationOrbit_predecessorClosed
    (Q : AR.NonfixedTwoCycle σ) {x y : ι}
    (hxy : HasIrreducibleMorphism (σ.obj x) (σ.obj y))
    (hy : y ∈ Q.translationOrbit (K := K) σ) :
    x ∈ Q.translationOrbit (K := K) σ := by
  obtain ⟨n, hyn | hyn⟩ := hy
  · let C :=
      (fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q
    have hpred := AR.predecessor_eq_or_eq_arTranslation_of_two_cycle
      (K := K) σ C.left C.right C.left_nonprojective
        C.right_nonprojective C.left_not_fixed C.right_not_fixed
        C.left_to_right C.right_to_left (by simpa [C, hyn] using hxy)
    rcases hpred with hx | hx
    · exact ⟨n, Or.inr hx⟩
    · refine ⟨n + 1, Or.inr ?_⟩
      simpa [C, NonfixedTwoCycle.translate,
        Function.iterate_succ_apply'] using hx
  · let C :=
      (fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q
    have hpred := AR.predecessor_eq_or_eq_arTranslation_of_two_cycle
      (K := K) σ C.right C.left C.right_nonprojective
        C.left_nonprojective C.right_not_fixed C.left_not_fixed
        C.right_to_left C.left_to_right (by simpa [C, hyn] using hxy)
    rcases hpred with hx | hx
    · exact ⟨n, Or.inl hx⟩
    · refine ⟨n + 1, Or.inl ?_⟩
      simpa [C, NonfixedTwoCycle.translate,
        Function.iterate_succ_apply'] using hx

include K in
/-- The full local two-cycle lemma: one member of every opposite-arrow pair
is fixed by AR translation. -/
theorem exists_arTranslation_eq_self_of_two_cycle_aux
    (y z : ι)
    (hyz : HasIrreducibleMorphism (σ.obj y) (σ.obj z))
    (hzy : HasIrreducibleMorphism (σ.obj z) (σ.obj y)) :
    (∃ hy : ¬ Projective (σ.obj y),
      (AR.arTranslation σ ⟨y, hy⟩).1 = y) ∨
    (∃ hz : ¬ Projective (σ.obj z),
      (AR.arTranslation σ ⟨z, hz⟩).1 = z) := by
  classical
  by_cases hy : Projective (σ.obj y)
  · exact Or.inr
      (AR.arTranslation_eq_self_of_projective_two_cycle
        (K := K) σ y z hy hyz hzy)
  · by_cases hz : Projective (σ.obj z)
    · exact Or.inl
        (AR.arTranslation_eq_self_of_projective_two_cycle
          (K := K) σ z y hz hzy hyz)
    · by_cases hy_fixed : (AR.arTranslation σ ⟨y, hy⟩).1 = y
      · exact Or.inl ⟨hy, hy_fixed⟩
      · by_cases hz_fixed : (AR.arTranslation σ ⟨z, hz⟩).1 = z
        · exact Or.inr ⟨hz, hz_fixed⟩
        · let Q : AR.NonfixedTwoCycle σ := {
            left := y
            right := z
            left_nonprojective := hy
            right_nonprojective := hz
            left_to_right := hyz
            right_to_left := hzy
            left_not_fixed := hy_fixed
            right_not_fixed := hz_fixed }
          have hroot := isProjectivelyRooted_univ (K := K) σ y
            (Finset.mem_univ y)
          obtain ⟨p, hp_boundary, _, hpy⟩ := hroot
          have hp_projective : Projective (σ.obj p) := by
            simpa [projectiveLabelFinset] using hp_boundary
          have hy_orbit : y ∈ Q.translationOrbit (K := K) σ :=
            ⟨0, Or.inl rfl⟩
          have backward : ∀ {a b : ι},
              Relation.ReflTransGen
                  (QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
                    σ.irreducibleEdge Finset.univ) a b →
                b ∈ Q.translationOrbit (K := K) σ →
                a ∈ Q.translationOrbit (K := K) σ := by
            intro a b hab hb
            induction hab using Relation.ReflTransGen.head_induction_on with
            | refl => exact hb
            | @head c d hcd _ ih =>
                exact Q.translationOrbit_predecessorClosed
                  (K := K) σ hcd.2.2 ih
          have hp_orbit : p ∈ Q.translationOrbit (K := K) σ := by
            exact backward hpy hy_orbit
          obtain ⟨n, hp_left | hp_right⟩ := hp_orbit
          · let C :=
              (fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q
            exact (C.left_nonprojective (hp_left ▸ hp_projective)).elim
          · let C :=
              (fun C : AR.NonfixedTwoCycle σ ↦ C.translate (K := K) σ)^[n] Q
            exact (C.right_nonprojective (hp_right ▸ hp_projective)).elim

end NonfixedTwoCycle

include K in
/-- Manuscript-facing form of the first clause of the local two-cycle
lemma. -/
theorem exists_arTranslation_eq_self_of_two_cycle
    (y z : ι)
    (hyz : HasIrreducibleMorphism (σ.obj y) (σ.obj z))
    (hzy : HasIrreducibleMorphism (σ.obj z) (σ.obj y)) :
    (∃ hy : ¬ Projective (σ.obj y),
      (AR.arTranslation σ ⟨y, hy⟩).1 = y) ∨
    (∃ hz : ¬ Projective (σ.obj z),
      (AR.arTranslation σ ⟨z, hz⟩).1 = z) :=
  NonfixedTwoCycle.exists_arTranslation_eq_self_of_two_cycle_aux
    (K := K) (AR := AR) σ y z hyz hzy

/-- The finite partial translation viewed as an abstract pair of boundary
complements. -/
def boundaryTranslationChainData :
    QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data ι
      (fun x ↦ Projective (σ.obj x))
      (fun x ↦ Injective (σ.obj x)) where
  tau := AR.arTranslationEquiv σ

/-- A projective vertex reaches an injective vertex by repeatedly applying
inverse AR translation.  No representation-directedness assumption is
needed; periodic components away from this chain are allowed. -/
theorem exists_iterate_arSuccessor_injective
    (p : ι) (hp : Projective (σ.obj p)) :
    ∃ n ≤ Fintype.card ι,
      Injective (σ.obj
        ((AR.boundaryTranslationChainData σ).successor^[n] p)) :=
  (AR.boundaryTranslationChainData σ).exists_iterate_mem_target p hp

/-- Before the injective endpoint, the boundary-chain successor is
nonprojective and has ordinary AR translate equal to the previous vertex. -/
theorem arTranslation_successor_of_noninjective
    (x : ι) (hx : ¬ Injective (σ.obj x)) :
    let y := (AR.boundaryTranslationChainData σ).successor x
    let hy : ¬ Projective (σ.obj y) :=
      (AR.boundaryTranslationChainData σ).successor_not_mem_source_of_not_mem_target hx
    (AR.arTranslation σ ⟨y, hy⟩).1 = x := by
  let T := AR.boundaryTranslationChainData σ
  let y := T.successor x
  let hy : ¬ Projective (σ.obj y) :=
    T.successor_not_mem_source_of_not_mem_target hx
  have h := T.tau_successor_of_not_mem_target hx
  change (AR.arTranslationEquiv σ) ⟨y, hy⟩ = ⟨x, hx⟩ at h
  exact congrArg Subtype.val h

omit [Fintype ι] in
/-- An irreducible arrow into a projective endpoint points from a strictly
smaller ground-field dimension. -/
theorem groundFinrank_lt_of_irreducible_to_projective
    {x p : ι} (hp : Projective (σ.obj p))
    (hxp : HasIrreducibleMorphism (σ.obj x) (σ.obj p)) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj x) <
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj p) := by
  obtain ⟨f, hf⟩ := hxp
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) := Module.Finite.trans R (σ.obj x)
  letI : Module K (σ.obj p) := Module.restrictScalars K R (σ.obj p)
  letI : IsScalarTower K R (σ.obj p) :=
    IsScalarTower.restrictScalars K R (σ.obj p)
  letI : FiniteDimensional K (σ.obj p) := Module.Finite.trans R (σ.obj p)
  rcases QuotientSubmoduleEquidistribution.RepresentationDirected.finrank_orientation_of_isIrreducibleMorphism
      (K := K) hf with h | h
  · exact h.1
  · letI : Epi f := h.2
    exact (QuotientSubmoduleEquidistribution.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
      hf hp).elim

omit [Fintype ι] in
/-- An irreducible arrow out of an injective source points to a strictly
smaller ground-field dimension. -/
theorem groundFinrank_lt_of_irreducible_from_injective
    {i x : ι} (hi : Injective (σ.obj i))
    (hix : HasIrreducibleMorphism (σ.obj i) (σ.obj x)) :
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj x) <
      QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (σ.obj i) := by
  obtain ⟨f, hf⟩ := hix
  letI : Module K (σ.obj i) := Module.restrictScalars K R (σ.obj i)
  letI : IsScalarTower K R (σ.obj i) :=
    IsScalarTower.restrictScalars K R (σ.obj i)
  letI : FiniteDimensional K (σ.obj i) := Module.Finite.trans R (σ.obj i)
  letI : Module K (σ.obj x) := Module.restrictScalars K R (σ.obj x)
  letI : IsScalarTower K R (σ.obj x) :=
    IsScalarTower.restrictScalars K R (σ.obj x)
  letI : FiniteDimensional K (σ.obj x) := Module.Finite.trans R (σ.obj x)
  rcases QuotientSubmoduleEquidistribution.RepresentationDirected.finrank_orientation_of_isIrreducibleMorphism
      (K := K) hf with h | h
  · letI : Mono f := h.2
    exact (QuotientSubmoduleEquidistribution.RepresentationDirected.not_injective_source_of_isIrreducibleMorphism_of_mono
      hf hi).elim
  · exact h.1

include K AR in
/-- The projective member of an opposite-arrow pair is injective.  This is
the second projective clause of the manuscript's local two-cycle lemma. -/
theorem injective_of_projective_two_cycle
    (p z : ι) (hp : Projective (σ.obj p))
    (hpz : HasIrreducibleMorphism (σ.obj p) (σ.obj z))
    (hzp : HasIrreducibleMorphism (σ.obj z) (σ.obj p)) :
    Injective (σ.obj p) := by
  classical
  by_contra hpni
  obtain ⟨hz, hfix⟩ :=
    arTranslation_eq_self_of_projective_two_cycle
      (K := K) σ AR p z hp hpz hzp
  let T := AR.boundaryTranslationChainData σ
  have hex : ∃ n, Injective (σ.obj (T.successor^[n] p)) := by
    obtain ⟨n, _, hn⟩ := AR.exists_iterate_arSuccessor_injective σ p hp
    exact ⟨n, hn⟩
  let n := Nat.find hex
  let i : ι := T.successor^[n] p
  have hi : Injective (σ.obj i) := Nat.find_spec hex
  have hbefore : ∀ m, m < n →
      ¬ Injective (σ.obj (T.successor^[m] p)) := by
    intro m hm
    exact Nat.find_min hex (by simpa [n] using hm)
  have hcycles : ∀ m, m ≤ n →
      HasIrreducibleMorphism
          (σ.obj (T.successor^[m] p)) (σ.obj z) ∧
        HasIrreducibleMorphism
          (σ.obj z) (σ.obj (T.successor^[m] p)) := by
    intro m hm
    induction m with
    | zero => simpa using And.intro hpz hzp
    | succ m ih =>
        have hm_lt : m < n := by omega
        have hm_le : m ≤ n := by omega
        obtain ⟨hqz, hzq⟩ := ih hm_le
        let q : ι := T.successor^[m] p
        let r : ι := T.successor q
        have hqni : ¬ Injective (σ.obj q) := hbefore m hm_lt
        have hrnp : ¬ Projective (σ.obj r) :=
          T.successor_not_mem_source_of_not_mem_target hqni
        have htaur : (AR.arTranslation σ ⟨r, hrnp⟩).1 = q := by
          exact AR.arTranslation_successor_of_noninjective σ q hqni
        have hzr : HasIrreducibleMorphism (σ.obj z) (σ.obj r) := by
          apply (AR.arTranslation_incidence σ ⟨r, hrnp⟩ z).2
          simpa [htaur] using hqz
        have hrz : HasIrreducibleMorphism (σ.obj r) (σ.obj z) := by
          apply (AR.arTranslation_incidence σ ⟨z, hz⟩ r).2
          simpa [hfix] using hzr
        simpa [q, r, Function.iterate_succ_apply'] using And.intro hrz hzr
  obtain ⟨hiz, hzi⟩ := hcycles n le_rfl
  change HasIrreducibleMorphism (σ.obj i) (σ.obj z) at hiz
  change HasIrreducibleMorphism (σ.obj z) (σ.obj i) at hzi
  have hpgt := groundFinrank_lt_of_irreducible_to_projective
    (K := K) σ hp hzp
  have higt := groundFinrank_lt_of_irreducible_from_injective
    (K := K) σ hi hiz
  let A := AR.chosenRightAR σ ⟨z, hz⟩
  obtain ⟨tₚ, htₚ⟩ := (A.summandIrreducibleCorrespondence p).2 hpz
  obtain ⟨tᵢ, htᵢ⟩ := (A.summandIrreducibleCorrespondence i).2 hiz
  have hpi : p ≠ i := by
    intro h
    exact hpni (h ▸ hi)
  have htne : tₚ ≠ tᵢ := by
    intro h
    apply hpi
    rw [← htₚ, ← htᵢ, h]
  have hmiddle := add_groundFinrank_le_middle_of_two_occurrences
    (K := K) σ A tₚ tᵢ htne
  rw [htₚ, htᵢ] at hmiddle
  have hmesh := AR.arTranslation_add_endpoint_groundFinrank_eq_middle
    (K := K) σ ⟨z, hz⟩
  rw [hfix] at hmesh
  change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj z) +
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) (σ.obj z) =
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
      (K := K) A.middle at hmesh
  omega

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
