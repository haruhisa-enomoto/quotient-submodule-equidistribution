import OpConjecture.RepresentationDirected.IrreducibleDimensionGrowth
import OpConjecture.RepresentationTheory.FiniteDimensionalARNonvanishing

/-!
# Classification-free multiplicity one

This file proves the representation-directed bound `dim Irr(X,Y) ≤ 1` by
the classification-free dimension-ascent argument.  A hypothetical
two-dimensional irreducible space gives two copies of one indecomposable in
an almost-split middle term.  Rotating the mesh preserves that multiplicity
and strictly increases the larger module dimension, which is impossible on a
finite skeleton.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected

universe u v

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

attribute [local instance] FintypeCat.fintype

omit [IsAlgClosed K] [FiniteDimensional K R] [Fintype Iota] in
/-- Finrank at least two supplies two distinct copies of the source in any
minimal right almost-split middle decomposition. -/
theorem exists_two_rightAROccurrences_of_two_le_finrank
    [∀ i : Iota, Module K (sigma.obj i)]
    [∀ i : Iota, IsScalarTower K R (sigma.obj i)]
    {z x : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, a • 𝟙 (sigma.obj x) = f)
    (hbad : 2 ≤ Module.finrank K
      (sigma.irreducibleHomSpace (K := K) x z)) :
    ∃ t₁ t₂ : A.index, t₁ ≠ t₂ ∧ A.label t₁ = x ∧ A.label t₂ = x := by
  have hcard : 2 ≤ Nat.card (sigma.RightAROccurrence A x) := by
    rw [← sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence
      A x hscalar]
    exact hbad
  have hlt : 1 < Nat.card (sigma.RightAROccurrence A x) :=
    lt_of_lt_of_le (by decide) hcard
  letI : Nontrivial (sigma.RightAROccurrence A x) :=
    Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨t₁, t₂, hne⟩ :=
    exists_pair_ne (sigma.RightAROccurrence A x)
  exact ⟨t₁.1, t₂.1, fun h ↦ hne (Subtype.ext h), t₁.2, t₂.2⟩

/-- Classification-free multiplicity one from any supplied finite
AR-translation datum. -/
theorem finrank_irreducibleHomSpace_le_one_of_finiteARTranslationData
    (D : sigma.FiniteARTranslationData)
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (x y : Iota) :
    letI (i : Iota) : Module K (sigma.obj i) :=
      Module.restrictScalars K R (sigma.obj i)
    letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
      IsScalarTower.restrictScalars K R (sigma.obj i)
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) ≤ 1 := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : FiniteDimensional K (sigma.obj i) :=
    Module.Finite.trans R (sigma.obj i)
  let dim : Iota → ℕ := fun i ↦
    groundFinrank (K := K) (sigma.obj i)
  let Bad : Iota → Iota → Prop := fun a b ↦
    2 ≤ Module.finrank K
      (sigma.irreducibleHomSpace (K := K) a b)
  have irreducible_of_bad : ∀ {a b}, Bad a b →
      HasIrreducibleMorphism (sigma.obj a) (sigma.obj b) := by
    intro a b hab
    apply (sigma.finrank_irreducibleHomSpace_pos_iff_hasIrreducibleMorphism
      (K := K) a b).1
    exact lt_of_lt_of_le (by decide) hab
  have no_source_large : ¬ ∃ a b, Bad a b ∧ dim b < dim a := by
    apply no_large_source_pairs_of_strict_growth Bad dim
    intro a b hab hba
    obtain ⟨f, hf⟩ := irreducible_of_bad hab
    letI : Epi f :=
      epi_of_isIrreducibleMorphism_of_finrank_gt (K := K) hf hba
    have hbnp : ¬ Projective (sigma.obj b) :=
      not_projective_target_of_isIrreducibleMorphism_of_epi hf
    let z : sigma.NonprojectiveLabel := ⟨b, hbnp⟩
    let A := D.chosenRightAR sigma z
    obtain ⟨t₁, t₂, hne, ht₁, ht₂⟩ :=
      exists_two_rightAROccurrences_of_two_le_finrank sigma A
        (H.endomorphism_eq_smul_id K R sigma a) hab
    let a' : Iota := (D.arTranslation sigma z).1
    have hbad' : Bad a' a := by
      dsimp only [Bad, a']
      rw [← finrank_irreducibleHomSpace_eq_arTranslation
        (K := K) sigma D z a
          (H.endomorphism_eq_smul_id K R sigma a)]
      exact hab
    have hgrowKernel :=
      rightAR_kernel_groundFinrank_gt_of_two_occurrences
        (K := K) sigma A hbnp t₁ t₂ hne ht₁ ht₂ hba
    have hkiso := groundFinrank_eq_of_iso (K := K)
      (D.arTranslationKernelIso sigma z)
    have hgrow : dim a < dim a' := by
      dsimp only [dim]
      change groundFinrank (K := K) (sigma.obj a) <
        groundFinrank (K := K)
          (sigma.obj (D.arTranslationLabel sigma z))
      rw [← hkiso]
      exact hgrowKernel
    exact ⟨a', a, hbad', hgrow, hgrow⟩
  have no_target_large : ¬ ∃ a b, Bad a b ∧ dim a < dim b := by
    apply no_large_target_pairs_of_strict_growth Bad dim
    intro a b hab habdim
    obtain ⟨f, hf⟩ := irreducible_of_bad hab
    letI : Mono f :=
      mono_of_isIrreducibleMorphism_of_finrank_lt (K := K) hf habdim
    have hani : ¬ Injective (sigma.obj a) :=
      not_injective_source_of_isIrreducibleMorphism_of_mono hf
    let ai : sigma.NoninjectiveLabel := ⟨a, hani⟩
    let z : sigma.NonprojectiveLabel := (D.arTranslationEquiv sigma).symm ai
    have htauSubtype : D.arTranslationEquiv sigma z = ai :=
      (D.arTranslationEquiv sigma).apply_symm_apply ai
    have htau : (D.arTranslation sigma z).1 = a :=
      congrArg Subtype.val htauSubtype
    change D.arTranslationLabel sigma z = a at htau
    let A := D.chosenRightAR sigma z
    change 2 ≤ Module.finrank K
      (sigma.irreducibleHomSpace (K := K)
        a b) at hab
    have hbad' : Bad b z.1 := by
      dsimp only [Bad]
      rw [finrank_irreducibleHomSpace_eq_arTranslation
        (K := K) sigma D z b
          (H.endomorphism_eq_smul_id K R sigma b)]
      change 2 ≤ Module.finrank K
        (sigma.irreducibleHomSpace (K := K)
          (D.arTranslationLabel sigma z) b)
      rw [htau]
      exact hab
    obtain ⟨t₁, t₂, hne, ht₁, ht₂⟩ :=
      exists_two_rightAROccurrences_of_two_le_finrank sigma A
        (H.endomorphism_eq_smul_id K R sigma b) hbad'
    have hkiso := groundFinrank_eq_of_iso (K := K)
      (D.arTranslationKernelIso sigma z)
    have hklt : groundFinrank (K := K)
        (kernel A.map : FGModuleCat.{u} R) < dim b := by
      rw [hkiso, htau]
      dsimp only [dim] at habdim
      exact habdim
    have hgrow := rightAR_target_groundFinrank_gt_of_two_occurrences
      (K := K) sigma A z.2 t₁ t₂ hne ht₁ ht₂ hklt
    have hgrow' : dim b < dim z.1 := by
      exact hgrow
    exact ⟨b, z.1, hbad', hgrow', hgrow'⟩
  by_contra hle
  have hbad : Bad x y := by
    dsimp only [Bad]
    omega
  obtain ⟨f, hf⟩ := irreducible_of_bad hbad
  rcases finrank_orientation_of_isIrreducibleMorphism
      (K := K) hf with hxy | hyx
  · exact no_target_large ⟨x, y, hbad, hxy.1⟩
  · exact no_source_large ⟨x, y, hbad, hyx.1⟩

/-- Assem--Simson--Skowroński IV.4.9 in the exact finite directed setting
used by the paper: every irreducible-morphism space has dimension at most
one.  Finite-dimensional algebras automatically supply the required
AR-translation datum. -/
theorem finrank_irreducibleHomSpace_le_one
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (x y : Iota) :
    letI (i : Iota) : Module K (sigma.obj i) :=
      Module.restrictScalars K R (sigma.obj i)
    letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
      IsScalarTower.restrictScalars K R (sigma.obj i)
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) ≤ 1 :=
  finrank_irreducibleHomSpace_le_one_of_finiteARTranslationData
    (K := K) sigma (sigma.finiteDimensionalARTranslationData K R) H x y

/-- Paper-facing bundled form of the multiplicity-one conclusion. -/
def HasMultiplicityOneIrreducibles : Prop :=
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  ∀ x y : Iota,
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) ≤ 1

/-- Directedness on a finite skeleton proves the bundled multiplicity-one
property. -/
theorem hasMultiplicityOneIrreducibles
    (H : HasAcyclicNonzeroNonisomorphisms sigma) :
    HasMultiplicityOneIrreducibles (K := K) sigma := by
  intro x y
  exact finrank_irreducibleHomSpace_le_one (K := K) sigma H x y

include K in
/-- Every minimal right almost-split middle decomposition in the directed
setting is multiplicity-free, including projective radical decompositions. -/
theorem HasAcyclicNonzeroNonisomorphisms.rightARLabel_injective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z) :
    Function.Injective A.label := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  apply sigma.directedRightARLabel_injective_of_finrank_le_one
    (K := K) (R := R) H A
  intro x
  exact finrank_irreducibleHomSpace_le_one (K := K) sigma H x z

include K in
/-- Every minimal left almost-split middle decomposition in the directed
setting is multiplicity-free, including the injective boundary. -/
theorem HasAcyclicNonzeroNonisomorphisms.leftARLabel_injective
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {x : Iota} (A : sigma.MinimalLeftAlmostSplitDecomposition x) :
    Function.Injective A.label := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  apply sigma.directedLeftARLabel_injective_of_finrank_le_one
    (K := K) (R := R) H A
  intro y
  exact finrank_irreducibleHomSpace_le_one (K := K) sigma H x y

end OpConjecture.RepresentationDirected
