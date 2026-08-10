import QuotientSubmoduleEquidistribution.RepresentationDirected.IrreducibleDimensionGrowth
import QuotientSubmoduleEquidistribution.RepresentationTheory.ScalarModuloRadicalOccurrenceBasis
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalARNonvanishing

/-!
# Multiplicity one for representation-finite algebras

This file formalizes Assem--Simson--Skowroński IV.4.9 in the form needed
by the manuscript.  Over an algebraically closed field, a representation-
finite algebra has no multiple arrows in its Auslander--Reiten quiver.

The proof is classification-free.  Two independent irreducible maps give
two equal summands in an almost-split middle term.  Rotating the mesh keeps
that multiplicity and strictly increases one endpoint dimension; finiteness
of the indecomposable skeleton rules out indefinite ascent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

attribute [local instance] FintypeCat.fintype

omit [Fintype Iota] in
/-- Finrank at least two supplies two distinct copies of the source in any
minimal right almost-split middle decomposition over an algebraically closed
field. -/
theorem exists_two_rightAROccurrences_of_two_le_finrank_of_isAlgClosed
    {z x : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    (hbad :
      letI (i : Iota) : Module K (sigma.obj i) :=
        Module.restrictScalars K R (sigma.obj i)
      letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
        IsScalarTower.restrictScalars K R (sigma.obj i)
      2 ≤ Module.finrank K
        (sigma.irreducibleHomSpace (K := K) x z)) :
    letI (i : Iota) : Module K (sigma.obj i) :=
      Module.restrictScalars K R (sigma.obj i)
    letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
      IsScalarTower.restrictScalars K R (sigma.obj i)
    ∃ t₁ t₂ : A.index,
      t₁ ≠ t₂ ∧ A.label t₁ = x ∧ A.label t₂ = x := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  have hcard : 2 ≤ Nat.card (sigma.RightAROccurrence A x) := by
    rw [← sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
      (K := K) (R := R) A x]
    exact hbad
  have hlt : 1 < Nat.card (sigma.RightAROccurrence A x) :=
    lt_of_lt_of_le (by decide) hcard
  letI : Nontrivial (sigma.RightAROccurrence A x) :=
    Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨t₁, t₂, hne⟩ :=
    exists_pair_ne (sigma.RightAROccurrence A x)
  exact ⟨t₁.1, t₂.1, fun h ↦ hne (Subtype.ext h), t₁.2, t₂.2⟩

omit [Fintype Iota] in
/-- Mesh rotation preserves the dimension of the irreducible-morphism
space over an algebraically closed field. -/
theorem finrank_irreducibleHomSpace_eq_arTranslation_of_isAlgClosed
    (D : sigma.FiniteARTranslationData)
    (z : sigma.NonprojectiveLabel) (x : Iota) :
    letI (i : Iota) : Module K (sigma.obj i) :=
      Module.restrictScalars K R (sigma.obj i)
    letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
      IsScalarTower.restrictScalars K R (sigma.obj i)
    Module.finrank K
        (sigma.irreducibleHomSpace (K := K) x z.1) =
      Module.finrank K
        (sigma.irreducibleHomSpace (K := K)
          (D.arTranslation sigma z).1 x) := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        (K := K) (R := R) (D.chosenRightAR sigma z) x,
    sigma.finrank_irreducibleHomSpace_eq_card_leftAROccurrence_of_isAlgClosed
        (K := K) (R := R)
        (QuotientSubmoduleEquidistribution.RepresentationDirected.leftAROnChosenRightMiddle
          sigma D z) x]
  rfl

/-- Assem--Simson--Skowroński IV.4.9: on a finite complete skeleton over
an algebraically closed field, every irreducible-morphism space has
dimension at most one. -/
theorem finrank_irreducibleHomSpace_le_one_of_finiteARTranslationData_of_isAlgClosed
    (D : sigma.FiniteARTranslationData) (x y : Iota) :
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
    QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank (K := K) (sigma.obj i)
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
    apply QuotientSubmoduleEquidistribution.RepresentationDirected.no_large_source_pairs_of_strict_growth
      Bad dim
    intro a b hab hba
    obtain ⟨f, hf⟩ := irreducible_of_bad hab
    letI : Epi f :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.epi_of_isIrreducibleMorphism_of_finrank_gt
        (K := K) hf hba
    have hbnp : ¬ Projective (sigma.obj b) :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.not_projective_target_of_isIrreducibleMorphism_of_epi
        hf
    let z : sigma.NonprojectiveLabel := ⟨b, hbnp⟩
    let A := D.chosenRightAR sigma z
    obtain ⟨t₁, t₂, hne, ht₁, ht₂⟩ :=
      sigma.exists_two_rightAROccurrences_of_two_le_finrank_of_isAlgClosed
        A hab
    let a' : Iota := (D.arTranslation sigma z).1
    have hbad' : Bad a' a := by
      dsimp only [Bad, a']
      rw [← sigma.finrank_irreducibleHomSpace_eq_arTranslation_of_isAlgClosed
        D z a]
      exact hab
    have hgrowKernel :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.rightAR_kernel_groundFinrank_gt_of_two_occurrences
        (K := K) sigma A hbnp t₁ t₂ hne ht₁ ht₂ hba
    have hkiso := QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_of_iso
      (K := K) (D.arTranslationKernelIso sigma z)
    have hgrow : dim a < dim a' := by
      dsimp only [dim]
      change QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (sigma.obj a) <
        QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
          (K := K) (sigma.obj (D.arTranslationLabel sigma z))
      rw [← hkiso]
      exact hgrowKernel
    exact ⟨a', a, hbad', hgrow, hgrow⟩
  have no_target_large : ¬ ∃ a b, Bad a b ∧ dim a < dim b := by
    apply QuotientSubmoduleEquidistribution.RepresentationDirected.no_large_target_pairs_of_strict_growth
      Bad dim
    intro a b hab habdim
    obtain ⟨f, hf⟩ := irreducible_of_bad hab
    letI : Mono f :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.mono_of_isIrreducibleMorphism_of_finrank_lt
        (K := K) hf habdim
    have hani : ¬ Injective (sigma.obj a) :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.not_injective_source_of_isIrreducibleMorphism_of_mono
        hf
    let ai : sigma.NoninjectiveLabel := ⟨a, hani⟩
    let z : sigma.NonprojectiveLabel := (D.arTranslationEquiv sigma).symm ai
    have htauSubtype : D.arTranslationEquiv sigma z = ai :=
      (D.arTranslationEquiv sigma).apply_symm_apply ai
    have htau : (D.arTranslation sigma z).1 = a :=
      congrArg Subtype.val htauSubtype
    change D.arTranslationLabel sigma z = a at htau
    let A := D.chosenRightAR sigma z
    change 2 ≤ Module.finrank K
      (sigma.irreducibleHomSpace (K := K) a b) at hab
    have hbad' : Bad b z.1 := by
      dsimp only [Bad]
      rw [sigma.finrank_irreducibleHomSpace_eq_arTranslation_of_isAlgClosed
        D z b]
      change 2 ≤ Module.finrank K
        (sigma.irreducibleHomSpace (K := K)
          (D.arTranslationLabel sigma z) b)
      rw [htau]
      exact hab
    obtain ⟨t₁, t₂, hne, ht₁, ht₂⟩ :=
      sigma.exists_two_rightAROccurrences_of_two_le_finrank_of_isAlgClosed
        A hbad'
    have hkiso := QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank_eq_of_iso
      (K := K) (D.arTranslationKernelIso sigma z)
    have hklt : QuotientSubmoduleEquidistribution.RepresentationDirected.groundFinrank
        (K := K) (kernel A.map : FGModuleCat.{u} R) < dim b := by
      rw [hkiso, htau]
      dsimp only [dim] at habdim
      exact habdim
    have hgrow :=
      QuotientSubmoduleEquidistribution.RepresentationDirected.rightAR_target_groundFinrank_gt_of_two_occurrences
        (K := K) sigma A z.2 t₁ t₂ hne ht₁ ht₂ hklt
    have hgrow' : dim b < dim z.1 := hgrow
    exact ⟨b, z.1, hbad', hgrow', hgrow'⟩
  by_contra hle
  have hbad : Bad x y := by
    dsimp only [Bad]
    omega
  obtain ⟨f, hf⟩ := irreducible_of_bad hbad
  rcases QuotientSubmoduleEquidistribution.RepresentationDirected.finrank_orientation_of_isIrreducibleMorphism
      (K := K) hf with hxy | hyx
  · exact no_target_large ⟨x, y, hbad, hxy.1⟩
  · exact no_source_large ⟨x, y, hbad, hyx.1⟩

/-- Finite-dimensional algebras supply the AR-translation data needed for
the representation-finite multiplicity-one theorem. -/
theorem finrank_irreducibleHomSpace_le_one_of_isAlgClosed
    (x y : Iota) :
    letI (i : Iota) : Module K (sigma.obj i) :=
      Module.restrictScalars K R (sigma.obj i)
    letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
      IsScalarTower.restrictScalars K R (sigma.obj i)
    Module.finrank K (sigma.irreducibleHomSpace (K := K) x y) ≤ 1 :=
  sigma.finrank_irreducibleHomSpace_le_one_of_finiteARTranslationData_of_isAlgClosed
    (sigma.finiteDimensionalARTranslationData K R) x y

include K in
/-- Every minimal right almost-split middle decomposition is
multiplicity-free for a representation-finite algebra over an algebraically
closed field, including the projective boundary decomposition. -/
theorem rightARLabel_injective_of_finiteARTranslationData_of_isAlgClosed
    (D : sigma.FiniteARTranslationData) {z : Iota}
    (A : sigma.MinimalRightAlmostSplitDecomposition z) :
    Function.Injective A.label := by
  letI (i : Iota) : Module K (sigma.obj i) :=
    Module.restrictScalars K R (sigma.obj i)
  letI (i : Iota) : IsScalarTower K R (sigma.obj i) :=
    IsScalarTower.restrictScalars K R (sigma.obj i)
  intro t u htu
  let tx : sigma.RightAROccurrence A (A.label t) := ⟨t, rfl⟩
  let ux : sigma.RightAROccurrence A (A.label t) := ⟨u, htu.symm⟩
  have hcard : Nat.card
      (sigma.RightAROccurrence A (A.label t)) ≤ 1 := by
    rw [← sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
      (K := K) (R := R) A (A.label t)]
    exact sigma.finrank_irreducibleHomSpace_le_one_of_finiteARTranslationData_of_isAlgClosed
      D (A.label t) z
  have hsub : Subsingleton
      (sigma.RightAROccurrence A (A.label t)) :=
    Finite.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (@Subsingleton.elim _ hsub tx ux)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
