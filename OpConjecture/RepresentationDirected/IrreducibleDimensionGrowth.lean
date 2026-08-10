import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.Fintype.Lattice
import OpConjecture.RepresentationDirected.LeftAROccurrenceBasis
import OpConjecture.RepresentationDirected.RightAROccurrenceBasis
import OpConjecture.RepresentationTheory.FiniteARTranslationData

/-!
# Classification-free dimension growth for ASS IV.4.9

This file isolates the categorical mono/epi dichotomy, finite-dimension
exclusion, short-exact dimension formula, mesh-multiplicity rotation, and
finite-state ascent argument used to prove the representation-directed
irreducible-space bound.  No algebra presentation or module classification
enters.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected

universe u v

/-- In an abelian category, every irreducible morphism is monic or epic.
This is the canonical epi--mono image factorization argument. -/
theorem mono_or_epi_of_isIrreducibleMorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    Mono f ∨ Epi f := by
  rcases hf.factorization
      (Abelian.factorThruImage f) (Abelian.image.ι f)
      (Abelian.image.fac f) with hq | hi
  · letI : IsSplitMono (Abelian.factorThruImage f) := hq
    letI : IsIso (Abelian.factorThruImage f) :=
      isIso_of_epi_of_isSplitMono _
    exact Or.inl (by
      rw [← Abelian.image.fac f]
      infer_instance)
  · letI : IsSplitEpi (Abelian.image.ι f) := hi
    letI : IsIso (Abelian.image.ι f) :=
      isIso_of_mono_of_isSplitEpi _
    exact Or.inr (by
      rw [← Abelian.image.fac f]
      infer_instance)

/-- An irreducible epimorphism cannot end at a projective object. -/
theorem not_projective_target_of_isIrreducibleMorphism_of_epi
    {C : Type u} [Category.{v} C]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    [Epi f] : ¬ Projective Y := by
  intro hY
  letI : Projective Y := hY
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Y) f
  exact hf.not_isSplitEpi (IsSplitEpi.mk' {
    section_ := s
    id := hs })

/-- Dually, an irreducible monomorphism cannot start at an injective
object. -/
theorem not_injective_source_of_isIrreducibleMorphism_of_mono
    {C : Type u} [Category.{v} C]
    {X Y : C} {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    [Mono f] : ¬ Injective X := by
  intro hX
  letI : Injective X := hX
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 X) f
  exact hf.not_isSplitMono (IsSplitMono.mk' {
    retraction := r
    id := hr })

section FiniteDimension

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [IsNoetherianRing R]
  {X Y : FGModuleCat.{u} R}
  [Module K X] [IsScalarTower K R X] [FiniteDimensional K X]
  [Module K Y] [IsScalarTower K R Y] [FiniteDimensional K Y]

/-- Between finite-dimensional modules of equal ground-field dimension,
an irreducible morphism is impossible. -/
theorem finrank_ne_of_isIrreducibleMorphism
    {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    Module.finrank K X ≠ Module.finrank K Y := by
  intro hdim
  rcases mono_or_epi_of_isIrreducibleMorphism hf with hmono | hepi
  · letI : Mono f := hmono
    have hinj : Function.Injective
        (f.hom.hom.restrictScalars K) :=
      (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
    have hsurj : Function.Surjective
        (f.hom.hom.restrictScalars K) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
    letI : Epi f :=
      (IndecomposableSkeleton.fg_epi_iff_surjective f).2 hsurj
    letI : IsIso f := isIso_of_mono_of_epi f
    exact hf.not_isSplitMono inferInstance
  · letI : Epi f := hepi
    have hsurj : Function.Surjective
        (f.hom.hom.restrictScalars K) :=
      (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
    have hinj : Function.Injective
        (f.hom.hom.restrictScalars K) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
    letI : Mono f :=
      (IndecomposableSkeleton.fg_mono_iff_injective f).2 hinj
    letI : IsIso f := isIso_of_mono_of_epi f
    exact hf.not_isSplitEpi inferInstance

omit [FiniteDimensional K X] in
/-- If the source of an irreducible morphism has larger dimension, the
morphism is epic. -/
theorem epi_of_isIrreducibleMorphism_of_finrank_gt
    {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    (hdim : Module.finrank K Y < Module.finrank K X) :
    Epi f := by
  rcases mono_or_epi_of_isIrreducibleMorphism hf with hmono | hepi
  · letI : Mono f := hmono
    have hinj : Function.Injective
        (f.hom.hom.restrictScalars K) :=
      (IndecomposableSkeleton.fg_mono_iff_injective f).1 inferInstance
    have hle : Module.finrank K X ≤ Module.finrank K Y :=
      LinearMap.finrank_le_finrank_of_injective hinj
    exact False.elim ((not_le_of_gt hdim) hle)
  · exact hepi

omit [FiniteDimensional K Y] in
/-- If the target of an irreducible morphism has larger dimension, the
morphism is monic. -/
theorem mono_of_isIrreducibleMorphism_of_finrank_lt
    {f : X ⟶ Y} (hf : IsIrreducibleMorphism f)
    (hdim : Module.finrank K X < Module.finrank K Y) :
    Mono f := by
  rcases mono_or_epi_of_isIrreducibleMorphism hf with hmono | hepi
  · exact hmono
  · letI : Epi f := hepi
    have hsurj : Function.Surjective
        (f.hom.hom.restrictScalars K) :=
      (IndecomposableSkeleton.fg_epi_iff_surjective f).1 inferInstance
    have hle : Module.finrank K Y ≤ Module.finrank K X :=
      LinearMap.finrank_le_finrank_of_surjective hsurj
    exact False.elim ((not_le_of_gt hdim) hle)

/-- Exact dimension/orientation dichotomy for an irreducible morphism. -/
theorem finrank_orientation_of_isIrreducibleMorphism
    {f : X ⟶ Y} (hf : IsIrreducibleMorphism f) :
    (Module.finrank K X < Module.finrank K Y ∧ Mono f) ∨
      (Module.finrank K Y < Module.finrank K X ∧ Epi f) := by
  rcases lt_or_gt_of_ne (finrank_ne_of_isIrreducibleMorphism
    (K := K) hf) with hlt | hgt
  · exact Or.inl ⟨hlt,
      mono_of_isIrreducibleMorphism_of_finrank_lt (K := K) hf hlt⟩
  · exact Or.inr ⟨hgt,
      epi_of_isIrreducibleMorphism_of_finrank_gt (K := K) hf hgt⟩

end FiniteDimension

section ShortExactDimension

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [IsNoetherianRing R]
  (S : ShortComplex (FGModuleCat.{u} R))
  [Module K S.X₁] [IsScalarTower K R S.X₁]
  [Module K S.X₂] [IsScalarTower K R S.X₂]
  [FiniteDimensional K S.X₂]
  [Module K S.X₃] [IsScalarTower K R S.X₃]

/-- Ground-field dimension is additive in a short exact sequence of finite
modules. -/
theorem finrank_add_finrank_eq_of_shortExact (hS : S.ShortExact) :
    Module.finrank K S.X₁ + Module.finrank K S.X₃ =
      Module.finrank K S.X₂ := by
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  have hSU : (S.map U).ShortExact := hS.map_of_exact U
  let i : S.X₁ →ₗ[K] S.X₂ := S.f.hom.hom.restrictScalars K
  let p : S.X₂ →ₗ[K] S.X₃ := S.g.hom.hom.restrictScalars K
  have hExactR : Function.Exact (S.map U).f (S.map U).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map U)).1 hSU.exact
  change Function.Exact S.f.hom.hom S.g.hom.hom at hExactR
  have hExact : Function.Exact i p := by
    intro z
    exact hExactR z
  have hi : Function.Injective i := by
    exact (IndecomposableSkeleton.fg_mono_iff_injective S.f).1 hS.mono_f
  have hp : Function.Surjective p := by
    exact (IndecomposableSkeleton.fg_epi_iff_surjective S.g).1 hS.epi_g
  have hrangeKer : LinearMap.range i = LinearMap.ker p :=
    (LinearMap.exact_iff.mp hExact).symm
  have hiFinrank : Module.finrank K S.X₁ =
      Module.finrank K (LinearMap.range i) :=
    (LinearEquiv.ofInjective i hi).finrank_eq
  have hpFinrank : Module.finrank K (LinearMap.range p) =
      Module.finrank K S.X₃ := by
    rw [LinearMap.range_eq_top.mpr hp, finrank_top]
  have hkerFinrank : Module.finrank K S.X₁ =
      Module.finrank K (LinearMap.ker p) := by
    rw [← hrangeKer]
    exact hiFinrank
  have hsum := LinearMap.finrank_range_add_finrank_ker p
  omega

/-- If the middle of a short exact sequence has room for two copies of a
module larger than the right endpoint, then the left endpoint is larger
than that module.  This is the dimension-growth inequality for a right AR
sequence. -/
theorem left_finrank_gt_of_shortExact_of_two_mul_le
    (hS : S.ShortExact) (d : ℕ)
    (htwo : 2 * d ≤ Module.finrank K S.X₂)
    (hright : Module.finrank K S.X₃ < d) :
    d < Module.finrank K S.X₁ := by
  have hdim := finrank_add_finrank_eq_of_shortExact
    (K := K) (R := R) S hS
  omega

/-- Dual dimension-growth inequality for a left AR sequence. -/
theorem right_finrank_gt_of_shortExact_of_two_mul_le
    (hS : S.ShortExact) (d : ℕ)
    (htwo : 2 * d ≤ Module.finrank K S.X₂)
    (hleft : Module.finrank K S.X₁ < d) :
    d < Module.finrank K S.X₃ := by
  have hdim := finrank_add_finrank_eq_of_shortExact
    (K := K) (R := R) S hS
  omega

end ShortExactDimension

section MiddleDimension

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

/-- Ground-field dimension of a finite `R`-module, using restriction of
scalars along `K → R`. -/
def groundFinrank (X : FGModuleCat.{u} R) : ℕ :=
  letI : Module K X := Module.restrictScalars K R X
  Module.finrank K X

omit [FiniteDimensional K R] [IsNoetherianRing R] in
/-- Ground-field dimension is invariant under an isomorphism of finite
`R`-modules. -/
theorem groundFinrank_eq_of_iso {X Y : FGModuleCat.{u} R} (e : X ≅ Y) :
    groundFinrank (K := K) X = groundFinrank (K := K) Y := by
  letI : Module K X := Module.restrictScalars K R X
  letI : IsScalarTower K R X := IsScalarTower.restrictScalars K R X
  letI : Module K Y := Module.restrictScalars K R Y
  letI : IsScalarTower K R Y := IsScalarTower.restrictScalars K R Y
  exact (FGModuleCat.isoToLinearEquiv e).restrictScalars K |>.finrank_eq

/-- The ground-field dimension of a chosen finite indecomposable direct-sum
decomposition is the sum of the dimensions of its summands. -/
theorem groundFinrank_eq_sum_of_iso_sumOver
    (E : FGModuleCat.{u} R) (J : FintypeCat.{0}) (a : J → Iota)
    (e : E ≅ sigma.sumOver J a) :
    groundFinrank (K := K) E =
      ∑ t : J, groundFinrank (K := K) (sigma.obj (a t)) := by
  classical
  letI : Module K E := Module.restrictScalars K R E
  letI : IsScalarTower K R E := IsScalarTower.restrictScalars K R E
  letI : Module.Finite K E := Module.Finite.trans R E
  letI : ∀ t : J, Module K (sigma.obj (a t)) := fun t ↦
    Module.restrictScalars K R (sigma.obj (a t))
  letI : ∀ t : J, IsScalarTower K R (sigma.obj (a t)) := fun t ↦
    IsScalarTower.restrictScalars K R (sigma.obj (a t))
  letI : ∀ t : J, Module.Finite K (sigma.obj (a t)) := fun t ↦
    Module.Finite.trans R (sigma.obj (a t))
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  letI : PreservesBiproduct (fun t : J ↦ sigma.obj (a t)) U :=
    preservesBiproduct_of_preservesProduct U
  let eSumPi : U.obj (sigma.sumOver J a) ≅
      ModuleCat.of R (∀ t : J, sigma.obj (a t)) :=
    U.mapBiproduct (fun t : J ↦ sigma.obj (a t)) ≪≫
      ModuleCat.biproductIsoPi (fun t : J ↦ U.obj (sigma.obj (a t)))
  let ePiR : E ≃ₗ[R] (∀ t : J, sigma.obj (a t)) :=
    (FGModuleCat.isoToLinearEquiv e).trans eSumPi.toLinearEquiv
  let ePiK : E ≃ₗ[K] (∀ t : J, sigma.obj (a t)) :=
    ePiR.restrictScalars K
  change Module.finrank K E =
    ∑ t : J, Module.finrank K (sigma.obj (a t))
  rw [ePiK.finrank_eq, Module.finrank_pi_fintype K]

/-- Two distinct occurrences of one indecomposable in a chosen direct-sum
decomposition force twice its dimension below the middle dimension. -/
theorem two_mul_groundFinrank_le_of_two_occurrences
    (E : FGModuleCat.{u} R) (J : FintypeCat.{0}) (a : J → Iota)
    (e : E ≅ sigma.sumOver J a) (x : Iota)
    (t₁ t₂ : J) (hne : t₁ ≠ t₂)
    (ht₁ : a t₁ = x) (ht₂ : a t₂ = x) :
    2 * groundFinrank (K := K) (sigma.obj x) ≤
      groundFinrank (K := K) E := by
  classical
  rw [groundFinrank_eq_sum_of_iso_sumOver
    (K := K) sigma E J a e]
  calc
    2 * groundFinrank (K := K) (sigma.obj x) =
        ∑ t ∈ ({t₁, t₂} : Finset J),
          groundFinrank (K := K) (sigma.obj (a t)) := by
      simp [hne, ht₁, ht₂, two_mul]
    _ ≤ ∑ t : J, groundFinrank (K := K) (sigma.obj (a t)) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Right-AR dimension growth from two occurrences of one indecomposable in
the minimal right almost-split middle. -/
theorem rightAR_kernel_groundFinrank_gt_of_two_occurrences
    {z x : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    (hz : ¬ Projective (sigma.obj z))
    (t₁ t₂ : A.index) (hne : t₁ ≠ t₂)
    (ht₁ : A.label t₁ = x) (ht₂ : A.label t₂ = x)
    (hzx : groundFinrank (K := K) (sigma.obj z) <
      groundFinrank (K := K) (sigma.obj x)) :
    groundFinrank (K := K) (sigma.obj x) <
      groundFinrank (K := K) (kernel A.map : FGModuleCat.{u} R) := by
  letI : Module K (sigma.obj x) :=
    Module.restrictScalars K R (sigma.obj x)
  letI : IsScalarTower K R (sigma.obj x) :=
    IsScalarTower.restrictScalars K R (sigma.obj x)
  letI : Module K (sigma.obj z) :=
    Module.restrictScalars K R (sigma.obj z)
  letI : IsScalarTower K R (sigma.obj z) :=
    IsScalarTower.restrictScalars K R (sigma.obj z)
  letI : Module K A.middle := Module.restrictScalars K R A.middle
  letI : IsScalarTower K R A.middle :=
    IsScalarTower.restrictScalars K R A.middle
  letI : FiniteDimensional K A.middle := Module.Finite.trans R A.middle
  letI : Module K (kernel A.map : FGModuleCat.{u} R) :=
    Module.restrictScalars K R (kernel A.map : FGModuleCat.{u} R)
  letI : IsScalarTower K R (kernel A.map : FGModuleCat.{u} R) :=
    IsScalarTower.restrictScalars K R
      (kernel A.map : FGModuleCat.{u} R)
  have hnotTop : ¬ sigma.IsRelativeSplitProjective Set.univ z := by
    intro htop
    exact hz ((sigma.projective_iff_isRelativeSplitProjective_univ).2 htop)
  letI : Epi A.map := A.epi_of_not_topSplitProjective hnotTop
  let S := ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel A.map)
    mono_f := inferInstance
    epi_g := inferInstance }
  have htwo := two_mul_groundFinrank_le_of_two_occurrences
    (K := K) sigma A.middle A.index A.label A.decomposition x
      t₁ t₂ hne ht₁ ht₂
  change 2 * Module.finrank K (sigma.obj x) ≤
    Module.finrank K A.middle at htwo
  change Module.finrank K (sigma.obj z) <
    Module.finrank K (sigma.obj x) at hzx
  change Module.finrank K (sigma.obj x) <
    Module.finrank K (kernel A.map : FGModuleCat.{u} R)
  exact left_finrank_gt_of_shortExact_of_two_mul_le
    (K := K) (R := R) S hS (Module.finrank K (sigma.obj x)) htwo hzx

/-- The complementary right-AR growth inequality: if the kernel is smaller
than an indecomposable occurring twice in the middle, then the right endpoint
is larger than that indecomposable. -/
theorem rightAR_target_groundFinrank_gt_of_two_occurrences
    {z x : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    (hz : ¬ Projective (sigma.obj z))
    (t₁ t₂ : A.index) (hne : t₁ ≠ t₂)
    (ht₁ : A.label t₁ = x) (ht₂ : A.label t₂ = x)
    (hkx : groundFinrank (K := K) (kernel A.map : FGModuleCat.{u} R) <
      groundFinrank (K := K) (sigma.obj x)) :
    groundFinrank (K := K) (sigma.obj x) <
      groundFinrank (K := K) (sigma.obj z) := by
  letI : Module K (sigma.obj x) :=
    Module.restrictScalars K R (sigma.obj x)
  letI : IsScalarTower K R (sigma.obj x) :=
    IsScalarTower.restrictScalars K R (sigma.obj x)
  letI : Module K (sigma.obj z) :=
    Module.restrictScalars K R (sigma.obj z)
  letI : IsScalarTower K R (sigma.obj z) :=
    IsScalarTower.restrictScalars K R (sigma.obj z)
  letI : Module K A.middle := Module.restrictScalars K R A.middle
  letI : IsScalarTower K R A.middle :=
    IsScalarTower.restrictScalars K R A.middle
  letI : FiniteDimensional K A.middle := Module.Finite.trans R A.middle
  letI : Module K (kernel A.map : FGModuleCat.{u} R) :=
    Module.restrictScalars K R (kernel A.map : FGModuleCat.{u} R)
  letI : IsScalarTower K R (kernel A.map : FGModuleCat.{u} R) :=
    IsScalarTower.restrictScalars K R
      (kernel A.map : FGModuleCat.{u} R)
  have hnotTop : ¬ sigma.IsRelativeSplitProjective Set.univ z := by
    intro htop
    exact hz ((sigma.projective_iff_isRelativeSplitProjective_univ).2 htop)
  letI : Epi A.map := A.epi_of_not_topSplitProjective hnotTop
  let S := ShortComplex.mk (kernel.ι A.map) A.map (kernel.condition A.map)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel A.map)
    mono_f := inferInstance
    epi_g := inferInstance }
  have htwo := two_mul_groundFinrank_le_of_two_occurrences
    (K := K) sigma A.middle A.index A.label A.decomposition x
      t₁ t₂ hne ht₁ ht₂
  change 2 * Module.finrank K (sigma.obj x) ≤
    Module.finrank K A.middle at htwo
  change Module.finrank K (kernel A.map : FGModuleCat.{u} R) <
    Module.finrank K (sigma.obj x) at hkx
  change Module.finrank K (sigma.obj x) <
    Module.finrank K (sigma.obj z)
  exact right_finrank_gt_of_shortExact_of_two_mul_le
    (K := K) (R := R) S hS (Module.finrank K (sigma.obj x)) htwo hkx

/-- Left-AR dimension growth from two occurrences of one indecomposable in
the minimal left almost-split middle. -/
theorem leftAR_cokernel_groundFinrank_gt_of_two_occurrences
    {z x : Iota} (A : sigma.MinimalLeftAlmostSplitDecomposition z)
    (hz : ¬ Injective (sigma.obj z))
    (t₁ t₂ : A.index) (hne : t₁ ≠ t₂)
    (ht₁ : A.label t₁ = x) (ht₂ : A.label t₂ = x)
    (hzx : groundFinrank (K := K) (sigma.obj z) <
      groundFinrank (K := K) (sigma.obj x)) :
    groundFinrank (K := K) (sigma.obj x) <
      groundFinrank (K := K) (cokernel A.map : FGModuleCat.{u} R) := by
  letI : Module K (sigma.obj x) :=
    Module.restrictScalars K R (sigma.obj x)
  letI : IsScalarTower K R (sigma.obj x) :=
    IsScalarTower.restrictScalars K R (sigma.obj x)
  letI : Module K (sigma.obj z) :=
    Module.restrictScalars K R (sigma.obj z)
  letI : IsScalarTower K R (sigma.obj z) :=
    IsScalarTower.restrictScalars K R (sigma.obj z)
  letI : Module K A.middle := Module.restrictScalars K R A.middle
  letI : IsScalarTower K R A.middle :=
    IsScalarTower.restrictScalars K R A.middle
  letI : FiniteDimensional K A.middle := Module.Finite.trans R A.middle
  letI : Module K (cokernel A.map : FGModuleCat.{u} R) :=
    Module.restrictScalars K R (cokernel A.map : FGModuleCat.{u} R)
  letI : IsScalarTower K R (cokernel A.map : FGModuleCat.{u} R) :=
    IsScalarTower.restrictScalars K R
      (cokernel A.map : FGModuleCat.{u} R)
  have hnotTop : ¬ sigma.IsRelativeSplitInjective Set.univ z := by
    intro htop
    exact hz ((sigma.injective_iff_isRelativeSplitInjective_univ).2 htop)
  letI : Mono A.map := A.mono_of_not_topSplitInjective hnotTop
  let S := ShortComplex.mk A.map (cokernel.π A.map) (cokernel.condition A.map)
  have hS : S.ShortExact := {
    exact := S.exact_of_g_is_cokernel (cokernelIsCokernel A.map)
    mono_f := inferInstance
    epi_g := inferInstance }
  have htwo := two_mul_groundFinrank_le_of_two_occurrences
    (K := K) sigma A.middle A.index A.label A.decomposition x
      t₁ t₂ hne ht₁ ht₂
  change 2 * Module.finrank K (sigma.obj x) ≤
    Module.finrank K A.middle at htwo
  change Module.finrank K (sigma.obj z) <
    Module.finrank K (sigma.obj x) at hzx
  change Module.finrank K (sigma.obj x) <
    Module.finrank K (cokernel A.map : FGModuleCat.{u} R)
  exact right_finrank_gt_of_shortExact_of_two_mul_le
    (K := K) (R := R) S hS (Module.finrank K (sigma.obj x)) htwo hzx

end MiddleDimension

section MeshMultiplicityRotation

variable {K R : Type u} [Field K] [Ring R] [Algebra K R]
  [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)
  [∀ i : Iota, Module K (sigma.obj i)]
  [∀ i : Iota, IsScalarTower K R (sigma.obj i)]
  (D : sigma.FiniteARTranslationData)

open IndecomposableSkeleton.FiniteARTranslationData

/-- The kernel inclusion of a chosen right AR map, packaged as a left AR
decomposition while retaining literally the same middle coordinates. -/
def leftAROnChosenRightMiddle (z : sigma.NonprojectiveLabel) :
    sigma.MinimalLeftAlmostSplitDecomposition
      (arTranslation sigma D z).1 :=
  { middle := (chosenRightAR sigma D z).middle
    finiteLength := (chosenRightAR sigma D z).finiteLength
    map := arKernelMap sigma D z
    leftAlmostSplit := arKernelMap_leftAlmostSplit sigma D z
    leftMinimal := arKernelMap_leftMinimal sigma D z
    index := (chosenRightAR sigma D z).index
    label := (chosenRightAR sigma D z).label
    decomposition := (chosenRightAR sigma D z).decomposition }

omit [FiniteDimensional K R] in
/-- Mesh rotation preserves the dimension of the irreducible-morphism
space.  Reusing the same middle coordinates makes the two occurrence types
definitionally equal, so no Krull--Schmidt comparison is needed. -/
theorem finrank_irreducibleHomSpace_eq_arTranslation
    (z : sigma.NonprojectiveLabel) (x : Iota)
    (hscalar : ∀ f : sigma.obj x ⟶ sigma.obj x,
      ∃ a : K, a • 𝟙 (sigma.obj x) = f) :
    Module.finrank K
        (sigma.irreducibleHomSpace (K := K) x z.1) =
      Module.finrank K
        (sigma.irreducibleHomSpace (K := K)
          (arTranslation sigma D z).1 x) := by
  rw [sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence
        (chosenRightAR sigma D z) x hscalar,
    sigma.finrank_irreducibleHomSpace_eq_card_leftAROccurrence
        (leftAROnChosenRightMiddle sigma D z) x hscalar]
  rfl

end MeshMultiplicityRotation

section FiniteIteration

variable {Alpha : Type u} [Finite Alpha]

/-- A nonempty subset of a finite type cannot admit a strict weight ascent
from every one of its elements. -/
theorem not_exists_of_finite_strict_ascent
    (P : Alpha → Prop) (weight : Alpha → ℕ)
    (step : ∀ x, P x → ∃ y, P y ∧ weight x < weight y) :
    ¬ ∃ x, P x := by
  rintro ⟨x, hx⟩
  let S := {x : Alpha // P x}
  letI : Nonempty S := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_max (fun z : S ↦ weight z.1)
  obtain ⟨y, hy, hmy⟩ := step m.1 m.2
  exact (not_lt_of_ge (hm ⟨y, hy⟩)) hmy

/-- Finite-skeleton eliminator for the ASS iteration in the orientation
where the source has larger dimension. -/
theorem no_large_source_pairs_of_strict_growth
    {Iota : Type u} [Finite Iota]
    (Bad : Iota → Iota → Prop) (dim : Iota → ℕ)
    (step : ∀ x y, Bad x y → dim y < dim x →
      ∃ x' y', Bad x' y' ∧ dim y' < dim x' ∧ dim x < dim x') :
    ¬ ∃ x y, Bad x y ∧ dim y < dim x := by
  intro h
  have hno : ¬ ∃ p : Iota × Iota,
      Bad p.1 p.2 ∧ dim p.2 < dim p.1 :=
    not_exists_of_finite_strict_ascent
      (P := fun p : Iota × Iota ↦ Bad p.1 p.2 ∧ dim p.2 < dim p.1)
      (weight := fun p ↦ dim p.1) (by
        rintro ⟨x, y⟩ ⟨hbad, hdim⟩
        obtain ⟨x', y', hbad', hdim', hgrow⟩ := step x y hbad hdim
        exact ⟨(x', y'), ⟨hbad', hdim'⟩, hgrow⟩)
  apply hno
  obtain ⟨x, y, hbad, hdim⟩ := h
  exact ⟨(x, y), hbad, hdim⟩

/-- Dual finite-skeleton eliminator, where the target has larger
dimension. -/
theorem no_large_target_pairs_of_strict_growth
    {Iota : Type u} [Finite Iota]
    (Bad : Iota → Iota → Prop) (dim : Iota → ℕ)
    (step : ∀ x y, Bad x y → dim x < dim y →
      ∃ x' y', Bad x' y' ∧ dim x' < dim y' ∧ dim y < dim y') :
    ¬ ∃ x y, Bad x y ∧ dim x < dim y := by
  intro h
  have hno : ¬ ∃ p : Iota × Iota,
      Bad p.1 p.2 ∧ dim p.1 < dim p.2 :=
    not_exists_of_finite_strict_ascent
      (P := fun p : Iota × Iota ↦ Bad p.1 p.2 ∧ dim p.1 < dim p.2)
      (weight := fun p ↦ dim p.2) (by
        rintro ⟨x, y⟩ ⟨hbad, hdim⟩
        obtain ⟨x', y', hbad', hdim', hgrow⟩ := step x y hbad hdim
        exact ⟨(x', y'), ⟨hbad', hdim'⟩, hgrow⟩)
  apply hno
  obtain ⟨x, y, hbad, hdim⟩ := h
  exact ⟨(x, y), hbad, hdim⟩

end FiniteIteration

end OpConjecture.RepresentationDirected
