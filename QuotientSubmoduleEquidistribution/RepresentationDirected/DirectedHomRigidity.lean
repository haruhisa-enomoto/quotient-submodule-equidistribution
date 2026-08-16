import QuotientSubmoduleEquidistribution.RepresentationDirected.ARCoordinateRecurrence
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

namespace QuotientSubmoduleEquidistribution.RepresentationDirected

universe u v

variable (K R : Type u) [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

local instance : DecidableEq Iota := Classical.decEq Iota

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Precomposition by a morphism as a linear map on Hom spaces. -/
def precompLinearMap {Z E X : FGModuleCat.{u} R} (f : Z ⟶ E) :
    (E ⟶ X) →ₗ[K] (Z ⟶ X) where
  toFun g := f ≫ g
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem precompLinearMap_apply {Z E X : FGModuleCat.{u} R}
    (f : Z ⟶ E) (g : E ⟶ X) :
    precompLinearMap K R f g = f ≫ g := rfl

/-- Morphisms out of a categorical cokernel form the kernel of
precomposition. -/
def homCokernelLinearEquiv {Z E X : FGModuleCat.{u} R} (f : Z ⟶ E) :
    (cokernel f ⟶ X) ≃ₗ[K]
      LinearMap.ker (precompLinearMap K R (X := X) f) := by
  let L : (cokernel f ⟶ X) →ₗ[K]
      LinearMap.ker (precompLinearMap K R (X := X) f) :=
    { toFun := fun g ↦ ⟨cokernel.π f ≫ g, by
          simp [precompLinearMap, ← Category.assoc]⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        simp }
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro a b hab
    apply (cancel_epi (cokernel.π f)).1
    exact congrArg Subtype.val hab
  · intro h
    have hh' := h.property
    have hh : f ≫ h.1 = 0 := by
      change precompLinearMap K R f h.1 = 0 at hh'
      simpa only [precompLinearMap_apply] using hh'
    refine ⟨cokernel.desc f h.1 hh, ?_⟩
    apply Subtype.ext
    exact cokernel.π_desc f h.1 hh

theorem finiteDimensional_hom_fg (M N : FGModuleCat.{u} R) :
    FiniteDimensional K (M ⟶ N) := by
  letI : Module K M := Module.restrictScalars K R M
  letI : Module K N := Module.restrictScalars K R N
  letI : IsScalarTower K R M := IsScalarTower.restrictScalars K R M
  letI : IsScalarTower K R N := IsScalarTower.restrictScalars K R N
  letI : FiniteDimensional K M := Module.Finite.trans R M
  letI : FiniteDimensional K N := Module.Finite.trans R N
  let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
  letI : FiniteDimensional K (U.obj M ⟶ U.obj N) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := R) (M := M) (N := N)
  let forgetHom : (M ⟶ N) →ₗ[K] (U.obj M ⟶ U.obj N) :=
    { toFun := fun f ↦ f.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact FiniteDimensional.of_injective forgetHom (Functor.map_injective U)

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- Precomposition with a left almost-split map is surjective onto every
different indecomposable representative. -/
theorem leftAlmostSplit_precomp_surjective_of_ne
    {z a : Iota} {E : FGModuleCat.{u} R} {f : sigma.obj z ⟶ E}
    (hf : IsLeftAlmostSplit f) (haz : a ≠ z) :
    Function.Surjective
      (precompLinearMap K R (X := sigma.obj a) f) := by
  intro g
  have hg : ¬ IsSplitMono g := by
    intro hsplit
    letI : IsSplitMono g := hsplit
    letI : IsSplitEpi g :=
      sigma.isSplitEpi_of_isSplitMono_between_obj g
    letI : IsIso g := isIso_of_mono_of_isSplitEpi g
    exact haz.symm (sigma.eq_of_iso ⟨asIso g⟩)
  exact hf.factors g hg

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- At its source, precomposition with a left almost-split map is zero. -/
theorem leftAlmostSplit_precomp_eq_zero
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z : Iota} {E : FGModuleCat.{u} R} {f : sigma.obj z ⟶ E}
    (hf : IsLeftAlmostSplit f) :
    precompLinearMap K R (X := sigma.obj z) f = 0 := by
  apply LinearMap.ext
  intro h
  change f ≫ h = 0
  by_contra hne
  letI : IsIso (f ≫ h) :=
    H.isIso_of_ne_zero_endomorphism sigma z (f ≫ h) hne
  apply hf.not_isSplitMono
  exact IsSplitMono.mk'
    { retraction := h ≫ inv (f ≫ h)
      id := by
        rw [← Category.assoc]
        exact IsIso.hom_inv_id_assoc (f ≫ h) (𝟙 _) }

/-- Pointwise contravariant Hom-finrank form of a left almost-split mesh. -/
theorem homCokernel_add_source_eq_middle_add_delta
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z a : Iota} {E : FGModuleCat.{u} R} {f : sigma.obj z ⟶ E}
    (hf : IsLeftAlmostSplit f) :
    Module.finrank K (cokernel f ⟶ sigma.obj a) +
        Module.finrank K (sigma.obj z ⟶ sigma.obj a) =
      Module.finrank K (E ⟶ sigma.obj a) +
        if a = z then 1 else 0 := by
  classical
  letI : FiniteDimensional K (cokernel f ⟶ sigma.obj a) :=
    finiteDimensional_hom_fg K R (cokernel f) (sigma.obj a)
  letI : FiniteDimensional K (sigma.obj z ⟶ sigma.obj a) :=
    finiteDimensional_hom_fg K R (sigma.obj z) (sigma.obj a)
  letI : FiniteDimensional K (E ⟶ sigma.obj a) :=
    finiteDimensional_hom_fg K R E (sigma.obj a)
  let L := precompLinearMap K R (X := sigma.obj a) f
  have hker' := (homCokernelLinearEquiv K R (X := sigma.obj a) f).finrank_eq
  have hker : Module.finrank K (cokernel f ⟶ sigma.obj a) =
      Module.finrank K (LinearMap.ker L) := by
    simpa only [L] using hker'
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  by_cases haz : a = z
  · subst a
    have hL : L = 0 := leftAlmostSplit_precomp_eq_zero K R sigma H hf
    have hrange : Module.finrank K (LinearMap.range L) = 0 := by
      rw [hL]
      simp
    have hend := H.finrank_endomorphism_eq_one K R sigma z
    simp only [if_true]
    omega
  · have hsurj : Function.Surjective L :=
      leftAlmostSplit_precomp_surjective_of_ne K R sigma hf haz
    have hrange : Module.finrank K (LinearMap.range L) =
        Module.finrank K (sigma.obj z ⟶ sigma.obj a) := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    simp only [if_neg haz]
    omega

/-- Ordinary split coordinates, recovered from the directed Hom matrix. -/
def splitCoordinate
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (M : FGModuleCat.{u} R) : Iota → ℤ := by
  letI := directedLinearOrder sigma H
  exact UpperUnitriangular.coordinates
    (homFinrankMatrix K R sigma) ∅ (homFinrankVector K R sigma M)

/-- Contravariant Hom dimensions into a chosen indecomposable. -/
def reverseHomFinrankVector (M : FGModuleCat.{u} R) : Iota → ℤ :=
  fun z ↦ (Module.finrank K (M ⟶ sigma.obj z) : ℤ)

/-- Evaluate an integral split-multiplicity vector against contravariant
Hom dimensions. -/
def reverseEvaluation (c : Iota → ℤ) : Iota → ℤ :=
  fun z ↦ ∑ j, c j * (Module.finrank K (sigma.obj j ⟶ sigma.obj z) : ℤ)

theorem reverseEvaluation_directedSingle
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (j : Iota) :
    reverseEvaluation K R sigma (directedSingle sigma H j) =
      reverseHomFinrankVector K R sigma (sigma.obj j) := by
  classical
  funext z
  simp [reverseEvaluation, reverseHomFinrankVector, directedSingle,
    Pi.single_apply]

theorem reverseEvaluation_sum
    {J : Type*} [Fintype J] (c : J → Iota → ℤ) :
    reverseEvaluation K R sigma (∑ t, c t) =
      ∑ t, reverseEvaluation K R sigma (c t) := by
  classical
  funext z
  simp only [reverseEvaluation, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul]

theorem reverseEvaluation_add (c d : Iota → ℤ) :
    reverseEvaluation K R sigma (c + d) =
      reverseEvaluation K R sigma c + reverseEvaluation K R sigma d := by
  funext z
  simp [reverseEvaluation, add_mul, Finset.sum_add_distrib]

theorem reverseEvaluation_sub (c d : Iota → ℤ) :
    reverseEvaluation K R sigma (c - d) =
      reverseEvaluation K R sigma c - reverseEvaluation K R sigma d := by
  funext z
  simp [reverseEvaluation, sub_mul, Finset.sum_sub_distrib]

theorem reverseEvaluation_zsmul (n : ℤ) (c : Iota → ℤ) :
    reverseEvaluation K R sigma (n • c) =
      n • reverseEvaluation K R sigma c := by
  funext z
  simp [reverseEvaluation, Finset.mul_sum, mul_assoc]

theorem splitCoordinate_iso
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {M N : FGModuleCat.{u} R} (e : M ≅ N) :
    splitCoordinate K R sigma H M = splitCoordinate K R sigma H N := by
  letI := directedLinearOrder sigma H
  simp only [splitCoordinate, homFinrankVector_iso K R sigma e]

theorem splitCoordinate_biproduct
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {J : Type*} [Fintype J] (M : J → FGModuleCat.{u} R) :
    splitCoordinate K R sigma H (⨁ M) =
      ∑ j, splitCoordinate K R sigma H (M j) := by
  letI := directedLinearOrder sigma H
  simp only [splitCoordinate,
    homFinrankVector_biproduct_finite K R sigma M,
    UpperUnitriangular.coordinates_sum]

theorem splitCoordinate_obj
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (j : Iota) :
    splitCoordinate K R sigma H (sigma.obj j) =
      directedSingle sigma H j := by
  letI := directedLinearOrder sigma H
  have h := UpperUnitriangular.coordinates_retained_column
    (homFinrankMatrix K R sigma) ∅
    (H.homFinrankMatrix_blockTriangular K R sigma)
    (H.homFinrankMatrix_diagonal K R sigma) (j := j) (by simp)
  change UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
      (homFinrankVector K R sigma (sigma.obj j)) = _
  have hv : homFinrankVector K R sigma (sigma.obj j) =
      (homFinrankMatrix K R sigma).col j := rfl
  rw [hv]
  simpa only [directedSingle] using h

theorem coordinates_directedSingle_eq_arMesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (directedSingle sigma H x.1) =
      directedSingle sigma H x.1 +
        directedSingle sigma H (T.arTranslation sigma x).1 -
          splitCoordinate K R sigma H (T.chosenRightAR sigma x).middle := by
  letI := directedLinearOrder sigma H
  have hmesh := chosenRightAR_homFinrankVector_mesh
    (K := K) (R := R) sigma H T x
  have hc := congrArg
    (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅) hmesh
  simp only [UpperUnitriangular.coordinates_add] at hc
  change splitCoordinate K R sigma H (sigma.obj x.1) +
      splitCoordinate K R sigma H
        (sigma.obj (T.arTranslation sigma x).1) =
    splitCoordinate K R sigma H (T.chosenRightAR sigma x).middle +
      UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (directedSingle sigma H x.1) at hc
  rw [splitCoordinate_obj K R sigma H,
    splitCoordinate_obj K R sigma H] at hc
  funext a
  have hca := congrFun hc a
  change directedSingle sigma H x.1 a +
      directedSingle sigma H (T.arTranslation sigma x).1 a =
    splitCoordinate K R sigma H (T.chosenRightAR sigma x).middle a +
      UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (directedSingle sigma H x.1) a at hca
  change UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
      (directedSingle sigma H x.1) a =
    directedSingle sigma H x.1 a +
      directedSingle sigma H (T.arTranslation sigma x).1 a -
        splitCoordinate K R sigma H (T.chosenRightAR sigma x).middle a
  omega

theorem sum_zsmul_directedSingle
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (v : Iota → ℤ) :
    ∑ x, v x • directedSingle sigma H x = v := by
  classical
  funext a
  simp [directedSingle, Pi.single_apply]

theorem coordinates_zsmul
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (n : ℤ) (v : Iota → ℤ) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (n • v) =
      n • UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ v := by
  letI := directedLinearOrder sigma H
  funext a
  simp only [UpperUnitriangular.coordinates, Matrix.mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coordinates_sub
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (v w : Iota → ℤ) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (v - w) =
      UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ v -
        UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ w := by
  letI := directedLinearOrder sigma H
  simp [UpperUnitriangular.coordinates, Matrix.mulVec_sub]

/-- Expansion of any integral Hom-defect vector in the simple-functor
coordinate columns. -/
theorem coordinates_eq_sum_coordinates_directedSingle
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (v : Iota → ℤ) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ v =
      ∑ x, v x •
        UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
          (directedSingle sigma H x) := by
  letI := directedLinearOrder sigma H
  conv_lhs =>
    rw [← sum_zsmul_directedSingle R sigma H v]
  rw [UpperUnitriangular.coordinates_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact coordinates_zsmul K R sigma H (v x) (directedSingle sigma H x)

theorem reverseHomFinrankVector_iso
    {M N : FGModuleCat.{u} R} (e : M ≅ N) :
    reverseHomFinrankVector K R sigma M =
      reverseHomFinrankVector K R sigma N := by
  funext z
  change (Module.finrank K (M ⟶ sigma.obj z) : ℤ) =
    (Module.finrank K (N ⟶ sigma.obj z) : ℤ)
  exact_mod_cast (Linear.homCongr K e (Iso.refl _)).finrank_eq

theorem reverseHomFinrankVector_biproduct
    {J : Type*} [Fintype J] (M : J → FGModuleCat.{u} R) :
    reverseHomFinrankVector K R sigma (⨁ M) =
      ∑ j, reverseHomFinrankVector K R sigma (M j) := by
  funext z
  letI : FiniteDimensional K ((⨁ M) ⟶ sigma.obj z) :=
    finiteDimensional_hom_fg K R (⨁ M) (sigma.obj z)
  letI (j : J) : FiniteDimensional K (M j ⟶ sigma.obj z) :=
    finiteDimensional_hom_fg K R (M j) (sigma.obj z)
  simp only [reverseHomFinrankVector, Finset.sum_apply]
  exact_mod_cast finrank_biproduct_hom (K := K) M (sigma.obj z)

/-- The cokernel of the transported kernel inclusion in the chosen right AR
sequence is its indecomposable endpoint. -/
def arKernelMapCokernelIsoTarget
    (T : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    cokernel (T.arKernelMap sigma x) ≅ sigma.obj x.1 := by
  let A := T.chosenRightAR sigma x
  letI : Epi A.map :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      sigma A.map A.rightAlmostSplit x.2
  exact
    (cokernel.mapIso (T.arKernelMap sigma x) (kernel.ι A.map)
      (T.arTranslationKernelIso sigma x).symm (Iso.refl _) (by
        simp [QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData.arKernelMap,
          A])).trans
      (QuotientSubmoduleEquidistribution.cokernelKernelIsoTarget A.map)

/-- The chosen right AR sequence also satisfies the contravariant Hom mesh
identity, with its delta at the translated source. -/
theorem chosenRightAR_reverseHomFinrankVector_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    reverseHomFinrankVector K R sigma (sigma.obj x.1) +
        reverseHomFinrankVector K R sigma
          (sigma.obj (T.arTranslation sigma x).1) =
      reverseHomFinrankVector K R sigma (T.chosenRightAR sigma x).middle +
        directedSingle sigma H (T.arTranslation sigma x).1 := by
  funext a
  let f := T.arKernelMap sigma x
  have hmesh := homCokernel_add_source_eq_middle_add_delta
    K R sigma H (T.arKernelMap_leftAlmostSplit sigma x) (a := a)
  have hcNat : Module.finrank K (cokernel f ⟶ sigma.obj a) =
      Module.finrank K (sigma.obj x.1 ⟶ sigma.obj a) :=
    (Linear.homCongr K (arKernelMapCokernelIsoTarget R sigma T x)
      (Iso.refl _)).finrank_eq
  have hcInt : (Module.finrank K (cokernel f ⟶ sigma.obj a) : ℤ) =
      (Module.finrank K (sigma.obj x.1 ⟶ sigma.obj a) : ℤ) := by
    exact_mod_cast hcNat
  change (Module.finrank K (sigma.obj x.1 ⟶ sigma.obj a) : ℤ) +
      (Module.finrank K
        (sigma.obj (T.arTranslation sigma x).1 ⟶ sigma.obj a) : ℤ) =
    (Module.finrank K ((T.chosenRightAR sigma x).middle ⟶ sigma.obj a) : ℤ) +
      directedSingle sigma H (T.arTranslation sigma x).1 a
  rw [← hcInt]
  simp only [directedSingle, Pi.single_apply]
  by_cases ha : a = (T.arTranslation sigma x).1
  · simp [ha] at hmesh ⊢
    exact_mod_cast hmesh
  · simp [ha] at hmesh ⊢
    exact_mod_cast hmesh

/-- Contravariant Hom dimensions are obtained by evaluating the ordinary
Krull--Schmidt split coordinates. -/
theorem reverseHomFinrankVector_eq_reverseEvaluation_splitCoordinate
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (M : FGModuleCat.{u} R) :
    reverseHomFinrankVector K R sigma M =
      reverseEvaluation K R sigma (splitCoordinate K R sigma H M) := by
  classical
  obtain ⟨n, j, ⟨e⟩⟩ := sigma.decomposes M
  rw [reverseHomFinrankVector_iso K R sigma e,
    splitCoordinate_iso K R sigma H e,
    reverseHomFinrankVector_biproduct K R sigma,
    splitCoordinate_biproduct K R sigma H,
    reverseEvaluation_sum K R sigma]
  apply Finset.sum_congr rfl
  intro t _
  rw [splitCoordinate_obj K R sigma H]
  exact (reverseEvaluation_directedSingle K R sigma H (j t)).symm

/-- A nonprojective simple-functor coordinate evaluates contravariantly as
the Kronecker delta at the translated AR source. -/
theorem reverseEvaluation_coordinates_directedSingle
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    letI := directedLinearOrder sigma H
    reverseEvaluation K R sigma
      (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
        (directedSingle sigma H x.1)) =
      directedSingle sigma H (T.arTranslation sigma x).1 := by
  letI := directedLinearOrder sigma H
  rw [coordinates_directedSingle_eq_arMesh K R sigma H T x,
    reverseEvaluation_sub K R sigma,
    reverseEvaluation_add K R sigma,
    reverseEvaluation_directedSingle K R sigma H,
    reverseEvaluation_directedSingle K R sigma H,
    ← reverseHomFinrankVector_eq_reverseEvaluation_splitCoordinate
      K R sigma H]
  have hmesh := chosenRightAR_reverseHomFinrankVector_mesh
    K R sigma H T x
  funext a
  have ha := congrFun hmesh a
  simp only [Pi.add_apply, Pi.sub_apply] at ha ⊢
  omega

/-- If covariant Hom dimensions from every indecomposable weakly increase,
and they agree on projectives, then all contravariant Hom dimensions weakly
increase as well.  This is the numerical Auslander--Reiten rigidity step. -/
theorem reverseHomFinrankVector_le_of_homFinrankVector_le_of_projective_eq
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : sigma.FiniteARTranslationData)
    {M N : FGModuleCat.{u} R}
    (hle : ∀ x,
      homFinrankVector K R sigma M x ≤ homFinrankVector K R sigma N x)
    (hprojective : ∀ x, Projective (sigma.obj x) →
      homFinrankVector K R sigma M x = homFinrankVector K R sigma N x)
    (z : Iota) :
    reverseHomFinrankVector K R sigma M z ≤
      reverseHomFinrankVector K R sigma N z := by
  letI := directedLinearOrder sigma H
  let d : Iota → ℤ :=
    homFinrankVector K R sigma N - homFinrankVector K R sigma M
  have hd (x : Iota) : 0 ≤ d x := by
    dsimp only [d]
    simp only [Pi.sub_apply]
    exact sub_nonneg.mpr (hle x)
  have hd_projective (x : Iota) (hx : Projective (sigma.obj x)) :
      d x = 0 := by
    dsimp only [d]
    simp only [Pi.sub_apply]
    rw [hprojective x hx]
    simp
  have hsplit :
      splitCoordinate K R sigma H N - splitCoordinate K R sigma H M =
        UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ d := by
    change UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
          (homFinrankVector K R sigma N) -
        UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
          (homFinrankVector K R sigma M) = _
    rw [← coordinates_sub K R sigma H]
  have hreverse :
      reverseHomFinrankVector K R sigma N -
          reverseHomFinrankVector K R sigma M =
        reverseEvaluation K R sigma
          (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ d) := by
    rw [reverseHomFinrankVector_eq_reverseEvaluation_splitCoordinate
        K R sigma H,
      reverseHomFinrankVector_eq_reverseEvaluation_splitCoordinate
        K R sigma H,
      ← reverseEvaluation_sub K R sigma,
      hsplit]
  have hevaluation :
      reverseEvaluation K R sigma
          (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ d) z =
        ∑ x, d x *
          reverseEvaluation K R sigma
            (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
              (directedSingle sigma H x)) z := by
    rw [coordinates_eq_sum_coordinates_directedSingle K R sigma H d,
      reverseEvaluation_sum K R sigma]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [reverseEvaluation_zsmul K R sigma]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hterm (x : Iota) :
      0 ≤ d x *
        reverseEvaluation K R sigma
          (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅
            (directedSingle sigma H x)) z := by
    by_cases hx : Projective (sigma.obj x)
    · rw [hd_projective x hx, zero_mul]
    · let x' : sigma.NonprojectiveLabel := ⟨x, hx⟩
      rw [show x = x'.1 by rfl,
        reverseEvaluation_coordinates_directedSingle K R sigma H D x']
      by_cases hzx : z = (D.arTranslation sigma x').1
      · simpa [directedSingle, Pi.single_apply, hzx] using hd x
      · simp [directedSingle, Pi.single_apply, hzx]
  have hsum : 0 ≤
      reverseEvaluation K R sigma
        (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) ∅ d) z := by
    rw [hevaluation]
    exact Finset.sum_nonneg fun x _ ↦ hterm x
  have hz := congrFun hreverse z
  simp only [Pi.sub_apply] at hz
  omega

/-- Every indecomposable representative receives a nonzero morphism from
some indecomposable projective representative. -/
theorem exists_projective_obj_homFinrank_pos
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (y : Iota) :
    ∃ p, Projective (sigma.obj p) ∧
      0 < homFinrankVector K R sigma (sigma.obj y) p := by
  classical
  obtain ⟨P⟩ :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.inFac_projectiveLabels
      sigma (sigma.obj y)
  letI : Epi P.map := P.epi
  have hmap : P.map ≠ 0 := by
    intro hzero
    have hid : 𝟙 (sigma.obj y) = 0 := by
      apply (cancel_epi P.map).1
      rw [hzero]
      simp
    have hsub : Subsingleton (sigma.obj y ⟶ sigma.obj y) := by
      constructor
      intro f g
      rw [← Category.id_comp f, hid, zero_comp,
        ← Category.id_comp g, hid, zero_comp]
    have hfinzero : Module.finrank K (sigma.obj y ⟶ sigma.obj y) = 0 :=
      Module.finrank_zero_of_subsingleton
    have hfinone := H.finrank_endomorphism_eq_one K R sigma y
    omega
  have hcomponent : ∃ t : P.index,
      biproduct.ι (fun s ↦ sigma.obj (P.label s)) t ≫ P.map ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hmap
    apply biproduct.hom_ext'
    intro t
    simpa only [comp_zero] using hnone t
  obtain ⟨t, ht⟩ := hcomponent
  refine ⟨P.label t, P.mem t, ?_⟩
  change 0 < (Module.finrank K
    (sigma.obj (P.label t) ⟶ sigma.obj y) : ℤ)
  letI : FiniteDimensional K
      (sigma.obj (P.label t) ⟶ sigma.obj y) :=
    finiteDimensional_hom_from_obj K R sigma (P.label t) (sigma.obj y)
  haveI : Nontrivial (sigma.obj (P.label t) ⟶ sigma.obj y) :=
    ⟨⟨_, 0, ht⟩⟩
  exact_mod_cast (Module.finrank_pos (R := K)
    (M := sigma.obj (P.label t) ⟶ sigma.obj y))

/-- Directed Hom rigidity: a module without the indicated indecomposable
summand cannot be weakly Hom-dominated by that indecomposable with equality
on every projective row. -/
theorem exists_projective_obj_homFinrank_lt_of_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : sigma.FiniteARTranslationData)
    (y : Iota) (T : FGModuleCat.{u} R)
    (hno : splitCoordinate K R sigma H T y = 0)
    (hle : ∀ x,
      homFinrankVector K R sigma T x ≤
        homFinrankVector K R sigma (sigma.obj y) x) :
    ∃ p, Projective (sigma.obj p) ∧
      homFinrankVector K R sigma T p <
        homFinrankVector K R sigma (sigma.obj y) p := by
  classical
  letI := directedLinearOrder sigma H
  by_contra hnone
  push_neg at hnone
  have hprojective (p : Iota) (hp : Projective (sigma.obj p)) :
      homFinrankVector K R sigma T p =
        homFinrankVector K R sigma (sigma.obj y) p := by
    exact le_antisymm (hle p) (hnone p hp)
  have hreverse (z : Iota) :
      reverseHomFinrankVector K R sigma T z ≤
        reverseHomFinrankVector K R sigma (sigma.obj y) z :=
    reverseHomFinrankVector_le_of_homFinrankVector_le_of_projective_eq
      K R sigma H D hle hprojective z
  obtain ⟨n, j, ⟨e⟩⟩ := sigma.decomposes T
  have hn : n ≠ 0 := by
    intro hnzero
    subst n
    obtain ⟨p, hp, hpy⟩ := exists_projective_obj_homFinrank_pos
      K R sigma H y
    have hTzero : homFinrankVector K R sigma T p = 0 := by
      rw [homFinrankVector_iso K R sigma e,
        homFinrankVector_biproduct_finite K R sigma]
      simp
    have heq := hprojective p hp
    rw [hTzero] at heq
    omega
  let t : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let Z : FGModuleCat.{u} R := sigma.obj (j t)
  let i : Z ⟶ T :=
    biproduct.ι (fun s : Fin n ↦ sigma.obj (j s)) t ≫ e.inv
  let r : T ⟶ Z :=
    e.hom ≫ biproduct.π (fun s : Fin n ↦ sigma.obj (j s)) t
  have hir : i ≫ r = 𝟙 Z := by
    simp [i, r, Z]
  have hi : i ≠ 0 := by
    intro hizero
    rw [hizero, zero_comp] at hir
    have hsub : Subsingleton (Z ⟶ Z) := by
      constructor
      intro f g
      rw [← Category.id_comp f, ← hir, zero_comp,
        ← Category.id_comp g, ← hir, zero_comp]
    have hzero : Module.finrank K (Z ⟶ Z) = 0 :=
      Module.finrank_zero_of_subsingleton
    have hone := H.finrank_endomorphism_eq_one K R sigma (j t)
    change Module.finrank K (Z ⟶ Z) = 1 at hone
    omega
  have hr : r ≠ 0 := by
    intro hrzero
    rw [hrzero, comp_zero] at hir
    have hsub : Subsingleton (Z ⟶ Z) := by
      constructor
      intro f g
      rw [← Category.id_comp f, ← hir, zero_comp,
        ← Category.id_comp g, ← hir, zero_comp]
    have hzero : Module.finrank K (Z ⟶ Z) = 0 :=
      Module.finrank_zero_of_subsingleton
    have hone := H.finrank_endomorphism_eq_one K R sigma (j t)
    change Module.finrank K (Z ⟶ Z) = 1 at hone
    omega
  have hcoord : splitCoordinate K R sigma H T y =
      ∑ s : Fin n, directedSingle sigma H (j s) y := by
    rw [splitCoordinate_iso K R sigma H e,
      splitCoordinate_biproduct K R sigma H]
    simp only [Finset.sum_apply, splitCoordinate_obj K R sigma H,
      directedSingle]
  have hjy : j t ≠ y := by
    intro hjy'
    have hsumzero : (∑ s : Fin n,
        directedSingle sigma H (j s) y) = 0 := by
      rw [← hcoord, hno]
    have hleone : directedSingle sigma H (j t) y ≤
        ∑ s : Fin n, directedSingle sigma H (j s) y := by
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun s : Fin n ↦ directedSingle sigma H (j s) y) ?_ ?_
      · intro s _
        simp only [directedSingle, Pi.single_apply]
        split_ifs <;> omega
      · exact Finset.mem_univ t
    have htvalue : directedSingle sigma H (j t) y = 1 := by
      simp [directedSingle, Pi.single_apply, hjy'.symm]
    rw [htvalue, hsumzero] at hleone
    omega
  have hZTpos : 0 < homFinrankVector K R sigma T (j t) := by
    change 0 < (Module.finrank K (Z ⟶ T) : ℤ)
    letI : FiniteDimensional K (Z ⟶ T) :=
      finiteDimensional_hom_fg K R Z T
    haveI : Nontrivial (Z ⟶ T) := ⟨⟨i, 0, hi⟩⟩
    exact_mod_cast (Module.finrank_pos (R := K) (M := Z ⟶ T))
  have hTYpos : 0 < homFinrankVector K R sigma (sigma.obj y) (j t) :=
    lt_of_lt_of_le hZTpos (hle (j t))
  have hTZpos : 0 < reverseHomFinrankVector K R sigma T (j t) := by
    change 0 < (Module.finrank K (T ⟶ Z) : ℤ)
    letI : FiniteDimensional K (T ⟶ Z) :=
      finiteDimensional_hom_fg K R T Z
    haveI : Nontrivial (T ⟶ Z) := ⟨⟨r, 0, hr⟩⟩
    exact_mod_cast (Module.finrank_pos (R := K) (M := T ⟶ Z))
  have hYZpos : 0 < reverseHomFinrankVector K R sigma (sigma.obj y) (j t) :=
    lt_of_lt_of_le hTZpos (hreverse (j t))
  letI : FiniteDimensional K (Z ⟶ sigma.obj y) :=
    finiteDimensional_hom_fg K R Z (sigma.obj y)
  letI : FiniteDimensional K (sigma.obj y ⟶ Z) :=
    finiteDimensional_hom_fg K R (sigma.obj y) Z
  have hTYposNat : 0 < Module.finrank K (Z ⟶ sigma.obj y) := by
    change 0 < (Module.finrank K (Z ⟶ sigma.obj y) : ℤ) at hTYpos
    exact_mod_cast hTYpos
  have hYZposNat : 0 < Module.finrank K (sigma.obj y ⟶ Z) := by
    change 0 < (Module.finrank K (sigma.obj y ⟶ Z) : ℤ) at hYZpos
    exact_mod_cast hYZpos
  haveI : Nontrivial (Z ⟶ sigma.obj y) :=
    Module.nontrivial_of_finrank_pos hTYposNat
  haveI : Nontrivial (sigma.obj y ⟶ Z) :=
    Module.nontrivial_of_finrank_pos hYZposNat
  obtain ⟨f, hf⟩ := exists_ne (0 : Z ⟶ sigma.obj y)
  obtain ⟨g, hg⟩ := exists_ne (0 : sigma.obj y ⟶ Z)
  have hzy : j t < y :=
    (directedLinearOrder_homOrderProperty sigma H) f hf hjy
  have hyz : y < j t :=
    (directedLinearOrder_homOrderProperty sigma H) g hg hjy.symm
  exact asymm hzy hyz

end QuotientSubmoduleEquidistribution.RepresentationDirected
