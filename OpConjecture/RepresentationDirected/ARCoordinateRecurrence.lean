import OpConjecture.RepresentationDirected.ARWordDictionary
import OpConjecture.RepresentationDirected.EffectiveLiftingComplement
import OpConjecture.RepresentationDirected.EffectiveLiftingCoordinates

/-!
# Pointwise AR mesh and mixed-coordinate recurrence

This file contains only abstract arguments.  It first proves the
pointwise Hom-finrank mesh identity for a minimal right almost-split map,
including the projective (monic) boundary.  It then transports that identity
through the integral mixed-coordinate change of basis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

namespace OpConjecture.RepresentationDirected

universe u v uC vC

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

section KernelLinearEquiv

variable {K : Type u} [Field K]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear K C]

/-- Morphisms into a categorical kernel are the kernel of postcomposition. -/
def homKernelLinearEquiv {X T Y : C} (f : T ⟶ Y) [HasKernel f] :
    (X ⟶ kernel f) ≃ₗ[K]
      LinearMap.ker (postcompLinearMap (K := K) (X := X) f) := by
  let L : (X ⟶ kernel f) →ₗ[K]
      LinearMap.ker (postcompLinearMap (K := K) (X := X) f) :=
    { toFun := fun g ↦ ⟨g ≫ kernel.ι f, by
          simp [postcompLinearMap, Category.assoc, kernel.condition]⟩
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
    apply (cancel_mono (kernel.ι f)).1
    exact congrArg Subtype.val hab
  · intro h
    have hh' := h.property
    have hh : h.1 ≫ f = 0 := by
      change postcompLinearMap (K := K) f h.1 = 0 at hh'
      simpa only [postcompLinearMap_apply] using hh'
    refine ⟨kernel.lift f h.1 hh, ?_⟩
    apply Subtype.ext
    exact kernel.lift_ι f h.1 hh

end KernelLinearEquiv

section PointwiseMesh

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

local instance : DecidableEq Iota := Classical.decEq Iota

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- Postcomposition with a right almost-split map is surjective from every
different indecomposable representative. -/
theorem rightAlmostSplit_postcomp_surjective_of_ne
    {z a : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    (haz : a ≠ z) :
    Function.Surjective
      (postcompLinearMap (K := K) (X := sigma.obj a) A.map) := by
  intro g
  have hg : ¬ IsSplitEpi g := by
    intro hsplit
    letI : IsSplitEpi g := hsplit
    letI : IsSplitMono g :=
      sigma.isSplitMono_of_isSplitEpi_between_obj g
    letI : IsIso g := isIso_of_epi_of_isSplitMono g
    exact haz (sigma.eq_of_iso ⟨asIso g⟩)
  exact A.rightAlmostSplit.factors g hg

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- At the endpoint itself, postcomposition with a right almost-split map is
the zero linear map. -/
theorem rightAlmostSplit_postcomp_eq_zero
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z) :
    postcompLinearMap (K := K) (X := sigma.obj z) A.map = 0 := by
  apply LinearMap.ext
  intro h
  change h ≫ A.map = 0
  by_contra hne
  letI : IsIso (h ≫ A.map) :=
    H.isIso_of_ne_zero_endomorphism sigma z (h ≫ A.map) hne
  apply A.rightAlmostSplit.not_isSplitEpi
  exact IsSplitEpi.mk'
    { section_ := inv (h ≫ A.map) ≫ h
      id := by simp }

/-- Pointwise Hom-finrank form of the nonprojective AR mesh identity. -/
theorem homFinrank_add_kernel_eq_middle_add_delta
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z a : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z) :
    Module.finrank K (sigma.obj a ⟶ sigma.obj z) +
        Module.finrank K (sigma.obj a ⟶ kernel A.map) =
      Module.finrank K (sigma.obj a ⟶ A.middle) +
        if a = z then 1 else 0 := by
  letI : FiniteDimensional K (sigma.obj a ⟶ sigma.obj z) :=
    finiteDimensional_hom_from_obj K R sigma a (sigma.obj z)
  letI : FiniteDimensional K (sigma.obj a ⟶ A.middle) :=
    finiteDimensional_hom_from_obj K R sigma a A.middle
  letI : FiniteDimensional K (sigma.obj a ⟶ kernel A.map) :=
    finiteDimensional_hom_from_obj K R sigma a (kernel A.map)
  let L := postcompLinearMap (K := K) (X := sigma.obj a) A.map
  have hker' :=
    (homKernelLinearEquiv (K := K) (X := sigma.obj a) A.map).finrank_eq
  have hker : Module.finrank K (sigma.obj a ⟶ kernel A.map) =
      Module.finrank K (LinearMap.ker L) := by
    simpa only [L] using hker'
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  by_cases haz : a = z
  · subst a
    have hL : L = 0 := rightAlmostSplit_postcomp_eq_zero sigma H A
    have hrange : Module.finrank K (LinearMap.range L) = 0 := by
      rw [hL]
      simp
    have hend := H.finrank_endomorphism_eq_one K R sigma z
    simp only [if_true]
    omega
  · have hsurj : Function.Surjective L :=
      rightAlmostSplit_postcomp_surjective_of_ne (K := K) sigma A haz
    have hrange : Module.finrank K (LinearMap.range L) =
        Module.finrank K (sigma.obj a ⟶ sigma.obj z) := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    simp only [if_neg haz]
    omega

/-- Projective-boundary form: if the right almost-split map is monic, its
pointwise Hom defect is the Kronecker delta. -/
theorem homFinrank_eq_middle_add_delta_of_mono
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    {z a : Iota} (A : sigma.MinimalRightAlmostSplitDecomposition z)
    [Mono A.map] :
    Module.finrank K (sigma.obj a ⟶ sigma.obj z) =
      Module.finrank K (sigma.obj a ⟶ A.middle) +
        if a = z then 1 else 0 := by
  letI : FiniteDimensional K (sigma.obj a ⟶ sigma.obj z) :=
    finiteDimensional_hom_from_obj K R sigma a (sigma.obj z)
  letI : FiniteDimensional K (sigma.obj a ⟶ A.middle) :=
    finiteDimensional_hom_from_obj K R sigma a A.middle
  let L := postcompLinearMap (K := K) (X := sigma.obj a) A.map
  have hinj : Function.Injective L := by
    intro f g hfg
    exact (cancel_mono A.map).1 hfg
  by_cases haz : a = z
  · subst a
    have hL : L = 0 := rightAlmostSplit_postcomp_eq_zero sigma H A
    have hdomain : Module.finrank K (sigma.obj z ⟶ A.middle) = 0 := by
      have hsub : Subsingleton (sigma.obj z ⟶ A.middle) := by
        constructor
        intro f g
        apply hinj
        rw [hL]
        rfl
      exact Module.finrank_zero_of_subsingleton
    rw [H.finrank_endomorphism_eq_one K R sigma z, hdomain]
    simp
  · have hsurj : Function.Surjective L :=
      rightAlmostSplit_postcomp_surjective_of_ne (K := K) sigma A haz
    have hrank := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
    simpa only [if_neg haz, Nat.add_zero] using hrank.symm

end PointwiseMesh

section IntegralTransport

open DirectedAROrbit

universe uI

variable {I : Type uI} [Fintype I] [LinearOrder I]

/-- An omitted standard-basis column is already one of the mixed basis
columns, so its mixed coordinates are unchanged. -/
theorem coordinates_single_of_mem
    (Hmat : Matrix I I ℤ) (D : Finset I)
    (hupper : Hmat.BlockTriangular id) (hdiag : ∀ i, Hmat i i = 1)
    {x : I} (hx : x ∈ D) :
    UpperUnitriangular.coordinates Hmat D (Pi.single x (1 : ℤ)) =
      Pi.single x (1 : ℤ) := by
  apply UpperUnitriangular.coordinates_eq_of_mulVec_eq
    Hmat D hupper hdiag
  rw [Matrix.mulVec_single_one]
  funext a
  simp [UpperUnitriangular.mixedMatrix, hx, Pi.single_apply]

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
  {Iota : Type v} [Fintype Iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

/-- The standard coordinate vector, formed with the same directed linear
order instance used by `mixedMultiplicity`. -/
def directedSingle
    (H : HasAcyclicNonzeroNonisomorphisms sigma) (x : Iota) : Iota → ℤ := by
  letI := directedLinearOrder sigma H
  exact Pi.single x 1

/-- The directed standard vector is fixed by the mixed-coordinate inverse
when its label is omitted. -/
theorem coordinates_directedSingle_of_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) {x : Iota} (hx : x ∈ D) :
    letI := directedLinearOrder sigma H
    UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) D
        (directedSingle sigma H x) =
      directedSingle sigma H x := by
  letI := directedLinearOrder sigma H
  exact coordinates_single_of_mem
    (homFinrankMatrix K R sigma) D
    (H.homFinrankMatrix_blockTriangular K R sigma)
    (H.homFinrankMatrix_diagonal K R sigma) hx

omit [Fintype Iota] in
/-- Hom-finrank vectors satisfy the ordinary nonprojective AR mesh identity,
with the categorical kernel transported to the chosen `tau` representative. -/
theorem chosenRightAR_homFinrankVector_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (x : sigma.NonprojectiveLabel) :
    homFinrankVector K R sigma (sigma.obj x.1) +
        homFinrankVector K R sigma
          (sigma.obj (T.arTranslation sigma x).1) =
      homFinrankVector K R sigma (T.chosenRightAR sigma x).middle +
        directedSingle sigma H x.1 := by
  let A := T.chosenRightAR sigma x
  funext a
  have hmesh := homFinrank_add_kernel_eq_middle_add_delta
    (K := K) (R := R) sigma H A (a := a)
  letI : FiniteDimensional K (sigma.obj a ⟶ kernel A.map) :=
    finiteDimensional_hom_from_obj K R sigma a (kernel A.map)
  letI : FiniteDimensional K
      (sigma.obj a ⟶ sigma.obj (T.arTranslation sigma x).1) :=
    finiteDimensional_hom_from_obj K R sigma a
      (sigma.obj (T.arTranslation sigma x).1)
  have hkNat : Module.finrank K (sigma.obj a ⟶ kernel A.map) =
      Module.finrank K
        (sigma.obj a ⟶ sigma.obj (T.arTranslation sigma x).1) :=
    (Linear.homCongr K (Iso.refl _)
      (T.arTranslationKernelIso sigma x)).finrank_eq
  have hkInt :
      (Module.finrank K (sigma.obj a ⟶ kernel A.map) : ℤ) =
        (Module.finrank K
          (sigma.obj a ⟶ sigma.obj (T.arTranslation sigma x).1) : ℤ) := by
    exact_mod_cast hkNat
  change (Module.finrank K (sigma.obj a ⟶ sigma.obj x.1) : ℤ) +
      (Module.finrank K
        (sigma.obj a ⟶ sigma.obj (T.arTranslation sigma x).1) : ℤ) =
    (Module.finrank K (sigma.obj a ⟶ A.middle) : ℤ) +
      directedSingle sigma H x.1 a
  rw [← hkInt]
  simp only [directedSingle, Pi.single_apply]
  by_cases hax : a = x.1
  · simp [hax] at hmesh ⊢
    exact_mod_cast hmesh
  · simp [hax] at hmesh ⊢
    exact_mod_cast hmesh

omit [Fintype Iota] in
/-- The projective radical boundary has the same Hom-vector mesh identity,
with no predecessor term. -/
theorem projectiveBoundary_homFinrankVector_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (p : Iota) (hp : Projective (sigma.obj p)) :
    homFinrankVector K R sigma (sigma.obj p) =
      homFinrankVector K R sigma
          (sigma.projectiveBoundaryRadical p) +
        directedSingle sigma H p := by
  let A := sigma.projectiveBoundaryMinimalRightAlmostSplitDecomposition p hp
  letI : Mono A.map := by
    apply (IndecomposableSkeleton.fg_mono_iff_injective A.map).2
    change Function.Injective (Module.jacobson R (sigma.obj p)).subtype
    exact (Module.jacobson R (sigma.obj p)).subtype_injective
  funext a
  have hmesh := homFinrank_eq_middle_add_delta_of_mono
    (K := K) (R := R) sigma H A (a := a)
  change (Module.finrank K (sigma.obj a ⟶ sigma.obj p) : ℤ) =
    (Module.finrank K (sigma.obj a ⟶ A.middle) : ℤ) +
      directedSingle sigma H p a
  simp only [directedSingle, Pi.single_apply]
  by_cases hap : a = p
  · simp [hap] at hmesh ⊢
    exact_mod_cast hmesh
  · simp [hap] at hmesh ⊢
    exact_mod_cast hmesh

/-- Applying the integral mixed-basis inverse to a nonprojective AR mesh
preserves the mesh identity. -/
theorem chosenRightAR_mixedMultiplicity_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset Iota) (x : sigma.NonprojectiveLabel) (hx : x.1 ∈ D) :
    mixedMultiplicity K R sigma H D (sigma.obj x.1) +
        mixedMultiplicity K R sigma H D
          (sigma.obj (T.arTranslation sigma x).1) =
      mixedMultiplicity K R sigma H D (T.chosenRightAR sigma x).middle +
        directedSingle sigma H x.1 := by
  letI := directedLinearOrder sigma H
  have hvec := chosenRightAR_homFinrankVector_mesh
    (K := K) (R := R) sigma H T x
  have hcoord := congrArg
    (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) D) hvec
  simp only [UpperUnitriangular.coordinates_add] at hcoord
  rw [coordinates_directedSingle_of_mem
    (K := K) (R := R) sigma H D hx] at hcoord
  simpa only [mixedMultiplicity,
    UpperUnitriangular.coordinates_add] using hcoord

/-- Integral mixed-coordinate mesh identity at the projective boundary. -/
theorem projectiveBoundary_mixedMultiplicity_mesh
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (D : Finset Iota) (p : Iota) (hp : Projective (sigma.obj p))
    (hpD : p ∈ D) :
    mixedMultiplicity K R sigma H D (sigma.obj p) =
      mixedMultiplicity K R sigma H D
          (sigma.projectiveBoundaryRadical p) +
        directedSingle sigma H p := by
  letI := directedLinearOrder sigma H
  have hvec := projectiveBoundary_homFinrankVector_mesh
    (K := K) (R := R) sigma H p hp
  have hcoord := congrArg
    (UpperUnitriangular.coordinates (homFinrankMatrix K R sigma) D) hvec
  simp only [UpperUnitriangular.coordinates_add] at hcoord
  rw [coordinates_directedSingle_of_mem
    (K := K) (R := R) sigma H D hpD] at hcoord
  simpa only [mixedMultiplicity,
    UpperUnitriangular.coordinates_add] using hcoord

noncomputable local instance orderedMiddlePositionsFintype
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (x : Fin (OrderedARWord.word sigma H T).length) :
    Fintype {y : Fin (OrderedARWord.word sigma H T).length //
      ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.word sigma H T) y x} :=
  Fintype.ofFinite _

/-- The mixed coordinate of the actual chosen middle term is the sum over
the literal middle positions of the ordered AR word.  The equivalence
`middleIndexEquiv` retains every decomposition coordinate, not only support. -/
theorem chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositions
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData) (D : Finset Iota)
    (x : Fin (OrderedARWord.word sigma H T).length) (a : Iota) :
    mixedMultiplicity K R sigma H D
        (OrderedARWord.chosenRightARAt sigma T
          (OrderedARWord.positionEquiv sigma H T x)).middle a =
      ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.word sigma H T) y x},
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a := by
  let A := OrderedARWord.chosenRightARAt sigma T
    (OrderedARWord.positionEquiv sigma H T x)
  calc
    mixedMultiplicity K R sigma H D A.middle a =
        mixedMultiplicity K R sigma H D
          (sigma.sumOver A.index A.label) a :=
      congrFun (mixedMultiplicity_iso K R sigma H D A.decomposition) a
    _ = (∑ t : A.index,
        mixedMultiplicity K R sigma H D (sigma.obj (A.label t))) a :=
      congrFun
        (mixedMultiplicity_biproduct_finite K R sigma H D
          (fun t : A.index ↦ sigma.obj (A.label t))) a
    _ = ∑ t : A.index,
        mixedMultiplicity K R sigma H D (sigma.obj (A.label t)) a := by
      simp only [Finset.sum_apply]
    _ = ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.word sigma H T) y x},
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a := by
      apply Fintype.sum_equiv
        (OrderedARWord.middleIndexEquiv sigma K H T x)
      intro t
      simp [OrderedARWord.middleIndexEquiv, A]

/-- Retained-column case of the paper's coordinate recurrence. -/
theorem orderedARWord_mixedMultiplicity_retained
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData) (D : Finset Iota)
    (x : Fin (OrderedARWord.word sigma H T).length) (a : Iota)
    (hx : OrderedARWord.positionEquiv sigma H T x ∉ D) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) a =
      directedSingle sigma H
        (OrderedARWord.positionEquiv sigma H T x) a := by
  letI := directedLinearOrder sigma H
  by_cases hax : a = OrderedARWord.positionEquiv sigma H T x
  · subst a
    rw [H.mixedMultiplicity_obj_self K R sigma D hx]
    simp [directedSingle]
  · rw [H.mixedMultiplicity_obj_ne K R sigma D hx hax]
    have hxa : OrderedARWord.positionEquiv sigma H T x ≠ a := Ne.symm hax
    simp [directedSingle, hxa]

/-- Repeated-occurrence (nonprojective) case of the paper's coordinate
recurrence, including the literal sum over middle positions. -/
theorem orderedARWord_mixedMultiplicity_repeated
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData) (D : Finset Iota)
    (p x : Fin (OrderedARWord.word sigma H T).length)
    (hpx : ARWord.IsPrevious (OrderedARWord.word sigma H T) p x)
    (hx : OrderedARWord.positionEquiv sigma H T x ∈ D)
    (a : Iota) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) a =
      directedSingle sigma H
          (OrderedARWord.positionEquiv sigma H T x) a +
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a -
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquiv sigma H T p)) a := by
  have hxNonprojective :
      ¬ Projective
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) :=
    (OrderedARWord.exists_previous_position_iff_not_projective
      sigma H T (OrderedARWord.positionEquiv sigma H T x)).1
      ⟨p, by simpa only [OrderedARWord.positionEquiv_apply_symm_apply]
        using hpx⟩
  let xn : sigma.NonprojectiveLabel :=
    ⟨OrderedARWord.positionEquiv sigma H T x, hxNonprojective⟩
  have hpTau : OrderedARWord.positionEquiv sigma H T p =
      (T.arTranslation sigma xn).1 :=
    (OrderedARWord.isPrevious_position_iff_eq_arTranslation
      sigma H T xn p).1
      (by simpa only [xn, OrderedARWord.positionEquiv_apply_symm_apply]
        using hpx)
  have hmesh := congrFun
    (chosenRightAR_mixedMultiplicity_mesh
      (K := K) (R := R) sigma H T D xn hx) a
  have hmiddle :=
    chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositions
      (K := K) (R := R) sigma H T D x a
  have hmiddle' :
      mixedMultiplicity K R sigma H D
          (T.chosenRightAR sigma xn).middle a =
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a := by
    simpa [OrderedARWord.chosenRightARAt, xn, hxNonprojective] using hmiddle
  simp only [Pi.add_apply] at hmesh
  change mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) a +
      mixedMultiplicity K R sigma H D
        (sigma.obj (T.arTranslation sigma xn).1) a =
    mixedMultiplicity K R sigma H D
        (T.chosenRightAR sigma xn).middle a +
      directedSingle sigma H
        (OrderedARWord.positionEquiv sigma H T x) a at hmesh
  rw [hmiddle', ← hpTau] at hmesh
  omega

/-- First-occurrence (projective-boundary) case of the paper's coordinate
recurrence, again with the literal sum over middle positions. -/
theorem orderedARWord_mixedMultiplicity_first
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData) (D : Finset Iota)
    (x : Fin (OrderedARWord.word sigma H T).length)
    (hxProjective :
      Projective (sigma.obj (OrderedARWord.positionEquiv sigma H T x)))
    (hx : OrderedARWord.positionEquiv sigma H T x ∈ D)
    (a : Iota) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) a =
      directedSingle sigma H
          (OrderedARWord.positionEquiv sigma H T x) a +
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a := by
  have hmesh := congrFun
    (projectiveBoundary_mixedMultiplicity_mesh
      (K := K) (R := R) sigma H D
      (OrderedARWord.positionEquiv sigma H T x) hxProjective hx) a
  have hmiddle :=
    chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositions
      (K := K) (R := R) sigma H T D x a
  have hmiddle' :
      mixedMultiplicity K R sigma H D
          (sigma.projectiveBoundaryRadical
            (OrderedARWord.positionEquiv sigma H T x)) a =
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj (OrderedARWord.positionEquiv sigma H T y.1)) a := by
    simp only [OrderedARWord.chosenRightARAt, dif_pos hxProjective] at hmiddle
    change mixedMultiplicity K R sigma H D
        (sigma.projectiveBoundaryRadical
          (OrderedARWord.positionEquiv sigma H T x)) a = _ at hmiddle
    exact hmiddle
  simp only [Pi.add_apply] at hmesh
  rw [hmiddle'] at hmesh
  omega

/-! ## Literal position-indexed form of the manuscript recurrence -/

/-- Transport a finite set of word positions to the corresponding skeleton
labels. -/
def omittedLabelFinset
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length)) :
    Finset Iota := by
  classical
  exact D.map (OrderedARWord.positionEquiv sigma H T).toEmbedding

@[simp] theorem mem_omittedLabelFinset_iff
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (x : Fin (OrderedARWord.word sigma H T).length) :
    OrderedARWord.positionEquiv sigma H T x ∈
        omittedLabelFinset sigma H T D ↔ x ∈ D := by
  classical
  simp [omittedLabelFinset]

/-- The exact position-indexed integer `μ_D(a,x)` of the manuscript. -/
def wordMixedMultiplicity
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) : ℤ :=
  mixedMultiplicity K R sigma H (omittedLabelFinset sigma H T D)
    (sigma.obj (OrderedARWord.positionEquiv sigma H T x))
    (OrderedARWord.positionEquiv sigma H T a)

/-- The directed standard vector evaluated at word positions is the ordinary
Kronecker delta. -/
theorem directedSingle_positionEquiv_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (a x : Fin (OrderedARWord.word sigma H T).length) :
    directedSingle sigma H
        (OrderedARWord.positionEquiv sigma H T x)
        (OrderedARWord.positionEquiv sigma H T a) =
      if a = x then 1 else 0 := by
  letI := directedLinearOrder sigma H
  by_cases hax : a = x
  · subst a
    simp [directedSingle]
  · have hlabel : OrderedARWord.positionEquiv sigma H T x ≠
        OrderedARWord.positionEquiv sigma H T a := by
      intro h
      exact hax ((OrderedARWord.positionEquiv sigma H T).injective h.symm)
    simp [directedSingle, hax]

/-- Literal first branch of equation `eq:directed-coordinate-recurrence`. -/
theorem wordMixedMultiplicity_eq_delta_of_not_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hx : x ∉ D) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      if a = x then 1 else 0 := by
  have hx' : OrderedARWord.positionEquiv sigma H T x ∉
      omittedLabelFinset sigma H T D := by
    simpa only [mem_omittedLabelFinset_iff] using hx
  have h := orderedARWord_mixedMultiplicity_retained
    (K := K) (R := R) sigma H T (omittedLabelFinset sigma H T D)
    x (OrderedARWord.positionEquiv sigma H T a) hx'
  rw [← directedSingle_positionEquiv_apply sigma H T a x]
  exact h

/-- Literal repeated-occurrence branch of
equation `eq:directed-coordinate-recurrence`. -/
theorem wordMixedMultiplicity_recurrence_of_isPrevious
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a p x : Fin (OrderedARWord.word sigma H T).length)
    (hpx : ARWord.IsPrevious (OrderedARWord.word sigma H T) p x)
    (hx : x ∈ D) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      (if a = x then 1 else 0) +
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1 -
        wordMixedMultiplicity (K := K) (R := R) sigma H T D a p := by
  have hx' : OrderedARWord.positionEquiv sigma H T x ∈
      omittedLabelFinset sigma H T D := by
    simpa only [mem_omittedLabelFinset_iff] using hx
  have h := orderedARWord_mixedMultiplicity_repeated
    (K := K) (R := R) sigma H T (omittedLabelFinset sigma H T D)
    p x hpx hx' (OrderedARWord.positionEquiv sigma H T a)
  rw [← directedSingle_positionEquiv_apply sigma H T a x]
  simpa only [wordMixedMultiplicity] using h

/-- Literal first-occurrence branch of
equation `eq:directed-coordinate-recurrence`. -/
theorem wordMixedMultiplicity_recurrence_of_no_previous
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length)
    (hfirst : ¬ ∃ p, ARWord.IsPrevious
      (OrderedARWord.word sigma H T) p x)
    (hx : x ∈ D) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      (if a = x then 1 else 0) +
        ∑ y : {y : Fin (OrderedARWord.word sigma H T).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.word sigma H T) y x},
          wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1 := by
  have hxProjective :
      Projective
        (sigma.obj (OrderedARWord.positionEquiv sigma H T x)) := by
    by_contra hnonprojective
    apply hfirst
    obtain ⟨p, hp⟩ :=
      (OrderedARWord.exists_previous_position_iff_not_projective
        sigma H T (OrderedARWord.positionEquiv sigma H T x)).2
        hnonprojective
    exact ⟨p, by
      simpa only [OrderedARWord.positionEquiv_apply_symm_apply] using hp⟩
  have hx' : OrderedARWord.positionEquiv sigma H T x ∈
      omittedLabelFinset sigma H T D := by
    simpa only [mem_omittedLabelFinset_iff] using hx
  have h := orderedARWord_mixedMultiplicity_first
    (K := K) (R := R) sigma H T (omittedLabelFinset sigma H T D)
    x hxProjective hx' (OrderedARWord.positionEquiv sigma H T a)
  rw [← directedSingle_positionEquiv_apply sigma H T a x]
  simpa only [wordMixedMultiplicity] using h

/-- A fixed row of the word-coordinate matrix vanishes strictly before its
diagonal position, for every omission set. -/
theorem wordMixedMultiplicity_eq_zero_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length))
    {a x : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length}
    (hxa : x < a) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x = 0 := by
  let motive :
      Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length → Prop :=
    fun x ↦ x < a →
      wordMixedMultiplicity (K := K) (R := R) sigma H T D a x = 0
  exact (Finite.to_wellFoundedLT.wf.induction (C := motive) x (fun x ih ↦ by
    change x < a →
      wordMixedMultiplicity (K := K) (R := R) sigma H T D a x = 0
    intro hxa
    have hax : a ≠ x := Ne.symm (ne_of_lt hxa)
    by_cases hxD : x ∈ D
    · by_cases hprev : ∃ p,
          ARWord.IsPrevious (DirectedAROrbit.OrderedARWord.word sigma H T) p x
      · obtain ⟨p, hp⟩ := hprev
        rw [wordMixedMultiplicity_recurrence_of_isPrevious
          (K := K) (R := R) sigma H T D a p x hp hxD]
        have hpzero :
            wordMixedMultiplicity (K := K) (R := R) sigma H T D a p = 0 :=
          ih p hp.1 (hp.1.trans hxa)
        have hsum :
            (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                ARWord.IsMiddle
                  (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                  (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
              wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) = 0 := by
          apply Finset.sum_eq_zero
          intro y _
          exact ih y.1 y.property.2.1 (y.property.2.1.trans hxa)
        rw [hsum, hpzero]
        simp [hax]
      · rw [wordMixedMultiplicity_recurrence_of_no_previous
          (K := K) (R := R) sigma H T D a x hprev hxD]
        have hsum :
            (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                ARWord.IsMiddle
                  (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                  (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
              wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) = 0 := by
          apply Finset.sum_eq_zero
          intro y _
          exact ih y.1 y.property.2.1 (y.property.2.1.trans hxa)
        rw [hsum]
        simp [hax]
    · rw [wordMixedMultiplicity_eq_delta_of_not_mem
        (K := K) (R := R) sigma H T D a x hxD]
      simp [hax])) hxa

/-- Every word-coordinate row has diagonal entry one, independently of the
omission set. -/
theorem wordMixedMultiplicity_self_eq_one
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length))
    (a : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a a = 1 := by
  by_cases haD : a ∈ D
  · by_cases hprev : ∃ p,
        ARWord.IsPrevious (DirectedAROrbit.OrderedARWord.word sigma H T) p a
    · obtain ⟨p, hp⟩ := hprev
      rw [wordMixedMultiplicity_recurrence_of_isPrevious
        (K := K) (R := R) sigma H T D a p a hp haD]
      have hpzero :
          wordMixedMultiplicity (K := K) (R := R) sigma H T D a p = 0 :=
        wordMixedMultiplicity_eq_zero_of_lt
          (K := K) (R := R) sigma H T D hp.1
      have hsum :
          (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
              ARWord.IsMiddle
                (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                (DirectedAROrbit.OrderedARWord.word sigma H T) y a},
            wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        exact wordMixedMultiplicity_eq_zero_of_lt
          (K := K) (R := R) sigma H T D y.property.2.1
      rw [hsum, hpzero]
      simp
    · rw [wordMixedMultiplicity_recurrence_of_no_previous
        (K := K) (R := R) sigma H T D a a hprev haD]
      have hsum :
          (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
              ARWord.IsMiddle
                (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                (DirectedAROrbit.OrderedARWord.word sigma H T) y a},
            wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        exact wordMixedMultiplicity_eq_zero_of_lt
          (K := K) (R := R) sigma H T D y.property.2.1
      rw [hsum]
      simp
  · rw [wordMixedMultiplicity_eq_delta_of_not_mem
      (K := K) (R := R) sigma H T D a a haD]
    simp

/-- The manuscript's row-dependent omission set
`D[a] = {a} ∪ {d ∈ D | a < d}`. -/
def rowRestrictedOmissions
    {n : ℕ} (D : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  insert a (D.filter fun d ↦ a < d)

@[simp]
theorem mem_rowRestrictedOmissions_iff
    {n : ℕ} (D : Finset (Fin n)) (a x : Fin n) :
    x ∈ rowRestrictedOmissions D a ↔ x = a ∨ (x ∈ D ∧ a < x) := by
  simp [rowRestrictedOmissions]

/-- Equation `eq:directed-row-transport`: row `a` depends only on whether
positions strictly after `a` are omitted, after adjoining `a` itself. -/
theorem wordMixedMultiplicity_row_transport
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length))
    (a x : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length) :
    wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      wordMixedMultiplicity (K := K) (R := R) sigma H T
        (rowRestrictedOmissions D a) a x := by
  let motive :
      Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length → Prop :=
    fun x ↦
      wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
        wordMixedMultiplicity (K := K) (R := R) sigma H T
          (rowRestrictedOmissions D a) a x
  exact Finite.to_wellFoundedLT.wf.induction (C := motive) x (fun x ih ↦ by
    change wordMixedMultiplicity (K := K) (R := R) sigma H T D a x =
      wordMixedMultiplicity (K := K) (R := R) sigma H T
        (rowRestrictedOmissions D a) a x
    rcases lt_trichotomy x a with hxa | hxa | hax
    · rw [wordMixedMultiplicity_eq_zero_of_lt
          (K := K) (R := R) sigma H T D hxa,
        wordMixedMultiplicity_eq_zero_of_lt
          (K := K) (R := R) sigma H T (rowRestrictedOmissions D a) hxa]
    · subst x
      rw [wordMixedMultiplicity_self_eq_one
          (K := K) (R := R) sigma H T D a,
        wordMixedMultiplicity_self_eq_one
          (K := K) (R := R) sigma H T (rowRestrictedOmissions D a) a]
    · have hxmem : x ∈ rowRestrictedOmissions D a ↔ x ∈ D := by
        simp [rowRestrictedOmissions, hax, ne_of_gt hax]
      by_cases hxD : x ∈ D
      · have hxR : x ∈ rowRestrictedOmissions D a := hxmem.2 hxD
        by_cases hprev : ∃ p,
            ARWord.IsPrevious
              (DirectedAROrbit.OrderedARWord.word sigma H T) p x
        · obtain ⟨p, hp⟩ := hprev
          rw [wordMixedMultiplicity_recurrence_of_isPrevious
              (K := K) (R := R) sigma H T D a p x hp hxD,
            wordMixedMultiplicity_recurrence_of_isPrevious
              (K := K) (R := R) sigma H T
              (rowRestrictedOmissions D a) a p x hp hxR]
          have hpEq := ih p hp.1
          have hsum :
              (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                  ARWord.IsMiddle
                    (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                    (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
                wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) =
                ∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                    ARWord.IsMiddle
                      (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                      (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
                  wordMixedMultiplicity (K := K) (R := R) sigma H T
                    (rowRestrictedOmissions D a) a y.1 := by
            apply Finset.sum_congr rfl
            intro y _
            exact ih y.1 y.property.2.1
          rw [hsum, hpEq]
        · rw [wordMixedMultiplicity_recurrence_of_no_previous
              (K := K) (R := R) sigma H T D a x hprev hxD,
            wordMixedMultiplicity_recurrence_of_no_previous
              (K := K) (R := R) sigma H T
              (rowRestrictedOmissions D a) a x hprev hxR]
          have hsum :
              (∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                  ARWord.IsMiddle
                    (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                    (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
                wordMixedMultiplicity (K := K) (R := R) sigma H T D a y.1) =
                ∑ y : {y : Fin (DirectedAROrbit.OrderedARWord.word sigma H T).length //
                    ARWord.IsMiddle
                      (DirectedAROrbit.OrderedARWord.orbitGraph sigma H T)
                      (DirectedAROrbit.OrderedARWord.word sigma H T) y x},
                  wordMixedMultiplicity (K := K) (R := R) sigma H T
                    (rowRestrictedOmissions D a) a y.1 := by
            apply Finset.sum_congr rfl
            intro y _
            exact ih y.1 y.property.2.1
          rw [hsum]
      · have hxR : x ∉ rowRestrictedOmissions D a := by
          intro h
          exact hxD (hxmem.1 h)
        rw [wordMixedMultiplicity_eq_delta_of_not_mem
            (K := K) (R := R) sigma H T D a x hxD,
          wordMixedMultiplicity_eq_delta_of_not_mem
            (K := K) (R := R) sigma H T
            (rowRestrictedOmissions D a) a x hxR])

/-! ## Explicit directed-order recurrence -/

noncomputable local instance orderedMiddlePositionsFintypeFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    Fintype {y : Fin (OrderedARWord.wordFor sigma H T E).length //
      ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
        (OrderedARWord.wordFor sigma H T E) y x} :=
  Fintype.ofFinite _

/-- The mixed coordinate of a chosen right almost-split middle is the sum
over the literal middle positions of any explicit-order AR word. -/
theorem chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositionsFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset Iota)
    (x : Fin (OrderedARWord.wordFor sigma H T E).length) (a : Iota) :
    mixedMultiplicity K R sigma H D
        (OrderedARWord.chosenRightARAt sigma T
          (OrderedARWord.positionEquivFor sigma H T E x)).middle a =
      ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.wordFor sigma H T E) y x},
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquivFor sigma H T E y.1)) a := by
  let A := OrderedARWord.chosenRightARAt sigma T
    (OrderedARWord.positionEquivFor sigma H T E x)
  calc
    mixedMultiplicity K R sigma H D A.middle a =
        mixedMultiplicity K R sigma H D
          (sigma.sumOver A.index A.label) a :=
      congrFun (mixedMultiplicity_iso K R sigma H D A.decomposition) a
    _ = (∑ t : A.index,
        mixedMultiplicity K R sigma H D (sigma.obj (A.label t))) a :=
      congrFun
        (mixedMultiplicity_biproduct_finite K R sigma H D
          (fun t : A.index ↦ sigma.obj (A.label t))) a
    _ = ∑ t : A.index,
        mixedMultiplicity K R sigma H D (sigma.obj (A.label t)) a := by
      simp only [Finset.sum_apply]
    _ = ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
          ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
            (OrderedARWord.wordFor sigma H T E) y x},
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquivFor sigma H T E y.1)) a := by
      apply Fintype.sum_equiv
        (OrderedARWord.middleIndexEquivFor sigma K H T E x)
      intro t
      simp [OrderedARWord.middleIndexEquivFor, A]

/-- Repeated-occurrence branch of the mixed-coordinate recurrence for an
explicit directed order. -/
theorem orderedARWord_mixedMultiplicity_repeatedFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset Iota)
    (p x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hpx : ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p x)
    (hx : OrderedARWord.positionEquivFor sigma H T E x ∈ D)
    (a : Iota) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) a =
      directedSingle sigma H
          (OrderedARWord.positionEquivFor sigma H T E x) a +
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj
              (OrderedARWord.positionEquivFor sigma H T E y.1)) a -
        mixedMultiplicity K R sigma H D
          (sigma.obj (OrderedARWord.positionEquivFor sigma H T E p)) a := by
  have hxNonprojective :
      ¬ Projective
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) :=
    (OrderedARWord.exists_previous_positionFor_iff_not_projective
      sigma H T E (OrderedARWord.positionEquivFor sigma H T E x)).1
      ⟨p, by
        simpa only [OrderedARWord.positionEquivFor_apply_symm_apply]
          using hpx⟩
  let xn : sigma.NonprojectiveLabel :=
    ⟨OrderedARWord.positionEquivFor sigma H T E x, hxNonprojective⟩
  have hpTau : OrderedARWord.positionEquivFor sigma H T E p =
      (T.arTranslation sigma xn).1 :=
    (OrderedARWord.isPrevious_positionFor_iff_eq_arTranslation
      sigma H T E xn p).1
      (by simpa only [xn,
        OrderedARWord.positionEquivFor_apply_symm_apply] using hpx)
  have hmesh := congrFun
    (chosenRightAR_mixedMultiplicity_mesh
      (K := K) (R := R) sigma H T D xn hx) a
  have hmiddle :=
    chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositionsFor
      (K := K) (R := R) sigma H T E D x a
  have hmiddle' :
      mixedMultiplicity K R sigma H D
          (T.chosenRightAR sigma xn).middle a =
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj
              (OrderedARWord.positionEquivFor sigma H T E y.1)) a := by
    simpa [OrderedARWord.chosenRightARAt, xn, hxNonprojective] using hmiddle
  simp only [Pi.add_apply] at hmesh
  change mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) a +
      mixedMultiplicity K R sigma H D
        (sigma.obj (T.arTranslation sigma xn).1) a =
    mixedMultiplicity K R sigma H D
        (T.chosenRightAR sigma xn).middle a +
      directedSingle sigma H
        (OrderedARWord.positionEquivFor sigma H T E x) a at hmesh
  rw [hmiddle', ← hpTau] at hmesh
  omega

/-- First-occurrence projective-boundary branch for an explicit directed
order. -/
theorem orderedARWord_mixedMultiplicity_firstFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset Iota)
    (x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hxProjective : Projective
      (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)))
    (hx : OrderedARWord.positionEquivFor sigma H T E x ∈ D)
    (a : Iota) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) a =
      directedSingle sigma H
          (OrderedARWord.positionEquivFor sigma H T E x) a +
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj
              (OrderedARWord.positionEquivFor sigma H T E y.1)) a := by
  have hmesh := congrFun
    (projectiveBoundary_mixedMultiplicity_mesh
      (K := K) (R := R) sigma H D
      (OrderedARWord.positionEquivFor sigma H T E x)
      hxProjective hx) a
  have hmiddle :=
    chosenRightARAt_middle_mixedMultiplicity_eq_sum_middlePositionsFor
      (K := K) (R := R) sigma H T E D x a
  have hmiddle' :
      mixedMultiplicity K R sigma H D
          (sigma.projectiveBoundaryRadical
            (OrderedARWord.positionEquivFor sigma H T E x)) a =
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          mixedMultiplicity K R sigma H D
            (sigma.obj
              (OrderedARWord.positionEquivFor sigma H T E y.1)) a := by
    simp only [OrderedARWord.chosenRightARAt,
      dif_pos hxProjective] at hmiddle
    change mixedMultiplicity K R sigma H D
        (sigma.projectiveBoundaryRadical
          (OrderedARWord.positionEquivFor sigma H T E x)) a = _ at hmiddle
    exact hmiddle
  simp only [Pi.add_apply] at hmesh
  rw [hmiddle'] at hmesh
  omega

/-- Transport explicit-order word positions to skeleton labels. -/
def omittedLabelFinsetFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length)) :
    Finset Iota := by
  classical
  exact D.map
    (OrderedARWord.positionEquivFor sigma H T E).toEmbedding

@[simp] theorem mem_omittedLabelFinsetFor_iff
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    OrderedARWord.positionEquivFor sigma H T E x ∈
        omittedLabelFinsetFor sigma H T E D ↔ x ∈ D := by
  classical
  simp [omittedLabelFinsetFor]

/-- The exact position-indexed mixed multiplicity for an explicit order.
The underlying mixed-coordinate vector is independent of this order. -/
def wordMixedMultiplicityFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) : ℤ :=
  mixedMultiplicity K R sigma H (omittedLabelFinsetFor sigma H T E D)
    (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x))
    (OrderedARWord.positionEquivFor sigma H T E a)

/-- The explicit omitted-label set specializes definitionally to the
default chosen-order definition. -/
theorem omittedLabelFinsetFor_chosen
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length)) :
    omittedLabelFinsetFor sigma H T (.chosen sigma H) D =
      omittedLabelFinset sigma H T D := by
  rfl

omit [IsAlgClosed K] [FiniteDimensional K R] in
/-- The explicit position-indexed coordinate specializes definitionally to
the existing default-order coordinate. -/
theorem wordMixedMultiplicityFor_chosen
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (D : Finset (Fin (OrderedARWord.word sigma H T).length))
    (a x : Fin (OrderedARWord.word sigma H T).length) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T (.chosen sigma H) D a x =
      wordMixedMultiplicity (K := K) (R := R) sigma H T D a x := by
  rfl

/-- The directed standard vector remains the ordinary Kronecker delta after
any explicit position equivalence. -/
theorem directedSingle_positionEquivFor_apply
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    directedSingle sigma H
        (OrderedARWord.positionEquivFor sigma H T E x)
        (OrderedARWord.positionEquivFor sigma H T E a) =
      if a = x then 1 else 0 := by
  letI := directedLinearOrder sigma H
  by_cases hax : a = x
  · subst a
    simp [directedSingle]
  · have hlabel : OrderedARWord.positionEquivFor sigma H T E x ≠
        OrderedARWord.positionEquivFor sigma H T E a := by
      intro h
      exact hax
        ((OrderedARWord.positionEquivFor sigma H T E).injective h.symm)
    simp [directedSingle, hax]

/-- Retained-column branch for an explicit-order position. -/
theorem orderedARWord_mixedMultiplicity_retainedFor
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset Iota)
    (x : Fin (OrderedARWord.wordFor sigma H T E).length) (a : Iota)
    (hx : OrderedARWord.positionEquivFor sigma H T E x ∉ D) :
    mixedMultiplicity K R sigma H D
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) a =
      directedSingle sigma H
        (OrderedARWord.positionEquivFor sigma H T E x) a := by
  letI := directedLinearOrder sigma H
  by_cases hax : a = OrderedARWord.positionEquivFor sigma H T E x
  · subst a
    rw [H.mixedMultiplicity_obj_self K R sigma D hx]
    simp [directedSingle]
  · rw [H.mixedMultiplicity_obj_ne K R sigma D hx hax]
    have hxa : OrderedARWord.positionEquivFor sigma H T E x ≠ a :=
      Ne.symm hax
    simp [directedSingle, hxa]

/-- Literal retained-column branch for `wordMixedMultiplicityFor`. -/
theorem wordMixedMultiplicityFor_eq_delta_of_not_mem
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hx : x ∉ D) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x = if a = x then 1 else 0 := by
  have hx' : OrderedARWord.positionEquivFor sigma H T E x ∉
      omittedLabelFinsetFor sigma H T E D := by
    simpa only [mem_omittedLabelFinsetFor_iff] using hx
  have h := orderedARWord_mixedMultiplicity_retainedFor
    (K := K) (R := R) sigma H T E
    (omittedLabelFinsetFor sigma H T E D)
    x (OrderedARWord.positionEquivFor sigma H T E a) hx'
  rw [← directedSingle_positionEquivFor_apply sigma H T E a x]
  exact h

/-- Literal repeated-occurrence recurrence for an explicit order. -/
theorem wordMixedMultiplicityFor_recurrence_of_isPrevious
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a p x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hpx : ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p x)
    (hx : x ∈ D) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      (if a = x then 1 else 0) +
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          wordMixedMultiplicityFor (K := K) (R := R)
            sigma H T E D a y.1 -
        wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a p := by
  have hx' : OrderedARWord.positionEquivFor sigma H T E x ∈
      omittedLabelFinsetFor sigma H T E D := by
    simpa only [mem_omittedLabelFinsetFor_iff] using hx
  have h := orderedARWord_mixedMultiplicity_repeatedFor
    (K := K) (R := R) sigma H T E
    (omittedLabelFinsetFor sigma H T E D)
    p x hpx hx' (OrderedARWord.positionEquivFor sigma H T E a)
  rw [← directedSingle_positionEquivFor_apply sigma H T E a x]
  simpa only [wordMixedMultiplicityFor] using h

/-- Literal first-occurrence recurrence for an explicit order. -/
theorem wordMixedMultiplicityFor_recurrence_of_no_previous
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length)
    (hfirst : ¬ ∃ p,
      ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p x)
    (hx : x ∈ D) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      (if a = x then 1 else 0) +
        ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
            ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
              (OrderedARWord.wordFor sigma H T E) y x},
          wordMixedMultiplicityFor (K := K) (R := R)
            sigma H T E D a y.1 := by
  have hxProjective :
      Projective
        (sigma.obj (OrderedARWord.positionEquivFor sigma H T E x)) := by
    by_contra hnonprojective
    apply hfirst
    obtain ⟨p, hp⟩ :=
      (OrderedARWord.exists_previous_positionFor_iff_not_projective
        sigma H T E
        (OrderedARWord.positionEquivFor sigma H T E x)).2 hnonprojective
    exact ⟨p, by
      simpa only [OrderedARWord.positionEquivFor_apply_symm_apply] using hp⟩
  have hx' : OrderedARWord.positionEquivFor sigma H T E x ∈
      omittedLabelFinsetFor sigma H T E D := by
    simpa only [mem_omittedLabelFinsetFor_iff] using hx
  have h := orderedARWord_mixedMultiplicity_firstFor
    (K := K) (R := R) sigma H T E
    (omittedLabelFinsetFor sigma H T E D)
    x hxProjective hx' (OrderedARWord.positionEquivFor sigma H T E a)
  rw [← directedSingle_positionEquivFor_apply sigma H T E a x]
  simpa only [wordMixedMultiplicityFor] using h

/-- Every explicit-order coordinate row vanishes strictly before its
diagonal position. -/
theorem wordMixedMultiplicityFor_eq_zero_of_lt
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    {a x : Fin (OrderedARWord.wordFor sigma H T E).length}
    (hxa : x < a) :
    wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D a x = 0 := by
  let motive : Fin (OrderedARWord.wordFor sigma H T E).length → Prop :=
    fun x ↦ x < a →
      wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x = 0
  exact (Finite.to_wellFoundedLT.wf.induction (C := motive) x
    (fun x ih ↦ by
      change x < a →
        wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x = 0
      intro hxa
      have hax : a ≠ x := Ne.symm (ne_of_lt hxa)
      by_cases hxD : x ∈ D
      · by_cases hprev : ∃ p,
            ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p x
        · obtain ⟨p, hp⟩ := hprev
          rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
            (K := K) (R := R) sigma H T E D a p x hp hxD]
          have hpzero : wordMixedMultiplicityFor (K := K) (R := R)
              sigma H T E D a p = 0 :=
            ih p hp.1 (hp.1.trans hxa)
          have hsum :
              (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                  ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                    (OrderedARWord.wordFor sigma H T E) y x},
                wordMixedMultiplicityFor (K := K) (R := R)
                  sigma H T E D a y.1) = 0 := by
            apply Finset.sum_eq_zero
            intro y _
            exact ih y.1 y.property.2.1 (y.property.2.1.trans hxa)
          rw [hsum, hpzero]
          simp [hax]
        · rw [wordMixedMultiplicityFor_recurrence_of_no_previous
            (K := K) (R := R) sigma H T E D a x hprev hxD]
          have hsum :
              (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                  ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                    (OrderedARWord.wordFor sigma H T E) y x},
                wordMixedMultiplicityFor (K := K) (R := R)
                  sigma H T E D a y.1) = 0 := by
            apply Finset.sum_eq_zero
            intro y _
            exact ih y.1 y.property.2.1 (y.property.2.1.trans hxa)
          rw [hsum]
          simp [hax]
      · rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
          (K := K) (R := R) sigma H T E D a x hxD]
        simp [hax])) hxa

/-- Every explicit-order coordinate row has diagonal entry one. -/
theorem wordMixedMultiplicityFor_self_eq_one
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a : Fin (OrderedARWord.wordFor sigma H T E).length) :
    wordMixedMultiplicityFor (K := K) (R := R)
      sigma H T E D a a = 1 := by
  by_cases haD : a ∈ D
  · by_cases hprev : ∃ p,
        ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p a
    · obtain ⟨p, hp⟩ := hprev
      rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
        (K := K) (R := R) sigma H T E D a p a hp haD]
      have hpzero : wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a p = 0 :=
        wordMixedMultiplicityFor_eq_zero_of_lt
          (K := K) (R := R) sigma H T E D hp.1
      have hsum :
          (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
              ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                (OrderedARWord.wordFor sigma H T E) y a},
            wordMixedMultiplicityFor (K := K) (R := R)
              sigma H T E D a y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        exact wordMixedMultiplicityFor_eq_zero_of_lt
          (K := K) (R := R) sigma H T E D y.property.2.1
      rw [hsum, hpzero]
      simp
    · rw [wordMixedMultiplicityFor_recurrence_of_no_previous
        (K := K) (R := R) sigma H T E D a a hprev haD]
      have hsum :
          (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
              ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                (OrderedARWord.wordFor sigma H T E) y a},
            wordMixedMultiplicityFor (K := K) (R := R)
              sigma H T E D a y.1) = 0 := by
        apply Finset.sum_eq_zero
        intro y _
        exact wordMixedMultiplicityFor_eq_zero_of_lt
          (K := K) (R := R) sigma H T E D y.property.2.1
      rw [hsum]
      simp
  · rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
      (K := K) (R := R) sigma H T E D a a haD]
    simp

/-- Explicit-order form of the row-transport equation. -/
theorem wordMixedMultiplicityFor_row_transport
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (D : Finset (Fin (OrderedARWord.wordFor sigma H T E).length))
    (a x : Fin (OrderedARWord.wordFor sigma H T E).length) :
    wordMixedMultiplicityFor (K := K) (R := R)
        sigma H T E D a x =
      wordMixedMultiplicityFor (K := K) (R := R) sigma H T E
        (rowRestrictedOmissions D a) a x := by
  let motive : Fin (OrderedARWord.wordFor sigma H T E).length → Prop :=
    fun x ↦
      wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x =
        wordMixedMultiplicityFor (K := K) (R := R) sigma H T E
          (rowRestrictedOmissions D a) a x
  exact Finite.to_wellFoundedLT.wf.induction (C := motive) x
    (fun x ih ↦ by
      change wordMixedMultiplicityFor (K := K) (R := R)
          sigma H T E D a x =
        wordMixedMultiplicityFor (K := K) (R := R) sigma H T E
          (rowRestrictedOmissions D a) a x
      rcases lt_trichotomy x a with hxa | hxa | hax
      · rw [wordMixedMultiplicityFor_eq_zero_of_lt
            (K := K) (R := R) sigma H T E D hxa,
          wordMixedMultiplicityFor_eq_zero_of_lt
            (K := K) (R := R) sigma H T E
            (rowRestrictedOmissions D a) hxa]
      · subst x
        rw [wordMixedMultiplicityFor_self_eq_one
            (K := K) (R := R) sigma H T E D a,
          wordMixedMultiplicityFor_self_eq_one
            (K := K) (R := R) sigma H T E
            (rowRestrictedOmissions D a) a]
      · have hxmem : x ∈ rowRestrictedOmissions D a ↔ x ∈ D := by
          simp [rowRestrictedOmissions, hax, ne_of_gt hax]
        by_cases hxD : x ∈ D
        · have hxR : x ∈ rowRestrictedOmissions D a := hxmem.2 hxD
          by_cases hprev : ∃ p,
              ARWord.IsPrevious (OrderedARWord.wordFor sigma H T E) p x
          · obtain ⟨p, hp⟩ := hprev
            rw [wordMixedMultiplicityFor_recurrence_of_isPrevious
                (K := K) (R := R) sigma H T E D a p x hp hxD,
              wordMixedMultiplicityFor_recurrence_of_isPrevious
                (K := K) (R := R) sigma H T E
                (rowRestrictedOmissions D a) a p x hp hxR]
            have hpEq := ih p hp.1
            have hsum :
                (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                    ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                      (OrderedARWord.wordFor sigma H T E) y x},
                  wordMixedMultiplicityFor (K := K) (R := R)
                    sigma H T E D a y.1) =
                  ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                      ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                        (OrderedARWord.wordFor sigma H T E) y x},
                    wordMixedMultiplicityFor (K := K) (R := R)
                      sigma H T E (rowRestrictedOmissions D a) a y.1 := by
              apply Finset.sum_congr rfl
              intro y _
              exact ih y.1 y.property.2.1
            rw [hsum, hpEq]
          · rw [wordMixedMultiplicityFor_recurrence_of_no_previous
                (K := K) (R := R) sigma H T E D a x hprev hxD,
              wordMixedMultiplicityFor_recurrence_of_no_previous
                (K := K) (R := R) sigma H T E
                (rowRestrictedOmissions D a) a x hprev hxR]
            have hsum :
                (∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                    ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                      (OrderedARWord.wordFor sigma H T E) y x},
                  wordMixedMultiplicityFor (K := K) (R := R)
                    sigma H T E D a y.1) =
                  ∑ y : {y : Fin (OrderedARWord.wordFor sigma H T E).length //
                      ARWord.IsMiddle (OrderedARWord.orbitGraph sigma H T)
                        (OrderedARWord.wordFor sigma H T E) y x},
                    wordMixedMultiplicityFor (K := K) (R := R)
                      sigma H T E (rowRestrictedOmissions D a) a y.1 := by
              apply Finset.sum_congr rfl
              intro y _
              exact ih y.1 y.property.2.1
            rw [hsum]
        · have hxR : x ∉ rowRestrictedOmissions D a := by
            intro h
            exact hxD (hxmem.1 h)
          rw [wordMixedMultiplicityFor_eq_delta_of_not_mem
              (K := K) (R := R) sigma H T E D a x hxD,
            wordMixedMultiplicityFor_eq_delta_of_not_mem
              (K := K) (R := R) sigma H T E
              (rowRestrictedOmissions D a) a x hxR])

end IntegralTransport

end OpConjecture.RepresentationDirected
