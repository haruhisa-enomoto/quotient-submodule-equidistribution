import OpConjecture.RepresentationTheory.StandardQHSemantics
import OpConjecture.Foundation.RingTheory.KrullSchmidt.Indecomposable

/-!
# Simple tops and projective covers

An indecomposable finite-length projective module has a simple radical
quotient, and that quotient map is its canonical essential epimorphism.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.ProjectiveSimpleTop

universe u v w

variable {R : Type u} [Ring R]

/-- The quotient by any proper submodule of a projective module with local
endomorphism ring is an essential epimorphism.

The proof in fact only uses properness of the kernel: lifting along a
surjective composite produces an endomorphism `e`; localness says that `e` or
`1 - e` is invertible, and the latter would force the quotient map to vanish.
-/
theorem surjective_of_quotient_comp_surjective
    {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] [IsLocalRing (Module.End R P)]
    {N : Submodule R P} (hN : N ≠ ⊤)
    {Z : Type w} [AddCommGroup Z] [Module R Z]
    (g : Z →ₗ[R] P)
    (hg : Function.Surjective (N.mkQ.comp g)) :
    Function.Surjective g := by
  obtain ⟨h, hh⟩ :=
    Module.projective_lifting_property
      (N.mkQ.comp g) N.mkQ hg
  let e : Module.End R P := g.comp h
  have heq : N.mkQ.comp e = N.mkQ := by
    simpa [e, LinearMap.comp_assoc] using hh
  let e' : Module.End R P := 1 - e
  have hsum : IsUnit (e + e') := by
    simp [e']
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with he | he'
  · have hesurj : Function.Surjective e :=
      ((Module.End.isUnit_iff e).mp he).2
    intro p
    obtain ⟨x, hx⟩ := hesurj p
    exact ⟨h x, by simpa [e] using hx⟩
  · have he'Surj : Function.Surjective e' :=
      ((Module.End.isUnit_iff e').mp he').2
    have hzero : N.mkQ.comp e' = 0 := by
      ext p
      have hp := DFunLike.congr_fun heq p
      simp only [LinearMap.comp_apply] at hp
      change N.mkQ p - N.mkQ (e p) = 0
      rw [hp]
      exact sub_self _
    have hqzero : N.mkQ = 0 := by
      ext p
      obtain ⟨x, hx⟩ := he'Surj p
      rw [← hx]
      exact DFunLike.congr_fun hzero x
    exfalso
    apply hN
    rw [← N.ker_mkQ, hqzero, LinearMap.ker_zero]

/-- A finite projective module with local endomorphism ring has a unique
maximal submodule, namely its module Jacobson radical. -/
theorem jacobson_isCoatom_of_local_end
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)] :
    IsCoatom (Module.jacobson R P) := by
  obtain ⟨N, hNcoatom, -⟩ :=
    (eq_top_or_exists_le_coatom
      (⊥ : Submodule R P)).resolve_left bot_ne_top
  have hUnique :
      ∀ M : Submodule R P, IsCoatom M → M = N := by
    intro M hMcoatom
    by_contra hMN
    have hsup : N ⊔ M = ⊤ :=
      hNcoatom.sup_eq_top_of_ne hMcoatom (Ne.symm hMN)
    have hcompSurj :
        Function.Surjective (N.mkQ.comp M.subtype) := by
      rw [← LinearMap.range_eq_top]
      rw [LinearMap.range_comp, Submodule.range_subtype]
      exact (N.map_mkQ_eq_top M).mpr hsup
    have hsubtypeSurj : Function.Surjective M.subtype :=
      surjective_of_quotient_comp_surjective hNcoatom.ne_top
        M.subtype hcompSurj
    apply hMcoatom.ne_top
    rw [← Submodule.range_subtype M, LinearMap.range_eq_top]
    exact hsubtypeSurj
  have hjac : Module.jacobson R P = N := by
    apply le_antisymm
    · exact sInf_le hNcoatom
    · rw [Module.jacobson, le_sInf_iff]
      intro M hM
      rw [hUnique M hM]
  rw [hjac]
  exact hNcoatom

/-- The top of a finite projective module with local endomorphism ring is
simple. -/
theorem simple_top_of_local_end
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)] :
    IsSimpleModule R (P ⧸ Module.jacobson R P) :=
  isSimpleModule_iff_isCoatom.mpr
    jacobson_isCoatom_of_local_end

/-- An indecomposable finite-length projective module has simple top. -/
theorem simple_top_of_indec_projective
    {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (hfinite : IsFiniteLength R P)
    (hindec : OpConjecture.Foundation.IsIndecomposableModule R P) :
    IsSimpleModule R (P ⧸ Module.jacobson R P) := by
  letI : Nontrivial P := hindec.nontrivial
  letI : IsLocalRing (Module.End R P) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable hfinite hindec
  exact simple_top_of_local_end

/-! ## Epimorphisms to simple modules -/

/-- Every epimorphism from a finite projective with local endomorphism ring
to a simple module has the module Jacobson radical as its kernel. -/
theorem ker_eq_jacobson_of_surjective_to_simple
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)]
    {S : Type w} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (f : P →ₗ[R] S) (hf : Function.Surjective f) :
    LinearMap.ker f = Module.jacobson R P := by
  have hker : IsCoatom (LinearMap.ker f) := by
    rw [← isSimpleModule_iff_isCoatom]
    exact
      (f.quotKerEquivOfSurjective hf).isSimpleModule_iff.mpr
        (inferInstance : IsSimpleModule R S)
  have hrad : IsCoatom (Module.jacobson R P) :=
    jacobson_isCoatom_of_local_end
  have hle :
      Module.jacobson R P ≤ LinearMap.ker f :=
    sInf_le hker
  exact (hrad.le_iff_eq hker.ne_top).mp hle

/-- The semisimple top of the source is canonically linearly equivalent to
any simple target of a surjective map. -/
def topLinearEquivOfSurjectiveToSimple
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)]
    {S : Type w} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (f : P →ₗ[R] S) (hf : Function.Surjective f) :
    (P ⧸ Module.jacobson R P) ≃ₗ[R] S := by
  rw [← ker_eq_jacobson_of_surjective_to_simple f hf]
  exact f.quotKerEquivOfSurjective hf

/-! ## Categorical projective-cover package -/

/-- The quotient map from a module to its semisimple top, regarded as a
`ModuleCat` morphism. -/
def jacobsonQuotientMap
    {P : Type v} [AddCommGroup P] [Module R P] :
    ModuleCat.of R P ⟶
      ModuleCat.of R (P ⧸ Module.jacobson R P) :=
  ModuleCat.ofHom (Module.jacobson R P).mkQ

/-- For a finite projective module with local endomorphism ring, the
categorical quotient map to the top is an essential epimorphism. -/
theorem jacobsonQuotientMap_isEssentialEpi
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)] :
    OpConjecture.Tsukamoto.StandardSemantics.IsEssentialEpi
      (jacobsonQuotientMap (R := R) (P := P)) := by
  constructor
  · rw [ModuleCat.epi_iff_surjective]
    exact (Module.jacobson R P).mkQ_surjective
  · intro Z g hg
    rw [ModuleCat.epi_iff_surjective]
    apply surjective_of_quotient_comp_surjective
      (jacobson_isCoatom_of_local_end
        (R := R) (P := P)).ne_top
    have hcomp :
        Function.Surjective
          ((Module.jacobson R P).mkQ.comp g.hom) := by
      simpa [jacobsonQuotientMap] using
        ((ModuleCat.epi_iff_surjective
          (g ≫ jacobsonQuotientMap (R := R) (P := P))).mp hg)
    exact hcomp

/-- The radical quotient of a finite projective module with local
endomorphism ring, equipped with its canonical categorical projective cover.
-/
def jacobsonProjectiveCover
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)] :
    OpConjecture.Tsukamoto.StandardSemantics.ProjectiveCover
      (ModuleCat.of R (P ⧸ Module.jacobson R P)) where
  object := ModuleCat.of R P
  projective := by infer_instance
  map := jacobsonQuotientMap
  essentialEpi := jacobsonQuotientMap_isEssentialEpi

/-- The same projective-cover package, obtained from an indecomposable
finite-length projective module via the project foundation's local-endomorphism theorem. -/
def jacobsonProjectiveCoverOfIndecomposable
    {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (hfinite : IsFiniteLength R P)
    (hindec : OpConjecture.Foundation.IsIndecomposableModule R P) :
    OpConjecture.Tsukamoto.StandardSemantics.ProjectiveCover
      (ModuleCat.of R (P ⧸ Module.jacobson R P)) := by
  letI : Nontrivial P := hindec.nontrivial
  letI : IsLocalRing (Module.End R P) :=
    OpConjecture.Foundation.isLocalRing_end_of_isIndecomposable hfinite hindec
  exact jacobsonProjectiveCover

/-- A surjection from a finite projective with local endomorphism ring to a
simple module presents the source as the projective cover of that target. -/
def projectiveCoverOfSurjectiveToSimple
    {P : Type v} [AddCommGroup P] [Module R P]
    [Nontrivial P] [Module.Finite R P] [Module.Projective R P]
    [IsLocalRing (Module.End R P)]
    {S : Type v} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (f : P →ₗ[R] S) (hf : Function.Surjective f) :
    OpConjecture.Tsukamoto.StandardSemantics.ProjectiveCover
      (ModuleCat.of R S) :=
  (jacobsonProjectiveCover (R := R) (P := P)).postIso
    (topLinearEquivOfSurjectiveToSimple f hf).toModuleIso

end OpConjecture.ProjectiveSimpleTop
