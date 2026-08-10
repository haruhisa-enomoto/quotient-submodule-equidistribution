import OpConjecture.RepresentationTheory.StableQuotients
import Mathlib.CategoryTheory.Quotient.Linear

/-!
# Scalar linearity of the projective-stable quotient

For any selected `k`-linear structure on finitely generated `R`-modules,
scalar multiplication preserves factorization through projective modules.
Hence the quotient by projective factorizations is `k`-linear and the
quotient functor is `k`-linear.

The quotient linear structure is exported as an explicit definition rather
than a global instance.  Callers should select it locally with `letI`; this
respects whichever source linear structure is in scope and avoids a
typeclass diamond with the canonical integer-linear structure of every
preadditive category when `k = ℤ`.  For integer scalars the existing
preadditive and additive-functor instances already suffice, so no custom
selection is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RingelStable

universe uk uR

section ScalarStructure

variable {k : Type uk} [Semiring k]
  {R : Type uR} [Ring R] [Linear k (FGModuleCat.{uR} R)]

namespace FactorsThroughProjective

/-- Scalar multiplication preserves factorization through a projective
module. -/
def smul {X Y : FGModuleCat.{uR} R} {f : X ⟶ Y}
    (hf : FactorsThroughProjective f) (a : k) :
    FactorsThroughProjective (a • f) where
  middle := hf.middle
  projective := hf.projective
  left := a • hf.left
  right := hf.right
  fac := by rw [Linear.smul_comp, hf.fac]

end FactorsThroughProjective

/-- Scalar compatibility in the exact shape required by `Quotient.linear`. -/
theorem projectiveStableSmulCompat :
    ∀ (a : k) ⦃X Y : FGModuleCat.{uR} R⦄ (f g : X ⟶ Y),
      projectiveStableRel (R := R) f g →
      projectiveStableRel (R := R) (a • f) (a • g) := by
  rintro a X Y f g ⟨hfg⟩
  exact ⟨by simpa only [smul_sub] using hfg.smul a⟩

namespace ProjectiveStableScalar

/-- The scalar-linear structure on the projective-stable quotient.  It is not
installed globally; select it locally when a scalar-enriched construction
requires it. -/
@[implicit_reducible]
def linear (k : Type uk) [Semiring k]
    (R : Type uR) [Ring R] [Linear k (FGModuleCat.{uR} R)] :
    Linear k (ProjectiveStableCategory (R := R)) :=
  CategoryTheory.Quotient.linear k
    (projectiveStableRel (R := R))
    (projectiveStableSmulCompat (k := k) (R := R))

/-- Relative to `linear`, the canonical quotient functor is
scalar-linear. -/
theorem functorLinear (k : Type uk) [Semiring k]
    (R : Type uR) [Ring R] [Linear k (FGModuleCat.{uR} R)] :
    letI : Linear k (ProjectiveStableCategory (R := R)) := linear k R
    Functor.Linear k (projectiveStableFunctor (R := R)) := by
  infer_instance

end ProjectiveStableScalar

end ScalarStructure

namespace ProjectiveStableScalar

section HomQuotient

variable (k : Type uk) [Ring k]
  (R : Type uR) [Ring R] [Linear k (FGModuleCat.{uR} R)]
  [Linear k (ProjectiveStableCategory (R := R))]
  [Functor.Linear k (projectiveStableFunctor (R := R))]

/-- The quotient map on a projective-stable Hom space, as a linear map. -/
def mapLinear {X Y : FGModuleCat.{uR} R} :
    (X ⟶ Y) →ₗ[k]
      ((projectiveStableFunctor (R := R)).obj X ⟶
        (projectiveStableFunctor (R := R)).obj Y) :=
  (projectiveStableFunctor (R := R)).mapLinearMap k

/-- The quotient map is surjective on every projective-stable Hom space. -/
theorem mapLinear_surjective {X Y : FGModuleCat.{uR} R} :
    Function.Surjective (mapLinear k R (X := X) (Y := Y)) :=
  (projectiveStableFunctor (R := R)).map_surjective

/-- The scalar submodule of morphisms factoring through a projective. -/
abbrev factorsThroughProjectiveSubmodule
    (X Y : FGModuleCat.{uR} R) : Submodule k (X ⟶ Y) :=
  (mapLinear k R (X := X) (Y := Y)).ker

@[simp]
theorem mapLinear_eq_zero_iff
    {X Y : FGModuleCat.{uR} R} (f : X ⟶ Y) :
    mapLinear k R f = 0 ↔ Nonempty (FactorsThroughProjective f) := by
  change (projectiveStableFunctor (R := R)).map f = 0 ↔ _
  rw [← (projectiveStableFunctor (R := R)).map_zero X Y,
    projectiveStable_map_eq_iff]
  simp

@[simp]
theorem mem_factorsThroughProjectiveSubmodule_iff
    {X Y : FGModuleCat.{uR} R} (f : X ⟶ Y) :
    f ∈ factorsThroughProjectiveSubmodule k R X Y ↔
      Nonempty (FactorsThroughProjective f) :=
  mapLinear_eq_zero_iff k R f

/-- Stable Hom is the scalar quotient of ordinary Hom by the submodule of
morphisms factoring through projectives. -/
def homQuotientLinearEquiv (X Y : FGModuleCat.{uR} R) :
    ((X ⟶ Y) ⧸ factorsThroughProjectiveSubmodule k R X Y) ≃ₗ[k]
      ((projectiveStableFunctor (R := R)).obj X ⟶
        (projectiveStableFunctor (R := R)).obj Y) :=
  (mapLinear k R (X := X) (Y := Y)).quotKerEquivOfSurjective
    (mapLinear_surjective k R)

@[simp]
theorem homQuotientLinearEquiv_mk
    {X Y : FGModuleCat.{uR} R} (f : X ⟶ Y) :
    homQuotientLinearEquiv k R X Y (Submodule.Quotient.mk f) =
      (projectiveStableFunctor (R := R)).map f := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

@[simp]
theorem homQuotientLinearEquiv_symm_map
    {X Y : FGModuleCat.{uR} R} (f : X ⟶ Y) :
    (homQuotientLinearEquiv k R X Y).symm
        ((projectiveStableFunctor (R := R)).map f) =
      Submodule.Quotient.mk f := by
  apply (homQuotientLinearEquiv k R X Y).injective
  simp

/-- Postcomposition on ordinary Hom descends to the quotient by projective
factorizations. -/
def postcompQuotient (X : FGModuleCat.{uR} R)
    {Y Z : FGModuleCat.{uR} R} (g : Y ⟶ Z) :
    ((X ⟶ Y) ⧸ factorsThroughProjectiveSubmodule k R X Y) →ₗ[k]
      ((X ⟶ Z) ⧸ factorsThroughProjectiveSubmodule k R X Z) :=
  (factorsThroughProjectiveSubmodule k R X Y).mapQ
    (factorsThroughProjectiveSubmodule k R X Z)
    (CategoryTheory.Linear.rightComp k X g) (by
      intro f hf
      change f ≫ g ∈ factorsThroughProjectiveSubmodule k R X Z
      obtain ⟨hf⟩ :=
        (mem_factorsThroughProjectiveSubmodule_iff k R f).mp hf
      exact (mem_factorsThroughProjectiveSubmodule_iff k R (f ≫ g)).mpr
        ⟨hf.postcomp g⟩)

@[simp]
theorem postcompQuotient_mk
    {X Y Z : FGModuleCat.{uR} R} (g : Y ⟶ Z) (f : X ⟶ Y) :
    postcompQuotient k R X g (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f ≫ g) := by
  rfl

/-- The stable-Hom quotient equivalence is natural under postcomposition in
its target variable. -/
theorem homQuotientLinearEquiv_postcompQuotient
    {X Y Z : FGModuleCat.{uR} R} (g : Y ⟶ Z)
    (q : (X ⟶ Y) ⧸ factorsThroughProjectiveSubmodule k R X Y) :
    homQuotientLinearEquiv k R X Z (postcompQuotient k R X g q) =
      homQuotientLinearEquiv k R X Y q ≫
        (projectiveStableFunctor (R := R)).map g := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp

end HomQuotient

end ProjectiveStableScalar

end OpConjecture.RingelStable
