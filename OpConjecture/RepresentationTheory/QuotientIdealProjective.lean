import OpConjecture.RepresentationTheory.IdealLayerRestriction

/-!
# Projectivity of quotient-image ideals

An idempotent lower ideal kills itself after passage to the quotient.  This
file turns that observation into the noncommutative base-change statement
needed for successive strong-heredity-chain layers.
-/

noncomputable section

open CategoryTheory
open MulOpposite

namespace OpConjecture.Tsukamoto

universe u

/-- An `R`-linear map between modules restricted along a surjective map
`R → S` is automatically `S`-linear. -/
def linearMapOfRestrictScalarsOfSurjective
    {R S M N : Type u}
    [Ring R] [Ring S]
    [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N]
    (q : R →+* S) (hq : Function.Surjective q)
    (f :
      ((ModuleCat.restrictScalars q).obj
          (ModuleCat.of S M)) →ₗ[R]
        ((ModuleCat.restrictScalars q).obj
          (ModuleCat.of S N))) :
    M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s x := by
    obtain ⟨r, rfl⟩ := hq s
    exact f.map_smul r x

variable {A : Type u} [Ring A]

/-- If `J ≤ I` and `J` is idempotent, then `I J = J`. -/
theorem ideal_mul_eq_of_le_of_idempotent
    (J I : TwoSidedIdeal A) (hJI : J ≤ I)
    (hJidem : IsIdempotentIdeal J) :
    I.asIdeal * J.asIdeal = J.asIdeal := by
  change J.asIdeal * J.asIdeal = J.asIdeal at hJidem
  have hJI' : J.asIdeal ≤ I.asIdeal := hJI
  apply le_antisymm
  · exact Ideal.mul_le_left
  · calc
      J.asIdeal = J.asIdeal * J.asIdeal := hJidem.symm
      _ ≤ I.asIdeal * J.asIdeal :=
        Ideal.mul_mono hJI' (le_refl J.asIdeal)

/-- An `Aᵐᵒᵖ`-linear map from `I` to a module inflated from `A/J`
annihilates `J`, provided `J` is idempotent. -/
theorem linearMap_kills_idempotent_subideal
    (J I : TwoSidedIdeal A) (hJI : J ≤ I)
    (hJidem : IsIdempotentIdeal J)
    {M : Type u} [AddCommGroup M]
    [Module (A ⧸ J.asIdeal)ᵐᵒᵖ M]
    (f :
      I →ₗ[Aᵐᵒᵖ]
        (ModuleCat.restrictScalars
          (RingHom.op (Ideal.Quotient.mk J.asIdeal))).obj
            (ModuleCat.of (A ⧸ J.asIdeal)ᵐᵒᵖ M)) :
    ∀ z : J, f ⟨z.1, hJI z.property⟩ = 0 := by
  intro z
  let q := Ideal.Quotient.mk J.asIdeal
  have hmul :
      J.asIdeal * J.asIdeal ≤ I.asIdeal := by
    rw [hJidem]
    exact hJI
  have hzprod : z.1 ∈ J.asIdeal * J.asIdeal := by
    rw [hJidem]
    exact z.property
  have hz0 :
      f ⟨z.1, hmul hzprod⟩ = 0 := by
    refine
      Submodule.mul_induction_on'
        (M := J.asIdeal) (N := J.asIdeal)
        (C := fun a ha ↦ f ⟨a, hmul ha⟩ = 0)
        ?_ ?_ hzprod
    · intro x hx y hy
      change
        f ((op y) •
          (⟨x, hJI hx⟩ : I)) = 0
      rw [map_smul]
      change
        op (q y) • f (⟨x, hJI hx⟩ : I) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      exact zero_smul _ _
    · intro x hx y hy hx0 hy0
      change
        f ((⟨x, hmul hx⟩ : I) +
          (⟨y, hmul hy⟩ : I)) = 0
      rw [map_add, hx0, hy0, add_zero]
  simpa only using hz0

/-- The image of a projective right ideal in a quotient by an idempotent
subideal is projective over the quotient ring. -/
theorem quotientImage_isRightProjectiveIdeal
    (J I : TwoSidedIdeal A) (hJI : J ≤ I)
    (hJidem : IsIdempotentIdeal J)
    (hIprojective : IsRightProjectiveIdeal I) :
    IsRightProjectiveIdeal (quotientImage I J) := by
  let B := A ⧸ J.asIdeal
  let q : A →+* B := Ideal.Quotient.mk J.asIdeal
  let qop : Aᵐᵒᵖ →+* Bᵐᵒᵖ := RingHom.op q
  let p :=
    rightIdealToRestrictedQuotientImage J I
  have hp :
      Function.Surjective p :=
    rightIdealToRestrictedQuotientImage_surjective J I
  have hqop : Function.Surjective qop := by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unop y)
    refine ⟨op a, ?_⟩
    apply MulOpposite.unop_injective
    exact ha
  letI : Module.Projective Aᵐᵒᵖ I := hIprojective
  apply Module.Projective.of_lifting_property
  intro M N _ _ _ _ f g hf
  let F : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} Aᵐᵒᵖ :=
    ModuleCat.restrictScalars qop
  let fA :
      F.obj (ModuleCat.of Bᵐᵒᵖ M) →ₗ[Aᵐᵒᵖ]
        F.obj (ModuleCat.of Bᵐᵒᵖ N) :=
    (F.map (ModuleCat.ofHom f)).hom
  let gA :
      F.obj (ModuleCat.of Bᵐᵒᵖ (quotientImage I J)) →ₗ[Aᵐᵒᵖ]
        F.obj (ModuleCat.of Bᵐᵒᵖ N) :=
    (F.map (ModuleCat.ofHom g)).hom
  obtain ⟨hA, hhA⟩ :=
    Module.projective_lifting_property fA (gA.comp p) hf
  have hker :
      LinearMap.ker p ≤ LinearMap.ker hA := by
    rw [← range_rightIdealInclusion_eq_ker J I hJI]
    rintro x ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    exact
      linearMap_kills_idempotent_subideal
        J I hJI hJidem hA z
  let hquot :
      (I ⧸ LinearMap.ker p) →ₗ[Aᵐᵒᵖ]
        F.obj (ModuleCat.of Bᵐᵒᵖ M) :=
    (LinearMap.ker p).liftQ hA hker
  let ep :
      (I ⧸ LinearMap.ker p) ≃ₗ[Aᵐᵒᵖ]
        F.obj (ModuleCat.of Bᵐᵒᵖ (quotientImage I J)) :=
    p.quotKerEquivOfSurjective hp
  let hbarA :
      F.obj (ModuleCat.of Bᵐᵒᵖ (quotientImage I J)) →ₗ[Aᵐᵒᵖ]
        F.obj (ModuleCat.of Bᵐᵒᵖ M) :=
    hquot.comp ep.symm.toLinearMap
  let hbar : quotientImage I J →ₗ[Bᵐᵒᵖ] M :=
    linearMapOfRestrictScalarsOfSurjective qop hqop hbarA
  refine ⟨hbar, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hp y
  have hp_hbar : hbarA (p x) = hA x := by
    simp [hbarA, hquot, ep]
  have hhAx := DFunLike.congr_fun hhA x
  change f (hbar (p x)) = g (p x)
  change fA (hbarA (p x)) = gA (p x)
  rw [hp_hbar]
  exact hhAx

end OpConjecture.Tsukamoto
