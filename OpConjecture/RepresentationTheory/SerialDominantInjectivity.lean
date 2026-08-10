import OpConjecture.RepresentationTheory.SerialEndpointReduction
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Dominant injectivity for the serial endpoint

This file isolates the quotient-relative injectivity statement used
in the standard proof of Nakayama's serial-module theorem.  It contains no
concrete algebra or module classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.SerialEndpointReduction

universe u i

/-- The two-sided ideal `I` annihilates the module `M`. -/
def IdealAnnihilates
    {R : Type u} [Ring R]
    (I : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∀ r ∈ I, ∀ x : M, r • x = 0

/-- Quotient-relative injectivity, expressed without changing scalar types.
This is injectivity inside the full subcategory of modules annihilated by
`I`, hence is the exact module-theoretic content of injectivity over `R/I`.
-/
def IsInjectiveModuloIdeal
    {R : Type u} [Ring R]
    (I : Ideal R) (U : Type u)
    [AddCommGroup U] [Module R U] : Prop :=
  ∀ {M N : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N],
    IdealAnnihilates I M →
      IdealAnnihilates I N →
        ∀ (j : M →ₗ[R] N), Function.Injective j →
          ∀ f : M →ₗ[R] U,
            ∃ g : N →ₗ[R] U, g.comp j = f

theorem IdealAnnihilates.submodule
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (h : IdealAnnihilates I M) (U : Submodule R M) :
    IdealAnnihilates I U := by
  intro r hr x
  apply Subtype.ext
  exact h r hr x

/-- A quotient-relative injective submodule of an annihilated module is a
direct summand. -/
theorem exists_isCompl_of_isInjectiveModuloIdeal
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (U : Submodule R M)
    (hM : IdealAnnihilates I M)
    (hU : IsInjectiveModuloIdeal I U) :
    ∃ V : Submodule R M, IsCompl U V := by
  obtain ⟨p, hp⟩ :=
    hU (hM.submodule U) hM U.subtype U.subtype_injective LinearMap.id
  refine ⟨LinearMap.ker p, LinearMap.isCompl_of_proj ?_⟩
  intro x
  have hfun := LinearMap.congr_fun hp x
  simpa using hfun

section FiniteLength

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {kappa : Type i}
  (tau : OpConjecture.IndecomposableSkeleton.{u, i, u} R kappa)

/-- A nonzero uniserial submodule has globally maximal composition length among
the nonzero uniserial submodules of the same ambient module. -/
def IsMaximumLengthUniserialSubmodule (i : kappa)
    (U : Submodule R (tau.obj i)) : Prop :=
  U ≠ ⊥ ∧ OpConjecture.IsUniserialModule R U ∧
    ∀ V : Submodule R (tau.obj i),
      V ≠ ⊥ → OpConjecture.IsUniserialModule R V →
        Module.length R V ≤ Module.length R U

/-- The exact dominant-injectivity input in the standard serial-ring proof:
every maximum-length uniserial submodule is injective in a quotient which
annihilates its ambient module. -/
def MaximumLengthUniserialSubmodulesAreDominantInjective : Prop :=
  ∀ (i : kappa) (U : Submodule R (tau.obj i)),
    IsMaximumLengthUniserialSubmodule tau i U →
      ∃ I : Ideal R,
        IdealAnnihilates I (tau.obj i) ∧
          IsInjectiveModuloIdeal I U

/-- Global maximum dimension implies the inclusion-maximality predicate used
by `MaximalNonzeroUniserialSubmodulesSplit`. -/
theorem maximal_of_isMaximumLengthUniserialSubmodule
    {i : kappa} {U : Submodule R (tau.obj i)}
    (hU : IsMaximumLengthUniserialSubmodule tau i U) :
    ∀ V : Submodule R (tau.obj i),
      U ≤ V → V ≠ ⊥ →
        OpConjecture.IsUniserialModule R V → V ≤ U := by
  obtain ⟨hNoetherian, hArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp (tau.finiteLength i)
  letI : IsNoetherian R (tau.obj i) := hNoetherian
  letI : IsArtinian R (tau.obj i) := hArtinian
  intro V hUV hVne hV
  have hlengthLe : Module.length R V ≤ Module.length R U :=
    hU.2.2 V hVne hV
  by_contra hVU
  have hUneV : U ≠ V := by
    intro hEq
    apply hVU
    rw [hEq]
  have hUVlt : U < V := lt_of_le_of_ne hUV hUneV
  have hlengthLt : Module.length R U < Module.length R V := by
    simpa only [Module.length_submodule] using
      (Submodule.height_strictMono hUVlt)
  exact (not_lt_of_ge hlengthLe) hlengthLt

/-- Dominant injectivity gives the desired splitting for every globally
maximum-length uniserial submodule. -/
theorem exists_isCompl_of_isMaximumLengthUniserialSubmodule
    (hDominant :
      MaximumLengthUniserialSubmodulesAreDominantInjective tau)
    {i : kappa} {U : Submodule R (tau.obj i)}
    (hU : IsMaximumLengthUniserialSubmodule tau i U) :
    ∃ V : Submodule R (tau.obj i), IsCompl U V := by
  obtain ⟨I, hI, hInjective⟩ := hDominant i U hU
  exact exists_isCompl_of_isInjectiveModuloIdeal I U hI hInjective

/-- The projective-uniserial boundary supplies a uniserial submodule of
maximum composition length.  The maximum exists because all submodule lengths
are natural numbers bounded by the finite length of the ambient object. -/
theorem exists_maximumLengthUniserialSubmodule_of_projective_boundary
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    (i : kappa) :
    ∃ U : Submodule R (tau.obj i),
      IsMaximumLengthUniserialSubmodule tau i U := by
  classical
  obtain ⟨U₀, hU₀ne, hU₀⟩ :=
    exists_nonzero_uniserial_submodule_of_projective_boundary
      tau hProjective i
  let P : ℕ → Prop := fun n ↦
    ∃ U : Submodule R (tau.obj i),
      U ≠ ⊥ ∧ OpConjecture.IsUniserialModule R U ∧
        (Module.length R U).toNat = n
  have hLengthLe (W : Submodule R (tau.obj i)) :
      Module.length R W ≤ Module.length R (tau.obj i) := by
    calc
      Module.length R W = Order.height W := Module.length_submodule
      _ ≤ Order.height (⊤ : Submodule R (tau.obj i)) :=
        Order.height_mono le_top
      _ = Module.length R (tau.obj i) := by
        rw [← Module.length_top, Module.length_submodule]
  have hAmbientLengthFinite : Module.length R (tau.obj i) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (tau.finiteLength i)
  have hNatLengthLe (W : Submodule R (tau.obj i)) :
      (Module.length R W).toNat ≤ tau.compositionLength i := by
    exact ENat.toNat_le_toNat (hLengthLe W) hAmbientLengthFinite
  have hP₀ : P (Module.length R U₀).toNat :=
    ⟨U₀, hU₀ne, hU₀, rfl⟩
  let n := Nat.findGreatest P (tau.compositionLength i)
  have hnP : P n :=
    Nat.findGreatest_spec (hNatLengthLe U₀) hP₀
  obtain ⟨U, hUne, hU, hUn⟩ := hnP
  refine ⟨U, hUne, hU, ?_⟩
  intro V hVne hV
  have hPV : P (Module.length R V).toNat :=
    ⟨V, hVne, hV, rfl⟩
  have hVn : (Module.length R V).toNat ≤ n :=
    Nat.le_findGreatest (hNatLengthLe V) hPV
  have hUfinite : IsFiniteLength R U :=
    (tau.finiteLength i).of_injective (Submodule.injective_subtype U)
  have hVfinite : IsFiniteLength R V :=
    (tau.finiteLength i).of_injective (Submodule.injective_subtype V)
  have hUneTop : Module.length R U ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hUfinite
  have hVneTop : Module.length R V ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hVfinite
  rw [← ENat.coe_toNat hVneTop, ← ENat.coe_toNat hUneTop]
  exact ENat.coe_le_coe.mpr (hVn.trans_eq hUn.symm)

/-- This is the complete formal endpoint once the standard dominant-projective
injectivity theorem over radical-power quotients is supplied: a maximum-length
uniserial submodule splits, and indecomposability makes it the whole module. -/
theorem isNakayamaSkeleton_of_projective_boundary_of_dominantInjectivity
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    (hDominant :
      MaximumLengthUniserialSubmodulesAreDominantInjective tau) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton tau := by
  intro i
  obtain ⟨U, hU⟩ :=
    exists_maximumLengthUniserialSubmodule_of_projective_boundary
      tau hProjective i
  obtain ⟨V, hUV⟩ :=
    exists_isCompl_of_isMaximumLengthUniserialSubmodule tau hDominant hU
  rcases (tau.indecomposable i).eq_bot_or_eq_bot hUV with hUbot | hVbot
  · exact False.elim (hU.1 hUbot)
  · have hUtop : U = ⊤ := by
      apply top_unique
      simpa [hVbot] using hUV.sup_eq_top.ge
    exact
      OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
        (LinearEquiv.ofTop U hUtop) hU.2.1

end FiniteLength

theorem idealAnnihilates_iff_le_annihilator
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    IdealAnnihilates I M ↔ I ≤ Module.annihilator R M := by
  constructor
  · intro h r hr
    exact Module.mem_annihilator.mpr (h r hr)
  · intro h r hr
    exact Module.mem_annihilator.mp (h hr)

theorem idealAnnihilates_annihilator
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] :
    IdealAnnihilates (Module.annihilator R M) M := by
  rw [idealAnnihilates_iff_le_annihilator]

theorem annihilator_le_submodule_annihilator
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (U : Submodule R M) :
    Module.annihilator R M ≤ Module.annihilator R U := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  apply Subtype.ext
  exact hr x

/-- Projectivity inside the full subcategory of modules annihilated by `I`.
This is the scalar-free form of projectivity over `R/I`. -/
def IsProjectiveModuloIdeal
    {R : Type u} [Ring R]
    (I : Ideal R) (P : Type u)
    [AddCommGroup P] [Module R P] : Prop :=
  ∀ {M N : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N],
    IdealAnnihilates I M →
      IdealAnnihilates I N →
        ∀ (q : M →ₗ[R] N), Function.Surjective q →
          ∀ f : P →ₗ[R] N,
            ∃ g : P →ₗ[R] M, q.comp g = f

/-- Quotienting an `R`-projective by `I P` gives an `R/I`-projective,
expressed entirely with `R`-linear maps between `I`-annihilated modules. -/
theorem quotient_isProjectiveModuloIdeal
    {R P : Type u} [Ring R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (I : Ideal R) [I.IsTwoSided] :
    IsProjectiveModuloIdeal I
      (P ⧸ I • (⊤ : Submodule R P)) := by
  intro M N _ _ _ _ hM _hN q hq f
  let S : Submodule R P := I • (⊤ : Submodule R P)
  let f₀ : P →ₗ[R] N := f.comp S.mkQ
  obtain ⟨h, hh⟩ := Module.projective_lifting_property q f₀ hq
  have hker : S ≤ LinearMap.ker h := by
    intro x hx
    change h x = 0
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr p _hp
      rw [h.map_smul]
      exact hM r hr (h p)
    · intro x y hx hy
      rw [h.map_add, hx, hy, add_zero]
  let g : (P ⧸ S) →ₗ[R] M := S.liftQ h hker
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      have hx := LinearMap.congr_fun hh x
      simpa [g, f₀, S, Submodule.liftQ_apply] using hx

theorem IsProjectiveModuloIdeal.of_equiv
    {R P Q : Type u} [Ring R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    (I : Ideal R) (hP : IsProjectiveModuloIdeal I P)
    (e : P ≃ₗ[R] Q) :
    IsProjectiveModuloIdeal I Q := by
  intro M N _ _ _ _ hM hN q hq f
  obtain ⟨g, hg⟩ := hP hM hN q hq (f.comp e.toLinearMap)
  refine ⟨g.comp e.symm.toLinearMap, ?_⟩
  ext x
  have hx := LinearMap.congr_fun hg (e.symm x)
  simpa using hx

/-- The canonical factor of a map `P → U` through `P / I P`, when `I`
annihilates `U`. -/
def idealQuotientMap
    {R P U : Type u} [Ring R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) (hU : IdealAnnihilates I U)
    (p : P →ₗ[R] U) :
    (P ⧸ I • (⊤ : Submodule R P)) →ₗ[R] U :=
  (I • (⊤ : Submodule R P)).liftQ p <| by
    intro x hx
    change p x = 0
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _hy
      rw [p.map_smul]
      exact hU r hr (p y)
    · intro x y hx hy
      rw [p.map_add, hx, hy, add_zero]

@[simp]
theorem idealQuotientMap_mkQ
    {R P U : Type u} [Ring R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) (hU : IdealAnnihilates I U)
    (p : P →ₗ[R] U) (x : P) :
    idealQuotientMap I hU p
        ((I • (⊤ : Submodule R P)).mkQ x) = p x := by
  simp [idealQuotientMap, Submodule.liftQ_apply]

theorem idealQuotientMap_surjective
    {R P U : Type u} [Ring R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) (hU : IdealAnnihilates I U)
    (p : P →ₗ[R] U) (hp : Function.Surjective p) :
    Function.Surjective (idealQuotientMap I hU p) := by
  intro y
  obtain ⟨x, rfl⟩ := hp y
  exact ⟨(I • (⊤ : Submodule R P)).mkQ x,
    idealQuotientMap_mkQ I hU p x⟩

theorem idealAnnihilates_quotient_smul_top
    {R P : Type u} [Ring R]
    [AddCommGroup P] [Module R P]
    (I : Ideal R) [I.IsTwoSided] :
    IdealAnnihilates I
      (P ⧸ I • (⊤ : Submodule R P)) := by
  intro r hr x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      apply (Submodule.Quotient.eq _).mpr
      simpa only [sub_zero] using
        (Submodule.smul_mem_smul hr
          (show x ∈ (⊤ : Submodule R P) from trivial))

/-- A nonzero semisimple uniserial module is simple. -/
theorem isSimpleModule_of_uniserial_of_semisimple
    {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M] [Nontrivial M]
    [IsSemisimpleModule R M]
    (hM : OpConjecture.IsUniserialModule R M) :
    IsSimpleModule R M := by
  apply (isSimpleModule_iff R M).mpr
  refine IsSimpleOrder.mk fun N ↦ ?_
  obtain ⟨Q, hNQ⟩ := exists_isCompl N
  rcases hM.total N Q with hNle | hQle
  · left
    apply le_antisymm
    · calc
        N ≤ N ⊓ Q := le_inf le_rfl hNle
        _ = ⊥ := hNQ.inf_eq_bot
    · exact bot_le
  · right
    apply top_unique
    calc
      ⊤ = N ⊔ Q := hNQ.sup_eq_top.symm
      _ ≤ N := sup_le le_rfl hQle

theorem length_le_one_of_uniserial_of_semisimple
    {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M]
    (hM : OpConjecture.IsUniserialModule R M) :
    Module.length R M ≤ 1 := by
  by_cases hnontrivial : Nontrivial M
  · letI : Nontrivial M := hnontrivial
    letI : IsSimpleModule R M :=
      isSimpleModule_of_uniserial_of_semisimple hM
    rw [Module.length_eq_one_iff.mpr inferInstance]
  · haveI : Subsingleton M :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    rw [Module.length_eq_zero_iff.mpr inferInstance]
    exact bot_le

/-- The first radical truncation of a uniserial module has length at most
one.  This is the base layer of the radical-power quotient estimate. -/
theorem length_quotient_jacobson_smul_le_one
    {R P : Type u} [Ring R] [IsSemiprimaryRing R]
    [AddCommGroup P] [Module R P]
    (hP : OpConjecture.IsUniserialModule R P) :
    Module.length R
        (P ⧸ Ring.jacobson R • (⊤ : Submodule R P)) ≤ 1 := by
  let Q := P ⧸ Ring.jacobson R • (⊤ : Submodule R P)
  have hQann : IdealAnnihilates (Ring.jacobson R) Q :=
    idealAnnihilates_quotient_smul_top (P := P) (Ring.jacobson R)
  have hQtorsion :
      Module.IsTorsionBySet R Q (Ring.jacobson R) := by
    intro x r
    exact hQann r r.property x
  letI : Module (R ⧸ Ring.jacobson R) Q := hQtorsion.module
  haveI : IsSemisimpleModule (R ⧸ Ring.jacobson R) Q :=
    inferInstance
  letI : IsSemisimpleModule R Q :=
    hQtorsion.isSemisimpleModule_iff.mp inferInstance
  exact
    length_le_one_of_uniserial_of_semisimple
      (hP.quotient (Ring.jacobson R • (⊤ : Submodule R P)))

/-- A surjection of finite-length modules is injective as soon as its source
length is no larger than its target length. -/
theorem injective_of_surjective_of_length_le
    {R X Y : Type u} [Ring R]
    [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    (hY : IsFiniteLength R Y)
    (f : X →ₗ[R] Y) (hf : Function.Surjective f)
    (hle : Module.length R X ≤ Module.length R Y) :
    Function.Injective f := by
  have hlength :
      Module.length R X =
        Module.length R (LinearMap.ker f) + Module.length R Y :=
    Module.length_eq_add_of_exact
      (LinearMap.ker f).subtype f
      (Submodule.subtype_injective _) hf
      (LinearMap.exact_subtype_ker_map f)
  have hYne : Module.length R Y ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hY
  have hker : Module.length R (LinearMap.ker f) = 0 := by
    apply WithTop.add_right_cancel hYne
    apply le_antisymm
    · calc
        Module.length R (LinearMap.ker f) + Module.length R Y =
            Module.length R X := hlength.symm
        _ ≤ Module.length R Y := hle
        _ = 0 + Module.length R Y := by simp
    · calc
        0 + Module.length R Y = Module.length R Y := zero_add _
        _ ≤ Module.length R (LinearMap.ker f) + Module.length R Y :=
          le_add_self
  have hkerSubsingleton : Subsingleton (LinearMap.ker f) :=
    Module.length_eq_zero_iff.mp hker
  intro x y hxy
  have hmem : x - y ∈ LinearMap.ker f := by
    change f (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have heq : (⟨x - y, hmem⟩ : LinearMap.ker f) = 0 :=
    Subsingleton.elim _ _
  exact sub_eq_zero.mp (congrArg Subtype.val heq)

/-- Projective-cover transport over `R/I`: if the induced map from the
quotient of an `R`-projective has no room for a kernel by length, then the
target is projective over `R/I`. -/
theorem isProjectiveModuloIdeal_of_projective_quotient_length
    {R P U : Type u} [Ring R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) [I.IsTwoSided]
    (hUann : IdealAnnihilates I U)
    (p : P →ₗ[R] U) (hp : Function.Surjective p)
    (hUfinite : IsFiniteLength R U)
    (hle :
      Module.length R (P ⧸ I • (⊤ : Submodule R P)) ≤
        Module.length R U) :
    IsProjectiveModuloIdeal I U := by
  let q := idealQuotientMap I hUann p
  have hqSurj : Function.Surjective q :=
    idealQuotientMap_surjective I hUann p hp
  have hqInj : Function.Injective q :=
    injective_of_surjective_of_length_le hUfinite q hqSurj hle
  let e : (P ⧸ I • (⊤ : Submodule R P)) ≃ₗ[R] U :=
    LinearEquiv.ofBijective q ⟨hqInj, hqSurj⟩
  have hQ :
      IsProjectiveModuloIdeal I
        (P ⧸ I • (⊤ : Submodule R P)) :=
    quotient_isProjectiveModuloIdeal (R := R) (P := P) I
  intro M N _ _ _ _ hM hN r hr f
  obtain ⟨g, hg⟩ := hQ hM hN r hr (f.comp e.toLinearMap)
  refine ⟨g.comp e.symm.toLinearMap, ?_⟩
  ext x
  have hx := LinearMap.congr_fun hg (e.symm x)
  simpa using hx

/-- The exact dominant-projective assertion needed at one quotient layer. -/
def IsDominantProjectiveModuloIdeal
    {R U : Type u} [Ring R]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) : Prop :=
  IsProjectiveModuloIdeal I U → IsInjectiveModuloIdeal I U

theorem isInjectiveModuloIdeal_of_dominantProjective_of_quotient_length
    {R P U : Type u} [Ring R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup U] [Module R U]
    (I : Ideal R) [I.IsTwoSided]
    (hUann : IdealAnnihilates I U)
    (p : P →ₗ[R] U) (hp : Function.Surjective p)
    (hUfinite : IsFiniteLength R U)
    (hle :
      Module.length R (P ⧸ I • (⊤ : Submodule R P)) ≤
        Module.length R U)
    (hDominant : IsDominantProjectiveModuloIdeal (U := U) I) :
    IsInjectiveModuloIdeal I U :=
  hDominant <|
    isProjectiveModuloIdeal_of_projective_quotient_length
      I hUann p hp hUfinite hle

/-- The elements of `E` annihilated by the two-sided ideal `I`. -/
def idealAnnihilatorSubmodule
    {R E : Type u} [Ring R] [AddCommGroup E] [Module R E]
    (I : Ideal R) [I.IsTwoSided] : Submodule R E where
  carrier := {x | ∀ r ∈ I, r • x = 0}
  zero_mem' := by simp
  add_mem' hx hy r hr := by simp [hx r hr, hy r hr]
  smul_mem' s x hx := by
    intro r hr
    rw [← mul_smul]
    exact hx (r * s) (I.mul_mem_right s hr)

@[simp]
theorem mem_idealAnnihilatorSubmodule
    {R E : Type u} [Ring R] [AddCommGroup E] [Module R E]
    (I : Ideal R) [I.IsTwoSided] (x : E) :
    x ∈ idealAnnihilatorSubmodule (E := E) I ↔
      ∀ r ∈ I, r • x = 0 :=
  Iff.rfl

theorem idealAnnihilatorSubmodule_isInjectiveModuloIdeal
    {R E : Type u} [Ring R] [AddCommGroup E] [Module R E]
    (I : Ideal R) [I.IsTwoSided]
    [Module.Injective R E] :
    IsInjectiveModuloIdeal I (idealAnnihilatorSubmodule (E := E) I) := by
  intro M N _ _ _ _ hM hN j hj f
  obtain ⟨h, hh⟩ :=
    Module.Injective.out j hj
      ((idealAnnihilatorSubmodule (E := E) I).subtype.comp f)
  let g : N →ₗ[R] idealAnnihilatorSubmodule (E := E) I :=
    LinearMap.codRestrict (idealAnnihilatorSubmodule (E := E) I) h fun y ↦ by
      intro r hr
      rw [← h.map_smul, hN r hr y, map_zero]
  refine ⟨g, ?_⟩
  ext x
  exact hh x

/-- Quotient-relative injectivity transports across a linear equivalence. -/
theorem IsInjectiveModuloIdeal.of_equiv
    {R U V : Type u} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V]
    (I : Ideal R) (h : IsInjectiveModuloIdeal I U)
    (e : U ≃ₗ[R] V) :
    IsInjectiveModuloIdeal I V := by
  intro M N _ _ _ _ hM hN j hj f
  obtain ⟨g, hg⟩ := h hM hN j hj (e.symm.toLinearMap.comp f)
  refine ⟨e.toLinearMap.comp g, ?_⟩
  ext x
  change e (g (j x)) = f x
  have hx : g (j x) = e.symm (f x) := by
    simpa using LinearMap.congr_fun hg x
  rw [hx]
  simp

/-- Quotient-relative injectivity is invariant under linear equivalence. -/
theorem isInjectiveModuloIdeal_congr
    {R U V : Type u} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V]
    (I : Ideal R) (e : U ≃ₗ[R] V) :
    IsInjectiveModuloIdeal I U ↔ IsInjectiveModuloIdeal I V :=
  ⟨fun h ↦ h.of_equiv I e, fun h ↦ h.of_equiv I e.symm⟩

/-- An injective ambient module supplies quotient-relative injectivity to
every module which is equivalent to its `I`-annihilator layer. -/
theorem isInjectiveModuloIdeal_of_equiv_idealAnnihilatorSubmodule
    {R U E : Type u} [Ring R]
    [AddCommGroup U] [Module R U]
    [AddCommGroup E] [Module R E]
    (I : Ideal R) [I.IsTwoSided]
    [Module.Injective R E]
    (e : U ≃ₗ[R] idealAnnihilatorSubmodule (E := E) I) :
    IsInjectiveModuloIdeal I U :=
  (isInjectiveModuloIdeal_congr I e).mpr
    (idealAnnihilatorSubmodule_isInjectiveModuloIdeal I)

/-- Exact dominant-injective-hull criterion for the remaining serial seam.
It is enough to realize each maximum uniserial submodule as the annihilator
layer of an injective module for an ideal which kills the ambient object. -/
theorem maximumLengthUniserialSubmodulesAreDominantInjective_of_hulls
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {kappa : Type u}
    (tau : OpConjecture.IndecomposableSkeleton.{u, u, u} R kappa)
    (hHull :
      ∀ (i : kappa) (U : Submodule R (tau.obj i)),
        IsMaximumLengthUniserialSubmodule tau i U →
          ∃ (I : Ideal R) (_ : I.IsTwoSided),
            IdealAnnihilates I (tau.obj i) ∧
              ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module R E),
                Module.Injective R E ∧
                  Nonempty
                    (U ≃ₗ[R]
                      idealAnnihilatorSubmodule (E := E) I)) :
    MaximumLengthUniserialSubmodulesAreDominantInjective tau := by
  intro i U hU
  obtain ⟨I, hTwoSided, hM, E, hEadd, hEmod, hEinjective, e⟩ :=
    hHull i U hU
  letI : I.IsTwoSided := hTwoSided
  letI : AddCommGroup E := hEadd
  letI : Module R E := hEmod
  letI : Module.Injective R E := hEinjective
  exact ⟨I, hM,
    isInjectiveModuloIdeal_of_equiv_idealAnnihilatorSubmodule I e.some⟩

/-- A second exact decomposition of the serial seam.  It separates the
annihilator equality forced by maximality from the assertion that a uniserial
module is injective over its faithful quotient. -/
theorem maximumLengthUniserialSubmodulesAreDominantInjective_of_annihilator
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {kappa : Type u}
    (tau : OpConjecture.IndecomposableSkeleton.{u, u, u} R kappa)
    (hAnnihilator :
      ∀ (i : kappa) (U : Submodule R (tau.obj i)),
        IsMaximumLengthUniserialSubmodule tau i U →
          Module.annihilator R U =
            Module.annihilator R (tau.obj i))
    (hInjective :
      ∀ (i : kappa) (U : Submodule R (tau.obj i)),
        IsMaximumLengthUniserialSubmodule tau i U →
          IsInjectiveModuloIdeal (Module.annihilator R U) U) :
    MaximumLengthUniserialSubmodulesAreDominantInjective tau := by
  intro i U hU
  refine ⟨Module.annihilator R U, ?_, hInjective i U hU⟩
  rw [hAnnihilator i U hU]
  exact idealAnnihilates_annihilator

/-- Radical-power/projective-cover form of the exact remaining obligation.
For each maximum uniserial submodule it suffices to find a Jacobson-radical
power which annihilates the ambient object, a projective presentation whose
quotient has no greater length, and dominant-projective injectivity at that
quotient layer. -/
theorem maximumLengthUniserialSubmodulesAreDominantInjective_of_radicalPowerData
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {kappa : Type i}
    (tau : OpConjecture.IndecomposableSkeleton.{u, i, u} R kappa)
    (hData :
      ∀ (j : kappa) (U : Submodule R (tau.obj j)),
        IsMaximumLengthUniserialSubmodule tau j U →
          ∃ k : ℕ,
            IdealAnnihilates ((Ring.jacobson R) ^ k) (tau.obj j) ∧
              ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P),
                Module.Projective R P ∧
                  ∃ p : P →ₗ[R] U,
                    Function.Surjective p ∧
                      Module.length R
                          (P ⧸ (Ring.jacobson R) ^ k •
                            (⊤ : Submodule R P)) ≤
                        Module.length R U ∧
                      IsDominantProjectiveModuloIdeal
                        (U := U) ((Ring.jacobson R) ^ k)) :
    MaximumLengthUniserialSubmodulesAreDominantInjective tau := by
  intro j U hU
  obtain ⟨k, hM, P, hPadd, hPmod, hPprojective, p, hp, hle,
      hDominant⟩ := hData j U hU
  letI : AddCommGroup P := hPadd
  letI : Module R P := hPmod
  letI : Module.Projective R P := hPprojective
  have hUfinite : IsFiniteLength R U :=
    (tau.finiteLength j).of_injective U.subtype_injective
  refine ⟨(Ring.jacobson R) ^ k, hM, ?_⟩
  exact
    isInjectiveModuloIdeal_of_dominantProjective_of_quotient_length
      ((Ring.jacobson R) ^ k) (hM.submodule U) p hp hUfinite hle
      hDominant

/-- Every radical layer of a uniserial module contributes at most one
composition factor. -/
theorem length_quotient_jacobson_pow_smul_le
    {R P : Type u} [Ring R] [IsSemiprimaryRing R]
    [AddCommGroup P] [Module R P]
    (hP : OpConjecture.IsUniserialModule R P) (k : ℕ) :
    Module.length R
        (P ⧸ (Ring.jacobson R) ^ k • (⊤ : Submodule R P)) ≤ k := by
  let J : Ideal R := Ring.jacobson R
  induction k with
  | zero =>
      haveI : Subsingleton
          (P ⧸ J ^ 0 • (⊤ : Submodule R P)) := by
        constructor
        intro x y
        obtain ⟨x, rfl⟩ :=
          (J ^ 0 • (⊤ : Submodule R P)).mkQ_surjective x
        obtain ⟨y, rfl⟩ :=
          (J ^ 0 • (⊤ : Submodule R P)).mkQ_surjective y
        apply (Submodule.Quotient.eq _).mpr
        simpa only [one_smul] using
          (Submodule.smul_mem_smul
            (show (1 : R) ∈ J ^ 0 by
              rw [Submodule.pow_zero]
              simp)
            (show x - y ∈ (⊤ : Submodule R P) from trivial))
      rw [Module.length_eq_zero_iff.mpr inferInstance]
      exact le_rfl
  | succ k ih =>
      let S : Submodule R P := J ^ (k + 1) • ⊤
      let T : Submodule R P := J ^ k • ⊤
      have hST : S ≤ T :=
        Submodule.smul_mono_left
          (Ideal.pow_le_pow_right (Nat.le_succ k))
      let q : (P ⧸ S) →ₗ[R] (P ⧸ T) :=
        Submodule.factor hST
      have hqSurj : Function.Surjective q :=
        Submodule.factor_surjective hST
      have hkerAnn : IdealAnnihilates J (LinearMap.ker q) := by
        intro r hr x
        apply Subtype.ext
        change r • (x : P ⧸ S) = 0
        obtain ⟨t, htx⟩ := S.mkQ_surjective (x : P ⧸ S)
        have ht : t ∈ T := by
          apply (Submodule.Quotient.mk_eq_zero T).mp
          have hxzero : q (x : P ⧸ S) = 0 := x.property
          rw [← htx] at hxzero
          simpa [q] using hxzero
        rw [← htx, ← map_smul]
        apply (Submodule.Quotient.mk_eq_zero S).mpr
        refine Submodule.smul_induction_on ht ?_ ?_
        · intro a ha p _hp
          rw [smul_smul]
          apply Submodule.smul_mem_smul
          · have hpow : J ^ (k + 1) = J * J ^ k :=
              Ideal.IsTwoSided.pow_succ (I := J) k
            rw [hpow]
            exact Ideal.mul_mem_mul hr ha
          · trivial
        · intro x y hx hy
          rw [smul_add]
          exact S.add_mem hx hy
      have hkerTorsion :
          Module.IsTorsionBySet R (LinearMap.ker q) J := by
        intro x r
        exact hkerAnn r r.property x
      letI : Module (R ⧸ J) (LinearMap.ker q) :=
        hkerTorsion.module
      haveI : IsSemisimpleModule (R ⧸ J) (LinearMap.ker q) :=
        inferInstance
      letI : IsSemisimpleModule R (LinearMap.ker q) :=
        hkerTorsion.isSemisimpleModule_iff.mp inferInstance
      have hkerUniserial :
          OpConjecture.IsUniserialModule R (LinearMap.ker q) :=
        (hP.quotient S).submodule (LinearMap.ker q)
      have hkerLength : Module.length R (LinearMap.ker q) ≤ 1 :=
        length_le_one_of_uniserial_of_semisimple hkerUniserial
      have hlength :
          Module.length R (P ⧸ S) =
            Module.length R (LinearMap.ker q) +
              Module.length R (P ⧸ T) :=
        Module.length_eq_add_of_exact
          (LinearMap.ker q).subtype q
          (Submodule.subtype_injective _) hqSurj
          (LinearMap.exact_subtype_ker_map q)
      change Module.length R (P ⧸ S) ≤ (k + 1 : ℕ)
      calc
        Module.length R (P ⧸ S) =
            Module.length R (LinearMap.ker q) +
              Module.length R (P ⧸ T) := hlength
        _ ≤ 1 + k := add_le_add hkerLength ih
        _ = (k + 1 : ℕ) := by simp [add_comm]


/-- A finite-length module of length at most `n` is killed by the `n`th
power of the ring Jacobson radical. -/
theorem idealAnnihilates_jacobson_pow_of_length_le
    {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    (hMfinite : IsFiniteLength R M) (n : ℕ)
    (hlen : Module.length R M ≤ n) :
    IdealAnnihilates ((Ring.jacobson R) ^ n) M := by
  induction n generalizing M with
  | zero =>
      have hzero : Module.length R M = 0 := le_antisymm hlen bot_le
      letI : Subsingleton M := Module.length_eq_zero_iff.mp hzero
      intro r _hr x
      exact Subsingleton.elim _ _
  | succ n ih =>
      by_cases hnontrivial : Nontrivial M
      · letI : Nontrivial M := hnontrivial
        obtain ⟨hNoetherian, hArtinian⟩ :=
          isFiniteLength_iff_isNoetherian_isArtinian.mp hMfinite
        letI : IsNoetherian R M := hNoetherian
        letI : IsArtinian R M := hArtinian
        let J : Ideal R := Ring.jacobson R
        let N : Submodule R M := J • (⊤ : Submodule R M)
        have hNlt : N < ⊤ := by
          exact Submodule.FG.jacobson_smul_lt
            (N := (⊤ : Submodule R M)) top_ne_bot
            (IsNoetherian.noetherian ⊤)
        have hNlengthLt : Module.length R N < Module.length R M :=
          Submodule.length_lt hNlt.ne
        have hNlengthLe : Module.length R N ≤ n := by
          apply ENat.lt_coe_add_one_iff.mp
          calc
            Module.length R N < Module.length R M := hNlengthLt
            _ ≤ (↑(n + 1) : ℕ∞) := hlen
            _ = (↑n : ℕ∞) + 1 := by simp
        have hNfinite : IsFiniteLength R N :=
          hMfinite.of_injective N.subtype_injective
        have hNann : IdealAnnihilates (J ^ n) N :=
          ih hNfinite hNlengthLe
        have hJNbot : J ^ n • N = ⊥ := by
          apply le_antisymm ?_ bot_le
          rw [Submodule.smul_le]
          intro a ha x hx
          have hz := hNann a ha (⟨x, hx⟩ : N)
          simpa using congrArg Subtype.val hz
        change IdealAnnihilates (J ^ (n + 1)) M
        rw [idealAnnihilates_iff_le_annihilator,
          ← Submodule.annihilator_top, Submodule.le_annihilator_iff,
          Ideal.IsTwoSided.pow_add, Submodule.pow_one,
          Submodule.mul_smul]
        exact hJNbot
      · letI : Subsingleton M :=
          not_nontrivial_iff_subsingleton.mp hnontrivial
        intro r _hr x
        exact Subsingleton.elim _ _

/-- In particular, the exponent can be taken to be the composition length. -/
theorem idealAnnihilates_jacobson_pow_length_toNat
    {R M : Type u} [Ring R]
    [AddCommGroup M] [Module R M]
    (hMfinite : IsFiniteLength R M) :
    IdealAnnihilates
      ((Ring.jacobson R) ^ (Module.length R M).toNat) M := by
  apply idealAnnihilates_jacobson_pow_of_length_le hMfinite
  exact (ENat.coe_toNat (Module.length_ne_top_iff.mpr hMfinite)).ge

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
attribute [local instance] FintypeCat.fintype

/-- An ideal which kills every component image of a surjection from a finite
biproduct kills the target. -/
theorem idealAnnihilates_of_biproduct_component_ranges
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {J : FintypeCat.{0}} (X : J → FGModuleCat.{u} R)
    {M : FGModuleCat.{u} R}
    (I : Ideal R)
    (p : (biproduct X : FGModuleCat.{u} R) ⟶ M)
    (hp : Function.Surjective p.hom.hom)
    (hcomp :
      ∀ t : J,
        IdealAnnihilates I
          (LinearMap.range
            (biproduct.ι X t ≫ p).hom.hom)) :
    IdealAnnihilates I M := by
  have hmap :
      p =
        ∑ t : J,
          biproduct.π X t ≫ (biproduct.ι X t ≫ p) := by
    calc
      p = 𝟙 (biproduct X) ≫ p := by simp
      _ = (∑ t : J, biproduct.π X t ≫ biproduct.ι X t) ≫ p := by
        rw [biproduct.total]
      _ = ∑ t : J,
          biproduct.π X t ≫ (biproduct.ι X t ≫ p) := by
        simp only [Preadditive.sum_comp, Category.assoc]
  let underlying :
      ((biproduct X : FGModuleCat.{u} R) ⟶ M) →+
        ((biproduct X : FGModuleCat.{u} R) →ₗ[R] M) :=
    { toFun := fun f ↦ f.hom.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hlinear :
      p.hom.hom =
        ∑ t : J,
          (biproduct.π X t ≫
            (biproduct.ι X t ≫ p)).hom.hom := by
    calc
      p.hom.hom = underlying p := rfl
      _ = underlying
          (∑ t : J,
            biproduct.π X t ≫ (biproduct.ι X t ≫ p)) :=
        congrArg underlying hmap
      _ = ∑ t : J,
          (biproduct.π X t ≫
            (biproduct.ι X t ≫ p)).hom.hom :=
        map_sum underlying _ Finset.univ
  intro r hr x
  obtain ⟨y, rfl⟩ := hp x
  change r • p.hom.hom y = 0
  rw [hlinear, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro t _ht
  have hz :
      r •
          (⟨(biproduct.ι X t ≫ p).hom.hom
              ((biproduct.π X t).hom.hom y),
            ⟨((biproduct.π X t).hom.hom y), rfl⟩⟩ :
              LinearMap.range
                (biproduct.ι X t ≫ p).hom.hom) = 0 :=
    hcomp t r hr _
  have hz' := congrArg Subtype.val hz
  change
    r • (biproduct.ι X t ≫ p).hom.hom
        ((biproduct.π X t).hom.hom y) = 0 at hz'
  simpa only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply] using hz'

/-- A maximum-length uniserial submodule controls the Loewy exponent of
its ambient object when the indecomposable projective boundary is
uniserial. -/
theorem idealAnnihilates_jacobson_pow_ambient_of_projective_boundary
    {R : Type u} [Ring R] [IsNoetherianRing R]
    {kappa : Type i}
    (tau : OpConjecture.IndecomposableSkeleton.{u, i, u} R kappa)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    {j : kappa} {U : Submodule R (tau.obj j)}
    (hU : IsMaximumLengthUniserialSubmodule tau j U) :
    IdealAnnihilates
      ((Ring.jacobson R) ^ (Module.length R U).toNat)
      (tau.obj j) := by
  classical
  let n : ℕ := (Module.length R U).toNat
  let I : Ideal R := (Ring.jacobson R) ^ n
  obtain ⟨P⟩ :=
    OpConjecture.NakayamaRepresentationFiniteBridge.inFac_projectiveLabels
      tau (tau.obj j)
  letI : Epi P.map := P.epi
  have hpSurj : Function.Surjective P.map.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective P.map).mp
      inferInstance
  apply
    idealAnnihilates_of_biproduct_component_ranges
      (X := fun t : P.index ↦ tau.obj (P.label t))
      I P.map hpSurj
  intro t
  let g : tau.obj (P.label t) ⟶ tau.obj j :=
    biproduct.ι (fun a : P.index ↦ tau.obj (P.label a)) t ≫ P.map
  let V : Submodule R (tau.obj j) := LinearMap.range g.hom.hom
  change IdealAnnihilates I V
  have hSource : OpConjecture.IsUniserialModule R (tau.obj (P.label t)) :=
    hProjective (P.label t) (P.mem t)
  have hQuotient :
      OpConjecture.IsUniserialModule R
        ((tau.obj (P.label t)) ⧸ LinearMap.ker g.hom.hom) :=
    hSource.quotient (LinearMap.ker g.hom.hom)
  have hVuniserial : OpConjecture.IsUniserialModule R V :=
    OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
      g.hom.hom.quotKerEquivRange hQuotient
  have hVfinite : IsFiniteLength R V :=
    (tau.finiteLength j).of_injective V.subtype_injective
  have hVleU : Module.length R V ≤ Module.length R U := by
    by_cases hVbot : V = ⊥
    · rw [hVbot, Module.length_bot]
      exact bot_le
    · exact hU.2.2 V hVbot hVuniserial
  have hUfinite : IsFiniteLength R U :=
    (tau.finiteLength j).of_injective U.subtype_injective
  have hlengthLe : Module.length R V ≤ n := by
    exact hVleU.trans_eq <|
      (ENat.coe_toNat (Module.length_ne_top_iff.mpr hUfinite)).symm
  exact idealAnnihilates_jacobson_pow_of_length_le hVfinite n hlengthLe

/-- After the ambient radical exponent and projective truncation bounds,
the only remaining serial input is dominant-projective injectivity at that
exact quotient layer. -/
theorem maximumLengthUniserialSubmodulesAreDominantInjective_of_projective_boundary
    {R : Type u} [Ring R] [IsNoetherianRing R]
    [IsSemiprimaryRing R]
    {kappa : Type i}
    (tau : OpConjecture.IndecomposableSkeleton.{u, i, u} R kappa)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    (hDominant :
      ∀ (j : kappa) (U : Submodule R (tau.obj j)),
        IsMaximumLengthUniserialSubmodule tau j U →
          IsDominantProjectiveModuloIdeal
            (U := U)
            ((Ring.jacobson R) ^ (Module.length R U).toNat)) :
    MaximumLengthUniserialSubmodulesAreDominantInjective tau := by
  apply
    maximumLengthUniserialSubmodulesAreDominantInjective_of_radicalPowerData
      tau
  intro j U hU
  let n : ℕ := (Module.length R U).toNat
  have hAmbient :
      IdealAnnihilates ((Ring.jacobson R) ^ n) (tau.obj j) :=
    idealAnnihilates_jacobson_pow_ambient_of_projective_boundary
      tau hProjective hU
  let Ufg : FGModuleCat.{u} R := FGModuleCat.of R U
  letI : Nontrivial U :=
    Submodule.nontrivial_iff_ne_bot.mpr hU.1
  have hUindec : OpConjecture.Foundation.IsIndecomposableModule R Ufg :=
    hU.2.1.isIndecomposableModule
  obtain ⟨q, ⟨eU⟩⟩ := tau.complete Ufg hUindec
  have hQuniserial : OpConjecture.IsUniserialModule R (tau.obj q) :=
    OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
      (FGModuleCat.isoToLinearEquiv eU) hU.2.1
  have hQtop : IsSimpleModule R (tau.moduleTop q) :=
    tau.moduleTop_isSimple_of_isUniserial hQuniserial
  obtain ⟨pIndex, hpProjective, f, hf⟩ :=
    OpConjecture.NakayamaRepresentationFiniteBridge.exists_epi_from_indec_projective_of_simpleTop
      tau q hQtop
  letI : Epi f := hf
  let fU : tau.obj pIndex ⟶ Ufg := f ≫ eU.inv
  letI : Epi fU := by
    dsimp [fU]
    infer_instance
  have hfUSurj : Function.Surjective fU.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective fU).mp
      inferInstance
  have hPmoduleProjective : Module.Projective R (tau.obj pIndex) :=
    OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (tau.obj pIndex) hpProjective
  have hPuniserial :
      OpConjecture.IsUniserialModule R (tau.obj pIndex) :=
    hProjective pIndex hpProjective
  have hUfinite : IsFiniteLength R U :=
    (tau.finiteLength j).of_injective U.subtype_injective
  have hquotientLength :
      Module.length R
          ((tau.obj pIndex) ⧸
            (Ring.jacobson R) ^ n •
              (⊤ : Submodule R (tau.obj pIndex))) ≤
        Module.length R U := by
    calc
      Module.length R
          ((tau.obj pIndex) ⧸
            (Ring.jacobson R) ^ n •
              (⊤ : Submodule R (tau.obj pIndex))) ≤ n :=
        length_quotient_jacobson_pow_smul_le hPuniserial n
      _ = Module.length R U :=
        ENat.coe_toNat (Module.length_ne_top_iff.mpr hUfinite)
  refine
    ⟨n, hAmbient, tau.obj pIndex, inferInstance, inferInstance,
      hPmoduleProjective, fU.hom.hom, hfUSurj, hquotientLength, ?_⟩
  exact hDominant j U hU

/-- Paper-facing endpoint: dominant-projective injectivity at the exact
composition-length radical quotient upgrades the projective-uniserial
boundary to the full Nakayama property. -/
theorem isNakayamaSkeleton_of_projective_boundary_of_dominantProjectiveModuloRadicalPower
    {R : Type u} [Ring R] [IsNoetherianRing R]
    [IsSemiprimaryRing R]
    {kappa : Type i}
    (tau : OpConjecture.IndecomposableSkeleton.{u, i, u} R kappa)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    (hDominant :
      ∀ (j : kappa) (U : Submodule R (tau.obj j)),
        IsMaximumLengthUniserialSubmodule tau j U →
          IsDominantProjectiveModuloIdeal
            (U := U)
            ((Ring.jacobson R) ^ (Module.length R U).toNat)) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton tau :=
  isNakayamaSkeleton_of_projective_boundary_of_dominantInjectivity
    tau hProjective <|
      maximumLengthUniserialSubmodulesAreDominantInjective_of_projective_boundary
        tau hProjective hDominant

end OpConjecture.SerialEndpointReduction
