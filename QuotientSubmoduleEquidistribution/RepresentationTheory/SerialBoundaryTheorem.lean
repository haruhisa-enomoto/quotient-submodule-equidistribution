import QuotientSubmoduleEquidistribution.RepresentationTheory.SerialDominantInjectivity

/-!
# The abstract two-sided serial theorem

This file closes the quotient-relative injectivity seam in the standard
serial-ring argument.  It contains no concrete algebra or classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.SerialEndpointReduction

universe u i

/-- Over a left-Noetherian ring, an injective object among finitely generated
modules is an injective module. -/
theorem moduleInjective_of_fgInjective
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (E : FGModuleCat.{u} R) [CategoryTheory.Injective E] :
    Module.Injective R E := by
  apply Module.Baer.injective
  intro I g
  letI : Module.Finite R I :=
    Module.Finite.of_fg I.fg_of_isNoetherianRing
  let i : FGModuleCat.of R I ⟶ FGModuleCat.of R R :=
    FGModuleCat.ofHom I.subtype
  have hi : Mono i := by
    rw [QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective]
    exact Subtype.val_injective
  let f : FGModuleCat.of R I ⟶ E :=
    ConcreteCategory.ofHom g
  let h : FGModuleCat.of R R ⟶ E :=
    CategoryTheory.Injective.factorThru f i
  have hh : i ≫ h = f :=
    CategoryTheory.Injective.comp_factorThru f i
  refine ⟨h.hom.hom, ?_⟩
  intro x hx
  have heq : h.hom.hom.comp I.subtype = g :=
    congrArg (fun q ↦ q.hom.hom) hh
  exact LinearMap.congr_fun heq ⟨x, hx⟩

/-- An injection into a finite-length module is surjective once the target
has no greater composition length than the source. -/
theorem surjective_of_injective_of_length_le
    {R X Y : Type u} [Ring R]
    [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    (hY : IsFiniteLength R Y)
    (f : X →ₗ[R] Y) (hf : Function.Injective f)
    (hle : Module.length R Y ≤ Module.length R X) :
    Function.Surjective f := by
  by_contra hsurj
  have hrange : LinearMap.range f ≠ ⊤ := by
    intro htop
    exact hsurj (LinearMap.range_eq_top.mp htop)
  have hYinstances :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hY
  letI : IsNoetherian R Y := hYinstances.1
  letI : IsArtinian R Y := hYinstances.2
  have hlt : Module.length R (LinearMap.range f) < Module.length R Y :=
    Submodule.length_lt hrange
  let e : X ≃ₗ[R] LinearMap.range f :=
    LinearEquiv.ofBijective f.rangeRestrict
      ⟨f.injective_rangeRestrict_iff.mpr hf,
        LinearMap.surjective_rangeRestrict f⟩
  have heq : Module.length R X = Module.length R (LinearMap.range f) :=
    e.length_eq
  exact (not_lt_of_ge hle) (heq.trans_lt hlt)

/-- A nonzero finite-length uniserial module represented by the skeleton is
injective over its composition-length radical truncation whenever the chosen
indecomposable injectives are uniserial. -/
theorem isInjectiveModuloIdeal_jacobson_pow_length_of_injective_boundary
    {K R : Type u}
    [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [IsSemiprimaryRing R]
    {kappa : Type i}
    (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, i, u} R kappa)
    (hInjective :
      QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton tau)
    {U : Type u} [AddCommGroup U] [Module R U]
    (hUfinite : IsFiniteLength R U)
    (hUnontrivial : Nontrivial U)
    (hUuniserial : QuotientSubmoduleEquidistribution.IsUniserialModule R U) :
    IsInjectiveModuloIdeal
      ((Ring.jacobson R) ^ (Module.length R U).toNat) U := by
  classical
  letI : Nontrivial U := hUnontrivial
  obtain ⟨hUNoetherian, hUArtinian⟩ :=
    isFiniteLength_iff_isNoetherian_isArtinian.mp hUfinite
  letI : IsNoetherian R U := hUNoetherian
  letI : IsArtinian R U := hUArtinian
  let Ufg : FGModuleCat.{u} R := FGModuleCat.of R U
  have hUindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Ufg :=
    hUuniserial.isIndecomposableModule
  obtain ⟨q, ⟨eU⟩⟩ := tau.complete Ufg hUindec
  have hQuniserial :
      QuotientSubmoduleEquidistribution.IsUniserialModule R (tau.obj q) :=
    QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.isUniserialModule_congr
      (FGModuleCat.isoToLinearEquiv eU) hUuniserial
  have hQsocle : IsSimpleModule R (tau.moduleSocle q) :=
    tau.moduleSocle_isSimple_of_isUniserial hQuniserial
  obtain ⟨eIndex, hEInjective, f, hf⟩ :=
    QuotientSubmoduleEquidistribution.SerialRingBridge.exists_mono_to_indec_injective_of_simpleSocle
      (K := K) tau q hQsocle
  letI : Mono f := hf
  have hEuniserial :
      QuotientSubmoduleEquidistribution.IsUniserialModule R (tau.obj eIndex) :=
    hInjective eIndex hEInjective
  let g : Ufg ⟶ tau.obj eIndex := eU.hom ≫ f
  letI : Mono g := by
    dsimp [g]
    infer_instance
  have hgInjective : Function.Injective g.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective g).mp
      inferInstance
  let n : ℕ := (Module.length R U).toNat
  let I : Ideal R := (Ring.jacobson R) ^ n
  let A : Submodule R (tau.obj eIndex) :=
    idealAnnihilatorSubmodule (E := tau.obj eIndex) I
  have hUann : IdealAnnihilates I U := by
    simpa [I, n] using
      (idealAnnihilates_jacobson_pow_length_toNat hUfinite)
  let gA : U →ₗ[R] A :=
    LinearMap.codRestrict A g.hom.hom fun x ↦ by
      intro r hr
      rw [← g.hom.hom.map_smul, hUann r hr x, map_zero]
  have hgAInjective : Function.Injective gA := by
    intro x y hxy
    apply hgInjective
    exact congrArg Subtype.val hxy
  have hAfinite : IsFiniteLength R A :=
    (tau.finiteLength eIndex).of_injective A.subtype_injective
  have hAuniserial : QuotientSubmoduleEquidistribution.IsUniserialModule R A :=
    hEuniserial.submodule A
  have hAann : IdealAnnihilates I A := by
    intro r hr x
    apply Subtype.ext
    exact x.property r hr
  have hsmul : I • (⊤ : Submodule R A) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [Submodule.smul_le]
    intro r hr x _hx
    rw [Submodule.mem_bot]
    exact hAann r hr x
  have hquotientLength :
      Module.length R (A ⧸ I • (⊤ : Submodule R A)) ≤ n := by
    simpa [I] using
      (length_quotient_jacobson_pow_smul_le hAuniserial n)
  let eA : (A ⧸ I • (⊤ : Submodule R A)) ≃ₗ[R] A :=
    (I • (⊤ : Submodule R A)).quotEquivOfEqBot hsmul
  have hAlength : Module.length R A ≤ n := by
    rw [← eA.length_eq]
    exact hquotientLength
  have hAlengthU : Module.length R A ≤ Module.length R U :=
    hAlength.trans_eq
      (ENat.coe_toNat
        (Module.length_ne_top_iff.mpr hUfinite))
  have hgASurjective : Function.Surjective gA :=
    surjective_of_injective_of_length_le
      hAfinite gA hgAInjective hAlengthU
  let e : U ≃ₗ[R] A :=
    LinearEquiv.ofBijective gA ⟨hgAInjective, hgASurjective⟩
  letI : CategoryTheory.Injective (tau.obj eIndex) := hEInjective
  letI : Module.Injective R (tau.obj eIndex) :=
    moduleInjective_of_fgInjective (tau.obj eIndex)
  let e' :
      U ≃ₗ[R]
        idealAnnihilatorSubmodule (E := tau.obj eIndex) I := e
  change IsInjectiveModuloIdeal I U
  exact
    isInjectiveModuloIdeal_of_equiv_idealAnnihilatorSubmodule
      (R := R) (U := U) (E := (tau.obj eIndex : Type u)) I e'

/-- The injective-uniserial boundary supplies the exact dominant-projective
property at the composition-length radical power.  The projectivity premise
is not needed: quotient-relative injectivity already follows directly. -/
theorem isDominantProjectiveModuloIdeal_jacobson_pow_length_of_injective_boundary
    {K R : Type u}
    [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [IsSemiprimaryRing R]
    {kappa : Type i}
    (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, i, u} R kappa)
    (hInjective :
      QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton tau)
    {j : kappa} {U : Submodule R (tau.obj j)}
    (hU : IsMaximumLengthUniserialSubmodule tau j U) :
    IsDominantProjectiveModuloIdeal
      (U := U)
      ((Ring.jacobson R) ^ (Module.length R U).toNat) := by
  intro _hProjectiveModulo
  exact
    isInjectiveModuloIdeal_jacobson_pow_length_of_injective_boundary
      (K := K) tau hInjective
      ((tau.finiteLength j).of_injective U.subtype_injective)
      (Submodule.nontrivial_iff_ne_bot.mpr hU.1)
      hU.2.1

/-- The abstract two-sided serial theorem on a complete indecomposable
skeleton: uniserial indecomposable projectives and injectives force every
indecomposable representative to be uniserial. -/
theorem isNakayamaSkeleton_of_projective_and_injective_boundaries
    {K R : Type u}
    [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
    [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
    [IsSemiprimaryRing R]
    {kappa : Type i}
    (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, i, u} R kappa)
    (hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau)
    (hInjective :
      QuotientSubmoduleEquidistribution.SerialRingBridge.IsInjectiveNakayamaSkeleton tau) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton tau := by
  apply
    isNakayamaSkeleton_of_projective_boundary_of_dominantProjectiveModuloRadicalPower
      tau hProjective
  intro j U hU
  exact
    isDominantProjectiveModuloIdeal_jacobson_pow_length_of_injective_boundary
      (K := K) tau hInjective hU

end QuotientSubmoduleEquidistribution.SerialEndpointReduction
