import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveRadicalExt

/-!
# Ext forks from nonsimple radical tops

This file proves the general first-radical-layer step used in the seriality
reduction.  It contains no concrete algebra, quiver, or module classification.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RadicalTopExtFork

universe u v

variable {K A : Type u}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction

section RadicalTop

variable {kappa : Type v}
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} A kappa)

omit [IsAlgClosed K] [IsArtinianRing A] in
/-- A nonzero radical with nonsimple semisimple top already forces an
outgoing fork.  This extends the tracked decomposable-radical theorem to the
exact first radical layer and is the local step used when one tries to build
serial projective covers recursively. -/
theorem outgoing_of_nonsimple_radical_top
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (i : kappa)
    (hTop : IsSimpleModule A (tau.moduleTop i))
    (hRadical : tau.moduleRadical i ≠ ⊥)
    (hRadicalTop :
      ¬ IsSimpleModule A
          (tau.moduleRadical i ⧸
            Module.jacobson A (tau.moduleRadical i))) :
    HasOutgoingExtGabrielFork (K := K) tau := by
  let Top : FGModuleCat.{u} A := FGModuleCat.of A (tau.moduleTop i)
  have hTopSimple : Simple Top :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Top).mpr hTop
  have hTopIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A Top :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨sRaw, ⟨eTopM⟩⟩ := tau.complete Top hTopIndec
  have hsSimple : Simple (tau.obj sRaw) :=
    (Simple.iff_of_iso eTopM).mp hTopSimple
  let s : tau.SimpleIndex := ⟨sRaw, hsSimple⟩
  obtain ⟨proj, hProj, f, hf⟩ :=
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.exists_epi_from_indec_projective_of_simpleTop
      tau i hTop
  letI : CategoryTheory.Projective (tau.obj proj) := hProj
  letI : Module.Projective A (tau.obj proj) :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (tau.obj proj) hProj
  letI : Nontrivial (tau.obj proj) :=
    (tau.indecomposable proj).nontrivial
  letI : IsLocalRing (Module.End A (tau.obj proj)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      (tau.finiteLength proj) (tau.indecomposable proj)
  letI : IsSimpleModule A (tau.obj s.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj s.1)).mp s.2
  let qM : tau.obj i ⟶ Top :=
    FGModuleCat.ofHom (tau.moduleRadical i).mkQ
  haveI : Epi qM :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective qM).mpr
      (tau.moduleRadical i).mkQ_surjective
  let topMap : tau.obj proj ⟶ tau.obj s.1 :=
    f ≫ qM ≫ eTopM.hom
  haveI : Epi topMap := by
    dsimp only [topMap]
    infer_instance
  have htopSurj : Function.Surjective topMap.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective topMap).mp
      inferInstance
  let eTopP :
      (tau.obj proj ⧸ Module.jacobson A (tau.obj proj)) ≃ₗ[A]
        tau.obj s.1 :=
    QuotientSubmoduleEquidistribution.ProjectiveSimpleTop.topLinearEquivOfSurjectiveToSimple
      topMap.hom.hom htopSurj
  letI : IsArtinian A (tau.obj proj) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (tau.finiteLength proj)).2
  have hfSurj : Function.Surjective f.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective f).mp hf
  let rMap : tau.moduleRadical proj →ₗ[A] tau.moduleRadical i :=
    QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.radicalMapOfSurjective f.hom.hom
  have hrMap : Function.Surjective rMap :=
    QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.radicalMapOfSurjective_surjective
      f.hom.hom hfSurj
  let J : Type u := tau.moduleRadical i
  letI : AddCommGroup J := inferInstance
  letI : Module A J := inferInstance
  letI : Module.Finite A J := inferInstance
  letI : Nontrivial J := by
    change Nontrivial (tau.moduleRadical i)
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hRadical
  have hJfinite : IsFiniteLength A J :=
    (tau.finiteLength i).of_injective
      (Submodule.injective_subtype (tau.moduleRadical i))
  letI : IsNoetherian A J :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hJfinite).1
  letI : IsArtinian A J :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hJfinite).2
  let JTop : Type u := J ⧸ Module.jacobson A J
  letI : AddCommGroup JTop := inferInstance
  letI : Module A JTop := inferInstance
  letI : Module.Finite A JTop := inferInstance
  letI : IsSemisimpleModule A JTop := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact Module.jacobson_quotient_jacobson A J
  letI : Nontrivial JTop := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have htop : Module.jacobson A J = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hsub
    exact (Module.jacobson_lt_top A J).ne htop
  have hJTopNotIndec : ¬ QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A JTop := by
    intro hIndec
    apply hRadicalTop
    exact
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
        hIndec
  obtain ⟨p, q, radTopQuot, hradTopQuot⟩ :=
    QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.exists_epi_to_biprod_chosen_simples_of_not_indec
      tau hJTopNotIndec
  letI : Epi radTopQuot := hradTopQuot
  let rMapCat :
      ModuleCat.of A (tau.moduleRadical proj) ⟶
        ModuleCat.of A (tau.moduleRadical i) :=
    ModuleCat.ofHom rMap
  haveI : Epi rMapCat :=
    (ModuleCat.epi_iff_surjective rMapCat).mpr hrMap
  let qJ :
      ModuleCat.of A (tau.moduleRadical i) ⟶
        ModuleCat.of A JTop :=
    ModuleCat.ofHom (Module.jacobson A J).mkQ
  haveI : Epi qJ :=
    (ModuleCat.epi_iff_surjective qJ).mpr
      (Module.jacobson A J).mkQ_surjective
  let radQuotP :
      ModuleCat.of A (tau.moduleRadical proj) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj q.1).obj :=
    rMapCat ≫ qJ ≫ radTopQuot
  haveI : Epi (rMapCat ≫ qJ) := by infer_instance
  haveI : Epi (qJ ≫ radTopQuot) := by infer_instance
  haveI : Epi radQuotP := by
    apply (ModuleCat.epi_iff_surjective radQuotP).mpr
    have hRadTopSurj : Function.Surjective radTopQuot.hom :=
      (ModuleCat.epi_iff_surjective radTopQuot).mp inferInstance
    have hqJSurj : Function.Surjective qJ.hom :=
      (ModuleCat.epi_iff_surjective qJ).mp inferInstance
    have hrMapCatSurj : Function.Surjective rMapCat.hom :=
      (ModuleCat.epi_iff_surjective rMapCat).mp inferInstance
    intro y
    obtain ⟨z, hz⟩ := hRadTopSurj y
    obtain ⟨w, hw⟩ := hqJSurj z
    obtain ⟨x, hx⟩ := hrMapCatSurj w
    refine ⟨x, ?_⟩
    change radTopQuot.hom (qJ.hom (rMapCat.hom x)) = y
    rw [hx, hw, hz]
  let radQuotP' :
      ModuleCat.of A (Module.jacobson A (tau.obj proj)) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj q.1).obj :=
    radQuotP
  haveI : Epi radQuotP' := by
    dsimp only [radQuotP']
    exact (inferInstance : Epi radQuotP)
  by_cases hpq : p = q
  · subst q
    exact
      QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.outgoing_parallel_extGabrielFork_of_projective_radical_quotient
        tau hFinite s p (P := tau.obj proj)
          (radQuot := radQuotP') eTopP
  · exact
      QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.outgoing_extGabrielFork_of_projective_radical_quotient_distinct
        tau hFinite s p q hpq (P := tau.obj proj)
          (radQuot := radQuotP') eTopP

end RadicalTop

omit [IsAlgClosed K] [IsArtinianRing A] in
/-- Once the nonsimple-top disjunction is supplied, the tracked
projective-radical theorem fills the other nontrivial field of the complete
fork-extraction interface.  This isolates the Artinian serial-ring step as
the sole remaining mathematical premise. -/
theorem extGabrielForkExtraction_of_fork_of_nonsimple_top
    {kappa : Type v}
    (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} A kappa)
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (hNonsimple :
      ∀ i : kappa,
        ¬ IsSimpleModule A
            ((tau.obj i) ⧸ Module.jacobson A (tau.obj i)) →
          HasIncomingExtGabrielFork (K := K) tau ∨
            HasOutgoingExtGabrielFork (K := K) tau) :
    ExtGabrielForkExtraction (K := K) tau where
  finite_extOne := hFinite
  fork_of_nonsimple_top := hNonsimple
  outgoing_of_decomposable_radical i hTop hRadical hNotIndec :=
    QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.outgoing_of_decomposable_radical
      tau hFinite i hTop hRadical hNotIndec


end QuotientSubmoduleEquidistribution.RadicalTopExtFork
