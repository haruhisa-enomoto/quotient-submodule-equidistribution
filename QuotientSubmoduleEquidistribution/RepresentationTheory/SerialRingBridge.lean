import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaRepresentationFiniteBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserialSubmodule
import QuotientSubmoduleEquidistribution.RepresentationTheory.RadicalTopExtFork
import QuotientSubmoduleEquidistribution.RepresentationTheory.ExtDualTransport

/-!
# Two-sided serial boundary reduction

This file isolates the genuinely general module-theoretic seam in the
Artinian serial-ring theorem.  No quiver or concrete algebra is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.SerialRingBridge

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {K R : Type u}
  [Field K] [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {iota : Type v} [Finite iota]
  (sigma : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R iota)

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

/-- The indecomposable-injective boundary half of the Artinian serial
hypothesis. -/
def IsInjectiveNakayamaSkeleton : Prop :=
  ∀ i : iota,
    CategoryTheory.Injective (sigma.obj i) →
      QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj i)

/-- The pointwise top-or-socle alternative which is sufficient to pass from
two uniserial boundaries to all indecomposables. -/
def HasSimpleTopOrSocle : Prop :=
  ∀ i : iota,
    IsSimpleModule R (sigma.moduleTop i) ∨
      IsSimpleModule R (sigma.moduleSocle i)

omit [IsNoetherianRing Rᵐᵒᵖ] [Finite iota] in
/-- A simple top makes an indecomposable a quotient of one indecomposable
projective; a uniserial projective source therefore makes it uniserial. -/
theorem isUniserial_of_simpleTop_of_projectiveUniserial
    (hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma)
    (i : iota)
    (hTop : IsSimpleModule R (sigma.moduleTop i)) :
    QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj i) := by
  obtain ⟨p, hpProjective, f, hf⟩ :=
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.exists_epi_from_indec_projective_of_simpleTop
      sigma i hTop
  letI : Epi f := hf
  have hP : QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj p) :=
    hProjective p hpProjective
  have hQuot :
      QuotientSubmoduleEquidistribution.IsUniserialModule R
        ((sigma.obj p) ⧸ LinearMap.ker f.hom.hom) :=
    hP.quotient (LinearMap.ker f.hom.hom)
  have hfSurj : Function.Surjective f.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective f).mp
      inferInstance
  exact
    QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.isUniserialModule_congr
      (f.hom.hom.quotKerEquivOfSurjective hfSurj) hQuot

include K in
omit [Finite iota] in
/-- A finite-length indecomposable with simple socle embeds into one chosen
indecomposable injective.  This is the exact dual of the maintained
projective-source theorem for simple tops. -/
theorem exists_mono_to_indec_injective_of_simpleSocle
    (i : iota)
    (hSocle : IsSimpleModule R (sigma.moduleSocle i)) :
    ∃ j : iota,
      CategoryTheory.Injective (sigma.obj j) ∧
        ∃ f : sigma.obj i ⟶ sigma.obj j, Mono f := by
  let J : FGModuleCat.{u} R := dualRegular (R := R) K
  let hJ : FiniteInjectiveCogeneratorData (R := R) J :=
    dualRegularCogeneratorData (R := R) K
  obtain ⟨L, m, hm⟩ := hJ.cogenerates (sigma.obj i)
  have hJadd : sigma.InAdd (injectiveLabels sigma) J :=
    inAdd_injectiveLabels_of_injective sigma J hJ.injective
  have htargetAdd :
      sigma.InAdd (injectiveLabels sigma) (⨁ fun _ : L ↦ J) :=
    sigma.inAdd_biproduct L (fun _ : L ↦ J) (fun _ ↦ hJadd)
  obtain ⟨P⟩ := htargetAdd
  letI : Mono m := hm
  let q : sigma.obj i ⟶
      (⨁ fun t : P.index ↦ sigma.obj (P.label t)) :=
    m ≫ P.iso.hom
  letI : Mono q := by
    dsimp [q]
    infer_instance
  obtain ⟨t, ht⟩ :=
    sigma.exists_mono_biproduct_component_of_simple_socle
      hSocle P.index P.label q
  let f : sigma.obj i ⟶ sigma.obj (P.label t) :=
    q ≫ biproduct.π
      (fun b : P.index ↦ sigma.obj (P.label b)) t
  letI : Mono f := by
    dsimp only [f]
    exact ht
  exact ⟨P.label t, P.mem t, f, inferInstance⟩

include K in
omit [Finite iota] in
/-- A simple socle makes an indecomposable embed into one chosen
indecomposable injective.  Thus uniseriality of the injective boundary
passes to the indecomposable by taking a submodule. -/
theorem isUniserial_of_simpleSocle_of_injectiveUniserial
    (hInjective : IsInjectiveNakayamaSkeleton sigma)
    (i : iota)
    (hSocle : IsSimpleModule R (sigma.moduleSocle i)) :
    QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj i) := by
  obtain ⟨j, hjInjective, f, hf⟩ :=
    exists_mono_to_indec_injective_of_simpleSocle
      (K := K) sigma i hSocle
  letI : Mono f := hf
  have hfInjective : Function.Injective f.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective f).mp
      inferInstance
  have hTarget :
      QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj j) :=
    hInjective j hjInjective
  exact
    QuotientSubmoduleEquidistribution.IsUniserialModule.of_injective
      hTarget f.hom.hom hfInjective

section AntiEquivalenceBoundary

variable {S : Type u} [Ring S] [IsNoetherianRing S]
  {kappa : Type v}
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} S kappa)
  (D :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedAntiEquivalence sigma tau)

include D in
omit [FiniteDimensional K R] [IsNoetherianRing Rᵐᵒᵖ] [Finite iota] in
/-- An aligned anti-equivalence turns uniseriality of every target
indecomposable projective into uniseriality of every source indecomposable
injective.  This is the categorical dual-boundary transport needed before
any Ext-arrow endpoint calculation. -/
theorem injectiveNakayamaSkeleton_of_dual_projectiveNakayama
    (hDualProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau) :
    IsInjectiveNakayamaSkeleton sigma := by
  intro i hi
  have hOpProjective :
      CategoryTheory.Projective (Opposite.op (sigma.obj i)) :=
    CategoryTheory.Injective.injective_iff_projective_op.mp hi
  have hMapProjective :
      CategoryTheory.Projective
        (D.categoryEquiv.functor.obj (Opposite.op (sigma.obj i))) :=
    (D.categoryEquiv.map_projective_iff
      (Opposite.op (sigma.obj i))).mpr hOpProjective
  have hTargetProjective :
      CategoryTheory.Projective (tau.obj (D.labelEquiv i)) :=
    CategoryTheory.Projective.of_iso (D.objIso i) hMapProjective
  exact
    QuotientSubmoduleEquidistribution.DualFixedSocleTransport.isUniserialModule_of_image
      sigma tau D i
      (hDualProjective (D.labelEquiv i) hTargetProjective)

end AntiEquivalenceBoundary

section SourceSerial

variable [IsAlgClosed K] [Small.{u} R] [IsArtinianRing R]

open QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction
open QuotientSubmoduleEquidistribution.GabrielArrowBridge

omit [FiniteDimensional K R] [IsNoetherianRing Rᵐᵒᵖ] [Finite iota]
  [IsAlgClosed K] [IsArtinianRing R] in
/-- Outgoing Ext-degree one already forces every chosen indecomposable with
simple top to be uniserial.  The proof recursively applies the two compiled
radical-layer fork theorems: a decomposable radical or a nonsimple radical
top would give two arrows with the same source. -/
theorem isUniserial_of_simpleTop_of_extSource_injective
    (hFinite : FiniteExtOneSupport (K := K) sigma)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) sigma))
    (i : iota)
    (hTop : IsSimpleModule R (sigma.moduleTop i)) :
    QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj i) := by
  classical
  let measure : iota → ℕ := sigma.compositionLength
  induction i using
    (WellFounded.onFun (f := measure)
      (wellFounded_lt : WellFounded ((· < ·) : ℕ → ℕ → Prop))).induction with
  | h i ih =>
      obtain ⟨hNoetherianI, hArtinianI⟩ :=
        isFiniteLength_iff_isNoetherian_isArtinian.mp
          (sigma.finiteLength i)
      letI : IsNoetherian R (sigma.obj i) := hNoetherianI
      letI : IsArtinian R (sigma.obj i) := hArtinianI
      let J : Submodule R (sigma.obj i) :=
        Module.jacobson R (sigma.obj i)
      by_cases hJ : J = ⊥
      · haveI : Subsingleton J := by
          constructor
          intro x y
          apply Subtype.ext
          have hx : (x : sigma.obj i) = 0 := by
            have hxBot : (x : sigma.obj i) ∈
                (⊥ : Submodule R (sigma.obj i)) := by
              rw [← hJ]
              exact x.2
            simpa using hxBot
          have hy : (y : sigma.obj i) = 0 := by
            have hyBot : (y : sigma.obj i) ∈
                (⊥ : Submodule R (sigma.obj i)) := by
              rw [← hJ]
              exact y.2
            simpa using hyBot
          exact hx.trans hy.symm
        have hJUniserial : QuotientSubmoduleEquidistribution.IsUniserialModule R J :=
          QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.isUniserialModule_of_subsingleton
        exact
          QuotientSubmoduleEquidistribution.NoLoopNakayamaReduction.isUniserialModule_of_simpleTop_of_radicalUniserial
            hTop (by simpa only [J, IndecomposableSkeleton.moduleRadical] using hJUniserial)
      · have hJfinite : IsFiniteLength R J :=
          (sigma.finiteLength i).of_injective
            (Submodule.injective_subtype J)
        letI : IsNoetherian R J :=
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hJfinite).1
        letI : IsArtinian R J :=
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hJfinite).2
        have hJIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R J := by
          by_contra hNotIndec
          obtain ⟨a, b, hab, hsource⟩ :=
            QuotientSubmoduleEquidistribution.ProjectiveRadicalExt.outgoing_of_decomposable_radical
              sigma hFinite i hTop hJ hNotIndec
          exact hab (hSource hsource)
        have hJTop :
            IsSimpleModule R
              (J ⧸ Module.jacobson R J) := by
          by_contra hNotSimple
          obtain ⟨a, b, hab, hsource⟩ :=
            QuotientSubmoduleEquidistribution.RadicalTopExtFork.outgoing_of_nonsimple_radical_top
              sigma hFinite i hTop hJ hNotSimple
          exact hab (hSource hsource)
        let Jfg : FGModuleCat.{u} R := FGModuleCat.of R J
        obtain ⟨j, ⟨e⟩⟩ := sigma.complete Jfg hJIndec
        have hJlt : measure j < measure i := by
          have hLengthEq :
              Module.length R J = Module.length R (sigma.obj j) :=
            LinearEquiv.length_eq
              (FGModuleCat.isoToLinearEquiv e)
          have hJProper : J ≠ ⊤ := by
            letI : Nontrivial (sigma.obj i) :=
              (sigma.indecomposable i).nontrivial
            exact (Module.jacobson_lt_top R (sigma.obj i)).ne
          apply ENat.coe_lt_coe.mp
          rw [sigma.coe_compositionLength j,
            sigma.coe_compositionLength i, ← hLengthEq]
          exact Submodule.length_lt hJProper
        have hTopJRep : IsSimpleModule R (sigma.moduleTop j) := by
          let eLinear := FGModuleCat.isoToLinearEquiv e
          have hMap :
              (Module.jacobson R J).map eLinear.toLinearMap =
                Module.jacobson R (sigma.obj j) :=
            QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
              eLinear.toLinearMap eLinear.surjective
          let eTop :
              (J ⧸ Module.jacobson R J) ≃ₗ[R]
                sigma.moduleTop j :=
            Submodule.Quotient.equiv
              (Module.jacobson R J)
              (Module.jacobson R (sigma.obj j))
              eLinear hMap
          letI : IsSimpleModule R
              (J ⧸ Module.jacobson R J) := hJTop
          exact IsSimpleModule.congr eTop.symm
        have hRepUniserial :
            QuotientSubmoduleEquidistribution.IsUniserialModule R (sigma.obj j) :=
          ih j hJlt hTopJRep
        have hJUniserial : QuotientSubmoduleEquidistribution.IsUniserialModule R J :=
          QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.isUniserialModule_congr
            (FGModuleCat.isoToLinearEquiv e).symm hRepUniserial
        exact
          QuotientSubmoduleEquidistribution.NoLoopNakayamaReduction.isUniserialModule_of_simpleTop_of_radicalUniserial
            hTop hJUniserial

omit [FiniteDimensional K R] [IsNoetherianRing Rᵐᵒᵖ] [Finite iota]
  [IsAlgClosed K] [IsArtinianRing R] in
/-- Consequently outgoing Ext-degree one makes every indecomposable
projective uniserial, because an indecomposable finite-length projective has
simple top. -/
theorem projectiveNakayamaSkeleton_of_extSource_injective
    (hFinite : FiniteExtOneSupport (K := K) sigma)
    (hSource :
      Function.Injective
        (ExtGabrielArrowIndex.source (K := K) sigma)) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma := by
  intro i hi
  let p :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.ProjectiveIndex
        sigma := ⟨i, hi⟩
  have hTop : IsSimpleModule R (sigma.moduleTop i) := by
    exact
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop
          sigma p)).mp
        (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.projectiveTop_isSimple
          sigma p)
  exact
    isUniserial_of_simpleTop_of_extSource_injective
      sigma hFinite hSource i hTop

end SourceSerial

include K in
omit [Finite iota] in
/-- Every chosen indecomposable is uniserial if both boundaries are
uniserial and each indecomposable has a simple top or a simple socle.  Thus
the classical Artinian serial-ring theorem is reduced to the displayed
pointwise alternative. -/
theorem isNakayamaSkeleton_of_twoSidedBoundary_of_simpleTopOrSocle
    (hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma)
    (hInjective : IsInjectiveNakayamaSkeleton sigma)
    (hEndpoint : HasSimpleTopOrSocle sigma) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma := by
  intro i
  rcases hEndpoint i with hTop | hSocle
  · exact
      isUniserial_of_simpleTop_of_projectiveUniserial
        sigma hProjective i hTop
  · exact
      isUniserial_of_simpleSocle_of_injectiveUniserial
        (K := K) sigma hInjective i hSocle

include K in
omit [Finite iota] in
/-- Under the two serial boundary hypotheses, the full Nakayama conclusion
is equivalent to the strictly pointwise top-or-socle seam. -/
theorem isNakayamaSkeleton_iff_simpleTopOrSocle_of_twoSidedBoundary
    (hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma)
    (hInjective : IsInjectiveNakayamaSkeleton sigma) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma ↔
      HasSimpleTopOrSocle sigma := by
  constructor
  · intro hNakayama i
    exact Or.inl <|
      sigma.moduleTop_isSimple_of_isUniserial (hNakayama i)
  · exact
      isNakayamaSkeleton_of_twoSidedBoundary_of_simpleTopOrSocle
        (K := K) sigma hProjective hInjective

section TwoSidedExtBoundary

variable {S : Type u}
  [Ring S] [Small.{u} S] [IsNoetherianRing S] [Algebra K S]
  {kappa : Type v}
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} S kappa)
  (D :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedAntiEquivalence sigma tau)

include K D in
omit [Finite iota] in
/-- The complete compiled two-sided reduction.  Outgoing degree one on the
source and on an aligned dual skeleton makes the projective and injective
boundaries uniserial.  The only remaining serial-ring content is then the
pointwise assertion that every indecomposable has simple top or simple
socle. -/
theorem isNakayamaSkeleton_of_dual_extSource_injective_of_simpleTopOrSocle
    (hFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) sigma)
    (hSource :
      Function.Injective
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex.source
          (K := K) sigma))
    (hDualFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) tau)
    (hDualSource :
      Function.Injective
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex.source
          (K := K) tau))
    (hEndpoint : HasSimpleTopOrSocle sigma) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma := by
  have hProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton sigma :=
    projectiveNakayamaSkeleton_of_extSource_injective
      sigma hFinite hSource
  have hDualProjective :
      QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton tau :=
    projectiveNakayamaSkeleton_of_extSource_injective
      tau hDualFinite hDualSource
  have hInjective : IsInjectiveNakayamaSkeleton sigma :=
    injectiveNakayamaSkeleton_of_dual_projectiveNakayama
      sigma tau D hDualProjective
  exact
    isNakayamaSkeleton_of_twoSidedBoundary_of_simpleTopOrSocle
      (K := K) sigma hProjective hInjective hEndpoint

include K D in
omit [Finite iota] in
/-- Incoming- and outgoing-degree one on the source Ext--Gabriel support
supply both serial boundaries: aligned duality exchanges the incoming source
condition with outgoing degree one on the dual skeleton.  The remaining
general Artinian serial content is exactly the pointwise simple-top-or-socle
alternative. -/
theorem isNakayamaSkeleton_of_extSourceTarget_injective_of_simpleTopOrSocle
    [FiniteDimensional K S]
    (hFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) sigma)
    (hDualFinite :
      QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction.FiniteExtOneSupport
        (K := K) tau)
    (hNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) sigma)
    (hDualNoParallel :
      QuotientSubmoduleEquidistribution.GabrielArrowBridge.NoParallelExtSupport
        (K := K) tau)
    (hSource :
      Function.Injective
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex.source
          (K := K) sigma))
    (hTarget :
      Function.Injective
        (QuotientSubmoduleEquidistribution.GabrielArrowBridge.ExtGabrielArrowIndex.target
          (K := K) sigma))
    (hEndpoint : HasSimpleTopOrSocle sigma) :
    QuotientSubmoduleEquidistribution.LocalNakayamaBranch.IsNakayamaSkeleton sigma := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  letI : IsArtinianRing S := IsArtinianRing.of_finite K S
  apply
    isNakayamaSkeleton_of_dual_extSource_injective_of_simpleTopOrSocle
      (K := K) sigma tau D hFinite hSource hDualFinite
  · exact
      QuotientSubmoduleEquidistribution.ExtDualTransport.AlignedAntiEquivalence.dualExtSource_injective_of_extTarget_injective
        sigma tau D hNoParallel hDualNoParallel hTarget
  · exact hEndpoint

end TwoSidedExtBoundary

end QuotientSubmoduleEquidistribution.SerialRingBridge
