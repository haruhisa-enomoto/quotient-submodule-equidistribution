import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinLevels
import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore
import QuotientSubmoduleEquidistribution.RepresentationTheory.Trace

/-!
# Faithful cores and the second level over Artin algebras

This file removes finite-skeleton and field-basis hypotheses from the
faithful-core argument.  Artinian descent turns annihilator-zero into a
finite embedding of the regular module; this identifies the minimal
faithful quotient and submodule cores.  Singleton-core rigidity then makes
every faithful closed pair equal to its Ringel core, and exact-annihilator
inflation assembles the factorwise correspondences into an
annihilator-preserving bijection.

No classification of a concrete algebra or of its indecomposable modules
is used.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

universe u v vq

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Evaluation at one vector, viewed as a morphism from the left regular module. -/
def regularEvaluation (i : ι) (x : σ.obj i) :
    regularFGModule (R := R) ⟶ σ.obj i :=
  FGModuleCat.ofHom
    { toFun := fun r : R ↦ r • x
      map_add' := fun a b ↦ add_smul a b x
      map_smul' := fun a b ↦ by simp [mul_smul] }

@[simp]
theorem regularEvaluation_apply (i : ι) (x : σ.obj i) (r : R) :
    (regularEvaluation σ i x).hom.hom r = r • x :=
  rfl

/-- A faithful support has zero reject in the regular module. -/
theorem reject_regular_eq_bot_of_isFaithfulSupport
    (C : Set ι)
    (hC : AnnihilatorInflation.IsFaithfulSupport σ.obj C) :
    σ.reject C (regularFGModule (R := R)) = ⊥ := by
  apply bot_unique
  intro r hr
  have hrAnn : r ∈ AnnihilatorInflation.supportAnnihilator σ.obj C := by
    rw [AnnihilatorInflation.mem_supportAnnihilator]
    intro i hi x
    let f : σ.SelectedMapFrom C (regularFGModule (R := R)) :=
      { index := FintypeCat.of (Fin 1)
        label := fun _ ↦ i
        mem := fun _ ↦ hi
        map := biproduct.lift
          (fun _ : Fin 1 ↦ regularEvaluation σ i x) }
    have hker := σ.reject_le_ker f hr
    rw [LinearMap.mem_ker] at hker
    have hfac :
        f.map ≫ biproduct.π (fun _ : Fin 1 ↦ σ.obj i) 0 =
          regularEvaluation σ i x := by
      simp [f]
    have hlinear := congrArg (fun q ↦ q.hom.hom r) hfac
    rw [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, hker] at hlinear
    change (regularEvaluation σ i x).hom.hom r = 0
    simpa only [map_zero] using hlinear.symm
  rw [hC] at hrAnn
  simpa using hrAnn

/-- Over a left Artinian, left Noetherian ring, a faithful support
contains enough vectors to embed the regular module into a finite sum of
its selected indecomposables. -/
theorem regular_inSub_of_isFaithfulSupport
    [IsArtinianRing R]
    (C : Set ι)
    (hC : AnnihilatorInflation.IsFaithfulSupport σ.obj C) :
    σ.InSub C (regularFGModule (R := R)) := by
  apply σ.inSub_of_reject_eq_bot C (regularFGModule (R := R))
  · exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  · exact reject_regular_eq_bot_of_isFaithfulSupport σ C hC

/-- A projective embeds into a finite selected sum once the regular module does. -/
theorem projective_inSub_of_regular_inSub
    (C : Set ι) (P : FGModuleCat.{u} R)
    (hregular : σ.InSub C (regularFGModule (R := R)))
    (hP : Projective P) :
    σ.InSub C P := by
  classical
  obtain ⟨M⟩ := hregular
  obtain ⟨L, p, hp⟩ := regularFGModule_generates (R := R) P
  letI : Mono M.map := M.mono
  letI : Epi p := hp
  letI : Projective P := hP
  let lift : P ⟶ (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    Projective.factorThru (𝟙 P) p
  have hlift : lift ≫ p = 𝟙 P :=
    Projective.factorThru_comp (𝟙 P) p
  let J : FintypeCat.{0} := FintypeCat.of (Σ _ : L, M.index)
  let label : J → ι := fun t ↦ M.label t.2
  let flattenIso :
      (⨁ fun _ : L ↦ σ.sumOver M.index M.label) ≅
        σ.sumOver J label :=
    biproductBiproductIso
      (fun _ : L ↦ M.index)
      (fun _ t ↦ σ.obj (M.label t))
  let q : P ⟶ σ.sumOver J label :=
    lift ≫ biproduct.map (fun _ : L ↦ M.map) ≫ flattenIso.hom
  refine ⟨{
    index := J
    label := label
    mem := fun t ↦ M.mem t.2
    map := q
    mono := ?_ }⟩
  haveI : Mono lift := mono_of_mono_fac hlift
  dsimp only [q]
  infer_instance

/-- An injective is a quotient of a finite selected sum once the regular
module embeds into one. -/
theorem injective_inFac_of_regular_inSub
    (C : Set ι) (I : FGModuleCat.{u} R)
    (hregular : σ.InSub C (regularFGModule (R := R)))
    (hI : Injective I) :
    σ.InFac C I := by
  classical
  obtain ⟨M⟩ := hregular
  obtain ⟨L, p, hp⟩ := regularFGModule_generates (R := R) I
  letI : Mono M.map := M.mono
  letI : Epi p := hp
  letI : Injective I := hI
  let sourceMap :
      (⨁ fun _ : L ↦ regularFGModule (R := R)) ⟶
        ⨁ fun _ : L ↦ σ.sumOver M.index M.label :=
    biproduct.map (fun _ : L ↦ M.map)
  let extension : (⨁ fun _ : L ↦ σ.sumOver M.index M.label) ⟶ I :=
    Injective.factorThru p sourceMap
  have hextension : sourceMap ≫ extension = p :=
    Injective.comp_factorThru p sourceMap
  let J : FintypeCat.{0} := FintypeCat.of (Σ _ : L, M.index)
  let label : J → ι := fun t ↦ M.label t.2
  let flattenIso :
      (⨁ fun _ : L ↦ σ.sumOver M.index M.label) ≅
        σ.sumOver J label :=
    biproductBiproductIso
      (fun _ : L ↦ M.index)
      (fun _ t ↦ σ.obj (M.label t))
  let q : σ.sumOver J label ⟶ I := flattenIso.inv ≫ extension
  refine ⟨{
    index := J
    label := label
    mem := fun t ↦ M.mem t.2
    map := q
    epi := ?_ }⟩
  haveI : Epi extension := epi_of_epi_fac hextension
  dsimp only [q]
  infer_instance

/-- A finite-power subobject of an object in `add C` lies in `Sub C`. -/
theorem inSub_of_inSubOfModule_of_inAdd
    (C : Set ι) (J X : FGModuleCat.{u} R)
    (hJ : σ.InAdd C J)
    (hX : IndecomposableSkeleton.InSubOfModule J X) :
    σ.InSub C X := by
  classical
  obtain ⟨L, m, hm⟩ := hX
  have hsum : σ.InAdd C (⨁ fun _ : L ↦ J) :=
    σ.inAdd_biproduct L (fun _ : L ↦ J) (fun _ ↦ hJ)
  obtain ⟨P⟩ := hsum
  letI : Mono m := hm
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := m ≫ P.iso.hom
    mono := inferInstance }⟩

/-- A finite-power quotient of an object in `add C` lies in `Fac C`. -/
theorem inFac_of_inFacOfModule_of_inAdd
    (C : Set ι) (G X : FGModuleCat.{u} R)
    (hG : σ.InAdd C G)
    (hX : IndecomposableSkeleton.InFacOfModule G X) :
    σ.InFac C X := by
  classical
  obtain ⟨L, p, hp⟩ := hX
  have hsum : σ.InAdd C (⨁ fun _ : L ↦ G) :=
    σ.inAdd_biproduct L (fun _ : L ↦ G) (fun _ ↦ hG)
  obtain ⟨P⟩ := hsum
  letI : Epi p := hp
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.inv ≫ p
    epi := inferInstance }⟩

/-- Additive membership implies submodule membership. -/
theorem inSub_of_inAdd
    (C : Set ι) (X : FGModuleCat.{u} R)
    (hX : σ.InAdd C X) :
    σ.InSub C X := by
  obtain ⟨P⟩ := hX
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.hom
    mono := inferInstance }⟩

/-- Any support into whose selected sum the regular module embeds is faithful. -/
theorem isFaithfulSupport_of_regular_inSub
    (C : Set ι)
    (hregular : σ.InSub C (regularFGModule (R := R))) :
    AnnihilatorInflation.IsFaithfulSupport σ.obj C := by
  obtain ⟨P⟩ := hregular
  unfold AnnihilatorInflation.IsFaithfulSupport
  apply bot_unique
  intro r hr
  have hrSelected : ∀ t (x : σ.obj (P.label t)), r • x = 0 :=
    fun t x ↦
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.mem_supportAnnihilator σ.obj).mp hr
        (P.label t) (P.mem t) x
  have hrSum :
      ∀ y : σ.sumOver P.index P.label, r • y = 0 := by
    have hrMem :
        r ∈ Module.annihilator R
          (σ.sumOver P.index P.label : Type u) := by
      rw [annihilator_biproduct]
      rw [Submodule.mem_iInf]
      intro t
      apply Module.mem_annihilator.mpr
      intro x
      exact hrSelected t x
    exact (Module.mem_annihilator.mp hrMem)
  have hmapzero : P.map.hom.hom r = 0 := by
    calc
      P.map.hom.hom r = r • P.map.hom.hom 1 := by
        simpa using P.map.hom.hom.map_smul r (1 : R)
      _ = 0 := hrSum (P.map.hom.hom 1)
  have hinjective : Function.Injective P.map.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_mono_iff_injective P.map).1 P.mono
  have : r = 0 := by
    apply hinjective
    simpa only [map_zero] using hmapzero
  simp [this]

/-- Faithful closed supports over a left Artinian ring are exactly the
closed supports containing the appropriate projective/injective boundary,
provided a finite injective cogenerator is supplied. -/
theorem closedFaithfulNormalForm_of_artinian
    [IsArtinianRing R]
    (J : FGModuleCat.{u} R)
    (hJ : FiniteInjectiveCogeneratorData (R := R) J) :
    ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj) where
  quotient_iff := by
    intro C
    constructor
    · intro hC i hi
      have hregular : σ.InSub (C : Set ι) (regularFGModule (R := R)) :=
        regular_inSub_of_isFaithfulSupport σ (C : Set ι) hC
      have hiFac : σ.InFac (C : Set ι) (σ.obj i) :=
        injective_inFac_of_regular_inSub σ (C : Set ι) (σ.obj i)
          hregular hi
      have hiClosure : i ∈ σ.qClosure (C : Set ι) := hiFac
      rw [C.property.closure_eq] at hiClosure
      exact hiClosure
    · intro hInjectives
      have hJboundary : σ.InAdd (injectiveLabels σ) J :=
        inAdd_injectiveLabels_of_injective σ J hJ.injective
      have hJselected : σ.InAdd (C : Set ι) J := by
        obtain ⟨P⟩ := hJboundary
        exact ⟨{
          index := P.index
          label := P.label
          mem := fun t ↦ hInjectives (P.mem t)
          iso := P.iso }⟩
      have hregular : σ.InSub (C : Set ι) (regularFGModule (R := R)) :=
        inSub_of_inSubOfModule_of_inAdd σ (C : Set ι) J
          (regularFGModule (R := R)) hJselected
          (hJ.cogenerates (regularFGModule (R := R)))
      exact isFaithfulSupport_of_regular_inSub σ (C : Set ι) hregular
  submodule_iff := by
    intro C
    constructor
    · intro hC i hi
      have hregular : σ.InSub (C : Set ι) (regularFGModule (R := R)) :=
        regular_inSub_of_isFaithfulSupport σ (C : Set ι) hC
      have hiSub : σ.InSub (C : Set ι) (σ.obj i) :=
        projective_inSub_of_regular_inSub σ (C : Set ι) (σ.obj i)
          hregular hi
      have hiClosure : i ∈ σ.sClosure (C : Set ι) := hiSub
      rw [C.property.closure_eq] at hiClosure
      exact hiClosure
    · intro hProjectives
      have hregularBoundary :
          σ.InAdd (projectiveLabels σ) (regularFGModule (R := R)) :=
        regularFGModule_inAdd_projectiveLabels σ
      have hregularAdd : σ.InAdd (C : Set ι) (regularFGModule (R := R)) := by
        obtain ⟨P⟩ := hregularBoundary
        exact ⟨{
          index := P.index
          label := P.label
          mem := fun t ↦ hProjectives (P.mem t)
          iso := P.iso }⟩
      have hregular : σ.InSub (C : Set ι) (regularFGModule (R := R)) :=
        inSub_of_inAdd σ (C : Set ι) (regularFGModule (R := R)) hregularAdd
      exact isFaithfulSupport_of_regular_inSub σ (C : Set ι) hregular

/-- If the torsionless core has exactly one label, then the whole chosen
indecomposable skeleton has exactly one label. -/
theorem subsingleton_of_submoduleCore_ncard_eq_one
    (hcoreCard : (submoduleCore σ : Set ι).ncard = 1) :
    Subsingleton ι := by
  classical
  obtain ⟨p, hcore⟩ := Set.ncard_eq_one.mp hcoreCard
  have hpClosed : σ.sClosure.IsClosed ({p} : Set ι) := by
    rw [← hcore]
    exact (submoduleCore σ).property
  have hpSimple : Simple (σ.obj p) :=
    (σ.sClosure_isClosed_singleton_iff_simple).mp hpClosed
  have hprojectives : projectiveLabels σ ⊆ ({p} : Set ι) := by
    intro i hi
    rw [← hcore]
    exact σ.subset_sSet (projectiveLabels σ) hi
  have hregularBoundary :
      σ.InAdd (projectiveLabels σ) (regularFGModule (R := R)) :=
    regularFGModule_inAdd_projectiveLabels σ
  have hregular : σ.InAdd ({p} : Set ι) (regularFGModule (R := R)) := by
    obtain ⟨P⟩ := hregularBoundary
    exact ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ hprojectives (P.mem t)
      iso := P.iso }⟩
  constructor
  intro i j
  have label_eq (k : ι) : k = p := by
    have hgenerated :
        IndecomposableSkeleton.InFacOfModule
          (regularFGModule (R := R)) (σ.obj k) :=
      regularFGModule_generates (R := R) (σ.obj k)
    have hk : σ.InFac ({p} : Set ι) (σ.obj k) :=
      inFac_of_inFacOfModule_of_inAdd σ ({p} : Set ι)
        (regularFGModule (R := R)) (σ.obj k) hregular hgenerated
    exact (σ.mem_qClosure_singleton_iff_of_simple hpSimple).mp hk
  exact (label_eq i).trans (label_eq j).symm

/-- A Ringel core bijection transfers singleton rigidity from the
torsionless core to the cotorsionless core. -/
theorem subsingleton_of_quotientCore_ncard_eq_one
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)})
    (hcoreCard : (quotientCore σ : Set ι).ncard = 1) :
    Subsingleton ι := by
  apply subsingleton_of_submoduleCore_ncard_eq_one σ
  rw [Set.ncard_congr' e]
  exact hcoreCard

private theorem not_subsingleton_of_mem_skeleton
    {C : Set ι} {i : ι} (_hi : i ∈ C) :
    ¬ Subsingleton (σ.obj i) :=
  not_subsingleton_iff_nontrivial.mpr (σ.indecomposable i).nontrivial

/-- A faithful quotient-closed pair is exactly the cotorsionless core. -/
theorem faithfulQPair_eq_quotientCore
    (hNormal : ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)})
    (C : σ.qClosure.Closeds)
    (hCfaithful :
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 2) :
    (C : Set ι) = (quotientCore σ : Set ι) := by
  classical
  let Q := quotientCoreData σ hNormal
  have hsubset : (quotientCore σ : Set ι) ⊆ (C : Set ι) := by
    simpa only [Q, quotientCoreData_core] using Q.core_le C hCfaithful
  have hCfinite : (C : Set ι).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hcoreFinite : (quotientCore σ : Set ι).Finite :=
    hCfinite.subset hsubset
  have hcoreLe : (quotientCore σ : Set ι).ncard ≤ 2 := by
    simpa only [hCcard] using Set.ncard_le_ncard hsubset hCfinite
  have hcoreNeZero : (quotientCore σ : Set ι).ncard ≠ 0 := by
    intro hzero
    have hcoreEmpty : (quotientCore σ : Set ι) = ∅ :=
      (Set.ncard_eq_zero hcoreFinite).mp hzero
    have hcoreFaithful :
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
          (quotientCore σ : Set ι) := by
      simpa only [Q, quotientCoreData_core] using Q.core_faithful
    have htopbot : (⊤ : TwoSidedIdeal R) = ⊥ := by
      simpa [hcoreEmpty,
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport] using
          hcoreFaithful
    have hone : (1 : R) = 0 := by
      have honeMem : (1 : R) ∈ (⊥ : TwoSidedIdeal R) := by
        rw [← htopbot]
        exact Set.mem_univ 1
      simpa using honeMem
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      (C : Set ι).ncard ≠ 0)
    apply not_subsingleton_of_mem_skeleton σ hi
    constructor
    intro x y
    have hx : x = 0 := by
      calc
        x = (1 : R) • x := (one_smul R x).symm
        _ = (0 : R) • x := by rw [hone]
        _ = 0 := zero_smul R x
    have hy : y = 0 := by
      calc
        y = (1 : R) • y := (one_smul R y).symm
        _ = (0 : R) • y := by rw [hone]
        _ = 0 := zero_smul R y
    exact hx.trans hy.symm
  have hcoreNeOne : (quotientCore σ : Set ι).ncard ≠ 1 := by
    intro hone
    letI : Subsingleton ι :=
      subsingleton_of_quotientCore_ncard_eq_one σ e hone
    have hCle : (C : Set ι).ncard ≤ 1 :=
      Set.ncard_le_one_of_subsingleton (C : Set ι)
    omega
  have hcoreCard : (quotientCore σ : Set ι).ncard = 2 := by omega
  exact (Set.eq_of_subset_of_ncard_le hsubset
    (by omega) hCfinite).symm

/-- A faithful submodule-closed pair is exactly the torsionless core. -/
theorem faithfulSPair_eq_submoduleCore
    (hNormal : ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj))
    (C : σ.sClosure.Closeds)
    (hCfaithful :
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj (C : Set ι))
    (hCcard : (C : Set ι).ncard = 2) :
    (C : Set ι) = (submoduleCore σ : Set ι) := by
  classical
  let S := submoduleCoreData σ hNormal
  have hsubset : (submoduleCore σ : Set ι) ⊆ (C : Set ι) := by
    simpa only [S, submoduleCoreData_core] using S.core_le C hCfaithful
  have hCfinite : (C : Set ι).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have hcoreFinite : (submoduleCore σ : Set ι).Finite :=
    hCfinite.subset hsubset
  have hcoreLe : (submoduleCore σ : Set ι).ncard ≤ 2 := by
    simpa only [hCcard] using Set.ncard_le_ncard hsubset hCfinite
  have hcoreNeZero : (submoduleCore σ : Set ι).ncard ≠ 0 := by
    intro hzero
    have hcoreEmpty : (submoduleCore σ : Set ι) = ∅ :=
      (Set.ncard_eq_zero hcoreFinite).mp hzero
    have hcoreFaithful :
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
          (submoduleCore σ : Set ι) := by
      simpa only [S, submoduleCoreData_core] using S.core_faithful
    have htopbot : (⊤ : TwoSidedIdeal R) = ⊥ := by
      simpa [hcoreEmpty,
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport] using
          hcoreFaithful
    have hone : (1 : R) = 0 := by
      have honeMem : (1 : R) ∈ (⊥ : TwoSidedIdeal R) := by
        rw [← htopbot]
        exact Set.mem_univ 1
      simpa using honeMem
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      (C : Set ι).ncard ≠ 0)
    apply not_subsingleton_of_mem_skeleton σ hi
    constructor
    intro x y
    have hx : x = 0 := by
      calc
        x = (1 : R) • x := (one_smul R x).symm
        _ = (0 : R) • x := by rw [hone]
        _ = 0 := zero_smul R x
    have hy : y = 0 := by
      calc
        y = (1 : R) • y := (one_smul R y).symm
        _ = (0 : R) • y := by rw [hone]
        _ = 0 := zero_smul R y
    exact hx.trans hy.symm
  have hcoreNeOne : (submoduleCore σ : Set ι).ncard ≠ 1 := by
    intro hone
    letI : Subsingleton ι :=
      subsingleton_of_submoduleCore_ncard_eq_one σ hone
    have hCle : (C : Set ι).ncard ≤ 1 :=
      Set.ncard_le_one_of_subsingleton (C : Set ι)
    omega
  have hcoreCard : (submoduleCore σ : Set ι).ncard = 2 := by omega
  exact (Set.eq_of_subset_of_ncard_le hsubset
    (by omega) hCfinite).symm

/-- Faithful quotient- and submodule-closed pairs over one algebra are
canonically equivalent: whenever one exists, it is the corresponding
two-point Ringel core. -/
def faithfulPairEquiv
    (hNormal : ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)}) :
    {C : σ.qClosure.Closeds //
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
            (C : Set ι) ∧
          (C : Set ι).ncard = 2} ≃
      {C : σ.sClosure.Closeds //
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
            (C : Set ι) ∧
          (C : Set ι).ncard = 2} where
  toFun C := by
    let S := submoduleCoreData σ hNormal
    have hqeq : (C.1 : Set ι) = (quotientCore σ : Set ι) :=
      faithfulQPair_eq_quotientCore σ hNormal e C.1 C.2.1 C.2.2
    have hqcard : (quotientCore σ : Set ι).ncard = 2 := by
      rw [← hqeq]
      exact C.2.2
    have hscard : (submoduleCore σ : Set ι).ncard = 2 := by
      rw [Set.ncard_congr' e]
      exact hqcard
    exact ⟨submoduleCore σ,
      by simpa only [S, submoduleCoreData_core] using S.core_faithful,
      hscard⟩
  invFun C := by
    let Q := quotientCoreData σ hNormal
    have hseq : (C.1 : Set ι) = (submoduleCore σ : Set ι) :=
      faithfulSPair_eq_submoduleCore σ hNormal C.1 C.2.1 C.2.2
    have hscard : (submoduleCore σ : Set ι).ncard = 2 := by
      rw [← hseq]
      exact C.2.2
    have hqcard : (quotientCore σ : Set ι).ncard = 2 := by
      rw [← Set.ncard_congr' e]
      exact hscard
    exact ⟨quotientCore σ,
      by simpa only [Q, quotientCoreData_core] using Q.core_faithful,
      hqcard⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    change (quotientCore σ : Set ι) = (C.1 : Set ι)
    exact (faithfulQPair_eq_quotientCore σ hNormal e
      C.1 C.2.1 C.2.2).symm
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    change (submoduleCore σ : Set ι) = (C.1 : Set ι)
    exact (faithfulSPair_eq_submoduleCore σ hNormal
      C.1 C.2.1 C.2.2).symm

/-- A faithful quotient-closed pair exists precisely when the cotorsionless
core has two labels; when it exists, uniqueness makes the two types
equivalent. -/
def faithfulQPairCoreCardEquiv
    (hNormal : ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)}) :
    {C : σ.qClosure.Closeds //
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
            (C : Set ι) ∧
          (C : Set ι).ncard = 2} ≃
      PLift ((quotientCore σ : Set ι).ncard = 2) where
  toFun C := ⟨by
    rw [← faithfulQPair_eq_quotientCore σ hNormal e
      C.1 C.2.1 C.2.2]
    exact C.2.2⟩
  invFun h := by
    let Q := quotientCoreData σ hNormal
    exact ⟨quotientCore σ,
      by simpa only [Q, quotientCoreData_core] using Q.core_faithful,
      h.down⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    change (quotientCore σ : Set ι) = (C.1 : Set ι)
    exact (faithfulQPair_eq_quotientCore σ hNormal e
      C.1 C.2.1 C.2.2).symm
  right_inv _ := Subsingleton.elim _ _

/-- The submodule-side faithful pair is likewise the unique torsionless
core, with its size transported to the common Ringel core size. -/
def faithfulSPairCoreCardEquiv
    (hNormal : ClosedFaithfulNormalForm σ
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj))
    (e :
      {i // i ∈ (submoduleCore σ : Set ι)} ≃
        {i // i ∈ (quotientCore σ : Set ι)}) :
    {C : σ.sClosure.Closeds //
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport σ.obj
            (C : Set ι) ∧
          (C : Set ι).ncard = 2} ≃
      PLift ((quotientCore σ : Set ι).ncard = 2) where
  toFun C := ⟨by
    have hsub : (submoduleCore σ : Set ι).ncard = 2 := by
      rw [← faithfulSPair_eq_submoduleCore σ hNormal
        C.1 C.2.1 C.2.2]
      exact C.2.2
    rwa [Set.ncard_congr' e] at hsub⟩
  invFun h := by
    let S := submoduleCoreData σ hNormal
    have hsub : (submoduleCore σ : Set ι).ncard = 2 := by
      rw [Set.ncard_congr' e]
      exact h.down
    exact ⟨submoduleCore σ,
      by simpa only [S, submoduleCoreData_core] using S.core_faithful,
      hsub⟩
  left_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    change (submoduleCore σ : Set ι) = (C.1 : Set ι)
    exact (faithfulSPair_eq_submoduleCore σ hNormal
      C.1 C.2.1 C.2.2).symm
  right_inv _ := Subsingleton.elim _ _

/-- Quotient-closed pairs on the ambient skeleton. -/
abbrev ArtinQPair :=
  ArtinQLevel σ 2

/-- Submodule-closed pairs on the ambient skeleton. -/
abbrev ArtinSPair :=
  ArtinSLevel σ 2

/-- Decompose quotient-closed pairs by their exact annihilator. -/
def qPairSigmaAnnihilatorEquiv :
    ArtinQPair σ ≃
      Σ I : TwoSidedIdeal R,
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.QAnnihilatorLevel
          σ I 2 :=
  qLevelSigmaAnnihilatorEquiv σ 2

/-- Decompose submodule-closed pairs by their exact annihilator. -/
def sPairSigmaAnnihilatorEquiv :
    ArtinSPair σ ≃
      Σ I : TwoSidedIdeal R,
        QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.SAnnihilatorLevel
          σ I 2 :=
  sLevelSigmaAnnihilatorEquiv σ 2

section FactorwiseAssembly

variable {L : TwoSidedIdeal R → Type vq}
  [factorNoetherian :
    ∀ I : TwoSidedIdeal R,
      IsNoetherianRing (QuotientSubmoduleEquidistribution.AnnihilatorInflation.Quotient.Factor I)]
  (τ : ∀ I : TwoSidedIdeal R,
    IndecomposableSkeleton.{u, vq, u}
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.Quotient.Factor I) (L I))
  (D : ∀ I : TwoSidedIdeal R,
    QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData σ I (τ I))
  (normal : ∀ I : TwoSidedIdeal R,
    ClosedFaithfulNormalForm (τ I)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport (τ I).obj)
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.IsFaithfulSupport (τ I).obj))
  (coreEquiv : ∀ I : TwoSidedIdeal R,
    {i // i ∈ (submoduleCore (τ I) : Set (L I))} ≃
      {i // i ∈ (quotientCore (τ I) : Set (L I))})

/-- Ideals whose factor has common Ringel core size two. -/
abbrev CoreTwoIdeal :=
  {I : TwoSidedIdeal R //
    (quotientCore (τ I) : Set (L I)).ncard = 2}

private def sigmaPLiftSubtypeEquiv
    (P : TwoSidedIdeal R → Prop) :
    (Σ I : TwoSidedIdeal R, PLift (P I)) ≃
      {I : TwoSidedIdeal R // P I} where
  toFun I := ⟨I.1, I.2.down⟩
  invFun I := ⟨I.1, PLift.up I.2⟩
  left_inv I := by cases I; rfl
  right_inv _ := rfl

/-- On a fixed annihilator fiber, quotient- and submodule-closed pairs are
identified by factor inflation and the unique faithful two-point core. -/
def fixedAnnihilatorPairEquiv (I : TwoSidedIdeal R) :
    QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.QAnnihilatorLevel
        σ I 2 ≃
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.SAnnihilatorLevel
        σ I 2 :=
  (QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.faithfulQLevelEquiv
      σ I (τ I) (D I) 2).symm |>.trans
    (faithfulPairEquiv (τ I) (normal I) (coreEquiv I)) |>.trans
      (QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.faithfulSLevelEquiv
        σ I (τ I) (D I) 2)

/-- The exact abstract form of the Artin level-two theorem: quotient- and
submodule-closed pairs are paired within each annihilator fiber. -/
def annihilatorPreservingPairEquiv :
    ArtinQPair σ ≃ ArtinSPair σ :=
  (qPairSigmaAnnihilatorEquiv σ).trans
    ((Equiv.sigmaCongrRight fun I ↦
      fixedAnnihilatorPairEquiv σ τ D normal coreEquiv I).trans
        (sPairSigmaAnnihilatorEquiv σ).symm)

/-- Quotient-closed pairs are canonically parametrized by the ideals whose
factor has Ringel core size two. -/
def qPairCoreTwoIdealEquiv :
    ArtinQPair σ ≃ CoreTwoIdeal τ :=
  (qPairSigmaAnnihilatorEquiv σ).trans
    ((Equiv.sigmaCongrRight fun I ↦
      ((QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.faithfulQLevelEquiv
          σ I (τ I) (D I) 2).symm.trans
        (faithfulQPairCoreCardEquiv (τ I) (normal I) (coreEquiv I)))).trans
      (sigmaPLiftSubtypeEquiv fun I ↦
        (quotientCore (τ I) : Set (L I)).ncard = 2))

/-- Submodule-closed pairs have the same ideal parametrization. -/
def sPairCoreTwoIdealEquiv :
    ArtinSPair σ ≃ CoreTwoIdeal τ :=
  (sPairSigmaAnnihilatorEquiv σ).trans
    ((Equiv.sigmaCongrRight fun I ↦
      ((QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.faithfulSLevelEquiv
          σ I (τ I) (D I) 2).symm.trans
        (faithfulSPairCoreCardEquiv (τ I) (normal I) (coreEquiv I)))).trans
      (sigmaPLiftSubtypeEquiv fun I ↦
        (quotientCore (τ I) : Set (L I)).ncard = 2))

@[simp]
theorem qPairCoreTwoIdealEquiv_ideal (C : ArtinQPair σ) :
    (qPairCoreTwoIdealEquiv σ τ D normal coreEquiv C).1 =
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
        ((C.1 : σ.qClosure.Closeds) : Set ι) :=
  rfl

@[simp]
theorem sPairCoreTwoIdealEquiv_ideal (C : ArtinSPair σ) :
    (sPairCoreTwoIdealEquiv σ τ D normal coreEquiv C).1 =
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
        ((C.1 : σ.sClosure.Closeds) : Set ι) :=
  rfl

theorem annihilatorPreservingPairEquiv_annihilator
    (C : ArtinQPair σ) :
    QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
        (((annihilatorPreservingPairEquiv σ τ D normal coreEquiv C).1 :
          σ.sClosure.Closeds) : Set ι) =
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
        ((C.1 : σ.qClosure.Closeds) : Set ι) := by
  let I := QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
    ((C.1 : σ.qClosure.Closeds) : Set ι)
  let X :
      QuotientSubmoduleEquidistribution.AnnihilatorInflation.Skeleton.InflationData.QAnnihilatorLevel
        σ I 2 :=
    ⟨C.1, rfl, C.2⟩
  have h :=
    (fixedAnnihilatorPairEquiv σ τ D normal coreEquiv I X).2.1
  change
    QuotientSubmoduleEquidistribution.AnnihilatorInflation.supportAnnihilator σ.obj
        (((fixedAnnihilatorPairEquiv σ τ D normal coreEquiv I X).1 :
          σ.sClosure.Closeds) : Set ι) = I
  exact h

end FactorwiseAssembly

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
