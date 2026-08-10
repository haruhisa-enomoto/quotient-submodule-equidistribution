import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorHomRealization

/-!
# The reverse factor-Hom realization of reject coholes

This file gives the dual factor-Hom bridge used by the reverse factor-ladder
criterion.  A finite injective cogenerator supplies a finite presentation of
every object by the chosen indecomposable injectives.  No concrete algebra or
module classification is used.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Nonvanishing in the reverse factor Hom, represented by a map into a
deleted indecomposable injective which does not factor through `add K`. -/
def reverseFactorHomNonzero (K : Set ι)
    (i x : DeletedLabel K) : Prop :=
  ∃ f : σ.obj x.1 ⟶ σ.obj i.1,
    ¬ FactorsThroughAdd σ K f

/-- The reverse boundary consists of the deleted indecomposable injectives. -/
def deletedInjectiveSet (K : Set ι) : Set (DeletedLabel K) :=
  {i | Injective (σ.obj i.1)}

omit [Finite ι] in
/-- A morphism which factors through `add K` kills the reject of `add K`. -/
theorem reject_le_ker_of_factorsThroughAdd
    {K : Set ι} {X Y : FGModuleCat.{u} R} {f : X ⟶ Y}
    (hf : FactorsThroughAdd σ K f) :
    σ.reject K X ≤ LinearMap.ker f.hom.hom := by
  rcases hf with ⟨M, hM, left, right, rfl⟩
  obtain ⟨A⟩ := hM
  have hMsub : σ.InSub K M := ⟨{
    index := A.index
    label := A.label
    mem := A.mem
    map := A.iso.hom
    mono := inferInstance }⟩
  have hleft :
      σ.reject K X ≤ LinearMap.ker left.hom.hom :=
    reject_le_ker_of_inSub σ hMsub left
  intro x hx
  rw [LinearMap.mem_ker]
  have hxleft := hleft hx
  rw [LinearMap.mem_ker] at hxleft
  simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, hxleft,
    map_zero]

omit [Finite ι] in
/-- For an injective target, killing the reject is equivalent to factoring
through the selected additive subcategory. -/
theorem factorsThroughAdd_of_injective_of_reject_le_ker
    {K : Set ι} {X I : FGModuleCat.{u} R}
    (hX : IsFiniteLength R X) (hI : Injective I)
    (f : X ⟶ I)
    (hf : σ.reject K X ≤ LinearMap.ker f.hom.hom) :
    FactorsThroughAdd σ K f := by
  let gLinear : (X ⧸ σ.reject K X) →ₗ[R] I :=
    (σ.reject K X).liftQ f.hom.hom hf
  let g : σ.rejectQuotientObject K X ⟶ I :=
    ConcreteCategory.ofHom gLinear
  have hg : σ.rejectπ K X ≫ g = f := by
    apply FGModuleCat.hom_ext
    exact (σ.reject K X).liftQ_mkQ f.hom.hom hf
  obtain ⟨Q⟩ := rejectQuotientObject_inSub σ K X hX
  letI : Mono Q.map := Q.mono
  letI : Injective I := hI
  let extension : σ.sumOver Q.index Q.label ⟶ I :=
    Injective.factorThru g Q.map
  have hextension : Q.map ≫ extension = g :=
    Injective.comp_factorThru g Q.map
  refine ⟨σ.sumOver Q.index Q.label, ?_,
    σ.rejectπ K X ≫ Q.map, extension, ?_⟩
  · exact ⟨{
      index := Q.index
      label := Q.label
      mem := Q.mem
      iso := Iso.refl _ }⟩
  · rw [Category.assoc, hextension, hg]

omit [Finite ι] in
/-- Reverse factor Hom into an injective is nonzero exactly when some
representative does not kill the selected reject. -/
theorem reverseFactorHomNonzero_iff_exists_reject_not_le_ker
    (K : Set ι) (i x : DeletedLabel K)
    (hi : Injective (σ.obj i.1)) :
    reverseFactorHomNonzero σ K i x ↔
      ∃ f : σ.obj x.1 ⟶ σ.obj i.1,
        ¬ σ.reject K (σ.obj x.1) ≤ LinearMap.ker f.hom.hom := by
  constructor
  · rintro ⟨f, hnot⟩
    refine ⟨f, ?_⟩
    intro hker
    exact hnot
      (factorsThroughAdd_of_injective_of_reject_le_ker
        σ (σ.finiteLength x.1) hi f hker)
  · rintro ⟨f, hker⟩
    refine ⟨f, ?_⟩
    intro hfac
    exact hker (reject_le_ker_of_factorsThroughAdd σ hfac)

omit [Finite ι] in
/-- A finite injective cogenerator gives a finite selected-injective
copresentation of every finitely generated module. -/
theorem inSub_injectiveLabels_of_cogenerator
    (J X : FGModuleCat.{u} R)
    (hJ : FiniteInjectiveCogeneratorData (R := R) J) :
    σ.InSub (injectiveLabels σ) X := by
  obtain ⟨L, m, hm⟩ := hJ.cogenerates X
  have hJadd : σ.InAdd (injectiveLabels σ) J :=
    inAdd_injectiveLabels_of_injective σ J hJ.injective
  have htargetAdd :
      σ.InAdd (injectiveLabels σ) (⨁ fun _ : L ↦ J) :=
    inAdd_biproduct σ L (fun _ : L ↦ J) (fun _ ↦ hJadd)
  obtain ⟨P⟩ := htargetAdd
  letI : Mono m := hm
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := m ≫ P.iso.hom
    mono := inferInstance }⟩

omit [Finite ι] in
/-- A deleted reject cohole is detected by a nonzero reverse factor Hom into
a deleted indecomposable injective. -/
theorem rejectCohole_iff_exists_deletedInjective_factorHom
    (J : FGModuleCat.{u} R)
    (hJ : FiniteInjectiveCogeneratorData (R := R) J)
    (K : Set ι) (x : DeletedLabel K) :
    HasRejectCohole σ K x ↔
      ∃ i : DeletedLabel K,
        i ∈ deletedInjectiveSet σ K ∧
          reverseFactorHomNonzero σ K i x := by
  constructor
  · intro hhole
    by_contra hnone
    push Not at hnone
    obtain ⟨Q⟩ := inSub_injectiveLabels_of_cogenerator σ J
      (σ.obj x.1) hJ
    have hcomponent (t : Q.index) :
        FactorsThroughAdd σ K
          (Q.map ≫
            biproduct.π (fun j : Q.index ↦ σ.obj (Q.label j)) t) := by
      by_cases ht : Q.label t ∈ K
      · refine ⟨σ.obj (Q.label t), inAdd_obj σ ht,
          Q.map ≫
            biproduct.π (fun j : Q.index ↦ σ.obj (Q.label j)) t,
          𝟙 _, ?_⟩
        simp
      · let i : DeletedLabel K := ⟨Q.label t, ht⟩
        have hi : i ∈ deletedInjectiveSet σ K := Q.mem t
        have hzero := hnone i hi
        by_contra hnot
        exact hzero ⟨_, hnot⟩
    choose M hM left right hfactor using hcomponent
    let middle : FGModuleCat.{u} R := ⨁ fun t : Q.index ↦ M t
    have hmiddle : σ.InAdd K middle :=
      inAdd_biproduct σ Q.index M hM
    let leftMap : σ.obj x.1 ⟶ middle :=
      biproduct.lift left
    let rightMap : middle ⟶ σ.sumOver Q.index Q.label :=
      biproduct.map right
    have hmap : leftMap ≫ rightMap = Q.map := by
      apply biproduct.hom_ext
      intro t
      dsimp only [leftMap, rightMap]
      rw [Category.assoc, biproduct.map_π,
        ← Category.assoc, biproduct.lift_π]
      exact hfactor t
    letI : Mono Q.map := Q.mono
    letI : Mono leftMap := mono_of_mono_fac hmap
    obtain ⟨A⟩ := hmiddle
    have hinSub : σ.InSub K (σ.obj x.1) := ⟨{
      index := A.index
      label := A.label
      mem := A.mem
      map := leftMap ≫ A.iso.hom
      mono := inferInstance }⟩
    exact hhole
      ((inSub_iff_reject_eq_bot σ K (σ.obj x.1)
        (σ.finiteLength x.1)).1 hinSub)
  · rintro ⟨i, hi, hhom⟩ hbot
    obtain ⟨f, hnot⟩ := hhom
    apply hnot
    apply factorsThroughAdd_of_injective_of_reject_le_ker
      σ (σ.finiteLength x.1) hi f
    rw [hbot]
    exact bot_le

/-- The reverse factor-Hom input required by the abstract reverse-ladder
criterion is canonical once a finite injective cogenerator is supplied. -/
def rejectFactorHomInput
    (J : FGModuleCat.{u} R)
    (hJ : FiniteInjectiveCogeneratorData (R := R) J)
    (K : Set ι) :
    RejectFactorHomInput σ K (deletedInjectiveSet σ K) where
  reverseFactorHomNonzero := reverseFactorHomNonzero σ K
  cohole_iff_injective_factorHom :=
    rejectCohole_iff_exists_deletedInjective_factorHom σ J hJ K

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
