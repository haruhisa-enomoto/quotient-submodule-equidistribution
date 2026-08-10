import QuotientSubmoduleEquidistribution.RepresentationTheory.FamilyThreeClosure
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserialCollective

/-!
# Final reduction for collective generation by a length-three uniserial

The maintained Loewy-layer analysis leaves one genuinely filtered input:
the upper extension space from the simple top of the length-three source to
its length-two radical must have dimension at most one.  This file makes the
implication from that input to collective quotient closure literal.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.UniserialCollectiveFinal

universe x

variable {K A : Type x}
  [Field K] [IsAlgClosed K]
  [Ring A] [Algebra K A] [FiniteDimensional K A]

variable [IsNoetherianRing Aᵐᵒᵖ] [IsArtinianRing Aᵐᵒᵖ]
  {ι : Type x} [Finite ι]
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Regrouping an additive pair presentation -/

/-- A module in the additive closure of two skeleton representatives is
literally a product of a finite power of the first and a finite power of the
second.  No semisimplicity is needed. -/
theorem exists_pairPowerDecomposition_of_inAdd
    {M : Type x} [AddCommGroup M] [Module Aᵐᵒᵖ M]
    [Module.Finite Aᵐᵒᵖ M]
    {a b : ι}
    (hadd : σ.InAdd ({a, b} : Set ι) (FGModuleCat.of Aᵐᵒᵖ M)) :
    ∃ (J L : Type) (_ : Fintype J) (_ : Fintype L),
      Nonempty (M ≃ₗ[Aᵐᵒᵖ]
        (J → σ.obj a) × (L → σ.obj b)) := by
  classical
  obtain ⟨P⟩ := hadd
  let p : P.index → Prop := fun t ↦ P.label t = a
  let J := {t : P.index // p t}
  let L := {t : P.index // ¬ p t}
  let eIndex : J ⊕ L ≃ P.index := Equiv.sumCompl p
  let F : J ⊕ L → Type x := fun s ↦
    σ.obj (P.label (eIndex s))
  let G : J ⊕ L → Type x := fun s ↦
    match s with
    | .inl _ => σ.obj a
    | .inr _ => σ.obj b
  letI (s : J ⊕ L) : AddCommGroup (G s) := by
    cases s with
    | inl _ => exact (σ.obj a).obj.isAddCommGroup
    | inr _ => exact (σ.obj b).obj.isAddCommGroup
  letI (s : J ⊕ L) : Module Aᵐᵒᵖ (G s) := by
    cases s with
    | inl _ => exact (σ.obj a).obj.isModule
    | inr _ => exact (σ.obj b).obj.isModule
  let componentEquiv : ∀ s, F s ≃ₗ[Aᵐᵒᵖ] G s := fun s ↦ by
    cases s with
    | inl j =>
        change (σ.obj (P.label (eIndex (.inl j))) : Type x) ≃ₗ[Aᵐᵒᵖ]
          (σ.obj a : Type x)
        have hlabel : P.label (eIndex (.inl j)) = a := by
          change P.label j.1 = a
          exact j.2
        exact LinearEquiv.cast (M := fun i : ι ↦ (σ.obj i : Type x)) hlabel
    | inr l =>
        change (σ.obj (P.label (eIndex (.inr l))) : Type x) ≃ₗ[Aᵐᵒᵖ]
          (σ.obj b : Type x)
        have hmem : P.label l.1 = a ∨ P.label l.1 = b := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using P.mem l.1
        have hlabel : P.label (eIndex (.inr l)) = b := by
          have hne : P.label l.1 ≠ a := by simpa [p] using l.2
          change P.label l.1 = b
          exact hmem.resolve_left hne
        exact LinearEquiv.cast (M := fun i : ι ↦ (σ.obj i : Type x)) hlabel
  let ePresentation : M ≃ₗ[Aᵐᵒᵖ]
      σ.sumOver P.index P.label :=
    FGModuleCat.isoToLinearEquiv P.iso
  let ePi : σ.sumOver P.index P.label ≃ₗ[Aᵐᵒᵖ]
      (t : P.index) → σ.obj (P.label t) :=
    FGModuleCat.isoToLinearEquiv
      (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG _)
  let eReindex : ((s : J ⊕ L) → F s) ≃ₗ[Aᵐᵒᵖ]
      ((t : P.index) → σ.obj (P.label t)) :=
    LinearEquiv.piCongrLeft Aᵐᵒᵖ
      (fun t : P.index ↦ (σ.obj (P.label t) : Type x)) eIndex
  let eComponents : ((s : J ⊕ L) → F s) ≃ₗ[Aᵐᵒᵖ]
      ((s : J ⊕ L) → G s) :=
    LinearEquiv.piCongrRight componentEquiv
  let eSplit : ((s : J ⊕ L) → G s) ≃ₗ[Aᵐᵒᵖ]
      ((j : J) → σ.obj a) × ((l : L) → σ.obj b) := by
    simpa only [G] using
      (LinearEquiv.sumPiEquivProdPi Aᵐᵒᵖ J L G)
  letI : Fintype J := Fintype.ofFinite J
  letI : Fintype L := Fintype.ofFinite L
  let e :=
    ((ePresentation.trans ePi).trans eReindex.symm).trans
      (eComponents.trans eSplit)
  exact ⟨J, L, inferInstance, inferInstance, ⟨e⟩⟩

/-! ## The two-target upper-extension reduction -/

/-- If the upper extension space from the fixed simple top to the
length-two radical type has dimension at most one, a two-block radical
decomposition forces the top of the indecomposable middle module to be
simple.  The other radical block is simple, so its `Ext¹` bound is the
maintained no-parallel theorem. -/
theorem moduleTop_isSimple_of_upperExtBound_of_twoBlockRadical
    (hnoParallel :
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.NoParallelExtOne σ K)
    {j w t s : ι}
    (ht : Simple (σ.obj t)) (hs : Simple (σ.obj s))
    (hupperFinite : FiniteDimensional K
      (Ext (σ.obj s).obj (σ.obj w).obj 1))
    (hupper : Module.finrank K
      (Ext (σ.obj s).obj (σ.obj w).obj 1) ≤ 1)
    {J L I : Type} [Fintype J] [Fintype L] [Fintype I]
    (eRadical :
      ((J → σ.obj w) × (L → σ.obj t)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j)
    (eTop : (I → σ.obj s) ≃ₗ[Aᵐᵒᵖ] σ.moduleTop j)
    (hsourceLength :
      (Module.finrank K (I → K) : ℕ∞) =
        Module.length Aᵐᵒᵖ (σ.moduleTop j)) :
    IsSimpleModule Aᵐᵒᵖ (σ.moduleTop j) := by
  classical
  let leftIso :
      ((⨁ fun _ : J ↦ (σ.obj w).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (J → σ.obj w) :=
    ModuleCat.biproductIsoPi (fun _ : J ↦ (σ.obj w).obj)
  let rightIso :
      ((⨁ fun _ : L ↦ (σ.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (L → σ.obj t) :=
    ModuleCat.biproductIsoPi (fun _ : L ↦ (σ.obj t).obj)
  let radicalIso :
      (((⨁ fun _ : J ↦ (σ.obj w).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of Aᵐᵒᵖ (J → σ.obj w))
        (ModuleCat.of Aᵐᵒᵖ (L → σ.obj t)) ≪≫
      eRadical.toModuleIso
  let topIso :
      ((⨁ fun _ : I ↦ (σ.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (σ.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : I ↦ (σ.obj s).obj) ≪≫
      eTop.toModuleIso
  let eRadical' :
      ((((⨁ fun _ : J ↦ (σ.obj w).obj) ⊞
          (⨁ fun _ : L ↦ (σ.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle : (σ.obj j) ≃ₗ[Aᵐᵒᵖ] (σ.obj j) :=
    LinearEquiv.refl Aᵐᵒᵖ (σ.obj j)
  let eTop' :
      (((⨁ fun _ : I ↦ (σ.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        σ.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion :
      σ.moduleRadical j →ₗ[Aᵐᵒᵖ] σ.obj j :=
    (σ.moduleRadical j).subtype
  let topProjection :
      σ.obj j →ₗ[Aᵐᵒᵖ] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (σ.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{x} Aᵐᵒᵖ) :=
    ModuleCat.shortComplexOfConj
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact.linearMap_comp_eq_zero
  have hSC : SC.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact (σ.moduleRadical j).subtype_injective
      (σ.moduleRadical j).mkQ_surjective
  have hSC' : (ShortComplex.mk SC.f SC.g SC.zero).ShortExact := by
    simpa only [SC] using hSC
  letI : IsNoetherian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).1
  letI : IsArtinian Aᵐᵒᵖ (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hExtRight := hnoParallel hs ht
  letI : FiniteDimensional K
      (Ext (σ.obj s).obj (σ.obj w).obj 1) := hupperFinite
  letI : FiniteDimensional K
      (Ext (σ.obj s).obj (σ.obj t).obj 1) := hExtRight.1
  obtain ⟨ell, hell⟩ :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hupper
  obtain ⟨ell', hell'⟩ :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExtRight.2
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj t) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp ht
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj s) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hs
  letI : Simple (σ.obj t).obj :=
    (simple_iff_isSimpleModule' (σ.obj t).obj).mpr inferInstance
  letI : Simple (σ.obj s).obj :=
    (simple_iff_isSimpleModule' (σ.obj s).obj).mpr inferInstance
  letI : Nontrivial (σ.obj w) := (σ.indecomposable w).nontrivial
  have hwNonzero : 𝟙 (σ.obj w).obj ≠ 0 := by
    intro hzero
    obtain ⟨z, hz⟩ := exists_ne (0 : σ.obj w)
    apply hz
    have hzmap := congrArg
      (fun f : (σ.obj w).obj ⟶ (σ.obj w).obj ↦ f.hom z) hzero
    simpa using hzmap
  have htNonzero : 𝟙 (σ.obj t).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj t).obj
  have hsNonzero : 𝟙 (σ.obj s).obj ≠ 0 :=
    CategoryTheory.id_nonzero (σ.obj s).obj
  have hfork :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.shortExact_twoTargetScalarizedExtLinearMaps_isIdempotentIndecomposable
      (σ.obj s).obj (σ.obj w).obj (σ.obj t).obj (σ.obj j).obj
      hsNonzero hwNonzero htNonzero
      SC.f SC.g SC.zero hSC' (σ.indecomposable j)
      ell hell ell' hell'
  letI : Nontrivial (σ.obj j) :=
    (σ.indecomposable j).nontrivial
  change
    (Module.finrank K (I → K) : ℕ∞) =
      Module.length Aᵐᵒᵖ
        ((σ.obj j) ⧸ Module.jacobson Aᵐᵒᵖ (σ.obj j))
    at hsourceLength
  exact
    QuotientSubmoduleEquidistribution.FamilyThreeSpecialization.moduleTop_isSimple_of_twoTargetModel
      (K := K) (R := Aᵐᵒᵖ) (M := σ.obj j)
      (QuotientSubmoduleEquidistribution.YonedaExtReflection.firstTargetScalarizedExtLinearMap
        (σ.obj s).obj (σ.obj w).obj (σ.obj t).obj ell hSC'.extClass)
      (QuotientSubmoduleEquidistribution.YonedaExtReflection.secondTargetScalarizedExtLinearMap
        (σ.obj s).obj (σ.obj w).obj (σ.obj t).obj ell' hSC'.extClass)
      hfork (by simpa using hsourceLength)

/-! ## Exact filtered input and collective closure -/

/-- The remaining filtered input for a chosen length-three uniserial source:
`Ext¹` from its simple top to its length-two radical type has dimension at
most one.  Finite-dimensionality itself follows from the finite-dimensional
algebra hypotheses, so the definition quantifies over that proof only to keep
the predicate independent of a chosen typeclass witness. -/
def UpperRadicalExtOneBound
    {u : σ.LengthThreeUniserialIndex}
    (W : σ.LengthTwoSubmodule u.1)
    (s : ι) : Prop :=
  ∀ [FiniteDimensional K
      (Ext (σ.obj s).obj (σ.obj W.index).obj 1)],
    Module.finrank K
      (Ext (σ.obj s).obj (σ.obj W.index).obj 1) ≤ 1

/-- The upper radical `Ext¹` bound forces simple top for every indecomposable
generated by the uniserial quotient chain.  All Loewy-layer and additive
decomposition inputs are discharged by maintained theorems. -/
theorem moduleTop_isSimple_of_inFac_quotientChain_of_upperRadicalExtOneBound
    {u : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain u)
    (W : σ.LengthTwoSubmodule u.1)
    (Q : σ.SimpleQuotient W.index)
    (T : σ.SimpleSubmodule W.index)
    (hupper : UpperRadicalExtOneBound (K := K) σ W C.bottom.index)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    IsSimpleModule Aᵐᵒᵖ (σ.moduleTop j) := by
  classical
  obtain ⟨P⟩ :=
    σ.exists_twoStepPowerPresentation_of_inFac_quotientChain C hj
  have hadd :
      σ.InAdd ({W.index, Q.index} : Set ι)
        (FGModuleCat.of Aᵐᵒᵖ (σ.moduleRadical j)) :=
    QuotientSubmoduleEquidistribution.LengthThreePaperSpecialization.moduleRadical_inAdd_lengthTwoPair
      K A σ u.2 W Q T P
  obtain ⟨J, L, hJ, hL, ⟨eRadical⟩⟩ :=
    exists_pairPowerDecomposition_of_inAdd (A := A) σ hadd
  letI : Fintype J := hJ
  letI : Fintype L := hL
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj C.bottom.index) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      C.bottom.simple
  have htopIsotypic :
      IsIsotypicOfType Aᵐᵒᵖ
        (σ.moduleTop j) (σ.obj C.bottom.index) :=
    σ.moduleTop_isIsotypicOfType_of_inFac_quotientChain C hj
  letI : IsSemisimpleModule Aᵐᵒᵖ (σ.moduleTop j) :=
    σ.moduleTop_isSemisimple j
  letI : Module.Finite Aᵐᵒᵖ (σ.moduleTop j) := inferInstance
  obtain ⟨I, eTop, htopLength⟩ :=
    QuotientSubmoduleEquidistribution.LoewyTwoRankCore.exists_isotypicMultiplicity
      htopIsotypic
  letI : FiniteDimensional K
      (Ext (σ.obj C.bottom.index).obj (σ.obj W.index).obj 1) :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.moduleFinite_ext_one_of_finiteDimensional
      (K := K) (R := Aᵐᵒᵖ)
  have hupper' :
      Module.finrank K
        (Ext (σ.obj C.bottom.index).obj (σ.obj W.index).obj 1) ≤ 1 :=
    hupper
  have hnoParallel :
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.NoParallelExtOne σ K :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
      K A σ
  apply moduleTop_isSimple_of_upperExtBound_of_twoBlockRadical
    (K := K) σ hnoParallel Q.simple C.bottom.simple
    (inferInstance : FiniteDimensional K
      (Ext (σ.obj C.bottom.index).obj (σ.obj W.index).obj 1))
    hupper' eRadical.symm eTop.symm
  simpa using htopLength

/-- Under the exact upper-radical `Ext¹` input, the support of a
length-three uniserial quotient chain is collectively quotient-closed. -/
theorem qClosure_isClosed_quotientChain_of_upperRadicalExtOneBound
    {u : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain u)
    (W : σ.LengthTwoSubmodule u.1)
    (Q : σ.SimpleQuotient W.index)
    (T : σ.SimpleSubmodule W.index)
    (hupper : UpperRadicalExtOneBound (K := K) σ W C.bottom.index) :
    σ.qClosure.IsClosed C.support := by
  rw [σ.qClosure_isClosed_quotientChain_iff_targetsHaveSimpleTop C]
  intro j hj
  exact
    moduleTop_isSimple_of_inFac_quotientChain_of_upperRadicalExtOneBound
      (K := K) σ C W Q T hupper hj

/-- Choice-free form of the exact filtered input: one (equivalently, by
uniserial uniqueness, any) chosen length-two submodule type of the source
satisfies the upper radical `Ext¹` bound. -/
def QuotientChainUpperRadicalExtOneBound
    {u : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain u) : Prop :=
  ∃ W : σ.LengthTwoSubmodule u.1,
    UpperRadicalExtOneBound (K := K) σ W C.bottom.index

/-- Choice-free final reduction: the sole upper-radical filtered bound
implies collective quotient closure of the entire three-object chain. -/
theorem qClosure_isClosed_quotientChain_of_filteredExtControl
    {u : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain u)
    (hfiltered : QuotientChainUpperRadicalExtOneBound (K := K) σ C) :
    σ.qClosure.IsClosed C.support := by
  obtain ⟨W, hupper⟩ := hfiltered
  let Q : σ.SimpleQuotient W.index :=
    Classical.choice (σ.exists_simpleQuotient W.index)
  let T : σ.SimpleSubmodule W.index :=
    Classical.choice (σ.exists_simpleSubmodule W.index)
  exact qClosure_isClosed_quotientChain_of_upperRadicalExtOneBound
    (K := K) σ C W Q T hupper

end QuotientSubmoduleEquidistribution.UniserialCollectiveFinal
