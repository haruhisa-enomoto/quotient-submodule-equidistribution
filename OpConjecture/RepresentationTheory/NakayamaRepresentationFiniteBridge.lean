import OpConjecture.RepresentationTheory.DualFixedSocleTransport
import OpConjecture.RepresentationTheory.ExtDegreeNakayamaReduction
import OpConjecture.RepresentationTheory.FaithfulCore

/-!
# Representation-finiteness from the Nakayama module condition

This file removes representation-finiteness as a separate hypothesis from the
all-indecomposables-uniserial formulation of the Nakayama theorem.  The proof
is classification-free: indecomposable projectives form a finite set because
they occur in a fixed finite decomposition of the regular module, and every
indecomposable is determined by a projective source and its composition
length.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.NakayamaRepresentationFiniteBridge

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

open OpConjecture.IndecomposableSkeleton.FaithfulCore

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} R ι)

/-- Every finitely generated module is a quotient of a finite sum of chosen
indecomposable projectives, without any finiteness hypothesis on the complete
skeleton. -/
theorem inFac_projectiveLabels
    (X : FGModuleCat.{u} R) :
    σ.InFac (projectiveLabels σ) X := by
  classical
  obtain ⟨L, p, hp⟩ :=
    regularFGModule_generates (R := R) X
  have hsumAdd :
      σ.InAdd (projectiveLabels σ)
        (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    σ.inAdd_biproduct L
      (fun _ : L ↦ regularFGModule (R := R))
      (fun _ ↦ regularFGModule_inAdd_projectiveLabels σ)
  obtain ⟨P⟩ := hsumAdd
  letI : Epi p := hp
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.inv ≫ p
    epi := by infer_instance }⟩

/-- A finite-length indecomposable with simple top is an epimorphic image of
one chosen indecomposable projective. -/
theorem exists_epi_from_indec_projective_of_simpleTop
    (i : ι)
    (hTop : IsSimpleModule R (σ.moduleTop i)) :
    ∃ p : ι,
      CategoryTheory.Projective (σ.obj p) ∧
        ∃ f : σ.obj p ⟶ σ.obj i, Epi f := by
  obtain ⟨P⟩ := inFac_projectiveLabels σ (σ.obj i)
  letI : Epi P.map := P.epi
  obtain ⟨t, ht⟩ :=
    σ.exists_epi_biproduct_component_of_simple_top
      P.index P.label hTop P.map
  exact ⟨P.label t, P.mem t,
    biproduct.ι (fun b : P.index ↦ σ.obj (P.label b)) t ≫ P.map,
    ht⟩

/-- Simple tops and uniserial indecomposable projectives force every
indecomposable to be uniserial, without first assuming a finite skeleton. -/
theorem all_indec_uniserial_of_simpleTops_of_projectiveUniserial
    (hTop :
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σ)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ) :
    OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ := by
  intro i
  obtain ⟨p, hpProjective, f, hf⟩ :=
    exists_epi_from_indec_projective_of_simpleTop σ i (hTop i)
  letI : Epi f := hf
  have hP : OpConjecture.IsUniserialModule R (σ.obj p) :=
    hProjective p hpProjective
  have hQuot :
      OpConjecture.IsUniserialModule R
        ((σ.obj p) ⧸ LinearMap.ker f.hom.hom) :=
    hP.quotient (LinearMap.ker f.hom.hom)
  have hfSurj : Function.Surjective f.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective f).mp
      inferInstance
  exact
    OpConjecture.ExtDegreeNakayamaReduction.isUniserialModule_congr
      (f.hom.hom.quotKerEquivOfSurjective hfSurj) hQuot

/-- The chosen indecomposable-projective labels form a finite set even if
the ambient complete indecomposable skeleton is not yet known to be finite. -/
theorem finite_projectiveLabels :
    (projectiveLabels σ).Finite := by
  classical
  obtain ⟨P⟩ := regularFGModule_inAdd_projectiveLabels σ
  let S : Set ι := Set.range P.label
  have hSfinite : S.Finite := Set.finite_range P.label
  apply hSfinite.subset
  intro i hi
  letI : CategoryTheory.Projective (σ.obj i) := hi
  obtain ⟨L, p, hp⟩ :=
    regularFGModule_generates (R := R) (σ.obj i)
  letI : Epi p := hp
  let lift : σ.obj i ⟶
      (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    CategoryTheory.Projective.factorThru (𝟙 (σ.obj i)) p
  have hlift : lift ≫ p = 𝟙 (σ.obj i) :=
    CategoryTheory.Projective.factorThru_comp (𝟙 (σ.obj i)) p
  let retract : Retract (σ.obj i)
      (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    { i := lift
      r := p
      retract := hlift }
  have hregS : σ.InAdd S (regularFGModule (R := R)) :=
    ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ ⟨t, rfl⟩
      iso := P.iso }⟩
  have hsumS :
      σ.InAdd S (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    σ.inAdd_biproduct L
      (fun _ : L ↦ regularFGModule (R := R))
      (fun _ ↦ hregS)
  exact σ.index_mem_of_retract_inAdd retract hsumS

/-- Equal-length epimorphic images of the same finite-length uniserial source
are represented by the same skeleton label. -/
theorem label_eq_of_epi_from_uniserial_of_compositionLength_eq
    {p i j : ι}
    (hP : OpConjecture.IsUniserialModule R (σ.obj p))
    (f : σ.obj p ⟶ σ.obj i) [Epi f]
    (g : σ.obj p ⟶ σ.obj j) [Epi g]
    (hLength : σ.compositionLength i = σ.compositionLength j) :
    i = j := by
  have hModuleLength :
      Module.length R (σ.obj i) = Module.length R (σ.obj j) := by
    rw [← σ.coe_compositionLength i,
      ← σ.coe_compositionLength j, hLength]
  have hker :
      LinearMap.ker f.hom.hom = LinearMap.ker g.hom.hom :=
    OpConjecture.NakayamaProjectiveQuotients.ker_eq_of_epi_of_length_eq_of_isUniserial
      hP (σ.finiteLength p) (σ.finiteLength i) f g hModuleLength
  have hfSurj : Function.Surjective f.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective f).mp
      inferInstance
  have hgSurj : Function.Surjective g.hom.hom :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective g).mp
      inferInstance
  let e : σ.obj i ≃ₗ[R] σ.obj j :=
    (f.hom.hom.quotKerEquivOfSurjective hfSurj).symm.trans
      ((Submodule.quotEquivOfEq
        (LinearMap.ker f.hom.hom)
        (LinearMap.ker g.hom.hom) hker).trans
          (g.hom.hom.quotKerEquivOfSurjective hgSurj))
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- A chosen indecomposable-projective epimorphism onto a simple-top
indecomposable. -/
structure ProjectiveQuotient (i : ι) where
  label : ι
  projective : CategoryTheory.Projective (σ.obj label)
  map : σ.obj label ⟶ σ.obj i
  epi : Epi map

/-- Choose the projective quotient supplied by a simple top. -/
def projectiveQuotientChoice
    (hTop :
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σ)
    (i : ι) : ProjectiveQuotient σ i :=
  let h :=
    exists_epi_from_indec_projective_of_simpleTop σ i (hTop i)
  let p := Classical.choose h
  let hp := (Classical.choose_spec h).1
  let hfExists := (Classical.choose_spec h).2
  let f := Classical.choose hfExists
  let hf := Classical.choose_spec hfExists
  ⟨p, hp, f, hf⟩

/-- The finite dependent type recording a projective source and a possible
composition length bounded by that source. -/
abbrev ProjectiveLengthCode :=
  Σ p : {i : ι // CategoryTheory.Projective (σ.obj i)},
    Fin (σ.compositionLength p.1 + 1)

/-- Code an indecomposable by a chosen projective source and its composition
length. -/
def projectiveLengthCode
    (hTop :
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σ)
    (i : ι) : ProjectiveLengthCode σ := by
  let Q := projectiveQuotientChoice σ hTop i
  refine ⟨⟨Q.label, Q.projective⟩,
    ⟨σ.compositionLength i, Nat.lt_succ_of_le ?_⟩⟩
  letI : Epi Q.map := Q.epi
  exact σ.compositionLength_le_of_epi Q.map

/-- Under projective uniseriality, the projective-length code is injective. -/
theorem projectiveLengthCode_injective
    (hTop :
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σ)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ) :
    Function.Injective (projectiveLengthCode σ hTop) := by
  intro i j hij
  let Qi := projectiveQuotientChoice σ hTop i
  let Qj := projectiveQuotientChoice σ hTop j
  have hpSubtype :
      (⟨Qi.label, Qi.projective⟩ :
          {k : ι // CategoryTheory.Projective (σ.obj k)}) =
        ⟨Qj.label, Qj.projective⟩ :=
    congrArg Sigma.fst hij
  have hp : Qi.label = Qj.label :=
    congrArg Subtype.val hpSubtype
  have hLength :
      σ.compositionLength i = σ.compositionLength j :=
    congrArg (fun z ↦ z.2.val) hij
  letI : Epi Qi.map := Qi.epi
  letI : Epi Qj.map := Qj.epi
  let g : σ.obj Qi.label ⟶ σ.obj j :=
    eqToHom (congrArg σ.obj hp) ≫ Qj.map
  letI : Epi g := by
    dsimp [g]
    infer_instance
  exact
    label_eq_of_epi_from_uniserial_of_compositionLength_eq
      σ (hProjective Qi.label Qi.projective)
      Qi.map g hLength

/-- A complete skeleton with simple indecomposable tops and uniserial
indecomposable projectives is finite. -/
theorem finite_of_simpleTops_of_projectiveUniserial
    (hTop :
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σ)
    (hProjective :
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σ) :
    Finite ι := by
  letI : Finite
      {i : ι // CategoryTheory.Projective (σ.obj i)} :=
    finite_projectiveLabels σ
  exact Finite.of_injective
    (projectiveLengthCode σ hTop)
    (projectiveLengthCode_injective σ hTop hProjective)

/-- In particular, the all-indecomposables-uniserial Nakayama condition
already implies representation-finiteness. -/
theorem finite_of_all_indec_uniserial
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σ) :
    Finite ι := by
  exact finite_of_simpleTops_of_projectiveUniserial σ
    (OpConjecture.ExtDegreeNakayamaReduction.simpleTops_of_isNakayamaSkeleton
      σ hNakayama)
    (OpConjecture.LocalNakayamaBranch.isProjectiveNakayamaSkeleton_of_isNakayamaSkeleton
      σ hNakayama)

/-! ## Canonical finite-dimensional right-module endpoints -/

universe z

/-- For a finite-dimensional algebra, the all-indecomposable-right-modules
uniserial condition implies right representation-finiteness. -/
theorem rightRepresentationFinite_of_all_indec_uniserial
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σA) :
    OpConjecture.IsRightRepresentationFinite.{z, z, z} K A := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  let σA := OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
  exact finite_of_all_indec_uniserial σA hNakayama

/-- The maintained strong equidistribution theorem therefore applies to the
all-indecomposable-right-modules-uniserial formulation with no separate
representation-finiteness assumption. -/
theorem rightEquidistribution_of_all_indec_uniserial
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σA) :
    ∃ hA : OpConjecture.IsRightRepresentationFinite.{z, z, z} K A,
      OpConjecture.RightQuotientSubmoduleEquidistribution K A hA := by
  let hA : OpConjecture.IsRightRepresentationFinite.{z, z, z} K A :=
    rightRepresentationFinite_of_all_indec_uniserial K A hNakayama
  refine ⟨hA, ?_⟩
  apply
    OpConjecture.DualFixedSocleTransport.rightEquidistribution_of_all_indec_uniserial
      K A hA
  exact hNakayama

/-- Simple tops and uniserial indecomposable projectives give the same
paper-facing endpoint. -/
theorem rightEquidistribution_of_simpleTops_of_projectiveUniserial
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hTop :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
      OpConjecture.ExtDegreeNakayamaReduction.AllIndecomposableTopsSimple σA)
    (hProjective :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
      let σA :=
        OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
      OpConjecture.LocalNakayamaBranch.IsProjectiveNakayamaSkeleton σA) :
    ∃ hA : OpConjecture.IsRightRepresentationFinite.{z, z, z} K A,
      OpConjecture.RightQuotientSubmoduleEquidistribution K A hA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  let σA := OpConjecture.rightIndecomposableSkeleton.{z, z, z} K A
  have hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton σA :=
    all_indec_uniserial_of_simpleTops_of_projectiveUniserial
      σA hTop hProjective
  exact rightEquidistribution_of_all_indec_uniserial K A hNakayama

end OpConjecture.NakayamaRepresentationFiniteBridge
