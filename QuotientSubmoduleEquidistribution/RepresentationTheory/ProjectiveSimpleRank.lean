import QuotientSubmoduleEquidistribution.RepresentationTheory.FaithfulCore
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleTop

/-!
# Indecomposable projectives and simple labels

Maintained formalization of the classical bijection sending an indecomposable
projective module to its simple top.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore
open QuotientSubmoduleEquidistribution.ProjectiveSimpleTop
open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

omit [IsNoetherianRing R] in
/-- A categorical projective in `FGModuleCat` is projective as an
unbundled module. -/
theorem moduleProjective_of_fgProjective
    (X : FGModuleCat.{u} R) (hX : CategoryTheory.Projective X) :
    Module.Projective R X := by
  classical
  letI : CategoryTheory.Projective X := hX
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let F : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : F ⟶ X := FGModuleCat.ofHom p
  haveI : Epi q :=
    (IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  obtain ⟨s, hs⟩ := CategoryTheory.Projective.factors (𝟙 X) q
  letI : Module.Projective R F :=
    Module.Projective.of_basis (Pi.basisFun R (Fin n))
  apply Module.Projective.of_split s.hom.hom q.hom.hom
  exact congrArg (fun f : X ⟶ X ↦ f.hom.hom) hs

/-- The chosen indecomposable projective labels. -/
abbrev ProjectiveIndex :=
  {i : iota // CategoryTheory.Projective (sigma.obj i)}

/-- The concrete radical quotient attached to a projective label. -/
abbrev projectiveTop (p : ProjectiveIndex sigma) : FGModuleCat.{u} R :=
  FGModuleCat.of R
    ((sigma.obj p.1) ⧸ Module.jacobson R (sigma.obj p.1))

/-- The radical quotient of an indecomposable projective is simple. -/
theorem projectiveTop_isSimple (p : ProjectiveIndex sigma) :
    Simple (projectiveTop sigma p) := by
  letI : CategoryTheory.Projective (sigma.obj p.1) := p.2
  letI : Module.Projective R (sigma.obj p.1) :=
    moduleProjective_of_fgProjective (sigma.obj p.1) p.2
  rw [IndecomposableSkeleton.simple_iff_isSimpleModule_fg]
  exact
    simple_top_of_indec_projective
      (sigma.finiteLength p.1) (sigma.indecomposable p.1)

/-- A chosen skeleton representative of the simple top, together with the
identifying isomorphism. -/
def projectiveTopChoice (p : ProjectiveIndex sigma) :
    Σ s : sigma.SimpleIndex,
      projectiveTop sigma p ≅ sigma.obj s.1 := by
  let hsimple : Simple (projectiveTop sigma p) :=
    projectiveTop_isSimple sigma p
  letI : IsSimpleModule R (projectiveTop sigma p) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hsimple
  have hindec :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (projectiveTop sigma p) :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  let hcomplete := sigma.complete (projectiveTop sigma p) hindec
  let i := Classical.choose hcomplete
  let e := Classical.choice (Classical.choose_spec hcomplete)
  exact ⟨⟨i, (Simple.iff_of_iso e).mp hsimple⟩, e⟩

/-- The simple skeleton label given by the top of an indecomposable
projective. -/
def projectiveTopIndex (p : ProjectiveIndex sigma) : sigma.SimpleIndex :=
  (projectiveTopChoice sigma p).1

/-- The chosen projective top is isomorphic to the representative selected
by `projectiveTopIndex`. -/
def projectiveTopIso (p : ProjectiveIndex sigma) :
    projectiveTop sigma p ≅
      sigma.obj (projectiveTopIndex sigma p).1 :=
  (projectiveTopChoice sigma p).2

/-- The radical quotient map, transported to the selected simple skeleton
representative, is a projective cover in `ModuleCat`. -/
def projectiveCoverOfTopIndex (p : ProjectiveIndex sigma) :
    ProjectiveCover
      (ModuleCat.of R (sigma.obj (projectiveTopIndex sigma p).1)) := by
  letI : CategoryTheory.Projective (sigma.obj p.1) := p.2
  letI : Module.Projective R (sigma.obj p.1) :=
    moduleProjective_of_fgProjective (sigma.obj p.1) p.2
  let e := projectiveTopIso sigma p
  exact
    (jacobsonProjectiveCoverOfIndecomposable
      (sigma.finiteLength p.1) (sigma.indecomposable p.1)).postIso
        (FGModuleCat.isoToLinearEquiv e).toModuleIso

/-- The source of the selected projective cover is the original chosen
indecomposable projective. -/
theorem projectiveCoverOfTopIndex_object (p : ProjectiveIndex sigma) :
    (projectiveCoverOfTopIndex sigma p).object =
      ModuleCat.of R (sigma.obj p.1) := by
  rfl

/-- Two indecomposable projectives with isomorphic simple tops have the same
skeleton label. -/
theorem projectiveTopIndex_injective :
    Function.Injective (projectiveTopIndex sigma) := by
  intro p q hpq
  apply Subtype.ext
  apply sigma.eq_of_iso
  let eTop :
      ModuleCat.of R (sigma.obj (projectiveTopIndex sigma p).1) ≅
        ModuleCat.of R (sigma.obj (projectiveTopIndex sigma q).1) :=
    eqToIso (congrArg (fun s : sigma.SimpleIndex ↦
      ModuleCat.of R (sigma.obj s.1)) hpq)
  let eProjective :
      (projectiveCoverOfTopIndex sigma p).object ≅
        (projectiveCoverOfTopIndex sigma q).object :=
    ProjectiveCover.objectIsoOfTargetIso
      (projectiveCoverOfTopIndex sigma p)
      (projectiveCoverOfTopIndex sigma q) eTop
  let eProjective' :
      ModuleCat.of R (sigma.obj p.1) ≅
        ModuleCat.of R (sigma.obj q.1) :=
    eqToIso (projectiveCoverOfTopIndex_object sigma p).symm ≪≫
      eProjective ≪≫
        eqToIso (projectiveCoverOfTopIndex_object sigma q)
  exact ⟨eProjective'.toLinearEquiv.toFGModuleCatIso⟩

/-- Every finitely generated module is a quotient of a finite sum of chosen
indecomposable projectives, without a finiteness hypothesis on the complete
skeleton. -/
theorem inFac_projectiveLabels
    (X : FGModuleCat.{u} R) :
    sigma.InFac (projectiveLabels sigma) X := by
  classical
  obtain ⟨L, p, hp⟩ :=
    regularFGModule_generates (R := R) X
  have hsumAdd :
      sigma.InAdd (projectiveLabels sigma)
        (⨁ fun _ : L ↦ regularFGModule (R := R)) :=
    sigma.inAdd_biproduct L
      (fun _ : L ↦ regularFGModule (R := R))
      (fun _ ↦ regularFGModule_inAdd_projectiveLabels sigma)
  obtain ⟨P⟩ := hsumAdd
  letI : Epi p := hp
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.iso.inv ≫ p
    epi := by infer_instance }⟩

/-- Every simple skeleton label is the top of some chosen indecomposable
projective label.  The argument is local and does not assume that the ambient
indecomposable skeleton is finite. -/
theorem projectiveTopIndex_surjective :
    Function.Surjective (projectiveTopIndex sigma) := by
  intro s
  let S : FGModuleCat.{u} R := sigma.obj s.1
  letI : Simple S := s.2
  letI : IsSimpleModule R S :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg S).mp s.2
  have hfac : sigma.InFac (projectiveLabels sigma) S :=
    inFac_projectiveLabels sigma S
  obtain ⟨P⟩ := hfac
  letI : Epi P.map := P.epi
  have hmap : P.map ≠ 0 := by
    intro hzero
    exact Simple.not_isZero S (IsZero.of_epi_eq_zero P.map hzero)
  have hcomponent :
      ∃ t : P.index,
        biproduct.ι (fun a : P.index ↦ sigma.obj (P.label a)) t ≫
          P.map ≠ 0 := by
    by_contra h
    push Not at h
    apply hmap
    apply biproduct.hom_ext'
    intro t
    exact h t
  obtain ⟨t, ht⟩ := hcomponent
  let p : ProjectiveIndex sigma := ⟨P.label t, P.mem t⟩
  let f : sigma.obj p.1 ⟶ S :=
    biproduct.ι (fun a : P.index ↦ sigma.obj (P.label a)) t ≫ P.map
  have hf : f ≠ 0 := ht
  letI : Epi f := epi_of_nonzero_to_simple hf
  letI : CategoryTheory.Projective (sigma.obj p.1) := p.2
  letI : Module.Projective R (sigma.obj p.1) :=
    moduleProjective_of_fgProjective (sigma.obj p.1) p.2
  letI : Nontrivial (sigma.obj p.1) :=
    (sigma.indecomposable p.1).nontrivial
  letI : IsLocalRing (Module.End R (sigma.obj p.1)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      (sigma.finiteLength p.1) (sigma.indecomposable p.1)
  let eToSimple : projectiveTop sigma p ≅ S :=
    (topLinearEquivOfSurjectiveToSimple f.hom.hom
      ((IndecomposableSkeleton.fg_epi_iff_surjective f).mp inferInstance)).toFGModuleCatIso
  let eTop := projectiveTopIso sigma p
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply sigma.eq_of_iso
  exact ⟨eTop.symm ≪≫ eToSimple⟩

/-- Projective labels are in exact bijection with simple-module labels via
their radical quotients. -/
def projectiveIndexEquivSimpleIndex :
    ProjectiveIndex sigma ≃ sigma.SimpleIndex :=
  Equiv.ofBijective (projectiveTopIndex sigma)
    ⟨projectiveTopIndex_injective sigma,
      projectiveTopIndex_surjective sigma⟩

/-- The chosen indecomposable-projective label set and the chosen simple
label type have the same cardinality. -/
theorem ncard_projectiveLabels_eq_natCard_simpleIndex :
    (projectiveLabels sigma).ncard = Nat.card sigma.SimpleIndex := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr (projectiveIndexEquivSimpleIndex sigma)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
