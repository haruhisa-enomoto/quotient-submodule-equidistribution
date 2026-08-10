import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveSimpleRank

/-!
# Recognition of an indecomposable projective from its simple top

The maintained projective--simple bijection is upgraded here to an
object-level statement.  An arbitrary indecomposable projective with an
epimorphism to a chosen simple is isomorphic to the corresponding chosen
projective representative.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank

universe u v

open QuotientSubmoduleEquidistribution.ProjectiveSimpleTop

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The chosen indecomposable-projective label corresponding to a chosen
simple label. -/
def projectiveLabelOfSimple (j : σ.SimpleIndex) : ι :=
  ((projectiveIndexEquivSimpleIndex σ).symm j).1

omit [Finite ι] in
/-- The representative selected by `projectiveLabelOfSimple` is
projective. -/
theorem projective_projectiveLabelOfSimple (j : σ.SimpleIndex) :
    CategoryTheory.Projective (σ.obj (projectiveLabelOfSimple σ j)) :=
  ((projectiveIndexEquivSimpleIndex σ).symm j).2

omit [Finite ι] in
/-- An indecomposable projective admitting an epimorphism to a chosen simple
is isomorphic to the chosen projective corresponding to that simple. -/
theorem projective_iso_of_indec_of_epi_to_simple
    (X : FGModuleCat.{u} R)
    (hProjective : CategoryTheory.Projective X)
    (hIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (j : σ.SimpleIndex)
    (f : X ⟶ σ.obj j.1) [Epi f] :
    Nonempty
      (X ≅ σ.obj (projectiveLabelOfSimple σ j)) := by
  obtain ⟨i, ⟨e⟩⟩ := σ.complete X hIndec
  have hPi : CategoryTheory.Projective (σ.obj i) :=
    CategoryTheory.Projective.of_iso e hProjective
  let p : ProjectiveIndex σ := ⟨i, hPi⟩
  let f' : σ.obj p.1 ⟶ σ.obj j.1 := e.inv ≫ f
  letI : Epi f' := by
    dsimp [f']
    infer_instance
  letI : CategoryTheory.Projective (σ.obj p.1) := p.2
  letI : Module.Projective R (σ.obj p.1) :=
    moduleProjective_of_fgProjective (σ.obj p.1) p.2
  letI : Nontrivial (σ.obj p.1) := (σ.indecomposable p.1).nontrivial
  letI : IsLocalRing (Module.End R (σ.obj p.1)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      (σ.finiteLength p.1) (σ.indecomposable p.1)
  letI : IsSimpleModule R (σ.obj j.1) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp j.2
  let eTop : projectiveTop σ p ≅ σ.obj j.1 :=
    (topLinearEquivOfSurjectiveToSimple f'.hom.hom
      ((IndecomposableSkeleton.fg_epi_iff_surjective f').mp
        inferInstance)).toFGModuleCatIso
  have hTop : projectiveTopIndex σ p = j := by
    apply Subtype.ext
    apply σ.eq_of_iso
    exact ⟨(projectiveTopIso σ p).symm ≪≫ eTop⟩
  let q : ProjectiveIndex σ :=
    (projectiveIndexEquivSimpleIndex σ).symm j
  have hpq : p = q := by
    apply (projectiveIndexEquivSimpleIndex σ).injective
    change projectiveTopIndex σ p = projectiveTopIndex σ q
    rw [hTop]
    exact (projectiveIndexEquivSimpleIndex σ).apply_symm_apply j |>.symm
  let epq : σ.obj p.1 ≅ σ.obj q.1 :=
    eqToIso (congrArg (fun r : ProjectiveIndex σ ↦ σ.obj r.1) hpq)
  exact ⟨e ≪≫ epq⟩

omit [Finite ι] in
/-- Literal-top form: an indecomposable projective whose radical quotient is
the chosen simple `j` is the chosen projective corresponding to `j`. -/
theorem projective_iso_of_indec_of_top_iso
    (X : FGModuleCat.{u} R)
    (hProjective : CategoryTheory.Projective X)
    (hIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (j : σ.SimpleIndex)
    (eTop :
      FGModuleCat.of R (X ⧸ Module.jacobson R X) ≅ σ.obj j.1) :
    Nonempty
      (X ≅ σ.obj (projectiveLabelOfSimple σ j)) := by
  let q : X ⟶ FGModuleCat.of R (X ⧸ Module.jacobson R X) :=
    FGModuleCat.ofHom (Module.jacobson R X).mkQ
  let f : X ⟶ σ.obj j.1 := q ≫ eTop.hom
  have hq : Function.Surjective q.hom.hom :=
    (Module.jacobson R X).mkQ_surjective
  have hf : Function.Surjective f.hom.hom :=
    (FGModuleCat.isoToLinearEquiv eTop).surjective.comp hq
  letI : Epi f :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).mpr hf
  exact
    projective_iso_of_indec_of_epi_to_simple
      σ X hProjective hIndec j f

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank
