import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveBoundary
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Finite projective presentations and the Auslander transpose

This file constructs a two-step finite projective presentation of every
finitely generated module over a left Noetherian ring.  Applying regular-Hom
duality to its projective terms defines the Auslander transpose attached to
the chosen presentation.

The presentations in this file are arbitrary projective epimorphisms, not
minimal projective covers.  Accordingly the transpose is explicitly
presentation-dependent; no Auslander--Reiten translate is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose

universe u

open QuotientSubmoduleEquidistribution.RingelStable

variable {R : Type u} [Ring R]

private theorem projectivePresentation_nonempty
    (X : FGModuleCat.{u} R) : Nonempty (ProjectivePresentation X) := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let P : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : P ⟶ X := FGModuleCat.ofHom p
  have hP : Projective P := by
    apply fgProjective_of_moduleProjective
    exact Module.Projective.of_basis (Pi.basisFun R (Fin n))
  have hq : Epi q :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  exact ⟨{ p := P, projective := hP, f := q, epi := hq }⟩

/-- The category of finitely generated modules has enough finitely generated
projective objects over every ring. -/
instance fgModuleCat_enoughProjectives :
    EnoughProjectives (FGModuleCat.{u} R) where
  presentation := projectivePresentation_nonempty

variable [IsNoetherianRing R]

/-- A two-step finite projective presentation consists of a projective
epimorphism onto `X` and a projective epimorphism onto its kernel.  Neither
epimorphism is asserted to be minimal. -/
structure TwoStepProjectivePresentation (X : FGModuleCat.{u} R) where
  augmentation : ProjectivePresentation X
  syzygyPresentation : ProjectivePresentation (kernel augmentation.f)

/-- Every finitely generated module over a left Noetherian ring has a
two-step finite projective presentation. -/
theorem twoStepProjectivePresentation_nonempty
    (X : FGModuleCat.{u} R) :
    Nonempty (TwoStepProjectivePresentation X) := by
  obtain ⟨P₀⟩ :=
    (inferInstance : Nonempty (ProjectivePresentation X))
  obtain ⟨P₁⟩ :=
    (inferInstance : Nonempty (ProjectivePresentation (kernel P₀.f)))
  exact ⟨⟨P₀, P₁⟩⟩

namespace TwoStepProjectivePresentation

variable {X : FGModuleCat.{u} R}

/-- The first differential `P₁ ⟶ P₀`. -/
def differential (P : TwoStepProjectivePresentation X) :
    P.syzygyPresentation.p ⟶ P.augmentation.p :=
  P.syzygyPresentation.f ≫ kernel.ι P.augmentation.f

@[simp]
theorem differential_comp_augmentation
    (P : TwoStepProjectivePresentation X) :
    P.differential ≫ P.augmentation.f = 0 := by
  simp [differential]

/-- The projective presentation as the short complex `P₁ ⟶ P₀ ⟶ X`. -/
def presentationComplex (P : TwoStepProjectivePresentation X) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk P.differential P.augmentation.f
    P.differential_comp_augmentation

/-- The stored syzygy presentation certifies exactness of
`P₁ ⟶ P₀ ⟶ X`. -/
theorem presentationComplex_exact (P : TwoStepProjectivePresentation X) :
    P.presentationComplex.Exact := by
  change (ShortComplex.mk P.differential P.augmentation.f
    P.differential_comp_augmentation).Exact
  apply (ShortComplex.exact_iff_epi_kernel_lift _).2
  have hLift :
      kernel.lift P.augmentation.f P.differential
          P.differential_comp_augmentation =
        P.syzygyPresentation.f := by
    apply (cancel_mono (kernel.ι P.augmentation.f)).1
    simp [differential]
  rw [hLift]
  infer_instance

/-- The zeroth projective term, bundled in the full subcategory of finite
projectives. -/
abbrev P₀ (P : TwoStepProjectivePresentation X) : FGProjectives (R := R) :=
  ⟨P.augmentation.p, P.augmentation.projective⟩

/-- The first projective term, bundled in the full subcategory of finite
projectives. -/
abbrev P₁ (P : TwoStepProjectivePresentation X) : FGProjectives (R := R) :=
  ⟨P.syzygyPresentation.p, P.syzygyPresentation.projective⟩

/-- The differential bundled between finite projectives. -/
def projectiveDifferential (P : TwoStepProjectivePresentation X) :
    P.P₁ ⟶ P.P₀ :=
  ObjectProperty.homMk P.differential

variable [IsNoetherianRing Rᵐᵒᵖ]

/-- The regular-Hom dual of the zeroth projective term. -/
def homDualP₀ (P : TwoStepProjectivePresentation X) :
    FGProjectives (R := Rᵐᵒᵖ) :=
  (fgProjectiveHomDuality (R := R)).functor.obj (Opposite.op P.P₀)

/-- The regular-Hom dual of the first projective term. -/
def homDualP₁ (P : TwoStepProjectivePresentation X) :
    FGProjectives (R := Rᵐᵒᵖ) :=
  (fgProjectiveHomDuality (R := R)).functor.obj (Opposite.op P.P₁)

/-- The underlying Hom-dual differential `P₀* ⟶ P₁*`. -/
def dualDifferential (P : TwoStepProjectivePresentation X) :
    P.homDualP₀.obj ⟶ P.homDualP₁.obj :=
  ((fgProjectiveHomDuality (R := R)).functor.map
    P.projectiveDifferential.op).hom

/-- The Auslander transpose attached to the chosen projective presentation.
No minimal or presentation-independent object is asserted. -/
def transpose (P : TwoStepProjectivePresentation X) :
    FGModuleCat.{u} Rᵐᵒᵖ :=
  cokernel P.dualDifferential

/-- The cokernel projection `P₁* ⟶ Tr X`. -/
def transposeProjection (P : TwoStepProjectivePresentation X) :
    P.homDualP₁.obj ⟶ P.transpose :=
  cokernel.π P.dualDifferential

@[simp]
theorem dualDifferential_comp_transposeProjection
    (P : TwoStepProjectivePresentation X) :
    P.dualDifferential ≫ P.transposeProjection = 0 := by
  exact cokernel.condition P.dualDifferential

/-- The defining short complex `P₀* ⟶ P₁* ⟶ Tr X`. -/
def transposeComplex (P : TwoStepProjectivePresentation X) :
    ShortComplex (FGModuleCat.{u} Rᵐᵒᵖ) :=
  ShortComplex.mk P.dualDifferential P.transposeProjection
    P.dualDifferential_comp_transposeProjection

/-- The defining transpose complex is exact. -/
theorem transposeComplex_exact (P : TwoStepProjectivePresentation X) :
    P.transposeComplex.Exact :=
  ShortComplex.exact_cokernel _

end TwoStepProjectivePresentation

end QuotientSubmoduleEquidistribution.AuslanderTranspose
