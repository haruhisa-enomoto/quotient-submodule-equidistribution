import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderTranspose
import QuotientSubmoduleEquidistribution.RepresentationTheory.ArtinDualityInterface

/-!
# Artin duality applied to the Auslander transpose

An abstract finite-module Artin duality sends the defining cokernel sequence
of the transpose to an exact injective copresentation

`0 ⟶ DTr X ⟶ νP₁ ⟶ νP₀`.

As in `AuslanderTranspose`, all objects in this file are attached to a chosen,
possibly nonminimal, projective presentation.  In particular `DTr X` is not
asserted to be presentation-independent or to be the Auslander--Reiten
translate of `X`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.ArtinDuality

universe u

variable {R : Type u} [Ring R]

/-- A finite-module anti-equivalence, together with finite projective
presentations, gives enough injectives in the finite left-module category. -/
theorem Data.enoughInjectives (D : Data R) :
    EnoughInjectives (FGModuleCat.{u} R) :=
  (D.moduleEquiv.enoughInjectives_iff).mp inferInstance

end QuotientSubmoduleEquidistribution.ArtinDuality

namespace QuotientSubmoduleEquidistribution.AuslanderTranspose

universe u

variable {R : Type u} [Ring R]
  [IsNoetherianRing R] [IsNoetherianRing Rᵐᵒᵖ]
  {X : FGModuleCat.{u} R}

namespace TwoStepProjectivePresentation

/-- The `DTr` object attached to the chosen projective presentation and
finite-module duality. -/
def dTranspose (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : FGModuleCat.{u} R :=
  D.moduleEquiv.functor.obj (Opposite.op P.transpose)

/-- The first Nakayama term `νP₁ = D(P₁*)` attached to the presentation. -/
def nakayamaP₁ (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : FGModuleCat.{u} R :=
  D.moduleEquiv.functor.obj (Opposite.op P.homDualP₁.obj)

/-- The zeroth Nakayama term `νP₀ = D(P₀*)` attached to the presentation. -/
def nakayamaP₀ (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : FGModuleCat.{u} R :=
  D.moduleEquiv.functor.obj (Opposite.op P.homDualP₀.obj)

/-- The monomorphism `DTr X ⟶ νP₁` obtained by dualizing the
transpose cokernel projection. -/
def dTransposeι (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) :
    P.dTranspose D ⟶ P.nakayamaP₁ D :=
  D.moduleEquiv.functor.map P.transposeProjection.op

/-- The second map `νP₁ ⟶ νP₀` in the `DTr` copresentation. -/
def dTransposeNext (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) :
    P.nakayamaP₁ D ⟶ P.nakayamaP₀ D :=
  D.moduleEquiv.functor.map P.dualDifferential.op

instance dTransposeι_mono (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : Mono (P.dTransposeι D) := by
  haveI : Epi (cokernel.π P.dualDifferential) := inferInstance
  haveI : Mono (cokernel.π P.dualDifferential).op := inferInstance
  dsimp [dTransposeι, transposeProjection, dTranspose, nakayamaP₁]
  exact Functor.map_mono D.moduleEquiv.functor
    (cokernel.π P.dualDifferential).op

@[simp]
theorem dTransposeι_comp_dTransposeNext
    (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) :
    P.dTransposeι D ≫ P.dTransposeNext D = 0 := by
  dsimp [dTransposeι, dTransposeNext, dTranspose, nakayamaP₁,
    nakayamaP₀]
  rw [← D.moduleEquiv.functor.map_comp]
  change D.moduleEquiv.functor.map
      (P.dualDifferential ≫ P.transposeProjection).op = 0
  rw [P.dualDifferential_comp_transposeProjection, op_zero,
    D.moduleEquiv.functor.map_zero]

/-- The two-term injective copresentation beginning at `DTr X`. -/
def dTransposeCopresentation (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) :
    ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (P.dTransposeι D) (P.dTransposeNext D)
    (P.dTransposeι_comp_dTransposeNext D)

/-- The first Nakayama term in the copresentation is injective. -/
theorem injective_nakayamaP₁ (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : Injective (P.nakayamaP₁ D) := by
  have hQop : Injective (Opposite.op P.homDualP₁.obj) :=
    Injective.projective_iff_injective_op.mp P.homDualP₁.property
  exact (D.moduleEquiv.map_injective_iff _).2 hQop

/-- The second Nakayama term in the copresentation is injective. -/
theorem injective_nakayamaP₀ (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) : Injective (P.nakayamaP₀ D) := by
  have hQop : Injective (Opposite.op P.homDualP₀.obj) :=
    Injective.projective_iff_injective_op.mp P.homDualP₀.property
  exact (D.moduleEquiv.map_injective_iff _).2 hQop

/-- Applying Artin duality to the defining transpose complex gives exactness
of `DTr X ⟶ νP₁ ⟶ νP₀`. -/
theorem dTransposeCopresentation_exact
    (P : TwoStepProjectivePresentation X)
    (D : QuotientSubmoduleEquidistribution.ArtinDuality.Data R) :
    (P.dTransposeCopresentation D).Exact := by
  have hD := P.transposeComplex_exact.op.map D.moduleEquiv.functor
  change (P.transposeComplex.op.map D.moduleEquiv.functor).Exact
  exact hD

end TwoStepProjectivePresentation

end QuotientSubmoduleEquidistribution.AuslanderTranspose
