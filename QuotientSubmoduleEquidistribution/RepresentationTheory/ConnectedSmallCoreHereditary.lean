import QuotientSubmoduleEquidistribution.RepresentationTheory.ConnectedSmallCoreRank
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableCoreCategories
import QuotientSubmoduleEquidistribution.RepresentationTheory.ProjectiveInjectiveBoundary

/-!
# From collapse of the torsionless core to finite left heredity

This file upgrades the actual `v = d` result from the chosen projective
generator to Ringel's source-faithful notion of a torsionless module.  It then
states the resulting hereditary conclusion in two literal module-theoretic
forms:

* every finitely generated submodule of a finitely generated projective left
  module is projective;
* every left ideal of the ring is projective.

The second statement is the standard ring-theoretic criterion used before the
Gabriel/Dynkin classification.  No Gabriel classification input is used here.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

/-- The regular module embeds into a finite power of the basic projective
generator.  Indeed, the generator surjects onto the regular module, and
projectivity of the regular module splits that epimorphism. -/
theorem regularFGModule_inSubOfModule_projectiveGenerator :
    IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator sigma) (regularFGModule (R := R)) := by
  obtain ⟨L, p, hp⟩ :=
    projectiveGenerator_generates sigma (regularFGModule (R := R))
  letI : Epi p := hp
  letI : Projective (regularFGModule (R := R)) :=
    projective_regularFGModule (R := R)
  let s : regularFGModule (R := R) ⟶
      (⨁ fun _ : L ↦ projectiveGenerator sigma) :=
    Projective.factorThru (CategoryStruct.id _) p
  have hs : s ≫ p = 𝟙 _ :=
    Projective.factorThru_comp (CategoryStruct.id _) p
  refine ⟨L, s, ?_⟩
  exact mono_of_mono_fac hs

/-- Every finite categorical projective embeds into a finite power of the
basic projective generator. -/
theorem inSubOfModule_projectiveGenerator_of_projective
    (P : FGModuleCat.{u} R) (hP : Projective P) :
    IndecomposableSkeleton.InSubOfModule (projectiveGenerator sigma) P :=
  projective_inSubOfModule_of_regular_inSub
    (projectiveGenerator sigma) P
    (regularFGModule_inSubOfModule_projectiveGenerator sigma) hP

/-- Ringel torsionlessness is equivalent, in the finite skeleton scope, to
embedding into a finite power of the chosen basic projective generator. -/
theorem torsionless_iff_inSubOfModule_projectiveGenerator
    (X : FGModuleCat.{u} R) :
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.Torsionless X ↔
      IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator sigma) X := by
  constructor
  · rintro ⟨P, f, hP, hf⟩
    obtain ⟨L, p, hp⟩ :=
      inSubOfModule_projectiveGenerator_of_projective sigma P hP
    letI : Mono f := hf
    letI : Mono p := hp
    exact ⟨L, f ≫ p, inferInstance⟩
  · exact
      QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.torsionless_of_inSubOfModule
        (projective_projectiveGenerator sigma)

/-- Under `v = d`, every finitely generated torsionless module is
projective.  This is the full source-language upgrade of the indecomposable
core equality. -/
theorem projective_of_torsionless_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (X : FGModuleCat.{u} R)
    (hX : QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.Torsionless X) :
    Projective X := by
  apply
    projective_of_inSubOfModule_projectiveGenerator_of_projectiveRank_eq_core
      sigma hRingel hvd X
  exact (torsionless_iff_inSubOfModule_projectiveGenerator sigma X).1 hX

/-- Under `v = d`, the entire finite torsionless class is exactly the class
of finite projectives, not merely on indecomposable representatives. -/
theorem torsionless_iff_projective_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (X : FGModuleCat.{u} R) :
    QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter.Torsionless X ↔
      Projective X := by
  constructor
  · exact projective_of_torsionless_of_projectiveRank_eq_core
      sigma hRingel hvd X
  · intro hX
    exact ⟨X, 𝟙 X, hX, inferInstance⟩

/-- Equivalently, `Sub(G)` for the chosen basic projective generator is
literally the class of finite projectives. -/
theorem inSubOfModule_projectiveGenerator_iff_projective_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (X : FGModuleCat.{u} R) :
    IndecomposableSkeleton.InSubOfModule
        (projectiveGenerator sigma) X ↔
      Projective X := by
  rw [← torsionless_iff_projective_of_projectiveRank_eq_core
    sigma hRingel hvd X]
  exact (torsionless_iff_inSubOfModule_projectiveGenerator sigma X).symm

/-- Categorical finite-left-heredity: under `v = d`, a finitely generated
submodule of any finitely generated projective left module is projective. -/
theorem projective_of_mono_to_projective_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    {X P : FGModuleCat.{u} R} (f : X ⟶ P)
    (hP : Projective P) (hf : Mono f) :
    Projective X := by
  apply projective_of_torsionless_of_projectiveRank_eq_core
    sigma hRingel hvd X
  exact ⟨P, f, hP, hf⟩

/-- Literal module-theoretic finite-left-heredity: every submodule of a
finitely generated projective left module is projective as an unbundled
module.  No separate finite-generation assumption on `S` is needed because
`R` is left Noetherian. -/
theorem moduleProjective_submodule_of_fgProjective_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (P : FGModuleCat.{u} R) (hP : Projective P)
    (S : Submodule R P) :
    Module.Projective R S := by
  let X : FGModuleCat.{u} R := FGModuleCat.of R S
  let f : X ⟶ P := FGModuleCat.ofHom S.subtype
  have hf : Mono f :=
    ConcreteCategory.mono_of_injective f S.subtype_injective
  have hX : Projective X :=
    projective_of_mono_to_projective_of_projectiveRank_eq_core
      sigma hRingel hvd f hP hf
  exact QuotientSubmoduleEquidistribution.RingelStable.moduleProjective_of_fgProjective X hX

/-- A compact predicate for the exact finite module statement usually
called finite left heredity in this Artinian/Noetherian scope. -/
def FinitelyGeneratedLeftHereditary (R : Type u) [Ring R]
    [IsNoetherianRing R] : Prop :=
  ∀ (P : FGModuleCat.{u} R), Projective P →
    ∀ S : Submodule R P, Module.Projective R S

/-- The literal left-ideal criterion for a left hereditary ring.  It is kept
as a separate predicate because Mathlib currently has no ring-theoretic
`IsLeftHereditary` interface. -/
def EveryLeftIdealProjective (R : Type u) [Ring R] : Prop :=
  ∀ I : Submodule R R, Module.Projective R I

/-- The `v = d` core collapse implies finite left heredity. -/
theorem finitelyGeneratedLeftHereditary_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard) :
    FinitelyGeneratedLeftHereditary R := by
  intro P hP S
  exact
    moduleProjective_submodule_of_fgProjective_of_projectiveRank_eq_core
      sigma hRingel hvd P hP S

/-- Every left ideal is projective.  This is the standard hereditary-ring
criterion in the source's finite-dimensional setting. -/
theorem moduleProjective_leftIdeal_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (I : Submodule R R) :
    Module.Projective R I := by
  exact
    moduleProjective_submodule_of_fgProjective_of_projectiveRank_eq_core
      sigma hRingel hvd (regularFGModule (R := R))
      (projective_regularFGModule (R := R)) I

/-- Packaged left-hereditary criterion obtained from the core collapse. -/
theorem everyLeftIdealProjective_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard) :
    EveryLeftIdealProjective R := by
  intro I
  exact moduleProjective_leftIdeal_of_projectiveRank_eq_core
    sigma hRingel hvd I

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
