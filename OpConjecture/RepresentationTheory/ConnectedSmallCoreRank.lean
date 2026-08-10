import OpConjecture.RepresentationTheory.FaithfulCoreNormalForm
import OpConjecture.RepresentationTheory.RingelCoreAdapter

/-!
# Actual projective rank inside the torsionless core

This file discharges the cardinality-theoretic part of `v <= d` for the
actual chosen indecomposable skeleton.  Here `v` is represented by the number
of indecomposable projective labels.  In the basic finite-dimensional scope
this is the number of simples.

It also proves the exact first half of the `v = d` branch: if the projective
rank equals the common Ringel core size, then every indecomposable in
`Sub(projectives)` is projective.  The remaining implication from this
module statement to hereditary Dynkin is deliberately not assumed here.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore

universe u v

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

/-- The number of indecomposable categorical projectives in the chosen
skeleton.  For a basic finite-dimensional algebra this is the number of
simple modules. -/
def projectiveRank : ℕ :=
  (projectiveLabels sigma).ncard

omit [Finite iota] in
/-- Every indecomposable projective label belongs to the actual torsionless
core `Sub(projectives)`. -/
theorem projectiveLabels_subset_submoduleCore :
    projectiveLabels sigma ⊆ (submoduleCore sigma : Set iota) := by
  intro i hi
  exact sigma.sClosure.le_closure (projectiveLabels sigma) hi

/-- The projective rank is at most the torsionless-core cardinality. -/
theorem projectiveRank_le_submoduleCore :
    projectiveRank sigma ≤
      (submoduleCore sigma : Set iota).ncard := by
  exact Set.ncard_le_ncard
    (projectiveLabels_subset_submoduleCore sigma) (Set.toFinite _)

/-- Ringel's equality transports `v <= d` to the quotient-side faithful
core used as the measure in the recurrence adapter. -/
theorem projectiveRank_le_quotientCore_of_ringel
    (hRingel : RingelCoreCardinality sigma) :
    projectiveRank sigma ≤
      (quotientCore sigma : Set iota).ncard := by
  calc
    projectiveRank sigma ≤
        (submoduleCore sigma : Set iota).ncard :=
      projectiveRank_le_submoduleCore sigma
    _ = (quotientCore sigma : Set iota).ncard := by
      simpa [RingelCoreCardinality] using hRingel.symm

/-- If the torsionless core and the projective boundary have equal finite
cardinality, containment forces literal equality of their label sets. -/
theorem submoduleCore_eq_projectiveLabels_of_ncard_eq
    (hcard :
      (submoduleCore sigma : Set iota).ncard =
        (projectiveLabels sigma).ncard) :
    (submoduleCore sigma : Set iota) = projectiveLabels sigma := by
  exact
    (Set.eq_of_subset_of_ncard_le
      (projectiveLabels_subset_submoduleCore sigma)
      (by rw [hcard])).symm

/-- Actual `v = d` core collapse, stated using the quotient core and
Ringel's comparison. -/
theorem submoduleCore_eq_projectiveLabels_of_projectiveRank_eq_quotientCore
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard) :
    (submoduleCore sigma : Set iota) = projectiveLabels sigma := by
  apply submoduleCore_eq_projectiveLabels_of_ncard_eq sigma
  calc
    (submoduleCore sigma : Set iota).ncard =
        (quotientCore sigma : Set iota).ncard := by
      simpa [RingelCoreCardinality] using hRingel.symm
    _ = projectiveRank sigma := hvd.symm
    _ = (projectiveLabels sigma).ncard := rfl

/-- Under `v = d`, membership in the torsionless core is exactly categorical
projectivity. -/
theorem mem_submoduleCore_iff_projective_of_projectiveRank_eq_quotientCore
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (i : iota) :
    i ∈ (submoduleCore sigma : Set iota) ↔
      CategoryTheory.Projective (sigma.obj i) := by
  rw [submoduleCore_eq_projectiveLabels_of_projectiveRank_eq_quotientCore
    sigma hRingel hvd]
  rfl

/-- Source-language form: if `v = d`, every indecomposable submodule of a
finite power of the basic projective generator is projective. -/
theorem projective_of_inSubOfProjectiveGenerator_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    {i : iota}
    (hi : IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator sigma) (sigma.obj i)) :
    CategoryTheory.Projective (sigma.obj i) := by
  apply
    (mem_submoduleCore_iff_projective_of_projectiveRank_eq_quotientCore
      sigma hRingel hvd i).1
  exact (mem_submoduleCore_iff_inSubOfModule sigma i).2 hi

/-- Stronger source-language form of the core collapse: under `v = d`,
every finitely generated module which embeds into a finite power of the basic
projective generator is projective.  This is the precise module statement
used before invoking the hereditary-algebra criterion. -/
theorem projective_of_inSubOfModule_projectiveGenerator_of_projectiveRank_eq_core
    (hRingel : RingelCoreCardinality sigma)
    (hvd :
      projectiveRank sigma =
        (quotientCore sigma : Set iota).ncard)
    (X : FGModuleCat.{u} R)
    (hX : IndecomposableSkeleton.InSubOfModule
      (projectiveGenerator sigma) X) :
    CategoryTheory.Projective X := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes X
  obtain ⟨J, p, hp⟩ := hX
  letI : Mono p := hp
  letI (t : Fin n) : CategoryTheory.Projective (sigma.obj (a t)) :=
    projective_of_inSubOfProjectiveGenerator_of_projectiveRank_eq_core
      sigma hRingel hvd (i := a t) (by
        refine ⟨J,
          biproduct.ι (fun s : Fin n ↦ sigma.obj (a s)) t ≫ e.inv ≫ p,
          ?_⟩
        infer_instance)
  have hsum :
      CategoryTheory.Projective
        (⨁ fun t : Fin n ↦ sigma.obj (a t)) := by
    constructor
    intro E Y f q _
    choose lift hlift using fun t : Fin n ↦
      CategoryTheory.Projective.factors
        (biproduct.ι (fun s : Fin n ↦ sigma.obj (a s)) t ≫ f) q
    refine ⟨biproduct.desc lift, ?_⟩
    apply biproduct.hom_ext'
    intro t
    simpa only [biproduct.ι_desc_assoc] using hlift t
  exact CategoryTheory.Projective.of_iso e.symm hsum

end OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore
