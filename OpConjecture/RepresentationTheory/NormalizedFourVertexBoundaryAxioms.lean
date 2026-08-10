import OpConjecture.RepresentationTheory.ARLocalRestrictions
import OpConjecture.RepresentationTheory.NormalizedFourVertexPacketAdapter

/-!
# Actual AR restrictions for normalized four-vertex boundary data

This file supplies the representation-theoretic hypotheses of the exact
four-label encoder.  It uses projective rootedness and the general local
two-cycle restrictions; no classification of algebras or modules enters.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

namespace NormalizedFour

open OpConjecture.NormalizedFourVertexLadderClassification

include k in
omit [DecidableEq ι] in
/-- The two local AR restrictions automatically discharge the non-rooted
fields of the semantic boundary-axiom package. -/
theorem BoundaryRealization.boundaryAxioms_eq_true_of_rooted
    {K : Set ι} (Q : BoundaryRealization (σ := σ) AR K)
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x) :
    BoundaryAxioms Q.code Q.additionalBoundary = true := by
  apply Q.boundaryAxioms_eq_true σ hroot
  · intro x y hxy hyx
    exact AR.exists_arTranslation_eq_self_of_two_cycle
      (K := k) σ x.1 y.1 hxy hyx
  · intro p b z hp hb htranslate hpz hzp
    have hpi : Injective (σ.obj p.1) :=
      AR.injective_of_projective_two_cycle
        (K := k) σ p.1 z.1 hp hpz hzp
    have htauNoninjective :
        ¬ Injective (σ.obj (AR.arTranslation σ ⟨b.1, hb⟩).1) :=
      (AR.arTranslation σ ⟨b.1, hb⟩).2
    apply htauNoninjective
    simpa [htranslate] using hpi

include k in
/-- Projective rootedness of a deleted four-support supplies the rootedness
hypothesis required by the exact boundary realization. -/
theorem BoundaryRealization.boundaryAxioms_eq_true_of_deleted_rooted
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (Q : BoundaryRealization (σ := σ) AR
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    BoundaryAxioms Q.code Q.additionalBoundary = true := by
  apply Q.boundaryAxioms_eq_true_of_rooted (k := k) σ
  intro x
  rcases (AR.fourVertexHookData σ Deleted hroot).rooted x with
    ⟨p, hp, hpx⟩
  refine ⟨p, ?_, ?_⟩
  · simpa [fourVertexHookData, deletedProjectiveSet] using hp
  · simpa [fourVertexHookData] using hpx

include k in
/-- Concrete boundary-axiom certificate obtained by relabelling a rooted
four-element retained support so that a chosen projective label is `0`. -/
theorem boundaryAxioms_of_deleted_four
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (p : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1)) :
    let Q := BoundaryRealization.ofDeletedFour
      (σ := σ) (AR := AR) Deleted hcard p hp
    BoundaryAxioms Q.code Q.additionalBoundary = true := by
  let Q := BoundaryRealization.ofDeletedFour
    (σ := σ) (AR := AR) Deleted hcard p hp
  exact Q.boundaryAxioms_eq_true_of_deleted_rooted
    (k := k) (AR := AR) σ Deleted hroot

end NormalizedFour

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
