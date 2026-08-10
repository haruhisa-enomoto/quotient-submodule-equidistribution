import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexReverseLastReversal

/-!
# Fan invariance at a translation-fixed hub

Fix a translation-fixed label `u`.  The interior arrow occurrences
attached to `u` — the hub maps irreducibly into the source or into the
target of the occurrence — form a successor-invariant family for mesh
rotation: rotation replaces `(c -> d)` by `(d -> tau^{-1} c)`, and
attachment to a fixed hub is symmetric (`fixed_hom_comm`) and descends
along the inverse translation of a neighbour (`fixed_hom_shift`).  The
boundary endpoint equivalence therefore restricts to the fan, and after
cancelling the common corner cell the strictly-source-boundary part of
the fan is equinumerous with the strictly-target-boundary part.  At the
projective-source boundary attachment collapses to target attachment:
source attachment would close a two-cycle at the projective,
noninjective source.  These are the per-hub counting steps of the
reverse-last invariance.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data

universe w

/-- Splitting a finite subtype along a second predicate. -/
theorem nat_card_subtype_split {α : Type w} [Finite α]
    (A B : α → Prop) :
    Nat.card {x // A x} =
      Nat.card {x // A x ∧ B x} + Nat.card {x // A x ∧ ¬ B x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    ((Equiv.sumCompl fun y : {x // A x} ↦ B y.1).symm.trans
      (Equiv.sumCongr
        (Equiv.subtypeSubtypeEquivSubtypeInter A B)
        (Equiv.subtypeSubtypeEquivSubtypeInter A fun x ↦ ¬ B x)))

variable {Vertex : Type w} {P I : Vertex → Prop}
  (T : QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data Vertex P I)

/-- For a successor-invariant predicate, the strictly-source part of the
boundary is equinumerous with the strictly-target part: the boundary
endpoint equivalence balances the two full boundaries, and the corner
cell is common to both. -/
theorem card_strict_source_eq_card_strict_target [Fintype Vertex]
    (Q : Vertex → Prop)
    (hsuccessor : ∀ x, ¬ I x → (Q (T.successor x) ↔ Q x)) :
    Nat.card {x // P x ∧ ¬ I x ∧ Q x} =
      Nat.card {x // I x ∧ ¬ P x ∧ Q x} := by
  have hb : Nat.card {p : {x // P x} // Q p.1} =
      Nat.card {i : {x // I x} // Q i.1} :=
    Nat.card_congr (T.boundaryPredicateEquiv Q hsuccessor)
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter P Q),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter I Q)] at hb
  have hsP := nat_card_subtype_split (fun x ↦ P x ∧ Q x) I
  have hsI := nat_card_subtype_split (fun x ↦ I x ∧ Q x) P
  have hcorner : Nat.card {x // (P x ∧ Q x) ∧ I x} =
      Nat.card {x // (I x ∧ Q x) ∧ P x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by tauto)
  have hPcell : Nat.card {x // (P x ∧ Q x) ∧ ¬ I x} =
      Nat.card {x // P x ∧ ¬ I x ∧ Q x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by tauto)
  have hIcell : Nat.card {x // (I x ∧ Q x) ∧ ¬ P x} =
      Nat.card {x // I x ∧ ¬ P x ∧ Q x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by tauto)
  omega

end QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- Attachment of an interior arrow occurrence to a hub label: the hub
maps irreducibly into the source or into the target of the occurrence. -/
def FanAttached (u : ι)
    (x : (AR.arMeshRotationData σ).InteriorArrow σ) : Prop :=
  HasIrreducibleMorphism (σ.obj u) (σ.obj x.1.1.1) ∨
    HasIrreducibleMorphism (σ.obj u) (σ.obj x.1.1.2)

omit [DecidableEq ι] in
/-- Attachment to a translation-fixed hub is invariant along mesh
rotation of interior arrow occurrences. -/
theorem fanAttached_successor_iff
    (u : ι) (huNP : ¬ Projective (σ.obj u))
    (hfix : (AR.arTranslation σ ⟨u, huNP⟩).1 = u)
    (x : (AR.arMeshRotationData σ).InteriorArrow σ)
    (hx : ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget
      x) :
    AR.FanAttached σ u
        (((AR.arMeshRotationData σ).arrowOrbitData σ).interior.successor
          x) ↔
      AR.FanAttached σ u x := by
  have hval1 :
      (((AR.arMeshRotationData σ).arrowOrbitData
        σ).interior.successor x).1 =
      ((AR.arMeshRotationData σ).arrowOrbitData σ).successor x.1 :=
    ((AR.arMeshRotationData σ).arrowOrbitData
      σ).interior_successor_val x hx
  have hsucc : ((AR.arMeshRotationData σ).arrowOrbitData σ).successor
      x.1 =
      (((AR.arMeshRotationData σ).arrowOrbitData σ).tau.symm
        ⟨x.1, x.2.2⟩).1 := by
    simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, x.2.2]
  have hpair : ((((AR.arMeshRotationData σ).arrowOrbitData σ).tau.symm
      ⟨x.1, x.2.2⟩)).1.1 =
      (x.1.1.2, ((AR.arTranslationEquiv σ).symm
        ⟨x.1.1.1, x.2.2⟩).1) :=
    ARMeshRotationData.arrowOrbitData_tau_symm_val σ
      (AR.arMeshRotationData σ) ⟨x.1, x.2.2⟩
  have hcomp :
      (((AR.arMeshRotationData σ).arrowOrbitData
        σ).interior.successor x).1.1 =
      (x.1.1.2, ((AR.arTranslationEquiv σ).symm
        ⟨x.1.1.1, x.2.2⟩).1) :=
    (congrArg Subtype.val (hval1.trans hsucc)).trans hpair
  have h1 : (((AR.arMeshRotationData σ).arrowOrbitData
      σ).interior.successor x).1.1.1 = x.1.1.2 :=
    congrArg Prod.fst hcomp
  have h2 : (((AR.arMeshRotationData σ).arrowOrbitData
      σ).interior.successor x).1.1.2 =
      ((AR.arTranslationEquiv σ).symm ⟨x.1.1.1, x.2.2⟩).1 :=
    congrArg Prod.snd hcomp
  simp only [FanAttached]
  rw [h1, h2, fixed_hom_shift σ AR u x.1.1.1 huNP hfix x.2.2]
  exact or_comm

omit [DecidableEq ι] in
include K in
/-- At the projective-source boundary of a fixed hub's fan, attachment
collapses to target attachment: source attachment would close a
two-cycle at the projective, noninjective source. -/
theorem fanAttached_iff_target_of_interior_source
    (u : ι) (huNP : ¬ Projective (σ.obj u))
    (hfix : (AR.arTranslation σ ⟨u, huNP⟩).1 = u)
    (x : (AR.arMeshRotationData σ).InteriorArrow σ)
    (hxs : ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource
      x) :
    AR.FanAttached σ u x ↔
      HasIrreducibleMorphism (σ.obj u) (σ.obj x.1.1.2) := by
  constructor
  · rintro (hsrc | htgt)
    · exfalso
      have hzP : Projective (σ.obj x.1.1.1) :=
        ((AR.arMeshRotationData σ).arrowInterior_source_iff σ x).1 hxs
      have hzu : HasIrreducibleMorphism
          (σ.obj x.1.1.1) (σ.obj u) :=
        (fixed_hom_comm σ AR u x.1.1.1 huNP hfix).2 hsrc
      exact x.2.2
        (AR.injective_of_projective_two_cycle (K := K) σ
          x.1.1.1 u hzP hzu hsrc)
    · exact htgt
  · exact Or.inr

omit [DecidableEq ι] in
/-- Per-hub fan balance: for a translation-fixed hub, the attached
interior arrow occurrences at the strict source boundary are
equinumerous with those at the strict target boundary. -/
theorem fan_strict_source_card_eq_strict_target_card
    (u : ι) (huNP : ¬ Projective (σ.obj u))
    (hfix : (AR.arTranslation σ ⟨u, huNP⟩).1 = u) :
    Nat.card {x : (AR.arMeshRotationData σ).InteriorArrow σ //
        ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorSource x ∧
          ¬ ((AR.arMeshRotationData σ).arrowOrbitData
            σ).InteriorTarget x ∧
          AR.FanAttached σ u x} =
      Nat.card {x : (AR.arMeshRotationData σ).InteriorArrow σ //
        ((AR.arMeshRotationData σ).arrowOrbitData σ).InteriorTarget x ∧
          ¬ ((AR.arMeshRotationData σ).arrowOrbitData
            σ).InteriorSource x ∧
          AR.FanAttached σ u x} :=
  (((AR.arMeshRotationData σ).arrowOrbitData
    σ).interior).card_strict_source_eq_card_strict_target
    (AR.FanAttached σ u)
    (fun x hx ↦ fanAttached_successor_iff σ AR u huNP hfix x hx)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData
