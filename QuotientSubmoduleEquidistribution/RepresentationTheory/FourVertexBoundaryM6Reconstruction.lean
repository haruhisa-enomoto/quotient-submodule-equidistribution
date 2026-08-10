import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexBoundaryStripReconstruction

/-!
# Reconstructing the regular first-coordinate boundary as `M6`

The first coordinate of an `M6` common-target occurrence starts at a
projective label.  The second coordinate is the orbit anchor immediately
before the displayed hook.  This file reconstructs that hook from the
anchor and isolates the one local reverse-arrow condition needed for an
admissible strip.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

namespace FiniteARTranslationData

variable (AR : sigma.FiniteARTranslationData)

omit [Fintype iota] [DecidableEq iota] in
include k AR in
/-- An irreducible arrow `a → u` with noninjective source canonically
extends one mesh further to `u → b`, where `tau b = a`.  The two
remaining admissibility clauses are supplied as the explicit regularity
conditions. -/
def stripTripleOfNoninjectiveArrow
    (q : sigma.IrreduciblePair)
    (haNI : ¬ Injective (sigma.obj q.1.1))
    (huNP : ¬ Projective (sigma.obj q.1.2))
    (ha_ne_b : q.1.1 ≠
      ((AR.arTranslationEquiv sigma).symm ⟨q.1.1, haNI⟩).1)
    (hb_not_to_u : ¬ HasIrreducibleMorphism
      (sigma.obj ((AR.arTranslationEquiv sigma).symm
        ⟨q.1.1, haNI⟩).1)
      (sigma.obj q.1.2)) :
    AR.StripAdmissibleTriple sigma := by
  let a := q.1.1
  let u := q.1.2
  let bLabel : sigma.NonprojectiveLabel :=
    (AR.arTranslationEquiv sigma).symm ⟨a, haNI⟩
  let b := bLabel.1
  have hbNP : ¬ Projective (sigma.obj b) := bLabel.2
  have htauB : (AR.arTranslation sigma bLabel).1 = a := by
    exact congrArg Subtype.val
      ((AR.arTranslationEquiv sigma).apply_symm_apply ⟨a, haNI⟩)
  have huB : HasIrreducibleMorphism (sigma.obj u) (sigma.obj b) := by
    apply (AR.arTranslation_incidence sigma bLabel u).2
    simpa only [htauB] using q.2
  exact
    { a := a
      u := u
      b := b
      a_ne_u := by
        change q.1.1 ≠ q.1.2
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj q.1.2
          (h ▸ q.2)
      a_ne_b := ha_ne_b
      u_ne_b := by
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj u (by
          simpa only [h] using huB)
      u_nonprojective := huNP
      b_nonprojective := hbNP
      a_to_u := q.2
      u_to_b := huB
      b_not_to_u := hb_not_to_u
      a_not_to_b :=
        AR.no_irreducible_transitiveTriangle (K := k) sigma q.2 huB
      tau_b := htauB }

/-- Advance the second occurrence of an interior common-target pair by one
ordinary mesh-rotation step. -/
def boundaryM6FirstArrow
    (p : AR.InteriorCommonTargetArrowPair sigma) :
    sigma.IrreduciblePair :=
  (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau.symm
    ⟨p.1.2.1, p.1.2.2.2⟩).1

/-- The canonical last label obtained by advancing once more from the
common target, assuming that target is noninjective. -/
def boundaryM6Last
    (p : AR.InteriorCommonTargetArrowPair sigma)
    (haNI : ¬ Injective (sigma.obj p.1.2.1.1.2)) : iota :=
  ((AR.arTranslationEquiv sigma).symm
    ⟨p.1.2.1.1.2, haNI⟩).1

/-- The regular part of the first-coordinate common-target boundary.  The
first occurrence literally starts at a projective, the common target is
noninjective, and the canonical next strip has no reverse last arrow. -/
structure BoundaryM6RegularPair where
  pair : AR.InteriorCommonTargetArrowPair sigma
  first_source :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      pair.1.1
  target_noninjective : ¬ Injective (sigma.obj pair.1.2.1.1.2)
  last_not_to_middle : ¬ HasIrreducibleMorphism
    (sigma.obj (AR.boundaryM6Last sigma pair target_noninjective))
    (sigma.obj (AR.boundaryM6FirstArrow sigma pair).1.2)

omit [DecidableEq iota] in
@[ext]
theorem BoundaryM6RegularPair.ext
    {p q : AR.BoundaryM6RegularPair sigma}
    (hpair : p.pair = q.pair) : p = q := by
  cases p
  cases q
  cases hpair
  rfl

omit [Fintype iota] in
noncomputable instance boundaryM6RegularPairFinite :
    Finite (AR.BoundaryM6RegularPair sigma) :=
  Finite.of_injective BoundaryM6RegularPair.pair (by
    intro p q h
    cases p
    cases q
    simp_all)

noncomputable instance boundaryM6RegularPairFintype :
    Fintype (AR.BoundaryM6RegularPair sigma) := Fintype.ofFinite _

noncomputable instance hookM6InteriorChannelFintype :
    Fintype (HookM6Channel.InteriorChannel sigma AR) := Fintype.ofFinite _

/-- The reconstructed `M6` term together with equality of its canonical
labelled occurrence and the original regular boundary pair. -/
structure BoundaryM6Reconstruction
    (p : AR.BoundaryM6RegularPair sigma) where
  term : HookM6Channel.InteriorChannel sigma AR
  occurrence_eq :
    HookM6Channel.interiorCommonTargetPair sigma AR term = p.pair

omit [DecidableEq iota] in
include k AR in
/-- Every regular first-coordinate boundary pair reconstructs a unique
interior `M6` occurrence. -/
def boundaryM6Reconstruction
    (p : AR.BoundaryM6RegularPair sigma) :
    AR.BoundaryM6Reconstruction sigma p := by
  classical
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let C : M.InteriorArrow sigma := p.pair.1.1
  let H : M.InteriorArrow sigma := p.pair.1.2
  let qsub := O.tau.symm ⟨H.1, H.2.2⟩
  let q : sigma.IrreduciblePair := qsub.1
  let a := H.1.1.2
  let u := q.1.2
  let bLabel : sigma.NonprojectiveLabel :=
    (AR.arTranslationEquiv sigma).symm ⟨a, p.target_noninjective⟩
  let b := bLabel.1
  let z := C.1.1.1
  have hqSource : q.1.1 = a := by
    have hval := M.arrowOrbitData_tau_symm_val sigma ⟨H.1, H.2.2⟩
    exact congrArg Prod.fst hval
  have hqTargetNP : ¬ Projective (sigma.obj u) := qsub.2
  have hzP : Projective (sigma.obj z) := by
    exact (M.arrowInterior_source_iff sigma C).1 p.first_source
  have hzNI : ¬ Injective (sigma.obj z) := C.2.2
  have hza : HasIrreducibleMorphism (sigma.obj z) (sigma.obj a) := by
    change HasIrreducibleMorphism
      (sigma.obj C.1.1.1) (sigma.obj H.1.1.2)
    rw [← p.pair.2]
    exact C.1.2
  have ha_ne_b : a ≠ b := by
    intro hab
    have hbNP : ¬ Projective (sigma.obj b) := bLabel.2
    have htauB : (AR.arTranslation sigma bLabel).1 = a := by
      exact congrArg Subtype.val
        ((AR.arTranslationEquiv sigma).apply_symm_apply
          ⟨a, p.target_noninjective⟩)
    have haZ : HasIrreducibleMorphism (sigma.obj a) (sigma.obj z) := by
      have h := (AR.arTranslation_incidence sigma bLabel z).1 (by
        simpa only [hab] using hza)
      simpa only [htauB] using h
    have hzI := AR.injective_of_projective_two_cycle
      (K := k) sigma z a hzP hza haZ
    exact hzNI hzI
  have hbNot : ¬ HasIrreducibleMorphism (sigma.obj b) (sigma.obj u) := by
    simpa only [b, u, boundaryM6Last, boundaryM6FirstArrow,
      q, qsub, a, H] using p.last_not_to_middle
  let qA : sigma.IrreduciblePair := ⟨(a, u), by
    simpa only [a, u, hqSource] using q.2⟩
  let T := stripTripleOfNoninjectiveArrow (k := k) sigma AR qA
    p.target_noninjective hqTargetNP ha_ne_b hbNot
  have hTa : T.a = a := rfl
  have hTu : T.u = u := rfl
  have hTb : T.b = b := rfl
  have hzNot : z ∉ T.support := by
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hza' : z = a := h.trans hTa
      exact sigma.hasNoIrreducibleEndomorphism_obj z (by
        simpa only [hza'] using hza)
    · intro h
      have hzu : z = u := h.trans hTu
      have haZ : HasIrreducibleMorphism (sigma.obj a) (sigma.obj z) := by
        simpa only [hzu] using qA.2
      have hzI := AR.injective_of_projective_two_cycle
        (K := k) sigma z a hzP hza haZ
      exact hzNI hzI
    · intro h
      rw [h] at hzP
      exact T.b_nonprojective hzP
  have hzNotU : ¬ HasIrreducibleMorphism
      (sigma.obj z) (sigma.obj T.u) := by
    intro hzu
    exact AR.no_irreducible_transitiveTriangle
      (K := k) sigma (by simpa only [hTa] using hza) T.a_to_u hzu
  have hzNotB : ¬ HasIrreducibleMorphism
      (sigma.obj z) (sigma.obj T.b) := by
    intro hzb
    have hAZ : HasIrreducibleMorphism (sigma.obj T.a) (sigma.obj z) := by
      have h := (AR.arTranslation_incidence sigma
        ⟨T.b, T.b_nonprojective⟩ z).1 hzb
      simpa only [T.tau_b] using h
    have hzA : HasIrreducibleMorphism (sigma.obj z) (sigma.obj T.a) := by
      simpa only [hTa] using hza
    have hzI := AR.injective_of_projective_two_cycle
      (K := k) sigma z T.a hzP hzA hAZ
    exact hzNI hzI
  have hzA : HasIrreducibleMorphism (sigma.obj z) (sigma.obj T.a) := by
    simpa only [hTa] using hza
  have hzMem : z ∈ insert z T.support :=
    Finset.mem_insert_self z T.support
  have haMem : T.a ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_a
  have huMem : T.u ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_u
  have hbMem : T.b ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_b
  have eZA : QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
      sigma.irreducibleEdge (insert z T.support) z T.a :=
    ⟨hzMem, haMem, hzA⟩
  have eAU : QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
      sigma.irreducibleEdge (insert z T.support) T.a T.u :=
    ⟨haMem, huMem, T.a_to_u⟩
  have eUB : QuotientSubmoduleEquidistribution.RootedDigraph.InsideEdge
      sigma.irreducibleEdge (insert z T.support) T.u T.b :=
    ⟨huMem, hbMem, T.u_to_b⟩
  have hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      sigma.irreducibleEdge sigma.projectiveLabelFinset
        (insert z T.support) := by
    intro x hx
    change x ∈ insert z ({T.a, T.u, T.b} : Finset iota) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨z, by simpa using hzP, hzMem,
        Relation.ReflTransGen.refl⟩
    · exact ⟨z, by simpa using hzP, hzMem,
        Relation.ReflTransGen.single eZA⟩
    · refine ⟨z, by simpa using hzP, hzMem, ?_⟩
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single eZA) eAU
    · refine ⟨z, by simpa using hzP, hzMem, ?_⟩
      apply Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single eZA) eAU)
      exact eUB
  let E : AR.HookFourthExtension sigma :=
    { triple := T
      z := z
      z_not_mem := hzNot
      rooted := hroot
      z_not_to_u := hzNotU
      z_not_to_b := hzNotB }
  let X : AR.HookM6Channel sigma := ⟨E, by
    simpa only [E, T, hTa] using H.2.1⟩
  have hassociated : X.associatedArrow sigma AR = C.1 := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hTa.trans p.pair.2.symm
  have hanchor : X.1.triple.hookOrbitAnchor sigma AR = H.1 := by
    let firstSub : {r : sigma.IrreduciblePair //
        ¬ Projective (sigma.obj r.1.2)} :=
      ⟨X.1.triple.firstArrow sigma AR, X.1.triple.u_nonprojective⟩
    have hfirst : firstSub = qsub := by
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact hqSource.symm
      · rfl
    change (O.tau firstSub).1 = H.1
    rw [hfirst]
    exact congrArg Subtype.val (O.tau.apply_symm_apply ⟨H.1, H.2.2⟩)
  have hanchorInterior : IsInteriorArrow sigma
      (X.1.triple.hookOrbitAnchor sigma AR) := by
    simpa only [hanchor, IsInteriorArrow] using H.2
  let XI : HookM6Channel.InteriorChannel sigma AR := ⟨X, by
    constructor
    · simpa only [hassociated, IsInteriorArrow] using C.2
    · exact hanchorInterior⟩
  refine ⟨XI, ?_⟩
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact hassociated
  · exact hanchor

namespace HookM6Channel

/-- On the labelled pair of an interior `M6` term, advancing the second
occurrence recovers the first displayed hook arrow. -/
theorem boundaryM6FirstArrow_interiorCommonTargetPair
    (X : HookM6Channel.InteriorChannel sigma AR) :
    AR.boundaryM6FirstArrow sigma
        (HookM6Channel.interiorCommonTargetPair sigma AR X) =
      X.1.1.triple.firstArrow sigma AR := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let T := X.1.1.triple
  let H := T.hookOrbitAnchor sigma AR
  have hHNI : ¬ Injective (sigma.obj H.1.1) := by
    simpa only [H, IsInteriorArrow] using X.2.2.2
  change (O.tau.symm ⟨H, hHNI⟩).1 = T.firstArrow sigma AR
  have hsuccessor : O.successor H = (O.tau.symm ⟨H, hHNI⟩).1 := by
    simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, hHNI]
  exact hsuccessor.symm.trans (T.hookOrbitAnchor_successor sigma AR)

/-- On the labelled pair of an interior `M6` term, the canonical last
label is the last label of its displayed hook. -/
theorem boundaryM6Last_interiorCommonTargetPair
    (X : HookM6Channel.InteriorChannel sigma AR) :
    AR.boundaryM6Last sigma
        (HookM6Channel.interiorCommonTargetPair sigma AR X)
        (by
          simpa only [HookM6Channel.interiorCommonTargetPair,
            toInteriorArrow,
            X.1.1.triple.hookOrbitAnchor_target sigma AR] using
              X.1.1.triple.a_noninjective sigma AR) =
      X.1.1.triple.b := by
  let T := X.1.1.triple
  let bLabel : sigma.NonprojectiveLabel := ⟨T.b, T.b_nonprojective⟩
  have htau : AR.arTranslationEquiv sigma bLabel =
      ⟨T.a, T.a_noninjective sigma AR⟩ := by
    apply Subtype.ext
    exact T.tau_b
  change ((AR.arTranslationEquiv sigma).symm
    ⟨T.a, T.a_noninjective sigma AR⟩).1 = T.b
  rw [← htau]
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv sigma).symm_apply_apply bLabel)

omit [DecidableEq iota] in
/-- Forget an interior `M6` term to its regular first-coordinate boundary
pair. -/
def toBoundaryM6RegularPair
    (X : HookM6Channel.InteriorChannel sigma AR) :
    AR.BoundaryM6RegularPair sigma := by
  let P := HookM6Channel.interiorCommonTargetPair sigma AR X
  refine
    { pair := P
      first_source := ?_
      target_noninjective := ?_
      last_not_to_middle := ?_ }
  · exact ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma P.1.1).2 (X.1.z_projective_and_z_to_a sigma AR).1
  · simpa only [P, HookM6Channel.interiorCommonTargetPair,
      toInteriorArrow,
      X.1.1.triple.hookOrbitAnchor_target sigma AR] using
        X.1.1.triple.a_noninjective sigma AR
  · simpa only [P,
      boundaryM6Last_interiorCommonTargetPair,
      boundaryM6FirstArrow_interiorCommonTargetPair,
      StripAdmissibleTriple.firstArrow] using
        X.1.1.triple.b_not_to_u

end HookM6Channel

include k AR in
/-- Interior `M6` terms are exactly the regular part of the first-coordinate
trimmed source boundary. -/
def boundaryM6RegularPairEquiv :
    HookM6Channel.InteriorChannel sigma AR ≃
      AR.BoundaryM6RegularPair sigma where
  toFun := HookM6Channel.toBoundaryM6RegularPair sigma AR
  invFun p := (AR.boundaryM6Reconstruction (k := k) sigma p).term
  left_inv X := by
    apply HookM6Channel.interiorCommonTargetPair_injective sigma AR
    exact (AR.boundaryM6Reconstruction (k := k) sigma
      (HookM6Channel.toBoundaryM6RegularPair sigma AR X)).occurrence_eq
  right_inv p := by
    apply BoundaryM6RegularPair.ext
    exact (AR.boundaryM6Reconstruction (k := k) sigma
      p).occurrence_eq

include k AR in
/-- Cardinal form of the regular first-coordinate boundary
classification. -/
theorem hookM6Interior_card_eq_boundaryM6RegularPair :
    Fintype.card (HookM6Channel.InteriorChannel sigma AR) =
      Fintype.card (AR.BoundaryM6RegularPair sigma) :=
  Fintype.card_congr (AR.boundaryM6RegularPairEquiv (k := k) sigma)

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
