import QuotientSubmoduleEquidistribution.Combinatorics.NormalizedFourVertexEncoding
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderARHooklessPackets
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexARHooks

/-!
# Decoding normalized four-vertex certificates into AR packets

This file is the representation-theoretic half of the finite classifier
adapter.  A realization identifies a deleted four-label type with `Fin 4`,
sends the unique projective to `0`, and states that the encoded edge and
partial-translation data are the actual AR data.  Certified rows `F` and
`T` then decode directly into the existing `FixedPacket` and
`TrianglePacket` structures.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

namespace NormalizedFour

open QuotientSubmoduleEquidistribution.NormalizedFourVertexLadderClassification

/-- Relabel a four-element deleted finset by `Fin 4`, postcomposing with a
swap so that a specified retained label is sent to `0`. -/
def labelEquivOfCardFour
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) :
    DeletedLabel ((Deleted : Set ι)ᶜ) ≃ Vertex := by
  classical
  let e₀ : DeletedLabel ((Deleted : Set ι)ᶜ) ≃ Vertex :=
    (deletedLabelComplEquiv Deleted).trans
    (Finset.equivFinOfCardEq hcard)
  exact e₀.trans (Equiv.swap (e₀ p) 0)

omit [Fintype ι] in
/-- The distinguished label is indeed the normalized vertex `0`. -/
@[simp]
theorem labelEquivOfCardFour_apply_distinguished
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ)) :
    labelEquivOfCardFour Deleted hcard p p = 0 := by
  classical
  simp [labelEquivOfCardFour]

/-- Exact realization before uniqueness of the projective root is known.
Vertex `0` is a chosen projective; the three boundary bits record all other
projective vertices. -/
structure BoundaryRealization (K : Set ι) where
  labelEquiv : DeletedLabel K ≃ Vertex
  code : Code
  additionalBoundary : AdditionalBoundary
  projective_iff_boundary (x : DeletedLabel K) :
    Projective (σ.obj x.1) ↔
      boundaryAt additionalBoundary (labelEquiv x) = true
  edge_iff (x y : DeletedLabel K) :
    edge code (labelEquiv x) (labelEquiv y) = true ↔
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1)
  tau_eq_iff (x y : DeletedLabel K)
      (hx : ¬ Projective (σ.obj x.1)) :
    tauEq code (labelEquiv x) (labelEquiv y) = true ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 = y.1
  tau_none_iff (x : DeletedLabel K)
      (hx : ¬ Projective (σ.obj x.1)) :
    tauNone code (labelEquiv x) = true ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K
  tau_none_of_projective (x : DeletedLabel K)
      (hx : Projective (σ.obj x.1)) :
    tauNone code (labelEquiv x) = true

/-- Exact realization of a normalized finite code by a deleted AR support.
The projective equivalence in particular says that the support has a unique
projective vertex. -/
structure Realization (K : Set ι) where
  labelEquiv : DeletedLabel K ≃ Vertex
  code : Code
  projective_iff_zero (x : DeletedLabel K) :
    Projective (σ.obj x.1) ↔ labelEquiv x = 0
  edge_iff (x y : DeletedLabel K) :
    edge code (labelEquiv x) (labelEquiv y) = true ↔
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1)
  tau_eq_iff (x y : DeletedLabel K)
      (hx : ¬ Projective (σ.obj x.1)) :
    tauEq code (labelEquiv x) (labelEquiv y) = true ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 = y.1
  tau_none_iff (x : DeletedLabel K)
      (hx : ¬ Projective (σ.obj x.1)) :
    tauNone code (labelEquiv x) = true ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K

namespace BoundaryRealization

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (Q : BoundaryRealization (σ := σ) AR K)

omit [Fintype ι] in
/-- For a nonprojective retained label, the semantic retained target is a
specified label exactly when the ordinary AR translate has that label. -/
theorem retainedARTranslationTarget_eq_some_iff
    (x y : DeletedLabel K) (hx : ¬ Projective (σ.obj x.1)) :
    AR.retainedARTranslationTarget σ K x = some y ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 = y.1 := by
  classical
  by_cases hm : (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K
  · constructor
    · intro h
      simp [retainedARTranslationTarget, hx, hm] at h
    · intro heq
      exfalso
      apply y.2
      rw [← heq]
      exact hm
  · simp [retainedARTranslationTarget, hx, hm, Subtype.ext_iff]

omit [Fintype ι] in
/-- For a nonprojective retained label, a missing semantic target means
that its ordinary AR translate leaves the retained support. -/
theorem retainedARTranslationTarget_eq_none_iff
    (x : DeletedLabel K) (hx : ¬ Projective (σ.obj x.1)) :
    AR.retainedARTranslationTarget σ K x = none ↔
      (AR.arTranslation σ ⟨x.1, hx⟩).1 ∈ K := by
  classical
  simp [retainedARTranslationTarget, hx]

/-- Construct the exact boundary realization from a relabelling which sends
a chosen projective vertex to `0`. -/
def ofLabelEquiv
    (e : DeletedLabel K ≃ Vertex)
    (hroot : Projective (σ.obj (e.symm 0).1)) :
    BoundaryRealization (σ := σ) AR K := by
  classical
  let E := fun x y : DeletedLabel K ↦
    HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1)
  let T := AR.retainedARTranslationTarget σ K
  let C := codeOfEquiv e E T
  let B := additionalBoundaryOfEquiv e
    (fun x : DeletedLabel K ↦ Projective (σ.obj x.1))
  have hTroot : T (e.symm 0) = none := by
    simp [T, retainedARTranslationTarget, hroot]
  refine
    { labelEquiv := e
      code := C
      additionalBoundary := B
      projective_iff_boundary := ?_
      edge_iff := ?_
      tau_eq_iff := ?_
      tau_none_iff := ?_
      tau_none_of_projective := ?_ }
  · intro x
    exact (boundaryAt_additionalBoundaryOfEquiv e
      (fun y : DeletedLabel K ↦ Projective (σ.obj y.1)) hroot x).symm
  · intro x y
    apply edge_codeOfEquiv e E T
    intro z
    exact σ.hasNoIrreducibleEndomorphism_obj z.1
  · intro x y hx
    exact (tauEq_codeOfEquiv e E T x y hTroot).trans
      (retainedARTranslationTarget_eq_some_iff (AR := AR) σ x y hx)
  · intro x hx
    exact (tauNone_codeOfEquiv e E T x hTroot).trans
      (retainedARTranslationTarget_eq_none_iff (AR := AR) σ x hx)
  · intro x hx
    apply (tauNone_codeOfEquiv e E T x hTroot).2
    simp [T, retainedARTranslationTarget, hx]

/-- Construct the exact boundary realization directly from a four-element
deleted finset and one chosen projective retained label. -/
def ofDeletedFour
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (p : DeletedLabel ((Deleted : Set ι)ᶜ))
    (hp : Projective (σ.obj p.1)) :
    BoundaryRealization (σ := σ) AR ((Deleted : Set ι)ᶜ) := by
  let e := labelEquivOfCardFour Deleted hcard p
  apply ofLabelEquiv (σ := σ) (AR := AR) e
  have hep : e p = 0 := by simp [e]
  have hp0 : e.symm 0 = p := by
    apply e.injective
    simpa using hep.symm
  simpa [hp0] using hp

omit [Fintype ι] in
/-- Assemble the semantic Boolean boundary axioms from an exact realization,
semantic rootedness, and the two local two-cycle restrictions. -/
theorem boundaryAxiomConditions
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (htwoCycle : ∀ x y : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1) →
      HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) →
        (∃ hx : ¬ Projective (σ.obj x.1),
          (AR.arTranslation σ ⟨x.1, hx⟩).1 = x.1) ∨
        (∃ hy : ¬ Projective (σ.obj y.1),
          (AR.arTranslation σ ⟨y.1, hy⟩).1 = y.1))
    (htranslatedBoundary : ∀ p b z : DeletedLabel K,
      Projective (σ.obj p.1) →
      ∀ hb : ¬ Projective (σ.obj b.1),
      (AR.arTranslation σ ⟨b.1, hb⟩).1 = p.1 →
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj z.1) →
      HasIrreducibleMorphism (σ.obj z.1) (σ.obj p.1) → False) :
    BoundaryAxiomConditions Q.code Q.additionalBoundary := by
  refine
    { rooted := ?_
      boundary_no_tau := ?_
      tau_valid := ?_
      tau_injective := ?_
      mesh_incidence := ?_
      two_cycle_fixed := ?_
      translated_boundary_no_two_cycle := ?_ }
  · intro x
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    rcases hroot x' with ⟨p, hp, hpx⟩
    refine ⟨Q.labelEquiv p, (Q.projective_iff_boundary p).1 hp, ?_⟩
    have hpx' : Relation.ReflTransGen
        (fun a b : Vertex ↦ edge Q.code a b = true)
        (Q.labelEquiv p) (Q.labelEquiv x') :=
      hpx.lift Q.labelEquiv (by
        intro a b hab
        exact (Q.edge_iff a b).2 hab)
    simpa [x'] using hpx'
  · intro x hx
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    have hp : Projective (σ.obj x'.1) :=
      (Q.projective_iff_boundary x').2 (by simpa [x'] using hx)
    simpa [x'] using Q.tau_none_of_projective x' hp
  · intro x
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    by_cases hp : Projective (σ.obj x'.1)
    · left
      simpa [x'] using Q.tau_none_of_projective x' hp
    · by_cases hm : (AR.arTranslation σ ⟨x'.1, hp⟩).1 ∈ K
      · left
        simpa [x'] using (Q.tau_none_iff x' hp).2 hm
      · let y : DeletedLabel K :=
          ⟨(AR.arTranslation σ ⟨x'.1, hp⟩).1, hm⟩
        right
        refine ⟨Q.labelEquiv y, ?_⟩
        simpa [x'] using (Q.tau_eq_iff x' y hp).2 rfl
  · intro x y
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    let y' : DeletedLabel K := Q.labelEquiv.symm y
    by_cases hnoneX : tauNone Q.code x = true
    · exact Or.inl hnoneX
    · by_cases hnoneY : tauNone Q.code y = true
      · exact Or.inr (Or.inl hnoneY)
      · by_cases hcode : tauCode Q.code x ≠ tauCode Q.code y
        · exact Or.inr (Or.inr (Or.inl hcode))
        · right
          right
          right
          have hxnp : ¬ Projective (σ.obj x'.1) := by
            intro hp
            apply hnoneX
            simpa [x'] using Q.tau_none_of_projective x' hp
          have hynp : ¬ Projective (σ.obj y'.1) := by
            intro hp
            apply hnoneY
            simpa [y'] using Q.tau_none_of_projective y' hp
          have htxOutside :
              (AR.arTranslation σ ⟨x'.1, hxnp⟩).1 ∉ K := by
            intro hm
            apply hnoneX
            simpa [x'] using (Q.tau_none_iff x' hxnp).2 hm
          let t : DeletedLabel K :=
            ⟨(AR.arTranslation σ ⟨x'.1, hxnp⟩).1, htxOutside⟩
          have hxt : tauEq Q.code x (Q.labelEquiv t) = true := by
            simpa [x'] using (Q.tau_eq_iff x' t hxnp).2 rfl
          have hyt : tauEq Q.code y (Q.labelEquiv t) = true := by
            rw [tauEq] at hxt ⊢
            rw [← not_ne_iff.mp hcode]
            exact hxt
          have htranslateY := (Q.tau_eq_iff y' t hynp).1 (by
            simpa [y'] using hyt)
          have hnonprojective :
              (⟨x'.1, hxnp⟩ : σ.NonprojectiveLabel) = ⟨y'.1, hynp⟩ := by
            apply AR.arTranslation_injective σ
            apply Subtype.ext
            exact htranslateY.symm
          have hxy' : x' = y' := by
            apply Subtype.ext
            exact congrArg (fun q : σ.NonprojectiveLabel ↦ q.1)
              hnonprojective
          have hlabels := congrArg Q.labelEquiv hxy'
          simpa [x', y'] using hlabels
  · intro y t x ht
    let y' : DeletedLabel K := Q.labelEquiv.symm y
    let t' : DeletedLabel K := Q.labelEquiv.symm t
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    have hynp : ¬ Projective (σ.obj y'.1) := by
      intro hp
      have hnone := Q.tau_none_of_projective y' hp
      have hfalse := tauEq_eq_false_of_tauNone hnone (Q.labelEquiv t')
      have ht' : tauEq Q.code (Q.labelEquiv y') (Q.labelEquiv t') = true := by
        simpa [y', t'] using ht
      simp [hfalse] at ht'
    have htranslate := (Q.tau_eq_iff y' t' hynp).1 (by
      simpa [y', t'] using ht)
    have hincidence := AR.arTranslation_incidence σ ⟨y'.1, hynp⟩ x'.1
    rw [htranslate] at hincidence
    constructor
    · intro hxy
      have hactual : HasIrreducibleMorphism (σ.obj t'.1) (σ.obj x'.1) := by
        apply hincidence.1
        exact (Q.edge_iff x' y').1 (by simpa [x', y'] using hxy)
      simpa [t', x'] using (Q.edge_iff t' x').2 hactual
    · intro htx
      have hactual : HasIrreducibleMorphism (σ.obj x'.1) (σ.obj y'.1) := by
        apply hincidence.2
        exact (Q.edge_iff t' x').1 (by simpa [t', x'] using htx)
      simpa [x', y'] using (Q.edge_iff x' y').2 hactual
  · intro x y hxy hyx
    let x' : DeletedLabel K := Q.labelEquiv.symm x
    let y' : DeletedLabel K := Q.labelEquiv.symm y
    have hxy' := (Q.edge_iff x' y').1 (by simpa [x', y'] using hxy)
    have hyx' := (Q.edge_iff y' x').1 (by simpa [y', x'] using hyx)
    rcases htwoCycle x' y' hxy' hyx' with ⟨hx, hfix⟩ | ⟨hy, hfix⟩
    · left
      simpa [x'] using (Q.tau_eq_iff x' x' hx).2 hfix
    · right
      simpa [y'] using (Q.tau_eq_iff y' y' hy).2 hfix
  · intro p hp ⟨b, hbp⟩ z
    let p' : DeletedLabel K := Q.labelEquiv.symm p
    let b' : DeletedLabel K := Q.labelEquiv.symm b
    let z' : DeletedLabel K := Q.labelEquiv.symm z
    have hp' : Projective (σ.obj p'.1) :=
      (Q.projective_iff_boundary p').2 (by simpa [p'] using hp)
    have hbnp : ¬ Projective (σ.obj b'.1) := by
      intro hbproj
      have hnone := Q.tau_none_of_projective b' hbproj
      have hfalse := tauEq_eq_false_of_tauNone hnone (Q.labelEquiv p')
      have hbp' : tauEq Q.code (Q.labelEquiv b') (Q.labelEquiv p') = true := by
        simpa [b', p'] using hbp
      simp [hfalse] at hbp'
    have htranslate := (Q.tau_eq_iff b' p' hbnp).1 (by
      simpa [b', p'] using hbp)
    cases hpz : edge Q.code p z
    · exact Or.inl rfl
    · cases hzp : edge Q.code z p
      · exact Or.inr rfl
      · exfalso
        apply htranslatedBoundary p' b' z' hp' hbnp htranslate
        · exact (Q.edge_iff p' z').1 (by simpa [p', z'] using hpz)
        · exact (Q.edge_iff z' p').1 (by simpa [z', p'] using hzp)

omit [Fintype ι] in
/-- Boolean form of the preceding semantic boundary-axiom assembly. -/
theorem boundaryAxioms_eq_true
    (hroot : ∀ x : DeletedLabel K, ∃ p : DeletedLabel K,
      Projective (σ.obj p.1) ∧
        Relation.ReflTransGen
          (fun a b : DeletedLabel K ↦
            HasIrreducibleMorphism (σ.obj a.1) (σ.obj b.1)) p x)
    (htwoCycle : ∀ x y : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1) →
      HasIrreducibleMorphism (σ.obj y.1) (σ.obj x.1) →
        (∃ hx : ¬ Projective (σ.obj x.1),
          (AR.arTranslation σ ⟨x.1, hx⟩).1 = x.1) ∨
        (∃ hy : ¬ Projective (σ.obj y.1),
          (AR.arTranslation σ ⟨y.1, hy⟩).1 = y.1))
    (htranslatedBoundary : ∀ p b z : DeletedLabel K,
      Projective (σ.obj p.1) →
      ∀ hb : ¬ Projective (σ.obj b.1),
      (AR.arTranslation σ ⟨b.1, hb⟩).1 = p.1 →
      HasIrreducibleMorphism (σ.obj p.1) (σ.obj z.1) →
      HasIrreducibleMorphism (σ.obj z.1) (σ.obj p.1) → False) :
    BoundaryAxioms Q.code Q.additionalBoundary = true :=
  boundaryAxioms_eq_true_of_conditions
    (Q.boundaryAxiomConditions σ hroot htwoCycle htranslatedBoundary)

/-- Decode a pre-normalization Boolean hook into an actual admissible AR
hook. -/
def admissibleHookOfBoundaryHookAt
    {a u b : Vertex}
    (h : BoundaryHookAt Q.code Q.additionalBoundary a u b = true) :
    AR.AdmissibleHook σ K := by
  let H := boundaryHookConditions_of_boundaryHookAt h
  let a' : DeletedLabel K := Q.labelEquiv.symm a
  let u' : DeletedLabel K := Q.labelEquiv.symm u
  let b' : DeletedLabel K := Q.labelEquiv.symm b
  have hu : ¬ Projective (σ.obj u'.1) := by
    intro hP
    have htrue := (Q.projective_iff_boundary u').1 hP
    have hfalse : boundaryAt Q.additionalBoundary u = false := by
      simpa [u'] using H.u_not_boundary
    have : boundaryAt Q.additionalBoundary u = true := by
      simpa [u'] using htrue
    simp [hfalse] at this
  have hb : ¬ Projective (σ.obj b'.1) := by
    intro hP
    have htrue := (Q.projective_iff_boundary b').1 hP
    have hfalse : boundaryAt Q.additionalBoundary b = false := by
      simpa [b'] using H.b_not_boundary
    have : boundaryAt Q.additionalBoundary b = true := by
      simpa [b'] using htrue
    simp [hfalse] at this
  refine
    { a := a'
      u := u'
      b := b'
      u_nonprojective := hu
      b_nonprojective := hb
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := (Q.tau_eq_iff b' a' hb).1 (by
        simpa [b', a'] using H.tau_b) }
  · constructor
    · apply (Q.edge_iff a' u').1
      simpa only [a', u', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u a).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w u').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u
        (Q.labelEquiv w)).1 (by simpa [u'] using hedge)
      simpa [a'] using heq
  · constructor
    · apply (Q.edge_iff u' b').1
      simpa only [u', b', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_b u).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w b').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_b
        (Q.labelEquiv w)).1 (by simpa [b'] using hedge)
      simpa [u'] using heq

omit [Fintype ι] in
/-- A successful pre-normalization hook search yields an actual admissible
hook. -/
theorem nonempty_admissibleHook_of_hasBoundaryHook
    (h : HasBoundaryHook Q.code Q.additionalBoundary = true) :
    Nonempty (AR.AdmissibleHook σ K) := by
  rcases exists_boundaryHookAt_of_hasBoundaryHook
    Q.code Q.additionalBoundary h with ⟨a, u, b, haub⟩
  exact ⟨Q.admissibleHookOfBoundaryHookAt σ haub⟩

omit [Fintype ι] in
/-- Actual hooklessness implies Boolean hooklessness before projective-root
uniqueness is known. -/
theorem hasBoundaryHook_eq_false_of_isEmpty
    [IsEmpty (AR.AdmissibleHook σ K)] :
    HasBoundaryHook Q.code Q.additionalBoundary = false := by
  cases h : HasBoundaryHook Q.code Q.additionalBoundary
  · rfl
  · exfalso
    exact (Q.nonempty_admissibleHook_of_hasBoundaryHook σ h).elim
      isEmptyElim

/-- Once the finite boundary certificate proves uniqueness, forget the
three empty boundary bits and obtain the unique-root realization consumed by
the packet classifier. -/
def toRealization (h : NoAdditionalBoundary Q.additionalBoundary = true) :
    Realization (σ := σ) AR K where
  labelEquiv := Q.labelEquiv
  code := Q.code
  projective_iff_zero x :=
    (Q.projective_iff_boundary x).trans
      (boundaryAt_eq_true_iff_of_noAdditionalBoundary h (Q.labelEquiv x))
  edge_iff := Q.edge_iff
  tau_eq_iff := Q.tau_eq_iff
  tau_none_iff := Q.tau_none_iff

omit [Fintype ι] in
/-- The finite pre-normalization classifier proves projective-root
uniqueness directly from actual hooklessness and its Boolean AR and ladder
certificates. -/
theorem noAdditionalBoundary_of_isEmpty
    [IsEmpty (AR.AdmissibleHook σ K)]
    {x : Vertex}
    (hAxioms : BoundaryAxioms Q.code Q.additionalBoundary = true)
    (hWitness : BoundaryWitness Q.code Q.additionalBoundary x = true) :
    NoAdditionalBoundary Q.additionalBoundary = true :=
  noAdditionalBoundary_of_axioms_of_hookless_of_witness
    Q.code Q.additionalBoundary x hAxioms
      (Q.hasBoundaryHook_eq_false_of_isEmpty σ) hWitness

end BoundaryRealization

namespace Realization

variable {AR : σ.FiniteARTranslationData} {K : Set ι}
  (Q : Realization (σ := σ) AR K)

/-- Decode a certified normalized hook into a literal admissible AR hook. -/
def admissibleHookOfHookAt
    {a u b : Vertex} (h : HookAt Q.code a u b = true) :
    AR.AdmissibleHook σ K := by
  let H := hookConditions_of_hookAt h
  let a' : DeletedLabel K := Q.labelEquiv.symm a
  let u' : DeletedLabel K := Q.labelEquiv.symm u
  let b' : DeletedLabel K := Q.labelEquiv.symm b
  have hu : ¬ Projective (σ.obj u'.1) := by
    intro hP
    apply H.u_ne_zero
    simpa [u'] using (Q.projective_iff_zero u').1 hP
  have hb : ¬ Projective (σ.obj b'.1) := by
    intro hP
    apply H.b_ne_zero
    simpa [b'] using (Q.projective_iff_zero b').1 hP
  refine
    { a := a'
      u := u'
      b := b'
      u_nonprojective := hu
      b_nonprojective := hb
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := (Q.tau_eq_iff b' a' hb).1 (by
        simpa [b', a'] using H.tau_b) }
  · constructor
    · apply (Q.edge_iff a' u').1
      simpa only [a', u', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u a).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w u').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_u
        (Q.labelEquiv w)).1 (by simpa [u'] using hedge)
      simpa [a'] using heq
  · constructor
    · apply (Q.edge_iff u' b').1
      simpa only [u', b', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_b u).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w b').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_b
        (Q.labelEquiv w)).1 (by simpa [b'] using hedge)
      simpa [u'] using heq

omit [Fintype ι] in
/-- A successful normalized hook search yields an actual admissible hook. -/
theorem nonempty_admissibleHook_of_hasHook
    (h : HasHook Q.code = true) :
    Nonempty (AR.AdmissibleHook σ K) := by
  rcases exists_hookAt_of_hasHook Q.code h with ⟨a, u, b, haub⟩
  exact ⟨Q.admissibleHookOfHookAt σ haub⟩

omit [Fintype ι] in
/-- If the actual deleted AR support is hookless, then so is every exact
normalized realization of it. -/
theorem hasHook_eq_false_of_isEmpty
    [IsEmpty (AR.AdmissibleHook σ K)] :
    HasHook Q.code = false := by
  cases h : HasHook Q.code
  · rfl
  · exfalso
    exact (Q.nonempty_admissibleHook_of_hasHook σ h).elim isEmptyElim

/-- Decode a certified normalized row `F` into the literal AR packet. -/
def fixedPacketOfFixedPacketAt
    {a c z : Vertex} (h : FixedPacketAt Q.code a c z = true) :
    AR.FixedPacket σ K := by
  let H := fixedPacketConditions_of_fixedPacketAt h
  let p' : DeletedLabel K := Q.labelEquiv.symm 0
  let a' : DeletedLabel K := Q.labelEquiv.symm a
  let c' : DeletedLabel K := Q.labelEquiv.symm c
  let z' : DeletedLabel K := Q.labelEquiv.symm z
  have hp : Projective (σ.obj p'.1) := by
    apply (Q.projective_iff_zero p').2
    simp [p']
  have ha : ¬ Projective (σ.obj a'.1) := by
    intro haP
    apply H.a_ne_zero
    simpa [a'] using (Q.projective_iff_zero a').1 haP
  have hc : ¬ Projective (σ.obj c'.1) := by
    intro hcP
    apply H.c_ne_zero
    simpa [c'] using (Q.projective_iff_zero c').1 hcP
  have hz : ¬ Projective (σ.obj z'.1) := by
    intro hzP
    apply H.z_ne_zero
    simpa [z'] using (Q.projective_iff_zero z').1 hzP
  refine
    { p := p'
      a := a'
      c := c'
      z := z'
      p_projective := hp
      a_nonprojective := ha
      c_nonprojective := hc
      z_nonprojective := hz
      p_to_a := (Q.edge_iff p' a').1 (by
        simpa [p', a'] using H.edge_root_a)
      c_to_a := (Q.edge_iff c' a').1 (by
        simpa [c', a'] using H.edge_c_a)
      predecessor_z := ?_
      predecessor_c := ?_
      tau_z := (Q.tau_eq_iff z' a' hz).1 (by
        simpa [z', a'] using H.tau_z)
      tau_c := (Q.tau_eq_iff c' c' hc).1 (by
        simpa [c'] using H.tau_c)
      tau_a_eq_z_or_mem := ?_
      p_not_to_z := ?_ }
  · constructor
    · apply (Q.edge_iff c' z').1
      simpa only [c', z', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_z c).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w z').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_z
        (Q.labelEquiv w)).1 (by simpa [z'] using hedge)
      simpa [c'] using heq
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      apply ne_of_exactlyTwoPredecessors H.predecessor_c
      have heq' := congrArg Q.labelEquiv heq
      simpa [a', z'] using heq'
    · apply (Q.edge_iff a' c').1
      simpa only [a', c', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_c a).2
          (Or.inl rfl)
    · apply (Q.edge_iff z' c').1
      simpa only [z', c', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_c z).2
          (Or.inr rfl)
    · intro w hw
      have hedge := (Q.edge_iff w c').2 hw
      rcases (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_c
        (Q.labelEquiv w)).1 (by simpa [c'] using hedge) with heq | heq
      · left
        apply Q.labelEquiv.injective
        simpa [a'] using heq
      · right
        apply Q.labelEquiv.injective
        simpa [z'] using heq
  · rcases H.tau_a with hta | hta
    · exact Or.inl ((Q.tau_eq_iff a' z' ha).1 (by
        simpa [a', z'] using hta))
    · exact Or.inr ((Q.tau_none_iff a' ha).1 (by
        simpa [a'] using hta))
  · intro hpz'
    have hedge := (Q.edge_iff p' z').2 hpz'
    have : edge Q.code 0 z = true := by simpa [p', z'] using hedge
    have hroot := H.root_not_to_z
    simp [this] at hroot

/-- Decode a certified normalized row `T` into the literal AR packet. -/
def trianglePacketOfTrianglePacketAt
    {A₁ A₂ x : Vertex} (h : TrianglePacketAt Q.code A₁ A₂ x = true) :
    AR.TrianglePacket σ K := by
  let H := trianglePacketConditions_of_trianglePacketAt h
  let p' : DeletedLabel K := Q.labelEquiv.symm 0
  let A₁' : DeletedLabel K := Q.labelEquiv.symm A₁
  let A₂' : DeletedLabel K := Q.labelEquiv.symm A₂
  let x' : DeletedLabel K := Q.labelEquiv.symm x
  have hp : Projective (σ.obj p'.1) := by
    apply (Q.projective_iff_zero p').2
    simp [p']
  have hA₁ : ¬ Projective (σ.obj A₁'.1) := by
    intro hP
    apply H.A₁_ne_zero
    simpa [A₁'] using (Q.projective_iff_zero A₁').1 hP
  have hA₂ : ¬ Projective (σ.obj A₂'.1) := by
    intro hP
    apply H.A₂_ne_zero
    simpa [A₂'] using (Q.projective_iff_zero A₂').1 hP
  have hx : ¬ Projective (σ.obj x'.1) := by
    intro hP
    apply H.x_ne_zero
    simpa [x'] using (Q.projective_iff_zero x').1 hP
  refine
    { p := p'
      A₁ := A₁'
      A₂ := A₂'
      x := x'
      p_projective := hp
      A₁_nonprojective := hA₁
      A₂_nonprojective := hA₂
      x_nonprojective := hx
      A₁_to_p := (Q.edge_iff A₁' p').1 (by
        simpa [A₁', p'] using H.edge_A₁_root)
      predecessor_A₁ := ?_
      predecessor_A₂ := ?_
      predecessor_x := ?_
      tau_A₁ := (Q.tau_eq_iff A₁' p' hA₁).1 (by
        simpa [A₁', p'] using H.tau_A₁)
      tau_A₂ := (Q.tau_eq_iff A₂' A₁' hA₂).1 (by
        simpa [A₂', A₁'] using H.tau_A₂)
      tau_x_mem := (Q.tau_none_iff x' hx).1 (by
        simpa [x'] using H.tau_x) }
  · constructor
    · apply (Q.edge_iff A₂' A₁').1
      simpa only [A₂', A₁', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_A₁ A₂).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w A₁').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_A₁
        (Q.labelEquiv w)).1 (by simpa [A₁'] using hedge)
      simpa [A₂'] using heq
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      apply ne_of_exactlyTwoPredecessors H.predecessor_A₂
      have heq' := congrArg Q.labelEquiv heq
      simpa [p', x'] using heq'
    · apply (Q.edge_iff p' A₂').1
      simpa only [p', A₂', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_A₂ 0).2
          (Or.inl rfl)
    · apply (Q.edge_iff x' A₂').1
      simpa only [x', A₂', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_A₂ x).2
          (Or.inr rfl)
    · intro w hw
      have hedge := (Q.edge_iff w A₂').2 hw
      rcases (edge_eq_true_iff_of_exactlyTwoPredecessors H.predecessor_A₂
        (Q.labelEquiv w)).1 (by simpa [A₂'] using hedge) with heq | heq
      · left
        apply Q.labelEquiv.injective
        simpa [p'] using heq
      · right
        apply Q.labelEquiv.injective
        simpa [x'] using heq
  · constructor
    · apply (Q.edge_iff A₁' x').1
      simpa only [A₁', x', Equiv.apply_symm_apply] using
        (edge_eq_true_iff_of_uniquePredecessor H.predecessor_x A₁).2 rfl
    · intro w hw
      apply Q.labelEquiv.injective
      have hedge := (Q.edge_iff w x').2 hw
      have heq := (edge_eq_true_iff_of_uniquePredecessor H.predecessor_x
        (Q.labelEquiv w)).1 (by simpa [x'] using hedge)
      simpa [A₁'] using heq

omit [Fintype ι] in
/-- A successful normalized row-`F` search yields an actual row-`F`
AR packet without retaining the normalized labels. -/
theorem nonempty_fixedPacket_of_hasFixedPacket
    (h : HasFixedPacket Q.code = true) :
    Nonempty (AR.FixedPacket σ K) := by
  rcases exists_fixedPacketAt_of_hasFixedPacket Q.code h with
    ⟨a, c, z, hacz⟩
  exact ⟨Q.fixedPacketOfFixedPacketAt σ hacz⟩

omit [Fintype ι] in
/-- A successful normalized row-`T` search yields an actual row-`T`
AR packet without retaining the normalized labels. -/
theorem nonempty_trianglePacket_of_hasTrianglePacket
    (h : HasTrianglePacket Q.code = true) :
    Nonempty (AR.TrianglePacket σ K) := by
  rcases exists_trianglePacketAt_of_hasTrianglePacket Q.code h with
    ⟨A₁, A₂, x, hA⟩
  exact ⟨Q.trianglePacketOfTrianglePacketAt σ hA⟩

end Realization

end NormalizedFour

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
