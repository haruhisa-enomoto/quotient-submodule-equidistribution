import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedNeighborCycles

/-!
# The projective--injective bridge for fixed strips

The fixed-strip argument compares arrows from a projective boundary vertex
to a periodic neighbor of a translation-fixed center with arrows from a
shifted neighbor into the paired injective boundary vertex.  Two mesh
incidence equivalences transport the arrow across each step of the finite
projective-to-injective translation chain.  This file proves that bridge
without choosing a concrete algebra or classifying its modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable {AR : σ.FiniteARTranslationData}
  {C : AR.FixedCenter σ}
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- Moving one step toward the injective boundary and one step backward
around the fixed-neighbor cycle preserves the existence of the boundary
arrow.  This is the two-mesh step in the fixed-strip bridge. -/
theorem boundarySuccessor_to_retreat_iff
    (q : ι) (hq : ¬ Injective (σ.obj q))
    (X : AR.FixedNeighbor σ C) :
    HasIrreducibleMorphism (σ.obj q) (σ.obj X.x) ↔
      HasIrreducibleMorphism
        (σ.obj ((AR.vertexOrbitData σ).successor q))
        (σ.obj
          (((FixedNeighbor.forwardEquiv
            (AR := AR) (C := C) (k := k) σ τ D ARτ).symm X).x)) := by
  let T := AR.vertexOrbitData σ
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  let q' := T.successor q
  let X' := E.symm X
  have hq'P : ¬ Projective (σ.obj q') :=
    T.successor_not_mem_source_of_not_mem_target hq
  have hτq' : (AR.arTranslation σ ⟨q', hq'P⟩).1 = q :=
    AR.arTranslation_successor_of_noninjective σ q hq
  have hτX' :
      (AR.arTranslation σ ⟨X'.x, X'.x_nonprojective⟩).1 = X.x :=
    FixedNeighbor.arTranslation_forwardEquiv_symm
      (AR := AR) (C := C) (k := k) σ τ D ARτ X
  constructor
  · intro hqX
    have hXq' : HasIrreducibleMorphism (σ.obj X.x) (σ.obj q') := by
      apply (AR.arTranslation_incidence σ ⟨q', hq'P⟩ X.x).2
      simpa only [hτq'] using hqX
    apply (AR.arTranslation_incidence σ
      ⟨X'.x, X'.x_nonprojective⟩ q').2
    simpa only [hτX'] using hXq'
  · intro hq'X'
    have hXq' : HasIrreducibleMorphism (σ.obj X.x) (σ.obj q') := by
      have h := (AR.arTranslation_incidence σ
        ⟨X'.x, X'.x_nonprojective⟩ q').1 hq'X'
      simpa only [hτX'] using h
    have hqX :=
      (AR.arTranslation_incidence σ ⟨q', hq'P⟩ X.x).1 hXq'
    simpa only [hτq'] using hqX

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- After `n` boundary-chain steps, the boundary arrow is shifted backward
by `n` positions around the fixed-neighbor cycle. -/
theorem vertexChainAt_to_retreat_iterate_iff
    (p : ι) (hp : Projective (σ.obj p))
    (X : AR.FixedNeighbor σ C) {n : ℕ}
    (hn : n ≤ AR.vertexChainLength σ p hp) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj X.x) ↔
      HasIrreducibleMorphism
        (σ.obj (AR.vertexChainAt σ p n))
        (σ.obj
          ((((FixedNeighbor.forwardEquiv
            (AR := AR) (C := C) (k := k) σ τ D ARτ).symm)^[n] X).x)) := by
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  induction n with
  | zero => simp [FiniteARTranslationData.vertexChainAt]
  | succ n ih =>
      have hnlt : n < AR.vertexChainLength σ p hp := by omega
      have hnle : n ≤ AR.vertexChainLength σ p hp := by omega
      have hnotI : ¬ Injective
          (σ.obj (AR.vertexChainAt σ p n)) :=
        (AR.vertexOrbitData σ).not_mem_target_before_firstTargetIndex
          p hp hnlt
      calc
        HasIrreducibleMorphism (σ.obj p) (σ.obj X.x) ↔
            HasIrreducibleMorphism
              (σ.obj (AR.vertexChainAt σ p n))
              (σ.obj ((E.symm^[n] X).x)) := ih hnle
        _ ↔ HasIrreducibleMorphism
              (σ.obj (AR.vertexChainAt σ p (n + 1)))
              (σ.obj ((E.symm^[n + 1] X).x)) := by
          simpa only [FiniteARTranslationData.vertexChainAt,
            Function.iterate_succ_apply'] using
            (boundarySuccessor_to_retreat_iff
              (AR := AR) (C := C) (k := k) σ τ D ARτ
              (AR.vertexChainAt σ p n) hnotI (E.symm^[n] X))

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- A boundary arrow to a translation-fixed center is unchanged when the
boundary vertex moves one step toward its injective endpoint. -/
theorem boundarySuccessor_to_fixedCenter_iff
    (q : ι) (hq : ¬ Injective (σ.obj q)) :
    HasIrreducibleMorphism (σ.obj q) (σ.obj C.c) ↔
      HasIrreducibleMorphism
        (σ.obj ((AR.vertexOrbitData σ).successor q))
        (σ.obj C.c) := by
  let T := AR.vertexOrbitData σ
  let q' := T.successor q
  have hq'P : ¬ Projective (σ.obj q') :=
    T.successor_not_mem_source_of_not_mem_target hq
  have hτq' : (AR.arTranslation σ ⟨q', hq'P⟩).1 = q :=
    AR.arTranslation_successor_of_noninjective σ q hq
  constructor
  · intro hqc
    have hcq' : HasIrreducibleMorphism (σ.obj C.c) (σ.obj q') := by
      apply (AR.arTranslation_incidence σ ⟨q', hq'P⟩ C.c).2
      simpa only [hτq'] using hqc
    apply (AR.arTranslation_incidence σ
      ⟨C.c, C.c_nonprojective⟩ q').2
    simpa only [C.tau_c] using hcq'
  · intro hq'c
    have hcq' : HasIrreducibleMorphism (σ.obj C.c) (σ.obj q') := by
      have h := (AR.arTranslation_incidence σ
        ⟨C.c, C.c_nonprojective⟩ q').1 hq'c
      simpa only [C.tau_c] using h
    have hqc :=
      (AR.arTranslation_incidence σ ⟨q', hq'P⟩ C.c).1 hcq'
    simpa only [hτq'] using hqc

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- Iterating the previous equivalence transports a center-boundary arrow
to every position of the projective-to-injective chain. -/
theorem vertexChainAt_to_fixedCenter_iff
    (p : ι) (hp : Projective (σ.obj p)) {n : ℕ}
    (hn : n ≤ AR.vertexChainLength σ p hp) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj C.c) ↔
      HasIrreducibleMorphism
        (σ.obj (AR.vertexChainAt σ p n)) (σ.obj C.c) := by
  induction n with
  | zero => simp [FiniteARTranslationData.vertexChainAt]
  | succ n ih =>
      have hnlt : n < AR.vertexChainLength σ p hp := by omega
      have hnle : n ≤ AR.vertexChainLength σ p hp := by omega
      have hnotI : ¬ Injective
          (σ.obj (AR.vertexChainAt σ p n)) :=
        (AR.vertexOrbitData σ).not_mem_target_before_firstTargetIndex
          p hp hnlt
      exact (ih hnle).trans (by
        simpa only [FiniteARTranslationData.vertexChainAt,
          Function.iterate_succ_apply'] using
          (boundarySuccessor_to_fixedCenter_iff
            (AR := AR) (C := C) σ
            (AR.vertexChainAt σ p n) hnotI))

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- The center version of the fixed-strip bridge has no cyclic phase:
`p → c` is equivalent to `c → I`. -/
theorem projective_to_fixedCenter_iff_fixedCenter_to_injective
    (p : ι) (hp : Projective (σ.obj p)) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj C.c) ↔
      HasIrreducibleMorphism (σ.obj C.c)
        (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
          ⟨p, hp⟩).1)) := by
  let n := AR.vertexChainLength σ p hp
  have hchain := vertexChainAt_to_fixedCenter_iff
    (AR := AR) (C := C) σ p hp
    (n := n) le_rfl
  calc
    HasIrreducibleMorphism (σ.obj p) (σ.obj C.c) ↔
        HasIrreducibleMorphism
          (σ.obj (AR.vertexChainAt σ p n)) (σ.obj C.c) := hchain
    _ ↔ HasIrreducibleMorphism (σ.obj C.c)
          (σ.obj (AR.vertexChainAt σ p n)) := by
      simpa only [C.tau_c] using
        (AR.arTranslation_incidence σ
          ⟨C.c, C.c_nonprojective⟩
          (AR.vertexChainAt σ p n))
    _ ↔ HasIrreducibleMorphism (σ.obj C.c)
          (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
            ⟨p, hp⟩).1)) := by rfl

/-- The neighbor which appears at the injective end of the fixed-strip
bridge.  It is one forward shift after retreating by the length of the
projective-to-injective chain. -/
def fixedBridgeNeighbor
    (p : ι) (hp : Projective (σ.obj p))
    (X : AR.FixedNeighbor σ C) : AR.FixedNeighbor σ C :=
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  E (E.symm^[AR.vertexChainLength σ p hp] X)

/-- The phase shift in the fixed-strip bridge is a permutation of the
fixed-neighbor family. -/
def fixedBridgeEquiv
    (p : ι) (hp : Projective (σ.obj p)) :
    AR.FixedNeighbor σ C ≃ AR.FixedNeighbor σ C :=
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  (E.symm ^ AR.vertexChainLength σ p hp).trans E

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
@[simp]
theorem fixedBridgeEquiv_apply
    (p : ι) (hp : Projective (σ.obj p))
    (X : AR.FixedNeighbor σ C) :
    fixedBridgeEquiv (AR := AR) (C := C)
      (k := k) σ τ D ARτ p hp X =
      fixedBridgeNeighbor (AR := AR) (C := C)
        (k := k) σ τ D ARτ p hp X := by
  simp only [fixedBridgeEquiv, fixedBridgeNeighbor,
    Equiv.trans_apply, Equiv.Perm.coe_pow]

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- The bridge phase commutes with the forward cyclic shift. -/
theorem fixedBridgeEquiv_forwardEquiv
    (p : ι) (hp : Projective (σ.obj p))
    (X : AR.FixedNeighbor σ C) :
    fixedBridgeEquiv (AR := AR) (C := C)
        (k := k) σ τ D ARτ p hp
        (FixedNeighbor.forwardEquiv
          (AR := AR) (C := C) (k := k) σ τ D ARτ X) =
      FixedNeighbor.forwardEquiv
        (AR := AR) (C := C) (k := k) σ τ D ARτ
        (fixedBridgeEquiv (AR := AR) (C := C)
          (k := k) σ τ D ARτ p hp X) := by
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  let n := AR.vertexChainLength σ p hp
  have hcomm : Function.Commute (E.symm : AR.FixedNeighbor σ C → _)
      E := fun Y ↦ (E.symm_apply_apply Y).trans
        (E.apply_symm_apply Y).symm
  have hiterate := hcomm.iterate_left n X
  simpa only [fixedBridgeEquiv, Equiv.trans_apply, Equiv.Perm.coe_pow,
    E, n] using congrArg E hiterate

omit [Algebra k R] [FiniteDimensional k R] [DecidableEq ι] in
/-- Fixed-strip bridge: `p → X` holds exactly when the shifted neighbor
points to the injective endpoint canonically paired with `p`. -/
theorem projective_to_neighbor_iff_bridgeNeighbor_to_injective
    (p : ι) (hp : Projective (σ.obj p))
    (X : AR.FixedNeighbor σ C) :
    HasIrreducibleMorphism (σ.obj p) (σ.obj X.x) ↔
      HasIrreducibleMorphism
        (σ.obj ((fixedBridgeNeighbor
          (AR := AR) (C := C) (k := k) σ τ D ARτ p hp X).x))
        (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
          ⟨p, hp⟩).1)) := by
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := C) (k := k) σ τ D ARτ
  let n := AR.vertexChainLength σ p hp
  let Y : AR.FixedNeighbor σ C := E.symm^[n] X
  have hchain := vertexChainAt_to_retreat_iterate_iff
    (AR := AR) (C := C) (k := k) σ τ D ARτ p hp X
    (n := n) le_rfl
  have hτY : (AR.arTranslation σ
      ⟨Y.x, Y.x_nonprojective⟩).1 = (E Y).x := by
    exact (FixedNeighbor.forwardEquiv_apply
      (AR := AR) (C := C) (k := k) σ τ D ARτ Y).symm
  calc
    HasIrreducibleMorphism (σ.obj p) (σ.obj X.x) ↔
        HasIrreducibleMorphism
          (σ.obj (AR.vertexChainAt σ p n))
          (σ.obj Y.x) := hchain
    _ ↔ HasIrreducibleMorphism
          (σ.obj (E Y).x)
          (σ.obj (AR.vertexChainAt σ p n)) := by
      simpa only [hτY] using
        (AR.arTranslation_incidence σ
          ⟨Y.x, Y.x_nonprojective⟩
          (AR.vertexChainAt σ p n))
    _ ↔ HasIrreducibleMorphism
          (σ.obj ((fixedBridgeNeighbor
            (AR := AR) (C := C) (k := k) σ τ D ARτ p hp X).x))
          (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
            ⟨p, hp⟩).1)) := by
      rfl

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
