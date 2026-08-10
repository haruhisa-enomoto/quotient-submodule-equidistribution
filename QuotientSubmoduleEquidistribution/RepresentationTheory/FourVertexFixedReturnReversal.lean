import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedStripBridge
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexPreliminaryM5
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexStripReversal

/-!
# Reversal of fixed two-cycle returns

A fixed return is a projectively based admissible strip together with a
fourth vertex joined in both directions to the strip middle.  The middle
cannot itself be translation-fixed: otherwise mesh incidence supplies an
opposite arrow at the projective hook source, forcing that source to be
injective.  Hence the fourth vertex is the fixed center.

The fixed-strip bridge transports the hook-source arrow to the paired
injective endpoint, with the middle vertex shifted around the finite cycle
of neighbors of that center.  Completing this transported arrow by one AR
mesh gives a reverse admissible strip.  Aligned duality then produces a
fixed return on the dual skeleton.  The construction uses only the general
finite AR-translation data.
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
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

namespace FiniteARTranslationData

variable (ARsigma : sigma.FiniteARTranslationData)
  (ARtau : tau.FiniteARTranslationData)
  (D : AlignedBiduality sigma tau)

namespace HookM5FixedReturn

variable (M : ARsigma.HookM5FixedReturn sigma)

include k in
/-- In a projectively based fixed return, the fixed vertex supplied by the
local two-cycle theorem is necessarily the fourth label. -/
theorem z_arTranslation_fixed :
    (ARsigma.arTranslation sigma
      ⟨M.1.z, M.1.z_nonprojective⟩).1 = M.1.z := by
  rcases M.exists_arTranslation_fixed (k := k) sigma ARsigma with
    hu | hz
  · rcases hu with ⟨huNP, huFixed⟩
    have hua : HasIrreducibleMorphism
        (sigma.obj M.1.triple.u) (sigma.obj M.1.triple.a) := by
      have h := (ARsigma.arTranslation_incidence sigma
        ⟨M.1.triple.u, huNP⟩ M.1.triple.a).1
          M.1.triple.a_to_u
      simpa only [huFixed] using h
    have haI := ARsigma.injective_of_projective_two_cycle
      (K := k) sigma M.1.triple.a M.1.triple.u
        M.1.a_projective M.1.triple.a_to_u hua
    exact (M.1.triple.a_noninjective sigma ARsigma haI).elim
  · rcases hz with ⟨hzNP, hzFixed⟩
    simpa only [] using hzFixed

include k in
/-- The fourth label, with its canonical fixed-center structure. -/
def fixedCenter : ARsigma.FixedCenter sigma where
  c := M.1.z
  c_nonprojective := M.1.z_nonprojective
  c_noninjective := by
    have h := (ARsigma.arTranslation sigma
      ⟨M.1.z, M.1.z_nonprojective⟩).2
    rw [M.z_arTranslation_fixed (k := k) sigma ARsigma] at h
    exact h
  tau_c := M.z_arTranslation_fixed (k := k) sigma ARsigma

include k D in
/-- The hook middle is a boundary-free neighbor of the fixed fourth
label. -/
def fixedNeighbor : ARsigma.FixedNeighbor sigma
    (M.fixedCenter (k := k) sigma ARsigma) where
  x := M.1.triple.u
  x_nonprojective := M.1.triple.u_nonprojective
  x_noninjective :=
    D.noninjective_of_nonprojective_two_cycle
      (k := k) sigma tau ARtau M.1.triple.u M.1.z
        M.1.triple.u_nonprojective M.2.1 M.2.2
  c_to_x := M.2.2
  x_to_c := M.2.1

/-- The injective endpoint canonically paired with the projective hook
source. -/
def pairedInjective : {i : iota // Injective (sigma.obj i)} :=
  ARsigma.projectiveLabelEquivInjectiveLabel sigma
    ⟨M.1.triple.a, M.1.a_projective⟩

/-- The paired injective endpoint remains nonprojective.  The boundary
chain has positive length because the original hook source is
noninjective. -/
theorem pairedInjective_nonprojective :
    ¬ Projective (sigma.obj (M.pairedInjective sigma ARsigma).1) := by
  let p := M.1.triple.a
  let hp := M.1.a_projective
  let n := ARsigma.vertexChainLength sigma p hp
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    have hi := ARsigma.vertexChainAt_length_injective sigma p hp
    rw [show ARsigma.vertexChainLength sigma p hp = 0 by exact hnzero] at hi
    exact M.1.triple.a_noninjective sigma ARsigma (by
      simpa [FiniteARTranslationData.vertexChainAt] using hi)
  have hnp := (ARsigma.vertexOrbitData sigma).iterate_not_mem_source_of_pos_le_firstTargetIndex
      p hp hnpos le_rfl
  change ¬ Projective
    (sigma.obj (ARsigma.vertexChainAt sigma p n))
  simpa [FiniteARTranslationData.vertexChainAt, n] using hnp

omit [DecidableEq kappa] in
include k D in
/-- The neighbor obtained at the injective wall after applying the bridge
phase. -/
def bridgedNeighbor : ARsigma.FixedNeighbor sigma
    (M.fixedCenter (k := k) sigma ARsigma) :=
  fixedBridgeNeighbor
    (AR := ARsigma) (C := M.fixedCenter (k := k) sigma ARsigma)
      (k := k) sigma tau D ARtau M.1.triple.a M.1.a_projective
      (M.fixedNeighbor (k := k) sigma tau ARsigma ARtau D)

omit [DecidableEq kappa] in
include k D in
/-- The transported neighbor points to the paired injective endpoint. -/
theorem bridgedNeighbor_to_pairedInjective :
    HasIrreducibleMorphism
      (sigma.obj (M.bridgedNeighbor
        (k := k) sigma tau ARsigma ARtau D).x)
      (sigma.obj (M.pairedInjective sigma ARsigma).1) := by
  exact (projective_to_neighbor_iff_bridgeNeighbor_to_injective
    (AR := ARsigma)
    (C := M.fixedCenter (k := k) sigma ARsigma)
    (k := k) sigma tau D ARtau
    M.1.triple.a M.1.a_projective
    (M.fixedNeighbor (k := k) sigma tau ARsigma ARtau D)).1
      M.1.triple.a_to_u

include k D in
/-- Complete the transported wall arrow by one AR mesh.  This is the
source-coordinate reverse admissible strip used before applying duality. -/
def reverseTriple : ARsigma.ReverseStripAdmissibleTriple sigma := by
  let C := M.fixedCenter (k := k) sigma ARsigma
  let X := M.bridgedNeighbor (k := k) sigma tau ARsigma ARtau D
  let i := (M.pairedInjective sigma ARsigma).1
  have hiI : Injective (sigma.obj i) :=
    (M.pairedInjective sigma ARsigma).2
  have hiNP : ¬ Projective (sigma.obj i) :=
    HookM5FixedReturn.pairedInjective_nonprojective
      (M := M) sigma ARsigma
  let b := (ARsigma.arTranslation sigma ⟨i, hiNP⟩).1
  have hbNI : ¬ Injective (sigma.obj b) :=
    (ARsigma.arTranslation sigma ⟨i, hiNP⟩).2
  have hXi : HasIrreducibleMorphism (sigma.obj X.x) (sigma.obj i) :=
    M.bridgedNeighbor_to_pairedInjective
      (k := k) sigma tau ARsigma ARtau D
  have hbX : HasIrreducibleMorphism (sigma.obj b) (sigma.obj X.x) := by
    exact (ARsigma.arTranslation_incidence sigma ⟨i, hiNP⟩ X.x).1 hXi
  have hXnotB :
      ¬ HasIrreducibleMorphism (sigma.obj X.x) (sigma.obj b) := by
    intro hXb
    rcases ARsigma.exists_arTranslation_eq_self_of_two_cycle
        (K := k) sigma X.x b hXb hbX with hXfixed | hbFixed
    · obtain ⟨hXNP, htauX⟩ := hXfixed
      have hiX : HasIrreducibleMorphism (sigma.obj i) (sigma.obj X.x) := by
        apply (ARsigma.arTranslation_incidence sigma
          ⟨X.x, hXNP⟩ i).2
        simpa only [htauX] using hXi
      exact hiNP (D.projective_of_injective_two_cycle
        (k := k) sigma tau ARtau i X.x hiI hiX hXi)
    · obtain ⟨hbNP, htauB⟩ := hbFixed
      have hib : i = b := by
        have hlabels : (⟨i, hiNP⟩ : sigma.NonprojectiveLabel) =
            ⟨b, hbNP⟩ := by
          apply ARsigma.arTranslation_injective sigma
          apply Subtype.ext
          exact rfl |>.trans htauB.symm
        exact congrArg Subtype.val hlabels
      exact hbNI (hib ▸ hiI)
  have hbNotI :
      ¬ HasIrreducibleMorphism (sigma.obj b) (sigma.obj i) :=
    ARsigma.no_irreducible_transitiveTriangle (K := k) sigma hbX hXi
  have hInvB : ((ARsigma.arTranslationEquiv sigma).symm
      ⟨b, hbNI⟩).1 = i := by
    have htauSubtype : ARsigma.arTranslationEquiv sigma
        ⟨i, hiNP⟩ = ⟨b, hbNI⟩ := by
      apply Subtype.ext
      rfl
    have hback := (ARsigma.arTranslationEquiv sigma).symm_apply_eq.mpr
      htauSubtype.symm
    exact congrArg Subtype.val hback
  exact
    { a := i
      u := X.x
      b := b
      a_ne_u := by
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj i (by
          simpa only [h] using hXi)
      a_ne_b := by
        intro h
        exact hbNI (h ▸ hiI)
      u_ne_b := by
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj X.x (by
          simpa only [h] using hbX)
      u_noninjective := X.x_noninjective
      b_noninjective := hbNI
      u_to_a := hXi
      b_to_u := hbX
      u_not_to_b := hXnotB
      b_not_to_a := hbNotI
      inverseTau_b := hInvB }

end HookM5FixedReturn

include k D in
/-- Fixed-center bridge transport followed by aligned duality sends a
fixed return to a fixed return on the dual skeleton. -/
def fixedReturnToDual
    (M : ARsigma.HookM5FixedReturn sigma) :
    ARtau.HookM5FixedReturn tau := by
  let C := M.fixedCenter (k := k) sigma ARsigma
  let X := M.bridgedNeighbor (k := k) sigma tau ARsigma ARtau D
  let U := M.reverseTriple (k := k) sigma tau ARsigma ARtau D
  let T := pushforwardReverseStripAdmissibleTriple
    sigma tau ARsigma ARtau D U
  let z := D.forward.labelEquiv C.c
  have hXz : HasIrreducibleMorphism (tau.obj T.u) (tau.obj z) := by
    exact (D.hasIrreducibleMorphism_image_iff sigma tau
      (x := C.c) (y := X.x)).2 X.c_to_x
  have hzX : HasIrreducibleMorphism (tau.obj z) (tau.obj T.u) := by
    exact (D.hasIrreducibleMorphism_image_iff sigma tau
      (x := X.x) (y := C.c)).2 X.x_to_c
  have hzNotMem : z ∉ T.support := by
    have hUi : U.a = (M.pairedInjective sigma ARsigma).1 := rfl
    have hUX : U.u = X.x := rfl
    have hzi : C.c ≠ U.a := by
      intro h
      exact C.c_noninjective ((h.trans hUi) ▸
        (M.pairedInjective sigma ARsigma).2)
    have hzXne : C.c ≠ U.u := by
      intro h
      have hcx : C.c = X.x := h.trans hUX
      exact sigma.hasNoIrreducibleEndomorphism_obj X.x
        (hcx ▸ X.c_to_x)
    have hzb : C.c ≠ U.b := by
      intro h
      have hiEq : U.a = C.c := by
        have hlabels :
            (⟨U.a, hUi ▸
              HookM5FixedReturn.pairedInjective_nonprojective
                (M := M) sigma ARsigma⟩ :
                sigma.NonprojectiveLabel) =
              ⟨C.c, C.c_nonprojective⟩ := by
          apply ARsigma.arTranslation_injective sigma
          apply Subtype.ext
          exact (by rfl :
            (ARsigma.arTranslation sigma
              ⟨U.a, hUi ▸
                HookM5FixedReturn.pairedInjective_nonprojective
                  (M := M) sigma ARsigma⟩).1 =
                U.b) |>.trans (h.symm.trans C.tau_c.symm)
        exact congrArg Subtype.val hlabels
      exact C.c_noninjective (hiEq.symm ▸
        (M.pairedInjective sigma ARsigma).2)
    change D.forward.labelEquiv C.c ∉
      ({D.forward.labelEquiv U.a,
        D.forward.labelEquiv U.u,
        D.forward.labelEquiv U.b} : Finset kappa)
    simpa only [Finset.mem_insert, Finset.mem_singleton,
      D.forward.labelEquiv.apply_eq_iff_eq] using
      (show C.c ∉ ({U.a, U.u, U.b} : Finset iota) by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
          ⟨hzi, hzXne, hzb⟩)
  refine ⟨
    { triple := T
      a_projective :=
        (D.forward.injective_iff_projective_image sigma tau U.a).1
          (M.pairedInjective sigma ARsigma).2
      z := z
      z_not_mem := hzNotMem
      z_nonprojective := by
        intro hzP
        exact C.c_noninjective
          ((D.forward.injective_iff_projective_image sigma tau C.c).2 hzP)
      outgoing_to_z := Or.inl hXz },
    hXz, hzX⟩

omit [Fintype iota] [DecidableEq iota] in
private theorem fixedNeighborSigma_eq_of_center_eq_of_val_eq
    {C1 C2 : ARsigma.FixedCenter sigma}
    (hC : C1 = C2)
    (X1 : ARsigma.FixedNeighbor sigma C1)
    (X2 : ARsigma.FixedNeighbor sigma C2)
    (hx : X1.x = X2.x) :
    (⟨C1, X1⟩ : Σ C : ARsigma.FixedCenter sigma,
      ARsigma.FixedNeighbor sigma C) = ⟨C2, X2⟩ := by
  subst C2
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  exact FixedNeighbor.ext hx

include k D in
/-- The fixed-return reversal construction is injective.  Its image
remembers the paired injective endpoint, the fixed center, and the
bridge-permuted neighbor; the two boundary equivalences recover the
original projective source and middle label. -/
theorem fixedReturnToDual_injective : Function.Injective
    (fixedReturnToDual (k := k) sigma tau ARsigma ARtau D) := by
  intro M1 M2 h
  let C1 := M1.fixedCenter (k := k) sigma ARsigma
  let C2 := M2.fixedCenter (k := k) sigma ARsigma
  let X1 := M1.fixedNeighbor (k := k) sigma tau ARsigma ARtau D
  let X2 := M2.fixedNeighbor (k := k) sigma tau ARsigma ARtau D
  let Y1 := M1.bridgedNeighbor (k := k) sigma tau ARsigma ARtau D
  let Y2 := M2.bridgedNeighbor (k := k) sigma tau ARsigma ARtau D
  let U1 := M1.reverseTriple (k := k) sigma tau ARsigma ARtau D
  let U2 := M2.reverseTriple (k := k) sigma tau ARsigma ARtau D
  have hpre :
      (fixedReturnToDual (k := k) sigma tau ARsigma ARtau D M1).1 =
        (fixedReturnToDual (k := k) sigma tau ARsigma ARtau D M2).1 :=
    congrArg Subtype.val h
  have htripleDual := congrArg HookM5Preliminary.triple hpre
  have hzDual := congrArg HookM5Preliminary.z hpre
  have hU : U1 = U2 := by
    apply (stripAdmissibleTripleEquivReverse
      sigma tau ARsigma ARtau D).symm.injective
    exact htripleDual
  have hz : C1.c = C2.c := by
    apply D.forward.labelEquiv.injective
    exact hzDual
  have hcenter : C1 = C2 := FixedCenter.ext hz
  have hi : U1.a = U2.a := congrArg ReverseStripAdmissibleTriple.a hU
  have hinjectiveEndpoint :
      M1.pairedInjective sigma ARsigma =
        M2.pairedInjective sigma ARsigma := by
    apply Subtype.ext
    exact hi
  have hprojectiveSource :
      (⟨M1.1.triple.a, M1.1.a_projective⟩ :
          {p : iota // Projective (sigma.obj p)}) =
        ⟨M2.1.triple.a, M2.1.a_projective⟩ := by
    exact (ARsigma.projectiveLabelEquivInjectiveLabel sigma).injective
      hinjectiveEndpoint
  have ha : M1.1.triple.a = M2.1.triple.a :=
    congrArg Subtype.val hprojectiveSource
  have hYval : Y1.x = Y2.x := by
    exact congrArg ReverseStripAdmissibleTriple.u hU
  let P := {p : iota // Projective (sigma.obj p)}
  let Z := Σ C : ARsigma.FixedCenter sigma,
    ARsigma.FixedNeighbor sigma C
  let p1 : P := ⟨M1.1.triple.a, M1.1.a_projective⟩
  let p2 : P := ⟨M2.1.triple.a, M2.1.a_projective⟩
  let B1 := fixedBridgeEquiv
    (AR := ARsigma) (C := C1) (k := k) sigma tau D ARtau
      p1.1 p1.2
  let B2 := fixedBridgeEquiv
    (AR := ARsigma) (C := C2) (k := k) sigma tau D ARtau
      p2.1 p2.2
  have hBval : (B1 X1).x = (B2 X2).x := by
    rw [fixedBridgeEquiv_apply, fixedBridgeEquiv_apply]
    exact hYval
  have hBZ : (⟨C1, B1 X1⟩ : Z) = ⟨C2, B2 X2⟩ :=
    fixedNeighborSigma_eq_of_center_eq_of_val_eq
      sigma ARsigma hcenter (B1 X1) (B2 X2) hBval
  have hkey : (p1, (⟨C1, B1 X1⟩ : Z)) =
      (p2, (⟨C2, B2 X2⟩ : Z)) := by
    apply Prod.ext
    · exact hprojectiveSource
    · exact hBZ
  let unbridgeLabel : P × Z → iota := fun Q ↦
    ((fixedBridgeEquiv
      (AR := ARsigma) (C := Q.2.1) (k := k) sigma tau D ARtau
        Q.1.1 Q.1.2).symm Q.2.2).x
  have hu : M1.1.triple.u = M2.1.triple.u := by
    have hlabel := congrArg unbridgeLabel hkey
    simpa only [unbridgeLabel, p1, p2, B1, B2,
      Equiv.symm_apply_apply, X1, X2, HookM5FixedReturn.fixedNeighbor]
      using hlabel
  have hfirst :
      M1.1.triple.firstArrow sigma ARsigma =
        M2.1.triple.firstArrow sigma ARsigma := by
    apply Subtype.ext
    apply Prod.ext
    · exact ha
    · exact hu
  have htriple : M1.1.triple = M2.1.triple :=
    StripAdmissibleTriple.firstArrow_injective sigma ARsigma hfirst
  have hpreOriginal : M1.1 = M2.1 := by
    apply HookM5Preliminary.ext
    · exact htriple
    · exact hz
  exact Subtype.ext hpreOriginal

include k D in
/-- Fixed two-cycle returns have the same cardinality on aligned opposite
skeletons. -/
theorem hookM5FixedReturn_card_eq :
    Fintype.card (ARsigma.HookM5FixedReturn sigma) =
      Fintype.card (ARtau.HookM5FixedReturn tau) := by
  let D' : AlignedBiduality tau sigma := D.swap sigma tau
  have hst : Fintype.card (ARsigma.HookM5FixedReturn sigma) ≤
      Fintype.card (ARtau.HookM5FixedReturn tau) :=
    Fintype.card_le_of_injective
      (fixedReturnToDual (k := k) sigma tau ARsigma ARtau D)
      (fixedReturnToDual_injective
        (k := k) sigma tau ARsigma ARtau D)
  have hts : Fintype.card (ARtau.HookM5FixedReturn tau) ≤
      Fintype.card (ARsigma.HookM5FixedReturn sigma) :=
    Fintype.card_le_of_injective
      (fixedReturnToDual (k := k) tau sigma ARtau ARsigma D')
      (fixedReturnToDual_injective
        (k := k) tau sigma ARtau ARsigma D')
  omega

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
