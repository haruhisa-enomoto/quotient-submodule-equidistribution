import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedStripReconstruction

/-!
# Reconstructing reverse fixed packets from cyclic falls

The projective--injective bridge turns a fall of the common projective wall
bit into the reversed row-`F` configuration at the canonically paired
injective endpoint.  This file carries out that inverse construction in
source coordinates.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable {AR : σ.FiniteARTranslationData}
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

/-- The neighbor at the injective wall obtained from a fixed-strip
position by the bridge phase. -/
def reverseFixedStripA (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : AR.FixedStripPosition σ C :=
  fixedBridgeEquiv
    (AR := AR) (C := C.center) (k := k) σ τ D ARτ
      C.p C.p_projective X

/-- The next injective-wall neighbor. -/
def reverseFixedStripZ (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : AR.FixedStripPosition σ C :=
  fixedBridgeEquiv
    (AR := AR) (C := C.center) (k := k) σ τ D ARτ
      C.p C.p_projective
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C X)

/-- The four source labels determined by a fixed-strip fall. -/
def reverseFixedStripDeleted (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : Finset ι :=
  {(AR.projectiveLabelEquivInjectiveLabel σ
      ⟨C.p, C.p_projective⟩).1,
    (reverseFixedStripA (AR := AR) (k := k) σ τ D ARτ C X).x,
    C.center.c,
    (reverseFixedStripZ (AR := AR) (k := k) σ τ D ARτ C X).x}

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
/-- A fall becomes a present `a → i` wall arrow followed by an absent
`z → i` wall arrow after applying the bridge phase. -/
theorem arrows_of_fixedStripFall
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    HasIrreducibleMorphism
        (σ.obj (reverseFixedStripA
          (AR := AR) (k := k) σ τ D ARτ C X).x)
        (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
          ⟨C.p, C.p_projective⟩).1)) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj (reverseFixedStripZ
          (AR := AR) (k := k) σ τ D ARτ C X).x)
        (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
          ⟨C.p, C.p_projective⟩).1)) := by
  have hpX := (fixedStripBit_eq_true_iff (AR := AR) σ C X).1 h.1
  have hpEX := (fixedStripBit_eq_false_iff (AR := AR) σ C
    (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C X)).1 h.2
  constructor
  · exact (projective_to_neighbor_iff_bridgeNeighbor_to_injective
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ
      C.p C.p_projective X).1 hpX
  · intro hzI
    apply hpEX
    exact (projective_to_neighbor_iff_bridgeNeighbor_to_injective
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ
      C.p C.p_projective
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C X)).2 hzI

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
/-- The bridge phase commutes with the cyclic step, so the reconstructed
`z` neighbor is the forward translate of `a`. -/
theorem forwardEquiv_reverseFixedStripA
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C) :
    fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
        (reverseFixedStripA (AR := AR) (k := k) σ τ D ARτ C X) =
      reverseFixedStripZ (AR := AR) (k := k) σ τ D ARτ C X := by
  exact (fixedBridgeEquiv_forwardEquiv
    (AR := AR) (C := C.center) (k := k) σ τ D ARτ
    C.p C.p_projective X).symm

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- A fall selects four pairwise distinct source labels. -/
theorem reverseFixedStripDeleted_card_of_isFall
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    (reverseFixedStripDeleted
      (AR := AR) (k := k) σ τ D ARτ C X).card = 4 := by
  let i := (AR.projectiveLabelEquivInjectiveLabel σ
    ⟨C.p, C.p_projective⟩).1
  let A := reverseFixedStripA (AR := AR) (k := k) σ τ D ARτ C X
  let Z := reverseFixedStripZ (AR := AR) (k := k) σ τ D ARτ C X
  have hiI : Injective (σ.obj i) :=
    (AR.projectiveLabelEquivInjectiveLabel σ
      ⟨C.p, C.p_projective⟩).2
  have hwalls := arrows_of_fixedStripFall
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hiA : i ≠ A.x := by
    intro heq
    exact A.x_noninjective (heq ▸ hiI)
  have hiC : i ≠ C.center.c := by
    intro heq
    exact C.center.c_noninjective (heq ▸ hiI)
  have hiZ : i ≠ Z.x := by
    intro heq
    exact Z.x_noninjective (heq ▸ hiI)
  have hAC : A.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using A.c_to_x)
  have hZC : Z.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using Z.c_to_x)
  have hAZ : A.x ≠ Z.x := by
    intro heq
    apply hwalls.2
    rw [← heq]
    exact hwalls.1
  change ({i, A.x, C.center.c, Z.x} : Finset ι).card = 4
  simp [hiA, hiC, hiZ, hAC, hZC.symm, hAZ]

omit [IsAlgClosed k] in
/-- A fall reconstructs the literal source-coordinate reverse row-`F`
packet on its four selected labels. -/
def reverseFixedPacketOfFixedStripFall
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    AR.ReverseFixedPacket σ
      (((reverseFixedStripDeleted
        (AR := AR) (k := k) σ τ D ARτ C X : Finset ι) : Set ι)ᶜ) := by
  let E := fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
  let i := (AR.projectiveLabelEquivInjectiveLabel σ
    ⟨C.p, C.p_projective⟩).1
  let A := reverseFixedStripA (AR := AR) (k := k) σ τ D ARτ C X
  let Z := reverseFixedStripZ (AR := AR) (k := k) σ τ D ARτ C X
  let Deleted := reverseFixedStripDeleted
    (AR := AR) (k := k) σ τ D ARτ C X
  let K : Set ι := ((Deleted : Finset ι) : Set ι)ᶜ
  let iD : DeletedLabel K :=
    ⟨i, by simp [K, Deleted, reverseFixedStripDeleted, i]⟩
  let aD : DeletedLabel K :=
    ⟨A.x, by simp [K, Deleted, reverseFixedStripDeleted, A]⟩
  let cD : DeletedLabel K :=
    ⟨C.center.c, by simp [K, Deleted, reverseFixedStripDeleted]⟩
  let zD : DeletedLabel K :=
    ⟨Z.x, by simp [K, Deleted, reverseFixedStripDeleted, Z]⟩
  have hwalls := arrows_of_fixedStripFall
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hEA : E A = Z :=
    forwardEquiv_reverseFixedStripA
      (AR := AR) (k := k) σ τ D ARτ C X
  have hInvZ : ((AR.arTranslationEquiv σ).symm
      ⟨Z.x, Z.x_noninjective⟩).1 = A.x := by
    have hstep := FixedNeighbor.successorEquiv_apply
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ Z
    have hback : E.symm Z = A := E.symm_apply_eq.mpr hEA.symm
    exact hstep.symm.trans (congrArg FixedNeighbor.x hback)
  have hInvC : ((AR.arTranslationEquiv σ).symm
      ⟨C.center.c, C.center.c_noninjective⟩).1 = C.center.c := by
    have htau : AR.arTranslationEquiv σ
        ⟨C.center.c, C.center.c_nonprojective⟩ =
          ⟨C.center.c, C.center.c_noninjective⟩ := by
      apply Subtype.ext
      exact C.center.tau_c
    have hback := (AR.arTranslationEquiv σ).symm_apply_eq.mpr htau.symm
    exact congrArg Subtype.val hback
  have hZnotA : Z.x ≠ A.x := by
    intro heq
    apply hwalls.2
    rw [heq]
    exact hwalls.1
  have hZnotToA :
      ¬ HasIrreducibleMorphism (σ.obj Z.x) (σ.obj A.x) := by
    intro hZA
    apply AR.no_irreducible_arTranslation_to_endpoint
      σ ⟨A.x, A.x_nonprojective⟩
    have hτA := FixedNeighbor.forwardEquiv_apply
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ A
    simpa only [hτA.symm.trans (congrArg FixedNeighbor.x hEA)] using hZA
  have hcNotI : ¬ HasIrreducibleMorphism (σ.obj C.center.c) (σ.obj i) := by
    intro hcI
    apply C.p_not_to_center
    exact (projective_to_fixedCenter_iff_fixedCenter_to_injective
      (AR := AR) (C := C.center) σ C.p C.p_projective).2 hcI
  refine
    { i := iD
      a := aD
      c := cD
      z := zD
      i_injective := (AR.projectiveLabelEquivInjectiveLabel σ
        ⟨C.p, C.p_projective⟩).2
      a_noninjective := A.x_noninjective
      c_noninjective := C.center.c_noninjective
      z_noninjective := Z.x_noninjective
      a_to_i := hwalls.1
      a_to_c := A.x_to_c
      successor_z := ?_
      successor_c := ?_
      inverseTau_z := hInvZ
      inverseTau_c := hInvC
      inverseTau_a_eq_z_or_mem := ?_
      z_not_to_i := hwalls.2 }
  · refine ⟨Z.x_to_c, ?_⟩
    intro q hZq
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, reverseFixedStripDeleted, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqi | hqA | hqC | hqZeq
    · exact (hwalls.2 (by simpa only [hqi] using hZq)).elim
    · exact (hZnotToA (by simpa only [hqA] using hZq)).elim
    · exact Subtype.ext hqC
    · exact (σ.hasNoIrreducibleEndomorphism_obj Z.x (by
        simpa only [hqZeq] using hZq)).elim
  · refine ⟨?_, A.c_to_x, Z.c_to_x, ?_⟩
    · intro hEq
      exact hZnotA (congrArg Subtype.val hEq).symm
    · intro q hcq
      have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
      simp only [Deleted, reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton] at hqmem
      rcases hqmem with hqi | hqA | hqCenter | hqZeq
      · exact (hcNotI (by simpa only [hqi] using hcq)).elim
      · exact Or.inl (Subtype.ext hqA)
      · exact (σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
          simpa only [hqCenter] using hcq)).elim
      · exact Or.inr (Subtype.ext hqZeq)
  · let Y := E.symm A
    have hInvA := FixedNeighbor.successorEquiv_apply
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ A
    by_cases hYZ : Y.x = Z.x
    · exact Or.inl (hInvA.symm.trans hYZ)
    · apply Or.inr
      change ((AR.arTranslationEquiv σ).symm
        ⟨A.x, A.x_noninjective⟩).1 ∈ K
      rw [← hInvA]
      change Y.x ∉ Deleted
      simp only [Deleted, reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_, hYZ⟩
      · intro hYi
        exact Y.x_noninjective (hYi ▸
          (AR.projectiveLabelEquivInjectiveLabel σ
            ⟨C.p, C.p_projective⟩).2)
      · intro hYA
        have hYAfull : Y = A := FixedNeighbor.ext hYA
        have hEAself : E A = A := by
          have hcongr := congrArg E hYAfull
          exact (by simpa [Y] using hcongr.symm)
        have hZA : Z = A := hEA.symm.trans hEAself
        exact hZnotA (congrArg FixedNeighbor.x hZA)
      · intro hYC
        exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
          simpa only [hYC] using Y.c_to_x)

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- The four displayed labels of a reverse fixed packet exhaust any
four-element source support. -/
theorem reverseFixedPacket_labels_eq_univ
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : AR.ReverseFixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    ({F.i, F.a, F.c, F.z} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) =
      Finset.univ := by
  classical
  have hia : F.i ≠ F.a := by
    intro hEq
    exact F.a_noninjective (hEq ▸ F.i_injective)
  have hic : F.i ≠ F.c := by
    intro hEq
    exact F.c_noninjective (hEq ▸ F.i_injective)
  have hiz : F.i ≠ F.z := by
    intro hEq
    exact F.z_noninjective (hEq ▸ F.i_injective)
  have hac : F.a ≠ F.c := by
    intro hEq
    exact σ.hasNoIrreducibleEndomorphism_obj F.c.1 (by
      simpa only [hEq] using F.a_to_c)
  have haz : F.a ≠ F.z := F.successor_c.1
  have hcz : F.c ≠ F.z := by
    intro hEq
    exact σ.hasNoIrreducibleEndomorphism_obj F.z.1 (by
      simpa only [hEq] using F.successor_z.1)
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteARTranslationData.natCard_deletedLabel_compl Deleted,
    hcard]
  simp [hia, hic, hiz, hac, haz, hcz]

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- Every source deleted label is one of the four reverse-packet labels. -/
theorem eq_reverseFixedPacket_label
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : AR.ReverseFixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ))
    (x : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ)) :
    x = F.i ∨ x = F.a ∨ x = F.c ∨ x = F.z := by
  have hx : x ∈ ({F.i, F.a, F.c, F.z} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) := by
    rw [reverseFixedPacket_labels_eq_univ
      (AR := AR) σ Deleted hcard F]
    exact Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- A four-element reverse row-`F` support cannot also carry a reverse
admissible hook. -/
theorem ReverseFixedPacket.no_reverseAdmissibleHook
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : AR.ReverseFixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    IsEmpty (AR.ReverseAdmissibleHook σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) := by
  constructor
  intro H
  rcases eq_reverseFixedPacket_label
      (AR := AR) σ Deleted hcard F H.b with
    hbI | hbA | hbC | hbZ
  · exact H.b_noninjective (hbI ▸ F.i_injective)
  · have hiu : F.i = H.u :=
      H.successor_b.2 F.i (by simpa only [hbA] using F.a_to_i)
    have hcu : F.c = H.u :=
      H.successor_b.2 F.c (by simpa only [hbA] using F.a_to_c)
    exact F.c_noninjective (hcu.trans hiu.symm ▸ F.i_injective)
  · have hau : F.a = H.u :=
      H.successor_b.2 F.a (by simpa only [hbC] using F.successor_c.2.1)
    have hzu : F.z = H.u :=
      H.successor_b.2 F.z (by simpa only [hbC] using F.successor_c.2.2.1)
    exact F.successor_c.1 (hau.trans hzu.symm)
  · have hcu : F.c = H.u :=
      H.successor_b.2 F.c (by simpa only [hbZ] using F.successor_z.1)
    have haA : F.a = H.a :=
      H.successor_u.2 F.a (by
        simpa only [← hcu] using F.successor_c.2.1)
    have hzA : F.z = H.a :=
      H.successor_u.2 F.z (by
        simpa only [← hcu] using F.successor_c.2.2.1)
    exact F.successor_c.1 (haA.trans hzA.symm)

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- The source support reconstructed from a fall is injectively corooted. -/
theorem reverseFixedStripDeleted_isInjectivelyCorooted_of_isFall
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
      σ.irreducibleEdge σ.injectiveLabelFinset
      (reverseFixedStripDeleted
        (AR := AR) (k := k) σ τ D ARτ C X) := by
  let i := (AR.projectiveLabelEquivInjectiveLabel σ
    ⟨C.p, C.p_projective⟩).1
  let A := reverseFixedStripA (AR := AR) (k := k) σ τ D ARτ C X
  let Z := reverseFixedStripZ (AR := AR) (k := k) σ τ D ARτ C X
  let Deleted := reverseFixedStripDeleted
    (AR := AR) (k := k) σ τ D ARτ C X
  have hwalls := arrows_of_fixedStripFall
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hi : i ∈ Deleted := by
    change i ∈ {i, A.x, C.center.c, Z.x}
    simp
  have ha : A.x ∈ Deleted := by
    change A.x ∈ {i, A.x, C.center.c, Z.x}
    simp
  have hc : C.center.c ∈ Deleted := by
    change C.center.c ∈ {i, A.x, C.center.c, Z.x}
    simp
  have hz : Z.x ∈ Deleted := by
    change Z.x ∈ {i, A.x, C.center.c, Z.x}
    simp
  have hiBoundary : i ∈ σ.injectiveLabelFinset := by
    simpa [injectiveLabelFinset, i] using
      (AR.projectiveLabelEquivInjectiveLabel σ
        ⟨C.p, C.p_projective⟩).2
  have hia : QuotientSubmoduleEquidistribution.RootedDigraph.ReachInside
      (fun x y ↦ σ.irreducibleEdge y x) Deleted i A.x :=
    Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨hi, ha, hwalls.1⟩
  have hiac : QuotientSubmoduleEquidistribution.RootedDigraph.ReachInside
      (fun x y ↦ σ.irreducibleEdge y x) Deleted i C.center.c :=
    hia.tail ⟨ha, hc, A.c_to_x⟩
  have hiacz : QuotientSubmoduleEquidistribution.RootedDigraph.ReachInside
      (fun x y ↦ σ.irreducibleEdge y x) Deleted i Z.x :=
    hiac.tail ⟨hc, hz, Z.x_to_c⟩
  intro y hy
  refine ⟨i, hiBoundary, hi, ?_⟩
  change y ∈ {i, A.x, C.center.c, Z.x} at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact hia
  · exact hiac
  · exact hiacz

omit [IsAlgClosed k] in
/-- Recovering the injective-wall data from an existing reverse row-`F`
packet recovers exactly its original source support. -/
theorem reverseFixedStripDeleted_reverseFixedPacket_eq
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : AR.ReverseFixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    reverseFixedStripDeleted (AR := AR) (k := k) σ τ D ARτ
      (F.fixedStripContext σ)
      (F.fallPosition (k := k) σ τ D ARτ) = Deleted := by
  classical
  let C := F.fixedStripContext σ
  let X := F.fallPosition (k := k) σ τ D ARτ
  let B := fixedBridgeEquiv
    (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
      (F.pairedProjective σ).1 (F.pairedProjective σ).2
  have hi : (AR.projectiveLabelEquivInjectiveLabel σ
      ⟨C.p, C.p_projective⟩).1 = F.i.1 := by
    change (AR.projectiveLabelEquivInjectiveLabel σ
      (F.pairedProjective σ)).1 = F.i.1
    exact congrArg Subtype.val
      ((AR.projectiveLabelEquivInjectiveLabel σ).apply_symm_apply
        ⟨F.i.1, F.i_injective⟩)
  have hA : reverseFixedStripA
      (AR := AR) (k := k) σ τ D ARτ C X = F.aNeighbor σ := by
    exact B.apply_symm_apply _
  have hZ : reverseFixedStripZ
      (AR := AR) (k := k) σ τ D ARτ C X = F.zNeighbor (k := k) σ := by
    calc
      reverseFixedStripZ
          (AR := AR) (k := k) σ τ D ARτ C X =
          fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
            (reverseFixedStripA
              (AR := AR) (k := k) σ τ D ARτ C X) :=
        (forwardEquiv_reverseFixedStripA
          (AR := AR) (k := k) σ τ D ARτ C X).symm
      _ = fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
            (F.aNeighbor σ) := congrArg _ hA
      _ = F.zNeighbor (k := k) σ := by
        change FixedNeighbor.forwardEquiv
          (AR := AR) (C := F.fixedCenter σ)
          (k := k) σ τ D ARτ (F.aNeighbor σ) =
            F.zNeighbor (k := k) σ
        exact F.forwardEquiv_aNeighbor_eq (k := k) σ τ D ARτ
  ext x
  constructor
  · intro hx
    simp only [reverseFixedStripDeleted, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with hxi | hxa | hxc | hxz
    · rw [hi] at hxi
      subst x
      simpa using F.i.2
    · rw [hA] at hxa
      change x = F.a.1 at hxa
      subst x
      simpa using F.a.2
    · change x = F.c.1 at hxc
      subst x
      simpa using F.c.2
    · rw [hZ] at hxz
      change x = F.z.1 at hxz
      subst x
      simpa using F.z.2
  · intro hx
    let q : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ) :=
      ⟨x, by simpa using hx⟩
    rcases eq_reverseFixedPacket_label
      (AR := AR) σ Deleted hcard F q with hqi | hqa | hqc | hqz
    · have hx' := congrArg Subtype.val hqi
      change x = F.i.1 at hx'
      simp only [reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl (hx'.trans hi.symm)
    · have hx' := congrArg Subtype.val hqa
      change x = F.a.1 at hx'
      simp only [reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr (Or.inl (hx'.trans (congrArg FixedNeighbor.x hA).symm))
    · have hx' := congrArg Subtype.val hqc
      change x = F.c.1 at hx'
      simp only [reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl (hx'.trans rfl)))
    · have hx' := congrArg Subtype.val hqz
      change x = F.z.1 at hx'
      simp only [reverseFixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr
        (hx'.trans (congrArg FixedNeighbor.x hZ).symm)))

/-- Reconstruct an actual source-coordinate reverse row-`F` support from
an arbitrary fall in the common fixed-strip system. -/
def fixedStripFallToSourceReverseFixedPacketFour
    (Y : FixedStripFall
      (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
      σ τ D (τ.finiteDimensionalARTranslationData k S)) :
    SourceReverseFixedPacketFour (k := k) (R := R) σ τ D := by
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ' := τ.finiteDimensionalARTranslationData k S
  let Deleted := reverseFixedStripDeleted
    (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1
  let F := reverseFixedPacketOfFixedStripFall
    (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  have hcard : Deleted.card = 4 :=
    reverseFixedStripDeleted_card_of_isFall
      (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  have hcoroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
      σ.irreducibleEdge σ.injectiveLabelFinset Deleted :=
    reverseFixedStripDeleted_isInjectivelyCorooted_of_isFall
      (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  let Q : QuotientRootedFour τ :=
    ⟨D.dualDeleted σ τ Deleted,
      D.dualDeleted_card σ τ Deleted |>.trans hcard,
      (D.isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
        σ τ Deleted).2 hcoroot⟩
  have hSource : sourceDeletedOfDualRooted σ τ D Q = Deleted := by
    change D.forward.labelEquiv.finsetCongr.symm
      (D.forward.labelEquiv.finsetCongr Deleted) = Deleted
    exact D.forward.labelEquiv.finsetCongr.symm_apply_apply Deleted
  let FQ : ARσ.ReverseFixedPacket σ
      (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ) := by
    rw [hSource]
    exact F
  have hEmpty : IsEmpty (ARσ.ReverseAdmissibleHook σ
      (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)) := by
    rw [hSource]
    exact F.no_reverseAdmissibleHook σ Deleted hcard
  exact ⟨Q, ⟨⟨FQ⟩, hEmpty⟩⟩

omit [IsAlgClosed k] in
/-- Reconstructing the dual rooted support after extracting an actual
reverse packet's fall returns the original dual support. -/
theorem fixedStripFallToSourceReverseFixedPacketFour_leftInverse :
    Function.LeftInverse
      (fixedStripFallToSourceReverseFixedPacketFour
        (k := k) (R := R) (S := S) σ τ D)
      (sourceReverseFixedPacketFourToFixedStripFall
        (k := k) (R := R) (S := S) σ τ D) := by
  intro Q
  let F := Classical.choice Q.2.1
  have hsourceCard :
      (sourceDeletedOfDualRooted σ τ D Q.1).card = 4 := by
    simpa [sourceDeletedOfDualRooted, Equiv.finsetCongr_apply] using Q.1.2.1
  apply Subtype.ext
  apply Subtype.ext
  change D.dualDeleted σ τ
      (reverseFixedStripDeleted
        (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
        σ τ D (τ.finiteDimensionalARTranslationData k S)
        (F.fixedStripContext σ)
        (F.fallPosition (k := k) σ τ D
          (τ.finiteDimensionalARTranslationData k S))) = Q.1.1
  rw [reverseFixedStripDeleted_reverseFixedPacket_eq
    (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
    σ τ D (τ.finiteDimensionalARTranslationData k S)
    (sourceDeletedOfDualRooted σ τ D Q.1) hsourceCard F]
  change D.forward.labelEquiv.finsetCongr
    (D.forward.labelEquiv.finsetCongr.symm Q.1.1) = Q.1.1
  exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1.1

omit [IsAlgClosed k] [DecidableEq ι] in
/-- A four-element dual rooted support carries at most one source-coordinate
reverse row-`F` packet. -/
theorem sourceReverseFixedPacket_unique
    (Q : QuotientRootedFour τ)
    (F₁ F₂ : (σ.finiteDimensionalARTranslationData k R).ReverseFixedPacket σ
      (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)) :
    F₁ = F₂ := by
  letI : DecidableEq κ := Classical.decEq κ
  let E := D.fixedPacketOnDualRootedEquivReverse
    (k := k) (R := R) (S := S) σ τ Q
  apply E.symm.injective
  exact fixedPacket_unique (k := k) (R := S) τ Q.1 Q.2.1
    (E.symm F₁) (E.symm F₂)

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
private theorem cast_reverseFixedPacket_i_val
    {K L : Set ι} (h : K = L) (F : AR.ReverseFixedPacket σ K) :
    (_root_.cast (congrArg (AR.ReverseFixedPacket σ) h) F).i.1 = F.i.1 := by
  subst L
  rfl

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
private theorem cast_reverseFixedPacket_a_val
    {K L : Set ι} (h : K = L) (F : AR.ReverseFixedPacket σ K) :
    (_root_.cast (congrArg (AR.ReverseFixedPacket σ) h) F).a.1 = F.a.1 := by
  subst L
  rfl

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
private theorem cast_reverseFixedPacket_c_val
    {K L : Set ι} (h : K = L) (F : AR.ReverseFixedPacket σ K) :
    (_root_.cast (congrArg (AR.ReverseFixedPacket σ) h) F).c.1 = F.c.1 := by
  subst L
  rfl

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Fintype ι] [DecidableEq ι] in
private theorem fixedStripPosition_sigma_eq_of_context_eq_of_val_eq
    {C₁ C₂ : AR.FixedStripContext σ}
    (hC : C₁ = C₂)
    (X₁ : AR.FixedStripPosition σ C₁)
    (X₂ : AR.FixedStripPosition σ C₂)
    (hX : X₁.x = X₂.x) :
    (⟨C₁, X₁⟩ : Σ C : AR.FixedStripContext σ,
      AR.FixedStripPosition σ C) = ⟨C₂, X₂⟩ := by
  subst C₂
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  apply FixedNeighbor.ext
  exact hX

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
private theorem fixedStripFall_eq_of_context_eq_of_val_eq
    {C₁ C₂ : AR.FixedStripContext σ}
    (X₁ : AR.FixedStripPosition σ C₁)
    (X₂ : AR.FixedStripPosition σ C₂)
    (h₁ : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C₁)
      (fixedStripBit (AR := AR) σ C₁) X₁)
    (h₂ : QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C₂)
      (fixedStripBit (AR := AR) σ C₂) X₂)
    (hC : C₁ = C₂) (hX : X₁.x = X₂.x) :
    (⟨C₁, ⟨X₁, h₁⟩⟩ : FixedStripFall
      (AR := AR) (k := k) σ τ D ARτ) = ⟨C₂, ⟨X₂, h₂⟩⟩ := by
  subst C₂
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  apply Subtype.ext
  apply FixedNeighbor.ext
  exact hX

omit [IsAlgClosed k] in
/-- Extracting the fall from the reverse packet reconstructed from that
fall returns the original cyclic position. -/
theorem fixedStripFallToSourceReverseFixedPacketFour_rightInverse :
    Function.RightInverse
      (fixedStripFallToSourceReverseFixedPacketFour
        (k := k) (R := R) (S := S) σ τ D)
      (sourceReverseFixedPacketFourToFixedStripFall
        (k := k) (R := R) (S := S) σ τ D) := by
  rintro ⟨C, ⟨X, h⟩⟩
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ' := τ.finiteDimensionalARTranslationData k S
  let Deleted := reverseFixedStripDeleted
    (AR := ARσ) (k := k) σ τ D ARτ' C X
  let F₀ := reverseFixedPacketOfFixedStripFall
    (AR := ARσ) (k := k) σ τ D ARτ' C X h
  let Q := fixedStripFallToSourceReverseFixedPacketFour
    (k := k) (R := R) (S := S) σ τ D ⟨C, ⟨X, h⟩⟩
  have hSource : sourceDeletedOfDualRooted σ τ D Q.1 = Deleted := by
    change D.forward.labelEquiv.finsetCongr.symm
      (D.forward.labelEquiv.finsetCongr Deleted) = Deleted
    exact D.forward.labelEquiv.finsetCongr.symm_apply_apply Deleted
  have hK :
      (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ) =
        (((Deleted : Finset ι) : Set ι)ᶜ) :=
    congrArg (fun T : Finset ι ↦ (((T : Finset ι) : Set ι)ᶜ)) hSource
  let FQ : ARσ.ReverseFixedPacket σ
      (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ) :=
    _root_.cast (congrArg (ARσ.ReverseFixedPacket σ) hK.symm) F₀
  have hF : Classical.choice Q.2.1 = FQ :=
    sourceReverseFixedPacket_unique
      (k := k) (R := R) (S := S) σ τ D Q.1
        (Classical.choice Q.2.1) FQ
  have hFQi : FQ.i.1 = F₀.i.1 := by
    exact cast_reverseFixedPacket_i_val
      (AR := ARσ) σ hK.symm F₀
  have hFQa : FQ.a.1 = F₀.a.1 := by
    exact cast_reverseFixedPacket_a_val
      (AR := ARσ) σ hK.symm F₀
  have hFQc : FQ.c.1 = F₀.c.1 := by
    exact cast_reverseFixedPacket_c_val
      (AR := ARσ) σ hK.symm F₀
  change (⟨(Classical.choice Q.2.1).fixedStripContext σ,
      ⟨(Classical.choice Q.2.1).fallPosition
          (k := k) σ τ D ARτ',
        (Classical.choice Q.2.1).isFall_fallPosition
          (k := k) σ τ D ARτ'⟩⟩ :
      FixedStripFall (AR := ARσ) (k := k) σ τ D ARτ') =
    ⟨C, ⟨X, h⟩⟩
  rw [hF]
  have hC : FQ.fixedStripContext σ = C := by
    apply FixedStripContext.ext
    · change ((ARσ.projectiveLabelEquivInjectiveLabel σ).symm
          ⟨FQ.i.1, FQ.i_injective⟩).1 = C.p
      have hi : (⟨FQ.i.1, FQ.i_injective⟩ :
          {i : ι // Injective (σ.obj i)}) =
          ARσ.projectiveLabelEquivInjectiveLabel σ
            ⟨C.p, C.p_projective⟩ := by
        apply Subtype.ext
        exact hFQi
      rw [hi]
      exact congrArg Subtype.val
        ((ARσ.projectiveLabelEquivInjectiveLabel σ).symm_apply_apply
          ⟨C.p, C.p_projective⟩)
    · apply FixedCenter.ext
      change FQ.c.1 = C.center.c
      exact hFQc
  have hAval : (FQ.aNeighbor σ).x =
      (reverseFixedStripA
        (AR := ARσ) (k := k) σ τ D ARτ' C X).x := hFQa
  have hASigma := fixedStripPosition_sigma_eq_of_context_eq_of_val_eq
    (AR := ARσ) σ hC (FQ.aNeighbor σ)
      (reverseFixedStripA
        (AR := ARσ) (k := k) σ τ D ARτ' C X) hAval
  let G : (Σ C : ARσ.FixedStripContext σ,
      ARσ.FixedStripPosition σ C) → ι := fun Y ↦
    ((fixedBridgeEquiv
      (AR := ARσ) (C := Y.1.center) (k := k) σ τ D ARτ'
        Y.1.p Y.1.p_projective).symm Y.2).x
  have hval := congrArg G hASigma
  apply fixedStripFall_eq_of_context_eq_of_val_eq
    (AR := ARσ) (k := k) σ τ D ARτ'
      (FQ.fallPosition (k := k) σ τ D ARτ') X _ h hC
  have hB : fixedBridgeEquiv
      (AR := ARσ) (C := (FQ.fixedStripContext σ).center)
        (k := k) σ τ D ARτ'
        (FQ.fixedStripContext σ).p
        (FQ.fixedStripContext σ).p_projective =
      fixedBridgeEquiv
        (AR := ARσ) (C := FQ.fixedCenter σ)
          (k := k) σ τ D ARτ'
          (FQ.pairedProjective σ).1 (FQ.pairedProjective σ).2 := by
    rfl
  have hval' :
      ((fixedBridgeEquiv
        (AR := ARσ) (C := (FQ.fixedStripContext σ).center)
          (k := k) σ τ D ARτ'
          (FQ.fixedStripContext σ).p
          (FQ.fixedStripContext σ).p_projective).symm
            (FQ.aNeighbor σ)).x = X.x := by
    simpa only [G, reverseFixedStripA,
      Equiv.symm_apply_apply] using hval
  change ((fixedBridgeEquiv
    (AR := ARσ) (C := FQ.fixedCenter σ)
      (k := k) σ τ D ARτ'
      (FQ.pairedProjective σ).1 (FQ.pairedProjective σ).2).symm
        (FQ.aNeighbor σ)).x = X.x
  rw [← hB]
  exact hval'

/-- Actual source-coordinate reverse fixed packets are exactly the falls in
the common fixed-strip cyclic systems. -/
def sourceReverseFixedPacketFourEquivFixedStripFall :
    SourceReverseFixedPacketFour (k := k) (R := R) σ τ D ≃
      FixedStripFall
        (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
        σ τ D (τ.finiteDimensionalARTranslationData k S) where
  toFun := sourceReverseFixedPacketFourToFixedStripFall
    (k := k) (R := R) (S := S) σ τ D
  invFun := fixedStripFallToSourceReverseFixedPacketFour
    (k := k) (R := R) (S := S) σ τ D
  left_inv := fixedStripFallToSourceReverseFixedPacketFour_leftInverse
    (k := k) (R := R) (S := S) σ τ D
  right_inv := fixedStripFallToSourceReverseFixedPacketFour_rightInverse
    (k := k) (R := R) (S := S) σ τ D

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
