import OpConjecture.RepresentationTheory.FourVertexFixedStripPositions

/-!
# Reconstructing fixed packets from cyclic transitions

This file proves the inverse local construction for the quotient side of
the fixed strip.  A rise of the projective wall bit determines the four
labels `p,a,c,z`, their exact predecessor relations, the row-`F`
translation identities, rootedness, and hooklessness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

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

/-- The neighbor immediately before a fixed-strip position. -/
def fixedStripPrevious (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : AR.FixedStripPosition σ C :=
  (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C).symm X

/-- The four source labels determined by a fixed-strip position. -/
def fixedStripDeleted (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : Finset ι :=
  {C.p, X.x, C.center.c,
    (fixedStripPrevious (AR := AR) (k := k) σ τ D ARτ C X).x}

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
/-- A rise supplies its present boundary arrow and excludes the preceding
one. -/
theorem arrows_of_fixedStripRise
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : OpConjecture.FixedStripCyclicBalance.IsRise
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    (¬ HasIrreducibleMorphism (σ.obj C.p)
        (σ.obj (fixedStripPrevious
          (AR := AR) (k := k) σ τ D ARτ C X).x)) ∧
      HasIrreducibleMorphism (σ.obj C.p) (σ.obj X.x) := by
  exact ⟨(fixedStripBit_eq_false_iff (AR := AR) σ _ _).1 h.1,
    (fixedStripBit_eq_true_iff (AR := AR) σ _ _).1 h.2⟩

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- The four labels selected by a rise are pairwise distinct. -/
theorem fixedStripDeleted_card_of_isRise
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : OpConjecture.FixedStripCyclicBalance.IsRise
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    (fixedStripDeleted (AR := AR) (k := k) σ τ D ARτ C X).card = 4 := by
  let E := fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
  let Z := fixedStripPrevious (AR := AR) (k := k) σ τ D ARτ C X
  have hwalls := arrows_of_fixedStripRise
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hpX : C.p ≠ X.x := by
    intro heq
    exact X.x_nonprojective (heq ▸ C.p_projective)
  have hpC : C.p ≠ C.center.c := by
    intro heq
    exact C.center.c_nonprojective (heq ▸ C.p_projective)
  have hpZ : C.p ≠ Z.x := by
    intro heq
    exact Z.x_nonprojective (heq ▸ C.p_projective)
  have hXC : X.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using X.c_to_x)
  have hZC : Z.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using Z.c_to_x)
  have hXZ : X.x ≠ Z.x := by
    intro heq
    apply hwalls.1
    simpa only [heq] using hwalls.2
  simp [fixedStripDeleted, Z, hpX, hpC, hpZ, hXC, hZC.symm, hXZ]

omit [IsAlgClosed k] [DecidableEq ι] in
/-- A rise reconstructs the literal quotient row-`F` packet on its four
selected labels. -/
def fixedPacketOfFixedStripRise
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : OpConjecture.FixedStripCyclicBalance.IsRise
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    AR.FixedPacket σ
      (((fixedStripDeleted (AR := AR) (k := k) σ τ D ARτ C X :
        Finset ι) : Set ι)ᶜ) := by
  let E := fixedStripStep (AR := AR) (k := k) σ τ D ARτ C
  let Z := fixedStripPrevious (AR := AR) (k := k) σ τ D ARτ C X
  let Deleted := fixedStripDeleted
    (AR := AR) (k := k) σ τ D ARτ C X
  let K : Set ι := ((Deleted : Finset ι) : Set ι)ᶜ
  let p : DeletedLabel K := ⟨C.p, by simp [K, Deleted, fixedStripDeleted]⟩
  let a : DeletedLabel K := ⟨X.x, by simp [K, Deleted, fixedStripDeleted]⟩
  let c : DeletedLabel K :=
    ⟨C.center.c, by simp [K, Deleted, fixedStripDeleted]⟩
  let z : DeletedLabel K :=
    ⟨Z.x, by simp [K, Deleted, fixedStripDeleted, Z]⟩
  have hwalls := arrows_of_fixedStripRise
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hEZ : E Z = X := E.apply_symm_apply X
  have hτZ : (AR.arTranslation σ ⟨Z.x, Z.x_nonprojective⟩).1 = X.x :=
    (FixedNeighbor.forwardEquiv_apply
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ Z).symm.trans
        (congrArg FixedNeighbor.x hEZ)
  have hXnotZ : X.x ≠ Z.x := by
    intro heq
    apply hwalls.1
    simpa only [heq] using hwalls.2
  have hXnotC : X.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using X.c_to_x)
  have hZnotC : Z.x ≠ C.center.c := by
    intro heq
    exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
      simpa only [heq] using Z.c_to_x)
  have hXnotToZ :
      ¬ HasIrreducibleMorphism (σ.obj X.x) (σ.obj Z.x) := by
    intro hXZ
    apply AR.no_irreducible_arTranslation_to_endpoint
      σ ⟨Z.x, Z.x_nonprojective⟩
    simpa only [hτZ] using hXZ
  refine
    { p := p
      a := a
      c := c
      z := z
      p_projective := C.p_projective
      a_nonprojective := X.x_nonprojective
      c_nonprojective := C.center.c_nonprojective
      z_nonprojective := Z.x_nonprojective
      p_to_a := hwalls.2
      c_to_a := X.c_to_x
      predecessor_z := ?_
      predecessor_c := ?_
      tau_z := hτZ
      tau_c := C.center.tau_c
      tau_a_eq_z_or_mem := ?_
      p_not_to_z := hwalls.1 }
  · refine ⟨Z.c_to_x, ?_⟩
    intro q hqZ
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, fixedStripDeleted, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqp | hqX | hqC | hqZeq
    · exact (hwalls.1 (by simpa only [hqp] using hqZ)).elim
    · exact (hXnotToZ (by simpa only [hqX] using hqZ)).elim
    · exact Subtype.ext hqC
    · exact (σ.hasNoIrreducibleEndomorphism_obj Z.x (by
        simpa only [hqZeq] using hqZ)).elim
  · refine ⟨?_, X.x_to_c, Z.x_to_c, ?_⟩
    · intro hEq
      exact hXnotZ (congrArg Subtype.val hEq)
    · intro q hqC
      have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
      simp only [Deleted, fixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton] at hqmem
      rcases hqmem with hqp | hqX | hqCenter | hqZeq
      · exact (C.p_not_to_center (by simpa only [hqp] using hqC)).elim
      · exact Or.inl (Subtype.ext hqX)
      · exact (σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
          simpa only [hqCenter] using hqC)).elim
      · exact Or.inr (Subtype.ext hqZeq)
  · have hτX := FixedNeighbor.forwardEquiv_apply
      (AR := AR) (C := C.center) (k := k) σ τ D ARτ X
    let Y := E X
    by_cases hYZ : Y.x = Z.x
    · exact Or.inl (hτX.symm.trans hYZ)
    · apply Or.inr
      change (AR.arTranslation σ ⟨X.x, X.x_nonprojective⟩).1 ∈ K
      rw [← hτX]
      change Y.x ∉ Deleted
      simp only [Deleted, fixedStripDeleted, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_, hYZ⟩
      · intro hYp
        exact Y.x_nonprojective (hYp ▸ C.p_projective)
      · intro hYX
        have hYXfull : Y = X := FixedNeighbor.ext hYX
        have hZX : Z = X := E.injective (hEZ.trans hYXfull.symm)
        exact hXnotZ (congrArg FixedNeighbor.x hZX.symm)
      · intro hYC
        exact σ.hasNoIrreducibleEndomorphism_obj C.center.c (by
          simpa only [hYC] using Y.c_to_x)

omit [IsAlgClosed k] AR in
/-- A four-element support carrying row `F` cannot also carry an admissible
hook. -/
theorem FixedPacket.no_admissibleHook
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    IsEmpty ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) := by
  constructor
  intro H
  rcases eq_fixedPacket_label (k := k) (R := R) σ Deleted hcard F H.b with
    hbP | hbA | hbC | hbZ
  · exact H.b_nonprojective (hbP ▸ F.p_projective)
  · have hcu : F.c = H.u :=
      H.predecessor_b.2 F.c (by simpa only [hbA] using F.c_to_a)
    have hpu : F.p = H.u :=
      H.predecessor_b.2 F.p (by simpa only [hbA] using F.p_to_a)
    exact F.c_nonprojective (hcu.trans hpu.symm ▸ F.p_projective)
  · have hau : F.a = H.u :=
      H.predecessor_b.2 F.a (by simpa only [hbC] using F.predecessor_c.2.1)
    have hzu : F.z = H.u :=
      H.predecessor_b.2 F.z (by simpa only [hbC] using F.predecessor_c.2.2.1)
    exact F.predecessor_c.1 (hau.trans hzu.symm)
  · have hcu : F.c = H.u :=
      H.predecessor_b.2 F.c (by simpa only [hbZ] using F.predecessor_z.1)
    have haA : F.a = H.a :=
      H.predecessor_u.2 F.a (by
        simpa only [← hcu] using F.predecessor_c.2.1)
    have hzA : F.z = H.a :=
      H.predecessor_u.2 F.z (by
        simpa only [← hcu] using F.predecessor_c.2.2.1)
    exact F.predecessor_c.1 (haA.trans hzA.symm)

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R] in
/-- The four labels reconstructed from a rise form a projectively rooted
support. -/
theorem fixedStripDeleted_isProjectivelyRooted_of_isRise
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C)
    (h : OpConjecture.FixedStripCyclicBalance.IsRise
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
      (fixedStripBit (AR := AR) σ C) X) :
    OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset
      (fixedStripDeleted (AR := AR) (k := k) σ τ D ARτ C X) := by
  let Z := fixedStripPrevious (AR := AR) (k := k) σ τ D ARτ C X
  let Deleted := fixedStripDeleted
    (AR := AR) (k := k) σ τ D ARτ C X
  have hwalls := arrows_of_fixedStripRise
    (AR := AR) (k := k) σ τ D ARτ C X h
  have hp : C.p ∈ Deleted := by simp [Deleted, fixedStripDeleted]
  have ha : X.x ∈ Deleted := by simp [Deleted, fixedStripDeleted]
  have hc : C.center.c ∈ Deleted := by simp [Deleted, fixedStripDeleted]
  have hz : Z.x ∈ Deleted := by simp [Deleted, fixedStripDeleted, Z]
  have hpBoundary : C.p ∈ σ.projectiveLabelFinset := by
    simpa [projectiveLabelFinset] using C.p_projective
  have hpa : OpConjecture.RootedDigraph.ReachInside
      σ.irreducibleEdge Deleted C.p X.x :=
    Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      ⟨hp, ha, hwalls.2⟩
  have hpac : OpConjecture.RootedDigraph.ReachInside
      σ.irreducibleEdge Deleted C.p C.center.c :=
    hpa.tail ⟨ha, hc, X.x_to_c⟩
  have hpacz : OpConjecture.RootedDigraph.ReachInside
      σ.irreducibleEdge Deleted C.p Z.x :=
    hpac.tail ⟨hc, hz, Z.c_to_x⟩
  intro y hy
  refine ⟨C.p, hpBoundary, hp, ?_⟩
  simp only [fixedStripDeleted, Finset.mem_insert,
    Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact hpa
  · exact hpac
  · exact hpacz

omit [IsAlgClosed k] AR in
/-- Recovering the cyclic data from an existing quotient row-`F` packet
recovers exactly its original four-element support. -/
theorem fixedStripDeleted_fixedPacket_eq
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    fixedStripDeleted
      (AR := σ.finiteDimensionalARTranslationData k R) (k := k) σ τ D ARτ
      (F.fixedStripContext (k := k) σ τ D ARτ)
      (F.aNeighbor (k := k) σ τ D ARτ) = Deleted := by
  classical
  ext x
  constructor
  · intro hx
    simp only [fixedStripDeleted, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with hxp | hxa | hxc | hxz
    · change x = F.p.1 at hxp
      subst x
      simpa using F.p.2
    · change x = F.a.1 at hxa
      subst x
      simpa using F.a.2
    · change x = F.c.1 at hxc
      subst x
      simpa using F.c.2
    · have hprev := F.forwardEquiv_symm_aNeighbor
        (k := k) σ τ D ARτ
      change x = ((FixedNeighbor.forwardEquiv
        (AR := σ.finiteDimensionalARTranslationData k R)
        (C := F.fixedCenter (k := k) σ τ D ARτ)
        (k := k) σ τ D ARτ).symm
          (F.aNeighbor (k := k) σ τ D ARτ)).x at hxz
      rw [hprev] at hxz
      change x = F.z.1 at hxz
      subst x
      simpa using F.z.2
  · intro hx
    change x ∈
      {F.p.1, F.a.1, F.c.1,
        ((FixedNeighbor.forwardEquiv
          (AR := σ.finiteDimensionalARTranslationData k R)
          (C := F.fixedCenter (k := k) σ τ D ARτ)
          (k := k) σ τ D ARτ).symm
            (F.aNeighbor (k := k) σ τ D ARτ)).x}
    let q : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ) :=
      ⟨x, by simpa using hx⟩
    rcases eq_fixedPacket_label (k := k) (R := R) σ Deleted hcard F q with
      hqp | hqa | hqc | hqz
    · have hx' := congrArg Subtype.val hqp
      change x = F.p.1 at hx'
      simp [hx']
    · have hx' := congrArg Subtype.val hqa
      change x = F.a.1 at hx'
      simp [hx']
    · have hx' := congrArg Subtype.val hqc
      change x = F.c.1 at hx'
      simp [hx']
    · have hx' := congrArg Subtype.val hqz
      change x = F.z.1 at hx'
      have hprev := F.forwardEquiv_symm_aNeighbor
        (k := k) σ τ D ARτ
      rw [hprev]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr (hx'.trans rfl)))

/-- Reconstruct an actual hookless quotient row-`F` support from an
arbitrary rise in the common fixed-strip system. -/
def fixedStripRiseToQuotientFixedPacketFour
    (Y : FixedStripRise
      (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
      σ τ D (τ.finiteDimensionalARTranslationData k S)) :
    QuotientFixedPacketFour (k := k) (R := R) σ := by
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ' := τ.finiteDimensionalARTranslationData k S
  let Deleted := fixedStripDeleted
    (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1
  let F := fixedPacketOfFixedStripRise
    (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  have hcard : Deleted.card = 4 :=
    fixedStripDeleted_card_of_isRise
      (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  have hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted :=
    fixedStripDeleted_isProjectivelyRooted_of_isRise
      (AR := ARσ) (k := k) σ τ D ARτ' Y.1 Y.2.1 Y.2.2
  have hEmpty : IsEmpty (ARσ.AdmissibleHook σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :=
    F.no_admissibleHook (k := k) (R := R) σ Deleted hcard
  exact ⟨⟨Deleted, hcard, hroot⟩, ⟨⟨F⟩, hEmpty⟩⟩

omit [IsAlgClosed k] in
/-- Reconstructing the support after extracting the rise from an actual
quotient fixed packet returns the original support. -/
theorem fixedStripRiseToQuotientFixedPacketFour_leftInverse :
    Function.LeftInverse
      (fixedStripRiseToQuotientFixedPacketFour
        (k := k) (R := R) (S := S) σ τ D)
      (quotientFixedPacketFourToFixedStripRise
        (k := k) (R := R) (S := S) σ τ D) := by
  intro Q
  apply Subtype.ext
  apply Subtype.ext
  change fixedStripDeleted
    (AR := σ.finiteDimensionalARTranslationData k R) (k := k) σ τ D
      (τ.finiteDimensionalARTranslationData k S)
      ((Classical.choice Q.2.1).fixedStripContext
        (k := k) σ τ D (τ.finiteDimensionalARTranslationData k S))
      ((Classical.choice Q.2.1).aNeighbor
        (k := k) σ τ D (τ.finiteDimensionalARTranslationData k S)) =
      Q.1.1
  exact fixedStripDeleted_fixedPacket_eq
    (k := k) (R := R) σ τ D
      (τ.finiteDimensionalARTranslationData k S)
      Q.1.1 Q.1.2.1 (Classical.choice Q.2.1)

omit [IsAlgClosed k] in
/-- Extracting the rise from the packet reconstructed from that rise
returns the original cyclic position. -/
theorem fixedStripRiseToQuotientFixedPacketFour_rightInverse :
    Function.RightInverse
      (fixedStripRiseToQuotientFixedPacketFour
        (k := k) (R := R) (S := S) σ τ D)
      (quotientFixedPacketFourToFixedStripRise
        (k := k) (R := R) (S := S) σ τ D) := by
  rintro ⟨C, ⟨X, h⟩⟩
  let ARσ := σ.finiteDimensionalARTranslationData k R
  let ARτ' := τ.finiteDimensionalARTranslationData k S
  let Deleted := fixedStripDeleted
    (AR := ARσ) (k := k) σ τ D ARτ' C X
  let F₀ := fixedPacketOfFixedStripRise
    (AR := ARσ) (k := k) σ τ D ARτ' C X h
  let Q := fixedStripRiseToQuotientFixedPacketFour
    (k := k) (R := R) (S := S) σ τ D ⟨C, ⟨X, h⟩⟩
  have hF : Classical.choice Q.2.1 = F₀ := by
    apply fixedPacket_unique (k := k) (R := R) σ Deleted
      (fixedStripDeleted_card_of_isRise
        (AR := ARσ) (k := k) σ τ D ARτ' C X h)
  change (⟨(Classical.choice Q.2.1).fixedStripContext
        (k := k) σ τ D ARτ',
      ⟨(Classical.choice Q.2.1).aNeighbor
          (k := k) σ τ D ARτ',
        (Classical.choice Q.2.1).isRise_aNeighbor
          (k := k) σ τ D ARτ'⟩⟩ :
      FixedStripRise (AR := ARσ) (k := k) σ τ D ARτ') =
    ⟨C, ⟨X, h⟩⟩
  rw [hF]
  have hC : F₀.fixedStripContext (k := k) σ τ D ARτ' = C := by
    apply FixedStripContext.ext
    · rfl
    · apply FixedCenter.ext
      rfl
  apply Sigma.ext hC
  cases hC
  apply heq_of_eq
  apply Subtype.ext
  apply FixedNeighbor.ext
  rfl

/-- Actual quotient fixed packets are exactly the rises in the common
fixed-strip cyclic systems. -/
def quotientFixedPacketFourEquivFixedStripRise :
    QuotientFixedPacketFour (k := k) (R := R) σ ≃
      FixedStripRise
        (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
        σ τ D (τ.finiteDimensionalARTranslationData k S) where
  toFun := quotientFixedPacketFourToFixedStripRise
    (k := k) (R := R) (S := S) σ τ D
  invFun := fixedStripRiseToQuotientFixedPacketFour
    (k := k) (R := R) (S := S) σ τ D
  left_inv := fixedStripRiseToQuotientFixedPacketFour_leftInverse
    (k := k) (R := R) (S := S) σ τ D
  right_inv := fixedStripRiseToQuotientFixedPacketFour_rightInverse
    (k := k) (R := R) (S := S) σ τ D

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
