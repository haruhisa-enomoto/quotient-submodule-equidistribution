import OpConjecture.RepresentationTheory.FourVertexFactorLadderPackets

/-!
# Reverse four-vertex packets by aligned duality

The reverse factor ladder on a skeleton is the forward factor ladder on an
aligned dual skeleton.  This file transports deleted finsets, rootedness,
the bad-ladder event, and finally the completed quotient packet
decomposition across that identification.  The packet labels remain those
of the dual skeleton; the killed supports are pulled back to the original
submodule-side coordinates.
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

/-- Send a deleted finset to the aligned dual label set. -/
def AlignedBiduality.dualDeleted
    (D : AlignedBiduality σ τ) (Deleted : Finset ι) : Finset κ :=
  D.forward.labelEquiv.finsetCongr Deleted

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

omit [Field k] [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Algebra k S] [FiniteDimensional k S] [Fintype ι] [Fintype κ]
  [DecidableEq ι] in
@[simp]
theorem dualDeleted_card (Deleted : Finset ι) :
    (D.dualDeleted σ τ Deleted).card = Deleted.card := by
  simp [dualDeleted, Equiv.finsetCongr_apply]

omit [Field k] [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Algebra k S] [FiniteDimensional k S] [Fintype ι] [Fintype κ]
  [DecidableEq ι] in
@[simp]
theorem mem_dualDeleted {Deleted : Finset ι} {x : κ} :
    x ∈ D.dualDeleted σ τ Deleted ↔
      D.forward.labelEquiv.symm x ∈ Deleted := by
  simp [dualDeleted, Equiv.finsetCongr_apply]

omit [Field k] [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Algebra k S] [FiniteDimensional k S] [Fintype ι] [Fintype κ]
  [DecidableEq ι] in
theorem image_compl_eq_dualDeleted_compl (Deleted : Finset ι) :
    D.forward.labelEquiv '' (((Deleted : Finset ι) : Set ι)ᶜ) =
      (((D.dualDeleted σ τ Deleted : Finset κ) : Set κ)ᶜ) := by
  ext x
  simp [dualDeleted, Equiv.finsetCongr_apply]

omit [Field k] [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Algebra k S] [FiniteDimensional k S] [DecidableEq ι] in
/-- Injective corootedness of a source support is projective rootedness of
its image in the dual translation quiver. -/
theorem isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
    (Deleted : Finset ι) :
    OpConjecture.RootedDigraph.IsProjectivelyRooted
        τ.irreducibleEdge τ.projectiveLabelFinset
          (D.dualDeleted σ τ Deleted) ↔
      OpConjecture.RootedDigraph.IsInjectivelyCorooted
        σ.irreducibleEdge σ.injectiveLabelFinset Deleted := by
  let e := D.forward.labelEquiv
  have hedge : ∀ {a b : ι},
      τ.irreducibleEdge (e a) (e b) ↔ σ.irreducibleEdge b a := by
    intro a b
    simpa [irreducibleEdge] using
      (D.hasIrreducibleMorphism_image_iff σ τ (x := b) (y := a))
  constructor
  · intro hroot x hx
    let y := e x
    have hy : y ∈ D.dualDeleted σ τ Deleted := by
      simpa [y, e] using hx
    obtain ⟨q, hqP, hqD, hqx⟩ := hroot y hy
    let p := e.symm q
    refine ⟨p, ?_, ?_, ?_⟩
    · have hqP' : Projective (τ.obj q) := by simpa using hqP
      rw [mem_injectiveLabelFinset]
      apply (D.forward.injective_iff_projective_image σ τ p).2
      simpa [p, e] using hqP'
    · simpa [p, e] using hqD
    · have hpath : Relation.ReflTransGen
          (OpConjecture.RootedDigraph.InsideEdge
            (fun a b ↦ σ.irreducibleEdge b a) Deleted)
          (e.symm q) (e.symm y) := by
        apply hqx.lift e.symm
        intro a b hab
        refine ⟨?_, ?_, ?_⟩
        · simpa [e] using hab.1
        · simpa [e] using hab.2.1
        · have h := (hedge
            (a := e.symm a) (b := e.symm b)).1 (by
              simpa [e] using hab.2.2)
          simpa [e] using h
      simpa only [OpConjecture.RootedDigraph.ReachInside, p, y, e,
        Equiv.symm_apply_apply] using hpath
  · intro hcoroot y hy
    let x := e.symm y
    have hx : x ∈ Deleted := by
      simpa [x, e] using hy
    obtain ⟨p, hpI, hpD, hpx⟩ := hcoroot x hx
    refine ⟨e p, ?_, ?_, ?_⟩
    · simpa [e] using
        (D.forward.injective_iff_projective_image σ τ p).1 (by
          simpa using hpI)
    · simpa [e] using hpD
    · have hpath : Relation.ReflTransGen
          (OpConjecture.RootedDigraph.InsideEdge τ.irreducibleEdge
            (D.dualDeleted σ τ Deleted))
          (e p) (e x) := by
        apply hpx.lift e
        intro a b hab
        refine ⟨?_, ?_, ?_⟩
        · simpa [e] using hab.1
        · simpa [e] using hab.2.1
        · exact (hedge (a := a) (b := b)).2 hab.2.2
      simpa only [OpConjecture.RootedDigraph.ReachInside, x, e,
        Equiv.apply_symm_apply] using hpath

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Fintype ι] [DecidableEq ι] in
/-- The reverse bad-ladder event is exactly the forward bad-ladder event
on the aligned dual deleted finset. -/
theorem quotientFactorLadderBad_dualDeleted_iff_submoduleFactorLadderBad
    (Deleted : Finset ι) :
    QuotientFactorLadderBad (k := k) (R := S) τ
        (D.dualDeleted σ τ Deleted) ↔
      SubmoduleFactorLadderBad (k := k) (S := S) σ τ D Deleted := by
  let K : Set ι := (((Deleted : Finset ι) : Set ι)ᶜ)
  let eDeleted := D.forward.deletedLabelEquiv σ τ K
  let A := D.finiteDimensionalReverseFactorLadderData
    (k := k) (S := S) σ τ K
  let B := τ.finiteDimensionalFactorLadderData k S
    (D.forward.labelEquiv '' K)
  have hK : D.forward.labelEquiv '' K =
      (((D.dualDeleted σ τ Deleted : Finset κ) : Set κ)ᶜ) := by
    exact D.image_compl_eq_dualDeleted_compl σ τ Deleted
  have hboundary :
      eDeleted '' deletedInjectiveSet σ K =
        deletedProjectiveSet τ (D.forward.labelEquiv '' K) :=
    D.forward.image_deletedInjectiveSet_eq_deletedProjectiveSet σ τ K
  have hrel : OpConjecture.FactorLadder.Data.Relabeling A B eDeleted :=
    D.finiteDimensionalReverseFactorLadderData_relabeling
      (k := k) (S := S) σ τ K
  rw [QuotientFactorLadderBad, SubmoduleFactorLadderBad]
  change
    (∃ y : DeletedLabel (((D.dualDeleted σ τ Deleted : Finset κ) : Set κ)ᶜ),
      ¬ (τ.finiteDimensionalFactorLadderData k S
        (((D.dualDeleted σ τ Deleted : Finset κ) : Set κ)ᶜ)).ReachesBoundary
          (deletedProjectiveSet τ
            (((D.dualDeleted σ τ Deleted : Finset κ) : Set κ)ᶜ)) y) ↔
      ∃ x : DeletedLabel K,
        ¬ A.ReachesBoundary (deletedInjectiveSet σ K) x
  rw [← hK]
  constructor
  · rintro ⟨y, hy⟩
    let x := eDeleted.symm y
    refine ⟨x, ?_⟩
    intro hx
    apply hy
    rw [← hboundary]
    have hreach := (hrel.reachesBoundary_image_iff
      (deletedInjectiveSet σ K) x).2 hx
    simpa [x] using hreach
  · rintro ⟨x, hx⟩
    refine ⟨eDeleted x, ?_⟩
    intro hy
    apply hx
    apply (hrel.reachesBoundary_image_iff
      (deletedInjectiveSet σ K) x).1
    rwa [hboundary]

end AlignedBiduality

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
/-- Membership in the reverse bad rooted family is membership in the dual
quotient bad rooted family after relabelling. -/
theorem mem_quotientBadRootedFourFamily_dualDeleted_iff
    (D : AlignedBiduality σ τ) (Deleted : Finset ι) :
    D.dualDeleted σ τ Deleted ∈
        quotientBadRootedFourFamily (k := k) (R := S) τ ↔
      Deleted ∈ submoduleBadRootedFourFamily
        (k := k) (S := S) σ τ D := by
  rw [quotientBadRootedFourFamily, submoduleBadRootedFourFamily,
    OpConjecture.SetClosure.mem_badRootedDeletions,
    OpConjecture.SetClosure.mem_badRootedDeletions]
  constructor
  · rintro ⟨hcard, hroot, hbad⟩
    exact ⟨by simpa using hcard,
      (D.isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
        σ τ Deleted).1 hroot,
      (D.quotientFactorLadderBad_dualDeleted_iff_submoduleFactorLadderBad
        (k := k) (R := R) (S := S) σ τ Deleted).1 hbad⟩
  · rintro ⟨hcard, hroot, hbad⟩
    exact ⟨by simpa using hcard,
      (D.isProjectivelyRooted_dualDeleted_iff_isInjectivelyCorooted
        σ τ Deleted).2 hroot,
      (D.quotientFactorLadderBad_dualDeleted_iff_submoduleFactorLadderBad
        (k := k) (R := R) (S := S) σ τ Deleted).2 hbad⟩

/-- Dual quotient bad supports and original reverse/submodule bad supports
are canonically equivalent. -/
def quotientBadRootedFourEquivSubmodule
    (D : AlignedBiduality σ τ) :
    QuotientBadRootedFour (k := k) (R := S) τ ≃
      SubmoduleBadRootedFour (k := k) (S := S) σ τ D where
  toFun Q := by
    let Deleted := D.forward.labelEquiv.finsetCongr.symm Q.1
    refine ⟨Deleted, ?_⟩
    apply (mem_quotientBadRootedFourFamily_dualDeleted_iff
      (k := k) (R := R) (S := S) σ τ D Deleted).1
    have hDeleted : D.dualDeleted σ τ Deleted = Q.1 := by
      change D.forward.labelEquiv.finsetCongr
        (D.forward.labelEquiv.finsetCongr.symm Q.1) = Q.1
      exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1
    rw [hDeleted]
    exact Q.2
  invFun Q := ⟨D.dualDeleted σ τ Q.1,
    (mem_quotientBadRootedFourFamily_dualDeleted_iff
      (k := k) (R := R) (S := S) σ τ D Q.1).2 Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    change D.forward.labelEquiv.finsetCongr
      (D.forward.labelEquiv.finsetCongr.symm Q.1) = Q.1
    exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1
  right_inv Q := by
    apply Subtype.ext
    change D.forward.labelEquiv.finsetCongr.symm
      (D.forward.labelEquiv.finsetCongr Q.1) = Q.1
    exact D.forward.labelEquiv.finsetCongr.symm_apply_apply Q.1

/-- The reverse-side hook occurrence type, represented on the aligned dual
skeleton. -/
abbrev SubmoduleHookOccurrenceFour :=
  QuotientHookOccurrenceFour (k := k) (R := S) τ

/-- The reverse-side double-hook support type. -/
abbrev SubmoduleDoubleHookFour :=
  QuotientDoubleHookFour (k := k) (R := S) τ

/-- The reverse-side row-`F` packet type. -/
abbrev SubmoduleFixedPacketFour :=
  QuotientFixedPacketFour (k := k) (R := S) τ

/-- The reverse-side row-`T` packet type. -/
abbrev SubmoduleTrianglePacketFour :=
  QuotientTrianglePacketFour (k := k) (R := S) τ

/-- Exact reverse/submodule packet decomposition with supports in the
original label coordinates and packets in the aligned dual coordinates. -/
abbrev SubmoduleFourPacketDecomposition (D : AlignedBiduality σ τ) :=
  OpConjecture.FourVertexLadderPackets.Decomposition
    (SubmoduleBadRootedFour (k := k) (S := S) σ τ D)
    (SubmoduleHookOccurrenceFour (k := k) (S := S) τ)
    (SubmoduleDoubleHookFour (k := k) (S := S) τ)
    (SubmoduleFixedPacketFour (k := k) (S := S) τ)
    (SubmoduleTrianglePacketFour (k := k) (S := S) τ)

/-- The completed quotient decomposition on the aligned dual skeleton
transports to the actual reverse/submodule bad family. -/
noncomputable def submoduleFourPacketDecomposition
    (D : AlignedBiduality σ τ) :
    SubmoduleFourPacketDecomposition
      (k := k) (R := R) (S := S) σ τ D := by
  classical
  let Q := quotientFourPacketDecomposition (k := k) (R := S) τ
  exact ⟨Q.classify.trans
    (Equiv.sumCongr
      (quotientBadRootedFourEquivSubmodule
        (k := k) (R := R) (S := S) σ τ D)
      (Equiv.refl _))⟩

/-- The two concrete reversal statements remaining after both actual packet
decompositions have been constructed. -/
abbrev ActualFourVertexReversalBalance :=
  OpConjecture.FourVertexLadderPackets.ReversalBalance
    (QuotientHookOccurrenceFour (k := k) (R := R) σ)
    (QuotientDoubleHookFour (k := k) (R := R) σ)
    (QuotientFixedPacketFour (k := k) (R := R) σ)
    (QuotientTrianglePacketFour (k := k) (R := R) σ)
    (SubmoduleHookOccurrenceFour (k := k) (S := S) τ)
    (SubmoduleDoubleHookFour (k := k) (S := S) τ)
    (SubmoduleFixedPacketFour (k := k) (S := S) τ)
    (SubmoduleTrianglePacketFour (k := k) (S := S) τ)

/-- The concrete reversal balance is now the sole input to equality of the
actual bad rooted four-support families. -/
theorem badRootedFour_card_eq_of_actualReversalBalance
    (D : AlignedBiduality σ τ)
    (B : ActualFourVertexReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    (quotientBadRootedFourFamily (k := k) (R := R) σ).card =
      (submoduleBadRootedFourFamily
        (k := k) (S := S) σ τ D).card := by
  classical
  exact badRootedFour_card_eq_of_packetDecompositions
    (k := k) (R := R) (S := S) σ τ D
      (quotientFourPacketDecomposition (k := k) (R := R) σ)
      (submoduleFourPacketDecomposition
        (k := k) (R := R) (S := S) σ τ D) B

/-- Paper-facing colevel-four equality reduced exactly to the concrete
strip and fixed-strip reversal counts. -/
theorem levelCount_card_sub_four_eq_of_actualReversalBalance
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    (B : ActualFourVertexReversalBalance
      (k := k) (R := R) (S := S) σ τ) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  classical
  exact levelCount_card_sub_four_eq_of_packetDecompositions
    (k := k) (R := R) (S := S) σ τ D hfour
      (quotientFourPacketDecomposition (k := k) (R := R) σ)
      (submoduleFourPacketDecomposition
        (k := k) (R := R) (S := S) σ τ D) B

end OpConjecture.IndecomposableSkeleton
