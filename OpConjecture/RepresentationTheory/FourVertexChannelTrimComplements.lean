import OpConjecture.RepresentationTheory.FourVertexBoundaryEndpointTransport

/-!
# Endpoint complements of the trimmed four channels

The global arrow-boundary argument uses only channel terms whose two assigned
arrow occurrences survive trimming.  This file records the complementary
finite types and the exact four exhaustive cardinal decompositions.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (AR : sigma.FiniteARTranslationData)

/-- Preliminary `M5` terms for which at least one assigned occurrence is
deleted by the outer-boundary trimming. -/
abbrev HookM5Preliminary.NonInteriorChannel :=
  {M : AR.HookM5Preliminary sigma //
    ¬ (IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.hookArrow sigma AR))}

/-- `M6` terms for which at least one assigned occurrence is deleted by
the outer-boundary trimming. -/
abbrev HookM6Channel.NonInteriorChannel :=
  {M : AR.HookM6Channel sigma //
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.1.triple.hookOrbitAnchor sigma AR))}

/-- `M2` wall terms for which at least one assigned occurrence is deleted
by the outer-boundary trimming. -/
abbrev HookWallBadU.NonInteriorChannel :=
  {M : AR.HookWallBadU sigma //
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.1.triple.firstArrow sigma AR))}

/-- `M3` wall terms for which at least one assigned occurrence is deleted
by the outer-boundary trimming. -/
abbrev HookWallBadBUnrestricted.NonInteriorChannel :=
  {M : AR.HookWallBadBUnrestricted sigma //
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.1.triple.secondArrow sigma AR))}

/-- The disjoint sum of the two noninterior wall-channel complements. -/
abbrev HookWallNonInteriorSum :=
  HookWallBadU.NonInteriorChannel sigma AR ⊕
    HookWallBadBUnrestricted.NonInteriorChannel sigma AR

/-- Endpoint form of a discarded preliminary `M5` term. -/
abbrev HookM5Preliminary.InjectiveMiddleEndpoint :=
  {M : AR.HookM5Preliminary sigma //
    ¬ HasIrreducibleMorphism (sigma.obj M.triple.u) (sigma.obj M.z) ∧
      Injective (sigma.obj M.triple.u)}

/-- Endpoint form of a discarded `M6` term. -/
abbrev HookM6Channel.InjectiveFourthEndpoint :=
  {M : AR.HookM6Channel sigma // Injective (sigma.obj M.1.z)}

/-- Endpoint form of a discarded `M2` term. -/
abbrev HookWallBadU.InjectiveFourthEndpoint :=
  {M : AR.HookWallBadU sigma // Injective (sigma.obj M.1.z)}

/-- Endpoint form of a discarded `M3` term. -/
abbrev HookWallBadBUnrestricted.InjectiveEndpoint :=
  {M : AR.HookWallBadBUnrestricted sigma //
    Injective (sigma.obj M.1.z) ∨
      Injective (sigma.obj M.1.triple.u)}

noncomputable instance hookM5PreliminaryNonInteriorChannelFintype :
    Fintype (HookM5Preliminary.NonInteriorChannel sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM6ChannelNonInteriorChannelFintype :
    Fintype (HookM6Channel.NonInteriorChannel sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookWallBadUNonInteriorChannelFintype :
    Fintype (HookWallBadU.NonInteriorChannel sigma AR) :=
  Fintype.ofFinite _

noncomputable instance
    hookWallBadBUnrestrictedNonInteriorChannelFintype :
    Fintype (HookWallBadBUnrestricted.NonInteriorChannel sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM5PreliminaryInjectiveMiddleEndpointFintype :
    Fintype (HookM5Preliminary.InjectiveMiddleEndpoint sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM6ChannelInjectiveFourthEndpointFintype :
    Fintype (HookM6Channel.InjectiveFourthEndpoint sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookWallBadUInjectiveFourthEndpointFintype :
    Fintype (HookWallBadU.InjectiveFourthEndpoint sigma AR) :=
  Fintype.ofFinite _

noncomputable instance
    hookWallBadBUnrestrictedInjectiveEndpointFintype :
    Fintype (HookWallBadBUnrestricted.InjectiveEndpoint sigma AR) :=
  Fintype.ofFinite _

namespace HookM5Preliminary

theorem nonInteriorChannel_iff (M : AR.HookM5Preliminary sigma) :
    ¬ (IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) ∧
        IsInteriorArrow sigma (M.hookArrow sigma AR)) ↔
      ¬ HasIrreducibleMorphism (sigma.obj M.triple.u) (sigma.obj M.z) ∧
        Injective (sigma.obj M.triple.u) := by
  classical
  rw [M.interiorChannel_iff sigma AR]
  simp only [not_or, not_not]

end HookM5Preliminary

namespace HookM6Channel

theorem nonInteriorChannel_iff (M : AR.HookM6Channel sigma) :
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
        IsInteriorArrow sigma (M.1.triple.hookOrbitAnchor sigma AR)) ↔
      Injective (sigma.obj M.1.z) := by
  rw [M.interiorChannel_iff sigma AR]
  simp only [not_not]

end HookM6Channel

namespace HookWallBadU

omit [Fintype iota] [DecidableEq iota] in
theorem nonInteriorChannel_iff (M : AR.HookWallBadU sigma) :
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
        IsInteriorArrow sigma (M.1.triple.firstArrow sigma AR)) ↔
      Injective (sigma.obj M.1.z) := by
  rw [M.interiorChannel_iff sigma AR]
  simp only [not_not]

end HookWallBadU

namespace HookWallBadBUnrestricted

omit [Fintype iota] [DecidableEq iota] in
theorem nonInteriorChannel_iff
    (M : AR.HookWallBadBUnrestricted sigma) :
    ¬ (IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
        IsInteriorArrow sigma (M.1.triple.secondArrow sigma AR)) ↔
      Injective (sigma.obj M.1.z) ∨
        Injective (sigma.obj M.1.triple.u) := by
  classical
  rw [M.interiorChannel_iff sigma AR]
  tauto

end HookWallBadBUnrestricted

/-- The trimming complement of preliminary `M5` is exactly its
injective-middle endpoint family. -/
def hookM5PreliminaryNonInteriorEquivInjectiveMiddleEndpoint :
    HookM5Preliminary.NonInteriorChannel sigma AR ≃
      HookM5Preliminary.InjectiveMiddleEndpoint sigma AR where
  toFun M := ⟨M.1, (HookM5Preliminary.nonInteriorChannel_iff
    sigma AR M.1).1 M.2⟩
  invFun M := ⟨M.1, (HookM5Preliminary.nonInteriorChannel_iff
    sigma AR M.1).2 M.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The trimming complement of `M6` is exactly its
projective-injective fourth-endpoint family. -/
def hookM6NonInteriorEquivInjectiveFourthEndpoint :
    HookM6Channel.NonInteriorChannel sigma AR ≃
      HookM6Channel.InjectiveFourthEndpoint sigma AR where
  toFun M := ⟨M.1,
    (HookM6Channel.nonInteriorChannel_iff sigma AR M.1).1 M.2⟩
  invFun M := ⟨M.1,
    (HookM6Channel.nonInteriorChannel_iff sigma AR M.1).2 M.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The trimming complement of `M2` is exactly its
projective-injective fourth-endpoint family. -/
def hookWallBadUNonInteriorEquivInjectiveFourthEndpoint :
    HookWallBadU.NonInteriorChannel sigma AR ≃
      HookWallBadU.InjectiveFourthEndpoint sigma AR where
  toFun M := ⟨M.1,
    (HookWallBadU.nonInteriorChannel_iff sigma AR M.1).1 M.2⟩
  invFun M := ⟨M.1,
    (HookWallBadU.nonInteriorChannel_iff sigma AR M.1).2 M.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The trimming complement of `M3` is exactly the family in which the
fourth endpoint or the hook middle is injective. -/
def hookWallBadBUnrestrictedNonInteriorEquivInjectiveEndpoint :
    HookWallBadBUnrestricted.NonInteriorChannel sigma AR ≃
      HookWallBadBUnrestricted.InjectiveEndpoint sigma AR where
  toFun M := ⟨M.1,
    (HookWallBadBUnrestricted.nonInteriorChannel_iff sigma AR M.1).1 M.2⟩
  invFun M := ⟨M.1,
    (HookWallBadBUnrestricted.nonInteriorChannel_iff sigma AR M.1).2 M.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def equivSubtypeSumNot
    {alpha : Type*} (P : alpha → Prop) [DecidablePred P] :
    alpha ≃ {x : alpha // P x} ⊕ {x : alpha // ¬ P x} where
  toFun x := if h : P x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, h⟩
  invFun x := by
    rcases x with x | x
    · exact x.1
    · exact x.1
  left_inv x := by
    by_cases h : P x
    · simp [h]
    · simp [h]
  right_inv x := by
    rcases x with x | x
    · simp [x.2]
    · simp [x.2]

/-- Exhaustive split of all preliminary `M5` terms into the trimmed part
and its endpoint complement. -/
def hookM5PreliminaryEquivInteriorSumNonInterior :
    AR.HookM5Preliminary sigma ≃
      HookM5Preliminary.InteriorChannel sigma AR ⊕
        HookM5Preliminary.NonInteriorChannel sigma AR := by
  classical
  exact equivSubtypeSumNot (fun M : AR.HookM5Preliminary sigma ↦
    IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.hookArrow sigma AR))

/-- Exhaustive split of all `M6` terms into the trimmed part and its
endpoint complement. -/
def hookM6ChannelEquivInteriorSumNonInterior :
    AR.HookM6Channel sigma ≃
      HookM6Channel.InteriorChannel sigma AR ⊕
        HookM6Channel.NonInteriorChannel sigma AR := by
  classical
  exact equivSubtypeSumNot (fun M : AR.HookM6Channel sigma ↦
    IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.1.triple.hookOrbitAnchor sigma AR))

/-- Exhaustive split of all `M2` wall terms into the trimmed part and its
endpoint complement. -/
def hookWallBadUEquivInteriorSumNonInterior :
    AR.HookWallBadU sigma ≃
      HookWallBadU.InteriorChannel sigma AR ⊕
        HookWallBadU.NonInteriorChannel sigma AR := by
  classical
  exact equivSubtypeSumNot (fun M : AR.HookWallBadU sigma ↦
    IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.1.triple.firstArrow sigma AR))

/-- Exhaustive split of all unrestricted `M3` wall terms into the trimmed
part and its endpoint complement. -/
def hookWallBadBUnrestrictedEquivInteriorSumNonInterior :
    AR.HookWallBadBUnrestricted sigma ≃
      HookWallBadBUnrestricted.InteriorChannel sigma AR ⊕
        HookWallBadBUnrestricted.NonInteriorChannel sigma AR := by
  classical
  exact equivSubtypeSumNot
    (fun M : AR.HookWallBadBUnrestricted sigma ↦
      IsInteriorArrow sigma (M.associatedArrow sigma AR) ∧
        IsInteriorArrow sigma (M.1.triple.secondArrow sigma AR))

theorem hookM5Preliminary_card_eq_interior_add_nonInterior :
    Fintype.card (AR.HookM5Preliminary sigma) =
      Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) +
        Fintype.card (HookM5Preliminary.NonInteriorChannel sigma AR) := by
  rw [Fintype.card_congr
    (AR.hookM5PreliminaryEquivInteriorSumNonInterior sigma)]
  exact Fintype.card_sum

theorem hookM6Channel_card_eq_interior_add_nonInterior :
    Fintype.card (AR.HookM6Channel sigma) =
      Fintype.card (HookM6Channel.InteriorChannel sigma AR) +
        Fintype.card (HookM6Channel.NonInteriorChannel sigma AR) := by
  rw [Fintype.card_congr
    (AR.hookM6ChannelEquivInteriorSumNonInterior sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
theorem hookWallBadU_card_eq_interior_add_nonInterior :
    Fintype.card (AR.HookWallBadU sigma) =
      Fintype.card (HookWallBadU.InteriorChannel sigma AR) +
        Fintype.card (HookWallBadU.NonInteriorChannel sigma AR) := by
  rw [Fintype.card_congr
    (AR.hookWallBadUEquivInteriorSumNonInterior sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
theorem hookWallBadBUnrestricted_card_eq_interior_add_nonInterior :
    Fintype.card (AR.HookWallBadBUnrestricted sigma) =
      Fintype.card
          (HookWallBadBUnrestricted.InteriorChannel sigma AR) +
        Fintype.card
          (HookWallBadBUnrestricted.NonInteriorChannel sigma AR) := by
  rw [Fintype.card_congr
    (AR.hookWallBadBUnrestrictedEquivInteriorSumNonInterior sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
/-- Cardinal decomposition of the full `M2`/`M3` wall sum into its trimmed
and noninterior parts. -/
theorem hookWallFull_card_eq_interior_add_nonInterior :
    Fintype.card (AR.HookWallBadU sigma) +
        Fintype.card (AR.HookWallBadBUnrestricted sigma) =
      (Fintype.card (HookWallBadU.InteriorChannel sigma AR) +
          Fintype.card
            (HookWallBadBUnrestricted.InteriorChannel sigma AR)) +
        (Fintype.card (HookWallBadU.NonInteriorChannel sigma AR) +
          Fintype.card
            (HookWallBadBUnrestricted.NonInteriorChannel sigma AR)) := by
  have hU := AR.hookWallBadU_card_eq_interior_add_nonInterior sigma
  have hB :=
    AR.hookWallBadBUnrestricted_card_eq_interior_add_nonInterior sigma
  omega

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
