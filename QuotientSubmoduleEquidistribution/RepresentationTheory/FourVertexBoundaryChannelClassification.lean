import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexBoundaryM6Reconstruction

/-!
# Cardinal classification of the trimmed source boundary

This file combines the exact preliminary-`M5` reconstruction with the
diagonal strip classification.  It first identifies all common-target
pairs whose second coordinate lies in the first two trimmed source layers.
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

/-- Common-target pairs whose second occurrence is in the first two
trimmed source layers. -/
abbrev SecondSourceBoundaryPair :=
  {p : AR.InteriorCommonTargetArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.1.2}

/-- The diagonal part of the second-coordinate trimmed source boundary. -/
abbrev SecondSourceBoundaryDiagonalPair :=
  {p : AR.InteriorCommonTargetArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        p.1.2 ∧
      p.1.1 = p.1.2}

noncomputable instance secondSourceBoundaryPairFintype :
    Fintype (AR.SecondSourceBoundaryPair sigma) := Fintype.ofFinite _

noncomputable instance secondSourceBoundaryDiagonalPairFintype :
    Fintype (AR.SecondSourceBoundaryDiagonalPair sigma) := Fintype.ofFinite _

noncomputable instance secondSourceBoundaryOffDiagonalPairFintype :
    Fintype (AR.SecondSourceBoundaryOffDiagonalPair sigma) := Fintype.ofFinite _

noncomputable instance hookM5PreliminaryInteriorChannelFintype :
    Fintype (HookM5Preliminary.InteriorChannel sigma AR) := Fintype.ofFinite _

noncomputable instance hookM5PreliminaryOffDiagonalInteriorChannelFintype :
    Fintype (HookM5Preliminary.OffDiagonalInteriorChannel sigma AR) :=
  Fintype.ofFinite _

noncomputable instance hookM5PreliminaryDiagonalInteriorChannelFintype :
    Fintype (HookM5Preliminary.DiagonalInteriorChannel sigma AR) :=
  Fintype.ofFinite _

/-- Split the second-coordinate source boundary into its off-diagonal and
diagonal parts. -/
def secondSourceBoundaryPairEquivOffDiagonalSumDiagonal :
    AR.SecondSourceBoundaryPair sigma ≃
      AR.SecondSourceBoundaryOffDiagonalPair sigma ⊕
        AR.SecondSourceBoundaryDiagonalPair sigma where
  toFun p := by
    classical
    by_cases h : p.1.1.1 = p.1.1.2
    · exact Sum.inr ⟨p.1, p.2, h⟩
    · exact Sum.inl ⟨p.1, p.2, h⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, p.2.1⟩
    · exact ⟨p.1, p.2.1⟩
  left_inv p := by
    classical
    by_cases h : p.1.1.1 = p.1.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2.2]
    · simp [p.2.2]

/-- The diagonal second-coordinate boundary is the same diagonal family
already classified inside the full shifted source boundary. -/
def secondSourceBoundaryDiagonalEquivSourceBoundaryDiagonal :
    AR.SecondSourceBoundaryDiagonalPair sigma ≃
      AR.InteriorSourceBoundaryDiagonalCommonTargetPair sigma where
  toFun p := ⟨⟨p.1, Or.inr p.2.1⟩, p.2.2⟩
  invFun p := ⟨p.1.1, by
    constructor
    · rcases p.1.2 with h | h
      · rw [← p.2]
        exact h
      · exact h
    · exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Split preliminary interior terms according to equality of their two
labelled occurrences. -/
def preliminaryInteriorChannelEquivOffDiagonalSumDiagonal :
    HookM5Preliminary.InteriorChannel sigma AR ≃
      HookM5Preliminary.OffDiagonalInteriorChannel sigma AR ⊕
        HookM5Preliminary.DiagonalInteriorChannel sigma AR where
  toFun X := by
    classical
    by_cases h :
        (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.1 =
          (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.2
    · exact Sum.inr ⟨X, h⟩
    · exact Sum.inl ⟨X, h⟩
  invFun X := by
    rcases X with X | X
    · exact X.1
    · exact X.1
  left_inv X := by
    classical
    by_cases h :
        (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.1 =
          (HookM5Preliminary.interiorCommonTargetPair sigma AR X).1.2
    · simp [h]
    · simp [h]
  right_inv X := by
    classical
    rcases X with X | X
    · simp [X.2]
    · simp [X.2]

include k AR in
/-- Preliminary interior occurrences are the disjoint union of all
off-diagonal second-boundary pairs and the diagonal candidates. -/
def preliminaryInteriorChannelEquivSecondBoundaryOffDiagonalSumCandidate :
    HookM5Preliminary.InteriorChannel sigma AR ≃
      AR.SecondSourceBoundaryOffDiagonalPair sigma ⊕
        AR.HookDiagonalCandidate sigma :=
  (AR.preliminaryInteriorChannelEquivOffDiagonalSumDiagonal sigma).trans <|
    Equiv.sumCongr
      (HookM5Preliminary.offDiagonalInteriorChannelEquivSecondSourceBoundaryPair
        (k := k) sigma AR)
      (HookM5Preliminary.diagonalInteriorChannelEquivDiagonalCandidate
        sigma AR)

include k AR in
/-- Exact cardinal classification of the second-coordinate source
boundary: preliminary `M5` accounts for every off-diagonal pair and one
diagonal candidate copy; the missing diagonal copy consists of all
projective strips. -/
theorem secondSourceBoundaryPair_card_eq_preliminary_add_projectiveStrip :
    Fintype.card (AR.SecondSourceBoundaryPair sigma) =
      Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) +
        Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} := by
  have hboundary :
      Fintype.card (AR.SecondSourceBoundaryPair sigma) =
        Fintype.card (AR.SecondSourceBoundaryOffDiagonalPair sigma) +
          Fintype.card (AR.SecondSourceBoundaryDiagonalPair sigma) := by
    rw [Fintype.card_congr
      (AR.secondSourceBoundaryPairEquivOffDiagonalSumDiagonal sigma)]
    exact Fintype.card_sum
  have hdiagonal :
      Fintype.card (AR.SecondSourceBoundaryDiagonalPair sigma) =
        2 * Fintype.card (AR.HookDiagonalCandidate sigma) +
          Fintype.card (AR.HookShortStrip sigma) := by
    rw [Fintype.card_congr
      (AR.secondSourceBoundaryDiagonalEquivSourceBoundaryDiagonal sigma)]
    exact AR.interiorSourceBoundaryDiagonalCommonTarget_card_eq
      (k := k) sigma
  have hpreliminary :
      Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) =
        Fintype.card (AR.SecondSourceBoundaryOffDiagonalPair sigma) +
          Fintype.card (AR.HookDiagonalCandidate sigma) := by
    rw [Fintype.card_congr
      (AR.preliminaryInteriorChannelEquivSecondBoundaryOffDiagonalSumCandidate
        (k := k) sigma)]
    exact Fintype.card_sum
  have hprojective :
      Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} =
        Fintype.card (AR.HookDiagonalCandidate sigma) +
          Fintype.card (AR.HookShortStrip sigma) := by
    rw [Fintype.card_congr
      (projectiveStripEquivDiagonalCandidateSumShort sigma AR)]
    exact Fintype.card_sum
  omega

/-- Common-target pairs whose first occurrence is literally in the first
trimmed source layer. -/
abbrev FirstSourceBoundaryPair :=
  {p : AR.InteriorCommonTargetArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      p.1.1}

/-- First-layer pairs for which the common target is already injective. -/
structure BoundaryM6InjectiveTargetPair where
  pair : AR.InteriorCommonTargetArrowPair sigma
  first_source :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      pair.1.1
  target_injective : Injective (sigma.obj pair.1.2.1.1.2)

/-- First-layer pairs with noninjective common target for which the
canonical reconstructed strip has a reverse arrow from its last label to
its middle. -/
structure BoundaryM6ReverseLastPair where
  pair : AR.InteriorCommonTargetArrowPair sigma
  first_source :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      pair.1.1
  target_noninjective : ¬ Injective (sigma.obj pair.1.2.1.1.2)
  last_to_middle : HasIrreducibleMorphism
    (sigma.obj (AR.boundaryM6Last sigma pair target_noninjective))
    (sigma.obj (AR.boundaryM6FirstArrow sigma pair).1.2)

omit [DecidableEq iota] in
@[ext]
theorem BoundaryM6InjectiveTargetPair.ext
    {p q : AR.BoundaryM6InjectiveTargetPair sigma}
    (hpair : p.pair = q.pair) : p = q := by
  cases p
  cases q
  cases hpair
  rfl

omit [DecidableEq iota] in
@[ext]
theorem BoundaryM6ReverseLastPair.ext
    {p q : AR.BoundaryM6ReverseLastPair sigma}
    (hpair : p.pair = q.pair) : p = q := by
  cases p
  cases q
  cases hpair
  rfl

noncomputable instance firstSourceBoundaryPairFintype :
    Fintype (AR.FirstSourceBoundaryPair sigma) := Fintype.ofFinite _

omit [Fintype iota] in
noncomputable instance boundaryM6InjectiveTargetPairFinite :
    Finite (AR.BoundaryM6InjectiveTargetPair sigma) :=
  Finite.of_injective BoundaryM6InjectiveTargetPair.pair (by
    intro p q h
    exact BoundaryM6InjectiveTargetPair.ext sigma AR h)

noncomputable instance boundaryM6InjectiveTargetPairFintype :
    Fintype (AR.BoundaryM6InjectiveTargetPair sigma) := Fintype.ofFinite _

omit [Fintype iota] in
noncomputable instance boundaryM6ReverseLastPairFinite :
    Finite (AR.BoundaryM6ReverseLastPair sigma) :=
  Finite.of_injective BoundaryM6ReverseLastPair.pair (by
    intro p q h
    exact BoundaryM6ReverseLastPair.ext sigma AR h)

noncomputable instance boundaryM6ReverseLastPairFintype :
    Fintype (AR.BoundaryM6ReverseLastPair sigma) := Fintype.ofFinite _

/-- The literal first layer splits into the regular `M6` image, the
injective-target endpoint, and the reverse-last-arrow exception. -/
def firstSourceBoundaryPairEquivM6RegularSumExceptions :
    AR.FirstSourceBoundaryPair sigma ≃
      AR.BoundaryM6RegularPair sigma ⊕
        (AR.BoundaryM6InjectiveTargetPair sigma ⊕
          AR.BoundaryM6ReverseLastPair sigma) where
  toFun p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.2.1.1.2)
    · exact Sum.inr (Sum.inl
        { pair := p.1
          first_source := p.2
          target_injective := hI })
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma p.1 hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma p.1).1.2)
      · exact Sum.inr (Sum.inr
          { pair := p.1
            first_source := p.2
            target_noninjective := hI
            last_to_middle := hlast })
      · exact Sum.inl
          { pair := p.1
            first_source := p.2
            target_noninjective := hI
            last_not_to_middle := hlast }
  invFun p := by
    rcases p with p | p
    · exact ⟨p.pair, p.first_source⟩
    · rcases p with p | p
      · exact ⟨p.pair, p.first_source⟩
      · exact ⟨p.pair, p.first_source⟩
  left_inv p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.2.1.1.2)
    · simp [hI]
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma p.1 hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma p.1).1.2)
      · simp [hI, hlast]
      · simp [hI, hlast]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.target_noninjective, p.last_not_to_middle]
    · rcases p with p | p
      · simp [p.target_injective]
      · simp [p.target_noninjective, p.last_to_middle]

include k AR in
/-- Cardinal form of the exhaustive first-layer classification. -/
theorem firstSourceBoundaryPair_card_eq_m6_add_exceptions :
    Fintype.card (AR.FirstSourceBoundaryPair sigma) =
      Fintype.card (HookM6Channel.InteriorChannel sigma AR) +
        Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) +
          Fintype.card (AR.BoundaryM6ReverseLastPair sigma) := by
  have hsplit :
      Fintype.card (AR.FirstSourceBoundaryPair sigma) =
        Fintype.card (AR.BoundaryM6RegularPair sigma) +
          (Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) +
            Fintype.card (AR.BoundaryM6ReverseLastPair sigma)) := by
    rw [Fintype.card_congr
      (AR.firstSourceBoundaryPairEquivM6RegularSumExceptions sigma)]
    simp only [Fintype.card_sum]
  have hM6 := AR.hookM6Interior_card_eq_boundaryM6RegularPair
    (k := k) sigma
  omega

omit [DecidableEq iota] in
/-- For a common-target pair, if the first occurrence is in the first two
trimmed source layers, then either it is literally in the first layer or
the second occurrence is itself in the first two layers. -/
theorem first_twoSource_imp_firstSource_or_second_twoSource
    (p : AR.InteriorCommonTargetArrowPair sigma)
    (hfirst :
      ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        p.1.1) :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.1 ∨
      ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        p.1.2 := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  let C := p.1.1
  let H := p.1.2
  by_cases hC : O.InteriorSource C
  · exact Or.inl hC
  · right
    by_cases hH : O.InteriorSource H
    · exact Or.inl hH
    · right
      intro _hH
      have hCprev : O.InteriorSource (U.tau ⟨C, hC⟩).1 := by
        rcases hfirst with h | h
        · exact (hC h).elim
        · exact h hC
      apply (M.arrowInterior_source_iff sigma (U.tau ⟨H, hH⟩).1).2
      have hCprojective : Projective
          (sigma.obj (U.tau ⟨C, hC⟩).1.1.1.1) :=
        (M.arrowInterior_source_iff sigma (U.tau ⟨C, hC⟩).1).1
          hCprev
      have hsources :
          (U.tau ⟨C, hC⟩).1.1.1.1 =
            (U.tau ⟨H, hH⟩).1.1.1.1 := by
        change
          (M.tau ⟨C.1.1.2, C.2.1⟩).1 =
            (M.tau ⟨H.1.1.2, H.2.1⟩).1
        have hinputs :
            (⟨C.1.1.2, C.2.1⟩ : sigma.NonprojectiveLabel) =
              ⟨H.1.1.2, H.2.1⟩ := by
          apply Subtype.ext
          exact p.2
        rw [hinputs]
      rw [← hsources]
      exact hCprojective

/-- The part of the literal first layer not already present through the
second coordinate. -/
abbrev FirstOnlySourceBoundaryPair :=
  {p : AR.FirstSourceBoundaryPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.1.1.2}

noncomputable instance firstOnlySourceBoundaryPairFintype :
    Fintype (AR.FirstOnlySourceBoundaryPair sigma) := Fintype.ofFinite _

include AR in
/-- The full trimmed source boundary is the disjoint union of the
second-coordinate boundary and the remaining literal first-coordinate
layer. -/
def interiorSourceBoundaryPairEquivSecondSourceSumFirstOnly :
    AR.InteriorSourceBoundaryCommonTargetArrowPair sigma ≃
      AR.SecondSourceBoundaryPair sigma ⊕
        AR.FirstOnlySourceBoundaryPair sigma where
  toFun p := by
    classical
    by_cases hsecond :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.1.1.2
    · exact Sum.inl ⟨p.1, hsecond⟩
    · have hfirstTwo :
          ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
            p.1.1.1 := by
          rcases p.2 with h | h
          · exact h
          · exact (hsecond h).elim
      have hfirst :
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.1 := by
        rcases AR.first_twoSource_imp_firstSource_or_second_twoSource
            sigma p.1 hfirstTwo with h | h
        · exact h
        · exact (hsecond h).elim
      exact Sum.inr ⟨⟨p.1, hfirst⟩, hsecond⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, Or.inr p.2⟩
    · exact ⟨p.1.1, Or.inl (Or.inl p.1.2)⟩
  left_inv p := by
    classical
    by_cases hsecond :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.1.1.2
    · simp [hsecond]
    · simp [hsecond]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

omit [DecidableEq iota] in
include AR in
/-- Cardinal form of the disjoint coordinate-boundary split. -/
theorem interiorSourceBoundaryPair_card_eq_secondSource_add_firstOnly :
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) =
      Fintype.card (AR.SecondSourceBoundaryPair sigma) +
        Fintype.card (AR.FirstOnlySourceBoundaryPair sigma) := by
  rw [Fintype.card_congr
    (AR.interiorSourceBoundaryPairEquivSecondSourceSumFirstOnly sigma)]
  exact Fintype.card_sum

/-- Regular first-layer pairs which also occur through the second
coordinate.  This is the overlap of the preliminary and `M6` boundary
regions. -/
abbrev BoundaryM6RegularSecondSourcePair :=
  {p : AR.BoundaryM6RegularPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

/-- Regular first-layer pairs not already present through the second
coordinate. -/
abbrev BoundaryM6RegularFirstOnlyPair :=
  {p : AR.BoundaryM6RegularPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

/-- Injective-target exceptions in the first-only region. -/
abbrev BoundaryM6InjectiveTargetFirstOnlyPair :=
  {p : AR.BoundaryM6InjectiveTargetPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

/-- Reverse-last-arrow exceptions in the first-only region. -/
abbrev BoundaryM6ReverseLastFirstOnlyPair :=
  {p : AR.BoundaryM6ReverseLastPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

noncomputable instance boundaryM6RegularSecondSourcePairFintype :
    Fintype (AR.BoundaryM6RegularSecondSourcePair sigma) := Fintype.ofFinite _

noncomputable instance boundaryM6RegularFirstOnlyPairFintype :
    Fintype (AR.BoundaryM6RegularFirstOnlyPair sigma) := Fintype.ofFinite _

noncomputable instance boundaryM6InjectiveTargetFirstOnlyPairFintype :
    Fintype (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) :=
  Fintype.ofFinite _

noncomputable instance boundaryM6ReverseLastFirstOnlyPairFintype :
    Fintype (AR.BoundaryM6ReverseLastFirstOnlyPair sigma) :=
  Fintype.ofFinite _

/-- Split the regular `M6` image according to whether it overlaps the
second-coordinate boundary. -/
def boundaryM6RegularPairEquivFirstOnlySumSecondSource :
    AR.BoundaryM6RegularPair sigma ≃
      AR.BoundaryM6RegularFirstOnlyPair sigma ⊕
        AR.BoundaryM6RegularSecondSourcePair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · exact Sum.inr ⟨p, h⟩
    · exact Sum.inl ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- The first-only boundary splits into its regular `M6` part and the two
explicit exceptional parts. -/
def firstOnlySourceBoundaryPairEquivM6AndExceptions :
    AR.FirstOnlySourceBoundaryPair sigma ≃
      AR.BoundaryM6RegularFirstOnlyPair sigma ⊕
        (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma ⊕
          AR.BoundaryM6ReverseLastFirstOnlyPair sigma) where
  toFun p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.1.2.1.1.2)
    · exact Sum.inr (Sum.inl
        ⟨{ pair := p.1.1
           first_source := p.1.2
           target_injective := hI }, p.2⟩)
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma p.1.1 hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma p.1.1).1.2)
      · exact Sum.inr (Sum.inr
          ⟨{ pair := p.1.1
             first_source := p.1.2
             target_noninjective := hI
             last_to_middle := hlast }, p.2⟩)
      · exact Sum.inl
          ⟨{ pair := p.1.1
             first_source := p.1.2
             target_noninjective := hI
             last_not_to_middle := hlast }, p.2⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨⟨p.1.pair, p.1.first_source⟩, p.2⟩
    · rcases p with p | p
      · exact ⟨⟨p.1.pair, p.1.first_source⟩, p.2⟩
      · exact ⟨⟨p.1.pair, p.1.first_source⟩, p.2⟩
  left_inv p := by
    classical
    by_cases hI : Injective (sigma.obj p.1.1.1.2.1.1.2)
    · simp [hI]
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma p.1.1 hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma p.1.1).1.2)
      · simp [hI, hlast]
      · simp [hI, hlast]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.1.target_noninjective, p.1.last_not_to_middle]
    · rcases p with p | p
      · simp [p.1.target_injective]
      · simp [p.1.target_noninjective, p.1.last_to_middle]

include k AR in
/-- The exact local boundary equation after the preliminary and regular
`M6` reconstructions.  Only the overlap and the two explicit exceptional
strata remain to be classified. -/
theorem interiorSourceBoundary_add_m6Overlap_card_eq_channels_add_corrections :
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card (AR.BoundaryM6RegularSecondSourcePair sigma) =
      Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) +
        Fintype.card (HookM6Channel.InteriorChannel sigma AR) +
          Fintype.card
            {T : AR.StripAdmissibleTriple sigma //
              Projective (sigma.obj T.a)} +
            Fintype.card
              (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
              Fintype.card
                (AR.BoundaryM6ReverseLastFirstOnlyPair sigma) := by
  have hboundary :=
    AR.interiorSourceBoundaryPair_card_eq_secondSource_add_firstOnly sigma
  have hsecond :=
    AR.secondSourceBoundaryPair_card_eq_preliminary_add_projectiveStrip
      (k := k) sigma
  have hfirstOnly :
      Fintype.card (AR.FirstOnlySourceBoundaryPair sigma) =
        Fintype.card (AR.BoundaryM6RegularFirstOnlyPair sigma) +
          (Fintype.card
              (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
            Fintype.card
              (AR.BoundaryM6ReverseLastFirstOnlyPair sigma)) := by
    rw [Fintype.card_congr
      (AR.firstOnlySourceBoundaryPairEquivM6AndExceptions sigma)]
    simp only [Fintype.card_sum]
  have hregular :
      Fintype.card (AR.BoundaryM6RegularPair sigma) =
        Fintype.card (AR.BoundaryM6RegularFirstOnlyPair sigma) +
          Fintype.card (AR.BoundaryM6RegularSecondSourcePair sigma) := by
    rw [Fintype.card_congr
      (AR.boundaryM6RegularPairEquivFirstOnlySumSecondSource sigma)]
    exact Fintype.card_sum
  have hM6 := AR.hookM6Interior_card_eq_boundaryM6RegularPair
    (k := k) sigma
  omega

/-- The disjoint sum of the two trimmed negative wall channels. -/
abbrev HookWallInteriorSum :=
  HookWallBadU.InteriorChannel sigma AR ⊕
    HookWallBadBUnrestricted.InteriorChannel sigma AR

noncomputable instance hookWallBadUInteriorChannelFintype :
    Fintype (HookWallBadU.InteriorChannel sigma AR) := Fintype.ofFinite _

noncomputable instance hookWallBadBUnrestrictedInteriorChannelFintype :
    Fintype (HookWallBadBUnrestricted.InteriorChannel sigma AR) :=
  Fintype.ofFinite _

/-- The common-target occurrence carried by either trimmed wall channel. -/
def hookWallInteriorPair :
    AR.HookWallInteriorSum sigma → AR.InteriorCommonTargetArrowPair sigma
  | Sum.inl X => HookWallBadU.interiorCommonTargetPair sigma AR X
  | Sum.inr X =>
      HookWallBadBUnrestricted.interiorCommonTargetPair sigma AR X

omit [DecidableEq iota] in
/-- The first occurrence of every trimmed wall pair is literally in the
first trimmed source layer. -/
theorem hookWallInteriorPair_firstSource
    (X : AR.HookWallInteriorSum sigma) :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      (AR.hookWallInteriorPair sigma X).1.1 := by
  rcases X with X | X
  · exact ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma _).2 X.1.1.z_projective
  · exact ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma _).2 X.1.1.z_projective

omit [DecidableEq iota] in
/-- The hook occurrence of every trimmed wall pair is in the first two
trimmed source layers. -/
theorem hookWallInteriorPair_secondTwoSource
    (X : AR.HookWallInteriorSum sigma) :
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      (AR.hookWallInteriorPair sigma X).1.2 := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  rcases X with X | X
  · left
    apply (M.arrowInterior_source_iff sigma _).2
    simpa [hookWallInteriorPair,
      HookWallBadU.interiorCommonTargetPair, toInteriorArrow,
      StripAdmissibleTriple.firstArrow] using X.1.1.a_projective
  · let H := toInteriorArrow sigma AR
        (X.1.1.triple.secondArrow sigma AR) X.2.2
    change U.TwoSource H
    have hnot : ¬ O.InteriorSource H := by
      intro h
      have hP := (M.arrowInterior_source_iff sigma H).1 h
      change Projective (sigma.obj X.1.1.triple.u) at hP
      exact X.1.1.triple.u_nonprojective hP
    right
    intro _hnot
    apply (M.arrowInterior_source_iff sigma (U.tau ⟨H, hnot⟩).1).2
    have hval : (U.tau ⟨H, hnot⟩).1.1 =
        X.1.1.triple.firstArrow sigma AR := by
      have hpred := congrArg Subtype.val
        (X.1.1.triple.secondArrow_predecessor sigma AR)
      simpa [U, M, O, H, ARMeshRotationData.arrowInteriorOrbitData,
        QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.interior,
        HookWallBadBUnrestricted.interiorCommonTargetPair,
        toInteriorArrow] using hpred
    rw [hval]
    simpa [StripAdmissibleTriple.firstArrow] using
      X.1.1.a_projective

omit [DecidableEq iota] in
/-- An `M3` wall pair can never be diagonal: that would identify its
projective fourth label with the nonprojective hook middle. -/
theorem hookWallBadBInteriorPair_ne
    (X : HookWallBadBUnrestricted.InteriorChannel sigma AR) :
    (HookWallBadBUnrestricted.interiorCommonTargetPair sigma AR X).1.1 ≠
      (HookWallBadBUnrestricted.interiorCommonTargetPair sigma AR X).1.2 := by
  intro h
  have hsources := congrArg
    (fun q : (AR.arMeshRotationData sigma).InteriorArrow sigma ↦
      q.1.1.1) h
  have hzEq : X.1.1.z = X.1.1.triple.u := by
    simpa [HookWallBadBUnrestricted.interiorCommonTargetPair,
      toInteriorArrow, HookWallBadBUnrestricted.associatedArrow,
      StripAdmissibleTriple.secondArrow] using hsources
  exact X.1.1.triple.u_nonprojective
    (hzEq ▸ X.1.1.z_projective)

/-- Diagonal trimmed `M2` wall terms. -/
abbrev HookWallBadUDiagonalInteriorChannel :=
  {X : HookWallBadU.InteriorChannel sigma AR //
    (HookWallBadU.interiorCommonTargetPair sigma AR X).1.1 =
      (HookWallBadU.interiorCommonTargetPair sigma AR X).1.2}

noncomputable instance hookWallBadUDiagonalInteriorChannelFintype :
    Fintype (AR.HookWallBadUDiagonalInteriorChannel sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
/-- Projectively based admissible strips are exactly the diagonal trimmed
`M2` wall terms. -/
def projectiveStripEquivHookWallBadUDiagonalInterior :
    {T : AR.StripAdmissibleTriple sigma //
        Projective (sigma.obj T.a)} ≃
      AR.HookWallBadUDiagonalInteriorChannel sigma where
  toFun T := by
    let W : AR.HookWallBadU sigma :=
      ⟨{ triple := T.1
         a_projective := T.2
         z := T.1.a
         z_projective := T.2 }, T.1.a_to_u⟩
    let X : HookWallBadU.InteriorChannel sigma AR :=
      ⟨W, W.firstArrow_isInterior sigma AR,
        W.firstArrow_isInterior sigma AR⟩
    exact ⟨X, by
      apply Subtype.ext
      rfl⟩
  invFun X := ⟨X.1.1.1.triple, X.1.1.1.a_projective⟩
  left_inv T := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply HookWallChoice.ext
    · rfl
    · have hsources := congrArg
          (fun q : (AR.arMeshRotationData sigma).InteriorArrow sigma ↦
            q.1.1.1) X.2
      simpa [HookWallBadU.interiorCommonTargetPair, toInteriorArrow,
        HookWallBadU.associatedArrow,
        StripAdmissibleTriple.firstArrow] using hsources.symm

omit [DecidableEq iota] in
/-- The occurrence assignment is injective even after adjoining the two
wall channels disjointly. -/
theorem hookWallInteriorPair_injective :
    Function.Injective (AR.hookWallInteriorPair sigma) := by
  intro X Y h
  rcases X with X | X <;> rcases Y with Y | Y
  · exact congrArg Sum.inl
      (HookWallBadU.interiorCommonTargetPair_injective sigma AR h)
  · have hsecond := congrArg
        (fun p : AR.InteriorCommonTargetArrowPair sigma ↦ p.1.2.1.1.1) h
    have haEq : X.1.1.triple.a = Y.1.1.triple.u := by
      simpa [hookWallInteriorPair,
        HookWallBadU.interiorCommonTargetPair,
        HookWallBadBUnrestricted.interiorCommonTargetPair,
        toInteriorArrow, StripAdmissibleTriple.firstArrow,
        StripAdmissibleTriple.secondArrow] using hsecond
    exact (Y.1.1.triple.u_nonprojective
      (haEq ▸ X.1.1.a_projective)).elim
  · have hsecond := congrArg
        (fun p : AR.InteriorCommonTargetArrowPair sigma ↦ p.1.2.1.1.1) h
    have huEq : X.1.1.triple.u = Y.1.1.triple.a := by
      simpa [hookWallInteriorPair,
        HookWallBadU.interiorCommonTargetPair,
        HookWallBadBUnrestricted.interiorCommonTargetPair,
        toInteriorArrow, StripAdmissibleTriple.firstArrow,
        StripAdmissibleTriple.secondArrow] using hsecond
    exact (X.1.1.triple.u_nonprojective
      (huEq ▸ Y.1.1.a_projective)).elim
  · exact congrArg Sum.inr
      (HookWallBadBUnrestricted.interiorCommonTargetPair_injective
        sigma AR h)

/-- Off-diagonal trimmed wall terms. -/
abbrev HookWallInteriorOffDiagonal :=
  {X : AR.HookWallInteriorSum sigma //
    (AR.hookWallInteriorPair sigma X).1.1 ≠
      (AR.hookWallInteriorPair sigma X).1.2}

noncomputable instance hookWallInteriorOffDiagonalFintype :
    Fintype (AR.HookWallInteriorOffDiagonal sigma) := Fintype.ofFinite _

/-- The two wall channels split into diagonal `M2` terms and all remaining
off-diagonal wall terms. -/
def hookWallInteriorSumEquivDiagonalM2SumOffDiagonal :
    AR.HookWallInteriorSum sigma ≃
      AR.HookWallBadUDiagonalInteriorChannel sigma ⊕
        AR.HookWallInteriorOffDiagonal sigma where
  toFun X := by
    classical
    rcases X with X | X
    · by_cases h :
          (HookWallBadU.interiorCommonTargetPair sigma AR X).1.1 =
            (HookWallBadU.interiorCommonTargetPair sigma AR X).1.2
      · exact Sum.inl ⟨X, h⟩
      · exact Sum.inr ⟨Sum.inl X, h⟩
    · exact Sum.inr ⟨Sum.inr X,
        AR.hookWallBadBInteriorPair_ne sigma X⟩
  invFun X := by
    rcases X with X | X
    · exact Sum.inl X.1
    · exact X.1
  left_inv X := by
    classical
    rcases X with X | X
    · by_cases h :
          (HookWallBadU.interiorCommonTargetPair sigma AR X).1.1 =
            (HookWallBadU.interiorCommonTargetPair sigma AR X).1.2
      · simp [h]
      · simp [h]
    · rfl
  right_inv X := by
    classical
    rcases X with X | X
    · simp [X.2]
    · rcases X with ⟨X, hX⟩
      rcases X with X | X
      · have hX' :
            (HookWallBadU.interiorCommonTargetPair sigma AR X).1.1 ≠
              (HookWallBadU.interiorCommonTargetPair sigma AR X).1.2 := by
            simpa [hookWallInteriorPair] using hX
        simp [hX']
      · rfl

omit [DecidableEq iota] in
include AR in
/-- Cardinal form of the diagonal/off-diagonal wall split. -/
theorem hookWallInteriorSum_card_eq_projectiveStrip_add_offDiagonal :
    Fintype.card (AR.HookWallInteriorSum sigma) =
      Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} +
        Fintype.card (AR.HookWallInteriorOffDiagonal sigma) := by
  have hsplit :
      Fintype.card (AR.HookWallInteriorSum sigma) =
        Fintype.card (AR.HookWallBadUDiagonalInteriorChannel sigma) +
          Fintype.card (AR.HookWallInteriorOffDiagonal sigma) := by
    rw [Fintype.card_congr
      (AR.hookWallInteriorSumEquivDiagonalM2SumOffDiagonal sigma)]
    exact Fintype.card_sum
  rw [Fintype.card_congr
    (AR.projectiveStripEquivHookWallBadUDiagonalInterior sigma)]
  exact hsplit

/-- The diagonal part of the regular preliminary/`M6` overlap. -/
abbrev BoundaryM6RegularSecondSourceDiagonalPair :=
  {p : AR.BoundaryM6RegularSecondSourcePair sigma //
    p.1.pair.1.1 = p.1.pair.1.2}

noncomputable instance boundaryM6RegularSecondSourceDiagonalPairFintype :
    Fintype (AR.BoundaryM6RegularSecondSourceDiagonalPair sigma) :=
  Fintype.ofFinite _

include k AR in
/-- Continuing projective strips are exactly the diagonal regular overlap
between the second-coordinate and `M6` boundary regions. -/
def hookDiagonalCandidateEquivM6RegularSecondSourceDiagonal :
    AR.HookDiagonalCandidate sigma ≃
      AR.BoundaryM6RegularSecondSourceDiagonalPair sigma where
  toFun C := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let H : M.InteriorArrow sigma :=
      ⟨C.1.firstArrow sigma AR, by
        exact ⟨by
          simpa [StripAdmissibleTriple.firstArrow] using
            C.1.u_nonprojective,
          by simpa [StripAdmissibleTriple.firstArrow] using
            C.1.a_noninjective sigma AR⟩⟩
    let P : AR.InteriorCommonTargetArrowPair sigma :=
      ⟨(H, H), rfl⟩
    have hfirst : O.InteriorSource H :=
      (M.arrowInterior_source_iff sigma H).2 (by
        simpa [H, StripAdmissibleTriple.firstArrow] using C.2.1)
    have htargetNI : ¬ Injective (sigma.obj P.1.2.1.1.2) := by
      simpa [P, H, StripAdmissibleTriple.firstArrow] using C.2.2
    have hsourceNI : ¬ Injective
        (sigma.obj (C.1.firstArrow sigma AR).1.1) := by
      simpa [StripAdmissibleTriple.firstArrow] using
        C.1.a_noninjective sigma AR
    have hnext : AR.boundaryM6FirstArrow sigma P =
        C.1.secondArrow sigma AR := by
      change (O.tau.symm
        ⟨C.1.firstArrow sigma AR, hsourceNI⟩).1 =
          C.1.secondArrow sigma AR
      have hs : O.successor (C.1.firstArrow sigma AR) =
          (O.tau.symm
            ⟨C.1.firstArrow sigma AR,
              hsourceNI⟩).1 := by
        simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor,
          hsourceNI]
      exact hs.symm.trans (C.1.firstArrow_successor sigma AR)
    have hlast : AR.boundaryM6Last sigma P htargetNI = C.z sigma AR := by
      rfl
    let p : AR.BoundaryM6RegularPair sigma :=
      { pair := P
        first_source := hfirst
        target_noninjective := htargetNI
        last_not_to_middle := by
          simpa only [hlast, hnext,
            StripAdmissibleTriple.secondArrow] using
              C.z_not_to_b (k := k) sigma AR }
    exact ⟨⟨p, Or.inl hfirst⟩, rfl⟩
  invFun p := by
    let H := p.1.1.pair.1.1
    have hP : Projective (sigma.obj H.1.1.1) :=
      ((AR.arMeshRotationData sigma).arrowInterior_source_iff
        sigma H).1 p.1.1.first_source
    let T := stripTripleOfProjectiveArrow (k := k) sigma AR H.1
      hP H.2.2 H.2.1
    refine ⟨T, hP, ?_⟩
    change ¬ Injective (sigma.obj H.1.1.2)
    have htargets : H.1.1.2 = p.1.1.pair.1.2.1.1.2 :=
      congrArg
        (fun q : (AR.arMeshRotationData sigma).InteriorArrow sigma ↦
          q.1.1.2) p.2
    rw [htargets]
    exact p.1.1.target_noninjective
  left_inv C := by
    apply Subtype.ext
    apply StripAdmissibleTriple.firstArrow_injective sigma AR
    exact stripTripleOfProjectiveArrow_firstArrow
      (k := k) sigma AR (C.1.firstArrow sigma AR) C.2.1
        (C.1.a_noninjective sigma AR) C.1.u_nonprojective
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply BoundaryM6RegularPair.ext sigma AR
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR p.1.1.pair.1.1.1
          (((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.pair.1.1).1 p.1.1.first_source)
          p.1.1.pair.1.1.2.2 p.1.1.pair.1.1.2.1
    · apply Subtype.ext
      exact (stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR p.1.1.pair.1.1.1
          (((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.pair.1.1).1 p.1.1.first_source)
          p.1.1.pair.1.1.2.2 p.1.1.pair.1.1.2.1).trans
            (congrArg Subtype.val p.2)

/-- The off-diagonal part of the regular preliminary/`M6` overlap. -/
abbrev BoundaryM6RegularSecondSourceOffDiagonalPair :=
  {p : AR.BoundaryM6RegularSecondSourcePair sigma //
    p.1.pair.1.1 ≠ p.1.pair.1.2}

noncomputable instance boundaryM6RegularSecondSourceOffDiagonalPairFintype :
    Fintype (AR.BoundaryM6RegularSecondSourceOffDiagonalPair sigma) :=
  Fintype.ofFinite _

/-- Off-diagonal common-target pairs whose first occurrence is literally
in the first source layer and whose second occurrence is in the first two
source layers. -/
abbrev BoundaryFirstSecondOffDiagonalPair :=
  {p : AR.FirstSourceBoundaryPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
        p.1.1.2 ∧
      p.1.1.1 ≠ p.1.1.2}

noncomputable instance boundaryFirstSecondOffDiagonalPairFintype :
    Fintype (AR.BoundaryFirstSecondOffDiagonalPair sigma) :=
  Fintype.ofFinite _

/-- A reconstructed off-diagonal wall term retaining equality of its
canonical occurrence pair. -/
structure BoundaryWallReconstruction
    (p : AR.BoundaryFirstSecondOffDiagonalPair sigma) where
  term : AR.HookWallInteriorOffDiagonal sigma
  occurrence_eq : AR.hookWallInteriorPair sigma term.1 = p.1.1

omit [DecidableEq iota] in
include AR in
/-- Every off-diagonal pair in both source-coordinate regions reconstructs
the unique trimmed `M2` or `M3` wall term with the same labelled
occurrence. -/
def boundaryWallReconstruction
    {K : Type u} [Field K] [Algebra K R] [FiniteDimensional K R]
    (p : AR.BoundaryFirstSecondOffDiagonalPair sigma) :
    AR.BoundaryWallReconstruction sigma p := by
  classical
  let Q : AR.SecondSourceBoundaryOffDiagonalPair sigma :=
    ⟨p.1.1, p.2.1, p.2.2⟩
  let Y := (AR.preliminaryInteriorOfSecondSourceBoundaryPair
    (k := K) sigma Q).term
  let P : AR.HookM5Preliminary sigma := Y.1
  let C := p.1.1.1.1
  let H := p.1.1.1.2
  have hocc := (AR.preliminaryInteriorOfSecondSourceBoundaryPair
    (k := K) sigma Q).occurrence_eq
  have hrot : toInteriorArrow sigma AR
      (P.rotatedAssociatedArrow sigma AR) Y.2.1 = C := by
    exact congrArg
      (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.1) hocc
  have hhook : toInteriorArrow sigma AR
      (P.hookArrow sigma AR) Y.2.2 = H := by
    exact congrArg
      (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.2) hocc
  have hrotRaw : P.rotatedAssociatedArrow sigma AR = C.1 :=
    congrArg Subtype.val hrot
  have hhookRaw : P.hookArrow sigma AR = H.1 :=
    congrArg Subtype.val hhook
  have hzP : Projective (sigma.obj C.1.1.1) :=
    ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma C).1 p.1.2
  by_cases hu : HasIrreducibleMorphism
      (sigma.obj P.triple.u) (sigma.obj P.z)
  · have htarget : C.1.1.2 = P.triple.u := by
      calc
        C.1.1.2 = (P.rotatedAssociatedArrow sigma AR).1.2 :=
          congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hrotRaw.symm
        _ = (P.hookArrow sigma AR).1.2 :=
          P.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR
        _ = P.triple.u := by
          simp [HookM5Preliminary.hookArrow, hu,
            StripAdmissibleTriple.firstArrow]
    let W : AR.HookWallBadU sigma :=
      ⟨{ triple := P.triple
         a_projective := P.a_projective
         z := C.1.1.1
         z_projective := hzP }, by
        simpa only [htarget] using C.1.2⟩
    have hassociated : W.associatedArrow sigma AR = C.1 := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact htarget.symm
    have hfirst : W.1.triple.firstArrow sigma AR = H.1 := by
      simpa [W, HookM5Preliminary.hookArrow, hu] using hhookRaw
    let X : HookWallBadU.InteriorChannel sigma AR :=
      ⟨W, by
        constructor
        · simpa only [hassociated, IsInteriorArrow] using C.2
        · simpa only [hfirst, IsInteriorArrow] using H.2⟩
    have hpair : AR.hookWallInteriorPair sigma (Sum.inl X) =
        p.1.1 := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext
      · exact hassociated
      · exact hfirst
    let Z : AR.HookWallInteriorOffDiagonal sigma :=
      ⟨Sum.inl X, by
        intro h
        apply p.2.2
        rw [← hpair]
        exact h⟩
    exact { term := Z, occurrence_eq := hpair }
  · have hb : HasIrreducibleMorphism
        (sigma.obj P.triple.b) (sigma.obj P.z) :=
      P.outgoing_to_z.resolve_left hu
    have htarget : C.1.1.2 = P.triple.b := by
      calc
        C.1.1.2 = (P.rotatedAssociatedArrow sigma AR).1.2 :=
          congrArg (fun q : sigma.IrreduciblePair ↦ q.1.2) hrotRaw.symm
        _ = (P.hookArrow sigma AR).1.2 :=
          P.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR
        _ = P.triple.b := by
          simp [HookM5Preliminary.hookArrow, hu,
            StripAdmissibleTriple.secondArrow]
    let W : AR.HookWallBadBUnrestricted sigma :=
      ⟨{ triple := P.triple
         a_projective := P.a_projective
         z := C.1.1.1
         z_projective := hzP }, by
        simpa only [htarget] using C.1.2⟩
    have hassociated : W.associatedArrow sigma AR = C.1 := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact htarget.symm
    have hsecond : W.1.triple.secondArrow sigma AR = H.1 := by
      simpa [W, HookM5Preliminary.hookArrow, hu] using hhookRaw
    let X : HookWallBadBUnrestricted.InteriorChannel sigma AR :=
      ⟨W, by
        constructor
        · simpa only [hassociated, IsInteriorArrow] using C.2
        · simpa only [hsecond, IsInteriorArrow] using H.2⟩
    have hpair : AR.hookWallInteriorPair sigma (Sum.inr X) =
        p.1.1 := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext
      · exact hassociated
      · exact hsecond
    let Z : AR.HookWallInteriorOffDiagonal sigma :=
      ⟨Sum.inr X, by
        intro h
        apply p.2.2
        rw [← hpair]
        exact h⟩
    exact { term := Z, occurrence_eq := hpair }

include AR in
/-- Off-diagonal trimmed `M2/M3` wall occurrences are exactly the
off-diagonal common-target pairs lying in both source-coordinate regions. -/
def hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
    {K : Type u} [Field K] [Algebra K R] [FiniteDimensional K R] :
    AR.HookWallInteriorOffDiagonal sigma ≃
      AR.BoundaryFirstSecondOffDiagonalPair sigma where
  toFun X :=
    ⟨⟨AR.hookWallInteriorPair sigma X.1,
        AR.hookWallInteriorPair_firstSource sigma X.1⟩,
      AR.hookWallInteriorPair_secondTwoSource sigma X.1, X.2⟩
  invFun p := (AR.boundaryWallReconstruction (K := K) sigma p).term
  left_inv X := by
    apply Subtype.ext
    apply AR.hookWallInteriorPair_injective sigma
    exact (AR.boundaryWallReconstruction (K := K) sigma _).occurrence_eq
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (AR.boundaryWallReconstruction (K := K) sigma p).occurrence_eq

/-- Off-diagonal wall terms satisfying the two regular `M6`
reconstruction conditions. -/
structure HookWallInteriorRegularOffDiagonal where
  term : AR.HookWallInteriorOffDiagonal sigma
  regular : AR.BoundaryM6RegularPair sigma
  occurrence_eq : regular.pair = AR.hookWallInteriorPair sigma term.1

omit [DecidableEq iota] in
@[ext]
theorem HookWallInteriorRegularOffDiagonal.ext
    {X Y : AR.HookWallInteriorRegularOffDiagonal sigma}
    (hterm : X.term = Y.term) : X = Y := by
  have hpair : X.regular.pair = Y.regular.pair :=
    X.occurrence_eq.trans <| (congrArg
      (fun Z : AR.HookWallInteriorOffDiagonal sigma ↦
        AR.hookWallInteriorPair sigma Z.1) hterm).trans Y.occurrence_eq.symm
  have hregular : X.regular = Y.regular :=
    BoundaryM6RegularPair.ext sigma AR hpair
  cases X
  cases Y
  simp_all

omit [Fintype iota] in
noncomputable instance hookWallInteriorRegularOffDiagonalFinite :
    Finite (AR.HookWallInteriorRegularOffDiagonal sigma) :=
  Finite.of_injective HookWallInteriorRegularOffDiagonal.term (by
    intro X Y h
    exact HookWallInteriorRegularOffDiagonal.ext sigma AR h)

noncomputable instance hookWallInteriorRegularOffDiagonalFintype :
    Fintype (AR.HookWallInteriorRegularOffDiagonal sigma) :=
  Fintype.ofFinite _

include k AR in
/-- Regular off-diagonal wall terms are exactly the off-diagonal regular
overlap of the preliminary and `M6` boundary regions. -/
def hookWallInteriorRegularOffDiagonalEquivM6Overlap :
    AR.HookWallInteriorRegularOffDiagonal sigma ≃
      AR.BoundaryM6RegularSecondSourceOffDiagonalPair sigma where
  toFun X :=
    ⟨⟨X.regular, by
        rw [X.occurrence_eq]
        exact AR.hookWallInteriorPair_secondTwoSource sigma X.term.1⟩,
      by
        rw [X.occurrence_eq]
        exact X.term.2⟩
  invFun p := by
    let Q : AR.BoundaryFirstSecondOffDiagonalPair sigma :=
      ⟨⟨p.1.1.pair, p.1.1.first_source⟩, p.1.2, p.2⟩
    let X := AR.boundaryWallReconstruction (K := k) sigma Q
    exact
      { term := X.term
        regular := p.1.1
        occurrence_eq := X.occurrence_eq.symm }
  left_inv X := by
    apply HookWallInteriorRegularOffDiagonal.ext sigma AR
    apply Subtype.ext
    apply AR.hookWallInteriorPair_injective sigma
    exact (AR.boundaryWallReconstruction (K := k) sigma _).occurrence_eq.trans
      X.occurrence_eq
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Off-diagonal wall terms whose common target is already injective. -/
abbrev HookWallInteriorInjectiveTargetOffDiagonal :=
  {X : AR.HookWallInteriorOffDiagonal sigma //
    Injective
      (sigma.obj (AR.hookWallInteriorPair sigma X.1).1.2.1.1.2)}

/-- Off-diagonal wall terms with noninjective common target and a reverse
arrow at the end of the canonical next strip. -/
structure HookWallInteriorReverseLastOffDiagonal where
  term : AR.HookWallInteriorOffDiagonal sigma
  target_noninjective : ¬ Injective
    (sigma.obj (AR.hookWallInteriorPair sigma term.1).1.2.1.1.2)
  last_to_middle : HasIrreducibleMorphism
    (sigma.obj (AR.boundaryM6Last sigma
      (AR.hookWallInteriorPair sigma term.1) target_noninjective))
    (sigma.obj (AR.boundaryM6FirstArrow sigma
      (AR.hookWallInteriorPair sigma term.1)).1.2)

omit [DecidableEq iota] in
@[ext]
theorem HookWallInteriorReverseLastOffDiagonal.ext
    {X Y : AR.HookWallInteriorReverseLastOffDiagonal sigma}
    (hterm : X.term = Y.term) : X = Y := by
  cases X
  cases Y
  cases hterm
  rfl

noncomputable instance hookWallInteriorInjectiveTargetOffDiagonalFintype :
    Fintype (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) :=
  Fintype.ofFinite _

omit [Fintype iota] in
noncomputable instance hookWallInteriorReverseLastOffDiagonalFinite :
    Finite (AR.HookWallInteriorReverseLastOffDiagonal sigma) :=
  Finite.of_injective HookWallInteriorReverseLastOffDiagonal.term (by
    intro X Y h
    exact HookWallInteriorReverseLastOffDiagonal.ext sigma AR h)

noncomputable instance hookWallInteriorReverseLastOffDiagonalFintype :
    Fintype (AR.HookWallInteriorReverseLastOffDiagonal sigma) :=
  Fintype.ofFinite _

/-- The injective-target part of the purely boundary-theoretic
first/second off-diagonal overlap. -/
abbrev BoundaryFirstSecondInjectiveTargetOffDiagonalPair :=
  {p : AR.BoundaryFirstSecondOffDiagonalPair sigma //
    Injective (sigma.obj
      (p.1.1 : AR.InteriorCommonTargetArrowPair sigma).1.2.1.1.2)}

noncomputable instance
    boundaryFirstSecondInjectiveTargetOffDiagonalPairFintype :
    Fintype (AR.BoundaryFirstSecondInjectiveTargetOffDiagonalPair sigma) :=
  Fintype.ofFinite _

include AR in
/-- The general wall occurrence equivalence restricts to the
injective-target exception. -/
def hookWallInteriorInjectiveTargetEquivBoundaryFirstSecond
    {K : Type u} [Field K] [Algebra K R] [FiniteDimensional K R] :
    AR.HookWallInteriorInjectiveTargetOffDiagonal sigma ≃
      AR.BoundaryFirstSecondInjectiveTargetOffDiagonalPair sigma where
  toFun X :=
    ⟨(AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
      (K := K) sigma).toFun X.1, X.2⟩
  invFun p := by
    let X := AR.boundaryWallReconstruction (K := K) sigma p.1
    refine ⟨X.term, ?_⟩
    have htarget := congrArg
      (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.2.1.1.2)
      X.occurrence_eq
    rw [htarget]
    exact p.2
  left_inv X := by
    apply Subtype.ext
    exact (AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
      (K := K) sigma).left_inv X.1
  right_inv p := by
    apply Subtype.ext
    exact (AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
      (K := K) sigma).right_inv p.1

/-- Injective-target first-layer pairs whose second occurrence is also in
the first two source layers. -/
abbrev BoundaryM6InjectiveTargetSecondSourcePair :=
  {p : AR.BoundaryM6InjectiveTargetPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

abbrev BoundaryM6InjectiveTargetSecondSourceDiagonalPair :=
  {p : AR.BoundaryM6InjectiveTargetSecondSourcePair sigma //
    p.1.pair.1.1 = p.1.pair.1.2}

abbrev BoundaryM6InjectiveTargetSecondSourceOffDiagonalPair :=
  {p : AR.BoundaryM6InjectiveTargetSecondSourcePair sigma //
    p.1.pair.1.1 ≠ p.1.pair.1.2}

noncomputable instance boundaryM6InjectiveTargetSecondSourcePairFintype :
    Fintype (AR.BoundaryM6InjectiveTargetSecondSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    boundaryM6InjectiveTargetSecondSourceDiagonalPairFintype :
    Fintype (AR.BoundaryM6InjectiveTargetSecondSourceDiagonalPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    boundaryM6InjectiveTargetSecondSourceOffDiagonalPairFintype :
    Fintype (AR.BoundaryM6InjectiveTargetSecondSourceOffDiagonalPair sigma) :=
  Fintype.ofFinite _

/-- Split all injective-target first-layer pairs according to whether the
second occurrence is also on the source boundary. -/
def boundaryM6InjectiveTargetPairEquivFirstOnlySumSecondSource :
    AR.BoundaryM6InjectiveTargetPair sigma ≃
      AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma ⊕
        AR.BoundaryM6InjectiveTargetSecondSourcePair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · exact Sum.inr ⟨p, h⟩
    · exact Sum.inl ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- Split the second-source injective-target family into diagonal and
off-diagonal parts. -/
def boundaryM6InjectiveTargetSecondSourceEquivDiagonalSumOffDiagonal :
    AR.BoundaryM6InjectiveTargetSecondSourcePair sigma ≃
      AR.BoundaryM6InjectiveTargetSecondSourceDiagonalPair sigma ⊕
        AR.BoundaryM6InjectiveTargetSecondSourceOffDiagonalPair sigma where
  toFun p := by
    classical
    by_cases h : p.1.pair.1.1 = p.1.pair.1.2
    · exact Sum.inl ⟨p, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h : p.1.pair.1.1 = p.1.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- Off-diagonal second-source injective-target pairs are the pure boundary
form of injective-target wall exceptions. -/
def boundaryM6InjectiveTargetSecondSourceOffDiagonalEquivFirstSecond :
    AR.BoundaryM6InjectiveTargetSecondSourceOffDiagonalPair sigma ≃
      AR.BoundaryFirstSecondInjectiveTargetOffDiagonalPair sigma where
  toFun p :=
    ⟨⟨⟨p.1.1.pair, p.1.1.first_source⟩, p.1.2, p.2⟩,
      p.1.1.target_injective⟩
  invFun p :=
    ⟨⟨
      { pair := p.1.1.1
        first_source := p.1.1.2
        target_injective := p.2 },
        p.1.2.1⟩,
      p.1.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply BoundaryM6InjectiveTargetPair.ext sigma AR
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [DecidableEq iota] in
include k AR in
/-- Diagonal injective-target first-layer pairs are exactly short
projective strips. -/
def hookShortStripEquivM6InjectiveTargetSecondSourceDiagonal :
    AR.HookShortStrip sigma ≃
      AR.BoundaryM6InjectiveTargetSecondSourceDiagonalPair sigma where
  toFun T := by
    let M := AR.arMeshRotationData sigma
    let H : M.InteriorArrow sigma :=
      ⟨T.1.firstArrow sigma AR, by
        exact ⟨by
          simpa [StripAdmissibleTriple.firstArrow] using
            T.1.u_nonprojective,
          by simpa [StripAdmissibleTriple.firstArrow] using
            T.1.a_noninjective sigma AR⟩⟩
    let P : AR.InteriorCommonTargetArrowPair sigma := ⟨(H, H), rfl⟩
    have hfirst := (M.arrowInterior_source_iff sigma H).2 (by
      simpa [H, StripAdmissibleTriple.firstArrow] using T.2.1)
    let X : AR.BoundaryM6InjectiveTargetPair sigma :=
      { pair := P
        first_source := hfirst
        target_injective := by
          simpa [P, H, StripAdmissibleTriple.firstArrow] using T.2.2 }
    exact ⟨⟨X, Or.inl hfirst⟩, rfl⟩
  invFun p := by
    let H := p.1.1.pair.1.1
    have hP : Projective (sigma.obj H.1.1.1) :=
      ((AR.arMeshRotationData sigma).arrowInterior_source_iff
        sigma H).1 p.1.1.first_source
    let T := stripTripleOfProjectiveArrow (k := k) sigma AR H.1
      hP H.2.2 H.2.1
    refine ⟨T, hP, ?_⟩
    change Injective (sigma.obj H.1.1.2)
    have htargets : H.1.1.2 = p.1.1.pair.1.2.1.1.2 :=
      congrArg
        (fun q : (AR.arMeshRotationData sigma).InteriorArrow sigma ↦
          q.1.1.2) p.2
    rw [htargets]
    exact p.1.1.target_injective
  left_inv T := by
    apply Subtype.ext
    apply StripAdmissibleTriple.firstArrow_injective sigma AR
    exact stripTripleOfProjectiveArrow_firstArrow
      (k := k) sigma AR (T.1.firstArrow sigma AR) T.2.1
        (T.1.a_noninjective sigma AR) T.1.u_nonprojective
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply BoundaryM6InjectiveTargetPair.ext sigma AR
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR p.1.1.pair.1.1.1
          (((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.pair.1.1).1 p.1.1.first_source)
          p.1.1.pair.1.1.2.2 p.1.1.pair.1.1.2.1
    · apply Subtype.ext
      exact (stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR p.1.1.pair.1.1.1
          (((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.pair.1.1).1 p.1.1.first_source)
          p.1.1.pair.1.1.2.2 p.1.1.pair.1.1.2.1).trans
            (congrArg Subtype.val p.2)

include k AR in
/-- All injective-target first-layer exceptions split into the first-only
part, short strips on the diagonal, and injective-target off-diagonal wall
exceptions. -/
theorem boundaryM6InjectiveTargetPair_card_eq_firstOnly_add_short_add_wall :
    Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) =
      Fintype.card (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
        Fintype.card (AR.HookShortStrip sigma) +
          Fintype.card
            (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) := by
  have hall :
      Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) =
        Fintype.card (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
          Fintype.card
            (AR.BoundaryM6InjectiveTargetSecondSourcePair sigma) := by
    rw [Fintype.card_congr
      (AR.boundaryM6InjectiveTargetPairEquivFirstOnlySumSecondSource sigma)]
    exact Fintype.card_sum
  have hsecond :
      Fintype.card (AR.BoundaryM6InjectiveTargetSecondSourcePair sigma) =
        Fintype.card
            (AR.BoundaryM6InjectiveTargetSecondSourceDiagonalPair sigma) +
          Fintype.card
            (AR.BoundaryM6InjectiveTargetSecondSourceOffDiagonalPair sigma) := by
    rw [Fintype.card_congr
      (AR.boundaryM6InjectiveTargetSecondSourceEquivDiagonalSumOffDiagonal
        sigma)]
    exact Fintype.card_sum
  have hdiag := Fintype.card_congr
    (AR.hookShortStripEquivM6InjectiveTargetSecondSourceDiagonal
      (k := k) sigma)
  have hoffBoundary := Fintype.card_congr
    (AR.boundaryM6InjectiveTargetSecondSourceOffDiagonalEquivFirstSecond
      sigma)
  have hoffWall := Fintype.card_congr
    (AR.hookWallInteriorInjectiveTargetEquivBoundaryFirstSecond
      (K := k) sigma)
  omega

/-- Pure boundary form of a reverse-last-arrow off-diagonal overlap. -/
structure BoundaryFirstSecondReverseLastOffDiagonalPair where
  term : AR.BoundaryFirstSecondOffDiagonalPair sigma
  target_noninjective : ¬ Injective
    (sigma.obj (term.1.1 :
      AR.InteriorCommonTargetArrowPair sigma).1.2.1.1.2)
  last_to_middle : HasIrreducibleMorphism
    (sigma.obj (AR.boundaryM6Last sigma term.1.1 target_noninjective))
    (sigma.obj (AR.boundaryM6FirstArrow sigma term.1.1).1.2)

omit [DecidableEq iota] in
@[ext]
theorem BoundaryFirstSecondReverseLastOffDiagonalPair.ext
    {X Y : AR.BoundaryFirstSecondReverseLastOffDiagonalPair sigma}
    (hterm : X.term = Y.term) : X = Y := by
  cases X
  cases Y
  cases hterm
  rfl

omit [Fintype iota] in
noncomputable instance boundaryFirstSecondReverseLastOffDiagonalPairFinite :
    Finite (AR.BoundaryFirstSecondReverseLastOffDiagonalPair sigma) :=
  Finite.of_injective BoundaryFirstSecondReverseLastOffDiagonalPair.term (by
    intro X Y h
    exact BoundaryFirstSecondReverseLastOffDiagonalPair.ext sigma AR h)

noncomputable instance boundaryFirstSecondReverseLastOffDiagonalPairFintype :
    Fintype (AR.BoundaryFirstSecondReverseLastOffDiagonalPair sigma) :=
  Fintype.ofFinite _

include AR in
/-- The general wall occurrence equivalence restricts to the
reverse-last-arrow exception. -/
def hookWallInteriorReverseLastEquivBoundaryFirstSecond
    {K : Type u} [Field K] [Algebra K R] [FiniteDimensional K R] :
    AR.HookWallInteriorReverseLastOffDiagonal sigma ≃
      AR.BoundaryFirstSecondReverseLastOffDiagonalPair sigma where
  toFun X :=
    { term := (AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
        (K := K) sigma).toFun X.term
      target_noninjective := X.target_noninjective
      last_to_middle := X.last_to_middle }
  invFun p := by
    let X := AR.boundaryWallReconstruction (K := K) sigma p.term
    have htarget := congrArg
      (fun q : AR.InteriorCommonTargetArrowPair sigma ↦ q.1.2.1.1.2)
      X.occurrence_eq
    have hNI : ¬ Injective
        (sigma.obj (AR.hookWallInteriorPair sigma X.term.1).1.2.1.1.2) := by
      rw [htarget]
      exact p.target_noninjective
    have hfirst := congrArg (AR.boundaryM6FirstArrow sigma)
      X.occurrence_eq
    have hlast : AR.boundaryM6Last sigma
          (AR.hookWallInteriorPair sigma X.term.1) hNI =
        AR.boundaryM6Last sigma p.term.1.1 p.target_noninjective := by
      unfold boundaryM6Last
      have hinput :
          (⟨(AR.hookWallInteriorPair sigma X.term.1).1.2.1.1.2,
              hNI⟩ : sigma.NoninjectiveLabel) =
            ⟨p.term.1.1.1.2.1.1.2, p.target_noninjective⟩ := by
        apply Subtype.ext
        exact htarget
      exact congrArg Subtype.val
        (congrArg (AR.arTranslationEquiv sigma).symm hinput)
    exact
      { term := X.term
        target_noninjective := hNI
        last_to_middle := by
          simpa only [hlast, hfirst] using p.last_to_middle }
  left_inv X := by
    apply HookWallInteriorReverseLastOffDiagonal.ext sigma AR
    exact (AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
      (K := K) sigma).left_inv X.term
  right_inv p := by
    apply BoundaryFirstSecondReverseLastOffDiagonalPair.ext sigma AR
    exact (AR.hookWallInteriorOffDiagonalEquivBoundaryFirstSecond
      (K := K) sigma).right_inv p.term

/-- Reverse-last-arrow first-layer pairs whose second occurrence is also
in the first two source layers. -/
abbrev BoundaryM6ReverseLastSecondSourcePair :=
  {p : AR.BoundaryM6ReverseLastPair sigma //
    ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
      p.pair.1.2}

abbrev BoundaryM6ReverseLastSecondSourceOffDiagonalPair :=
  {p : AR.BoundaryM6ReverseLastSecondSourcePair sigma //
    p.1.pair.1.1 ≠ p.1.pair.1.2}

noncomputable instance boundaryM6ReverseLastSecondSourcePairFintype :
    Fintype (AR.BoundaryM6ReverseLastSecondSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    boundaryM6ReverseLastSecondSourceOffDiagonalPairFintype :
    Fintype (AR.BoundaryM6ReverseLastSecondSourceOffDiagonalPair sigma) :=
  Fintype.ofFinite _

include k AR in
/-- A reverse-last-arrow exception whose second occurrence is also on the
source boundary cannot be diagonal.  On the diagonal the projective-arrow
reconstruction is a continuing strip, whose canonical last label has no
arrow back to the middle label. -/
theorem boundaryM6ReverseLastSecondSourcePair_offDiagonal
    (p : AR.BoundaryM6ReverseLastSecondSourcePair sigma) :
    p.1.pair.1.1 ≠ p.1.pair.1.2 := by
  intro hdiagonal
  let H := p.1.pair.1.1
  have hP : Projective (sigma.obj H.1.1.1) :=
    ((AR.arMeshRotationData sigma).arrowInterior_source_iff
      sigma H).1 p.1.first_source
  let T := stripTripleOfProjectiveArrow (k := k) sigma AR H.1
    hP H.2.2 H.2.1
  let C : AR.HookDiagonalCandidate sigma :=
    ⟨T, hP, by
      change ¬ Injective (sigma.obj H.1.1.2)
      have htargets : H.1.1.2 = p.1.pair.1.2.1.1.2 :=
        congrArg
          (fun q : (AR.arMeshRotationData sigma).InteriorArrow sigma ↦
            q.1.1.2) hdiagonal
      rw [htargets]
      exact p.1.target_noninjective⟩
  let q := (AR.hookDiagonalCandidateEquivM6RegularSecondSourceDiagonal
    (k := k) sigma).toFun C
  have hpair : q.1.1.pair = p.1.pair := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR H.1 hP H.2.2 H.2.1
    · apply Subtype.ext
      exact (stripTripleOfProjectiveArrow_firstArrow
        (k := k) sigma AR H.1 hP H.2.2 H.2.1).trans
          (congrArg Subtype.val hdiagonal)
  have hfirst := congrArg (AR.boundaryM6FirstArrow sigma) hpair
  have hlast : AR.boundaryM6Last sigma q.1.1.pair
        q.1.1.target_noninjective =
      AR.boundaryM6Last sigma p.1.pair p.1.target_noninjective := by
    unfold boundaryM6Last
    have hinput :
        (⟨q.1.1.pair.1.2.1.1.2,
            q.1.1.target_noninjective⟩ : sigma.NoninjectiveLabel) =
          ⟨p.1.pair.1.2.1.1.2, p.1.target_noninjective⟩ := by
      apply Subtype.ext
      exact congrArg
        (fun x : AR.InteriorCommonTargetArrowPair sigma ↦
          x.1.2.1.1.2) hpair
    exact congrArg Subtype.val
      (congrArg (AR.arTranslationEquiv sigma).symm hinput)
  exact q.1.1.last_not_to_middle (by
    simpa only [hlast, hfirst] using p.1.last_to_middle)

include k AR in
/-- Every second-source reverse-last-arrow exception is off-diagonal. -/
def boundaryM6ReverseLastSecondSourceEquivOffDiagonal :
    AR.BoundaryM6ReverseLastSecondSourcePair sigma ≃
      AR.BoundaryM6ReverseLastSecondSourceOffDiagonalPair sigma where
  toFun p :=
    ⟨p, AR.boundaryM6ReverseLastSecondSourcePair_offDiagonal
      (k := k) sigma p⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Off-diagonal second-source reverse-last pairs are the pure boundary
form of reverse-last wall exceptions. -/
def boundaryM6ReverseLastSecondSourceOffDiagonalEquivFirstSecond :
    AR.BoundaryM6ReverseLastSecondSourceOffDiagonalPair sigma ≃
      AR.BoundaryFirstSecondReverseLastOffDiagonalPair sigma where
  toFun p :=
    { term := ⟨⟨p.1.1.pair, p.1.1.first_source⟩, p.1.2, p.2⟩
      target_noninjective := p.1.1.target_noninjective
      last_to_middle := p.1.1.last_to_middle }
  invFun p :=
    ⟨⟨
      { pair := p.term.1.1
        first_source := p.term.1.2
        target_noninjective := p.target_noninjective
        last_to_middle := p.last_to_middle },
        p.term.2.1⟩,
      p.term.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply BoundaryM6ReverseLastPair.ext sigma AR
    rfl
  right_inv p := by
    apply BoundaryFirstSecondReverseLastOffDiagonalPair.ext sigma AR
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Split all reverse-last-arrow first-layer pairs according to whether
the second occurrence is also on the source boundary. -/
def boundaryM6ReverseLastPairEquivFirstOnlySumSecondSource :
    AR.BoundaryM6ReverseLastPair sigma ≃
      AR.BoundaryM6ReverseLastFirstOnlyPair sigma ⊕
        AR.BoundaryM6ReverseLastSecondSourcePair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · exact Sum.inr ⟨p, h⟩
    · exact Sum.inl ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).TwoSource
          p.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

include k AR in
/-- All reverse-last-arrow first-layer exceptions split into the
first-only part and the reverse-last off-diagonal wall exceptions. -/
theorem boundaryM6ReverseLastPair_card_eq_firstOnly_add_wall :
    Fintype.card (AR.BoundaryM6ReverseLastPair sigma) =
      Fintype.card (AR.BoundaryM6ReverseLastFirstOnlyPair sigma) +
        Fintype.card
          (AR.HookWallInteriorReverseLastOffDiagonal sigma) := by
  have hall :
      Fintype.card (AR.BoundaryM6ReverseLastPair sigma) =
        Fintype.card (AR.BoundaryM6ReverseLastFirstOnlyPair sigma) +
          Fintype.card
            (AR.BoundaryM6ReverseLastSecondSourcePair sigma) := by
    rw [Fintype.card_congr
      (AR.boundaryM6ReverseLastPairEquivFirstOnlySumSecondSource sigma)]
    exact Fintype.card_sum
  have hoff := Fintype.card_congr
    (((AR.boundaryM6ReverseLastSecondSourceEquivOffDiagonal
        (k := k) sigma).trans
        (AR.boundaryM6ReverseLastSecondSourceOffDiagonalEquivFirstSecond
          sigma)).trans
        (AR.hookWallInteriorReverseLastEquivBoundaryFirstSecond
          (K := k) sigma).symm)
  omega

/-- The off-diagonal wall family splits exhaustively into its regular,
injective-target, and reverse-last-arrow parts. -/
def hookWallInteriorOffDiagonalEquivRegularSumExceptions :
    AR.HookWallInteriorOffDiagonal sigma ≃
      AR.HookWallInteriorRegularOffDiagonal sigma ⊕
        (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma ⊕
          AR.HookWallInteriorReverseLastOffDiagonal sigma) where
  toFun X := by
    classical
    by_cases hI : Injective
        (sigma.obj (AR.hookWallInteriorPair sigma X.1).1.2.1.1.2)
    · exact Sum.inr (Sum.inl ⟨X, hI⟩)
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma
            (AR.hookWallInteriorPair sigma X.1) hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma
            (AR.hookWallInteriorPair sigma X.1)).1.2)
      · exact Sum.inr (Sum.inr
          { term := X
            target_noninjective := hI
            last_to_middle := hlast })
      · exact Sum.inl
          { term := X
            regular :=
              { pair := AR.hookWallInteriorPair sigma X.1
                first_source := AR.hookWallInteriorPair_firstSource sigma X.1
                target_noninjective := hI
                last_not_to_middle := hlast }
            occurrence_eq := rfl }
  invFun X := by
    rcases X with X | X
    · exact X.term
    · rcases X with X | X
      · exact X.1
      · exact X.term
  left_inv X := by
    classical
    by_cases hI : Injective
        (sigma.obj (AR.hookWallInteriorPair sigma X.1).1.2.1.1.2)
    · simp [hI]
    · by_cases hlast : HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma
            (AR.hookWallInteriorPair sigma X.1) hI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma
            (AR.hookWallInteriorPair sigma X.1)).1.2)
      · simp [hI, hlast]
      · simp [hI, hlast]
  right_inv X := by
    classical
    rcases X with X | X
    · have htarget := congrArg
          (fun p : AR.InteriorCommonTargetArrowPair sigma ↦ p.1.2.1.1.2)
          X.occurrence_eq
      have hNI : ¬ Injective
          (sigma.obj (AR.hookWallInteriorPair sigma X.term.1).1.2.1.1.2) := by
        rw [← htarget]
        exact X.regular.target_noninjective
      have hfirst := congrArg (AR.boundaryM6FirstArrow sigma)
        X.occurrence_eq
      have hlast : AR.boundaryM6Last sigma X.regular.pair
          X.regular.target_noninjective =
          AR.boundaryM6Last sigma
            (AR.hookWallInteriorPair sigma X.term.1) hNI := by
        unfold boundaryM6Last
        have hinput :
            (⟨X.regular.pair.1.2.1.1.2,
                X.regular.target_noninjective⟩ : sigma.NoninjectiveLabel) =
              ⟨(AR.hookWallInteriorPair sigma X.term.1).1.2.1.1.2,
                hNI⟩ := by
          apply Subtype.ext
          exact htarget
        exact congrArg Subtype.val
          (congrArg (AR.arTranslationEquiv sigma).symm hinput)
      have hnot : ¬ HasIrreducibleMorphism
          (sigma.obj (AR.boundaryM6Last sigma
            (AR.hookWallInteriorPair sigma X.term.1) hNI))
          (sigma.obj (AR.boundaryM6FirstArrow sigma
            (AR.hookWallInteriorPair sigma X.term.1)).1.2) := by
        simpa only [hlast, hfirst] using X.regular.last_not_to_middle
      simp only [hNI, dite_false, hnot]
      apply congrArg Sum.inl
      apply HookWallInteriorRegularOffDiagonal.ext sigma AR
      rfl
    · rcases X with X | X
      · simp [X.2]
      · simp [X.target_noninjective, X.last_to_middle]

/-- Split the regular overlap into diagonal candidates and its
off-diagonal part. -/
def boundaryM6RegularSecondSourcePairEquivDiagonalSumOffDiagonal :
    AR.BoundaryM6RegularSecondSourcePair sigma ≃
      AR.BoundaryM6RegularSecondSourceDiagonalPair sigma ⊕
        AR.BoundaryM6RegularSecondSourceOffDiagonalPair sigma where
  toFun p := by
    classical
    by_cases h : p.1.pair.1.1 = p.1.pair.1.2
    · exact Sum.inl ⟨p, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h : p.1.pair.1.1 = p.1.pair.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

include k AR in
/-- Exact local trimmed-boundary channel equation.  The only uncancelled
corrections are the continuing diagonal candidates, two copies of all
projective strips, and the four explicit endpoint/reverse exceptions. -/
theorem interiorSourceBoundary_local_channel_card_identity :
    Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) +
          Fintype.card (HookM6Channel.InteriorChannel sigma AR) +
        2 * Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} +
      Fintype.card (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
      Fintype.card (AR.BoundaryM6ReverseLastFirstOnlyPair sigma) +
      Fintype.card (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) +
      Fintype.card (AR.HookWallInteriorReverseLastOffDiagonal sigma) =
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) +
      Fintype.card (AR.HookDiagonalCandidate sigma) +
        Fintype.card (AR.HookWallInteriorSum sigma) := by
  have hbase :=
    AR.interiorSourceBoundary_add_m6Overlap_card_eq_channels_add_corrections
      (k := k) sigma
  have hoverlap :
      Fintype.card (AR.BoundaryM6RegularSecondSourcePair sigma) =
        Fintype.card (AR.HookDiagonalCandidate sigma) +
          Fintype.card (AR.HookWallInteriorRegularOffDiagonal sigma) := by
    have hsplit :
        Fintype.card (AR.BoundaryM6RegularSecondSourcePair sigma) =
          Fintype.card
              (AR.BoundaryM6RegularSecondSourceDiagonalPair sigma) +
            Fintype.card
              (AR.BoundaryM6RegularSecondSourceOffDiagonalPair sigma) := by
      rw [Fintype.card_congr
        (AR.boundaryM6RegularSecondSourcePairEquivDiagonalSumOffDiagonal
          sigma)]
      exact Fintype.card_sum
    have hdiag := Fintype.card_congr
      (AR.hookDiagonalCandidateEquivM6RegularSecondSourceDiagonal
        (k := k) sigma)
    have hoff := Fintype.card_congr
      (AR.hookWallInteriorRegularOffDiagonalEquivM6Overlap
        (k := k) sigma)
    omega
  have hoffwall :
      Fintype.card (AR.HookWallInteriorOffDiagonal sigma) =
        Fintype.card (AR.HookWallInteriorRegularOffDiagonal sigma) +
          (Fintype.card
              (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) +
            Fintype.card
              (AR.HookWallInteriorReverseLastOffDiagonal sigma)) := by
    rw [Fintype.card_congr
      (AR.hookWallInteriorOffDiagonalEquivRegularSumExceptions sigma)]
    simp only [Fintype.card_sum]
  have hwall :=
    AR.hookWallInteriorSum_card_eq_projectiveStrip_add_offDiagonal sigma
  omega

include k AR in
/-- Clean local form of the trimmed boundary classification.  After the
diagonal and off-diagonal overlap corrections are recombined, the two
trimmed positive channels together with the full projective, injective-target,
and reverse-last boundary strata equal the shifted source boundary plus the
two trimmed negative channels. -/
theorem interiorSourceBoundary_clean_local_channel_card_identity :
    Fintype.card (HookM5Preliminary.InteriorChannel sigma AR) +
        Fintype.card (HookM6Channel.InteriorChannel sigma AR) +
      Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} +
        Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) +
          Fintype.card (AR.BoundaryM6ReverseLastPair sigma) =
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) +
      Fintype.card (AR.HookWallInteriorSum sigma) := by
  have hlocal := AR.interiorSourceBoundary_local_channel_card_identity
    (k := k) sigma
  have hinjective :=
    AR.boundaryM6InjectiveTargetPair_card_eq_firstOnly_add_short_add_wall
      (k := k) sigma
  have hreverse :=
    AR.boundaryM6ReverseLastPair_card_eq_firstOnly_add_wall
      (k := k) sigma
  have hprojective :
      Fintype.card
          {T : AR.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} =
        Fintype.card (AR.HookDiagonalCandidate sigma) +
          Fintype.card (AR.HookShortStrip sigma) := by
    rw [Fintype.card_congr
      (projectiveStripEquivDiagonalCandidateSumShort sigma AR)]
    exact Fintype.card_sum
  omega

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
