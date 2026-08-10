import OpConjecture.RepresentationTheory.FourVertexFullBoundaryIncidence
import OpConjecture.RepresentationTheory.FourVertexBoundaryEndpointTransport

/-!
# Endpoint strata of the full four-vertex arrow boundary

The nonprojective-target/projective-source corner consists of the trimmed
literal-source common-target layer and the complementary pairs having an
injective source.  Aligned duality identifies the projective-target
common-source corner with common-target pairs having an injective source on
the opposite skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (AR : sigma.FiniteARTranslationData)

/-- The full projective-source corner whose two sources are both
noninjective. -/
abbrev NonprojectiveTargetProjectiveSourceNoninjectivePair :=
  {p : NonprojectiveTargetProjectiveSourcePair sigma //
    ¬ Injective (sigma.obj p.1.1.1.1.1) ∧
      ¬ Injective (sigma.obj p.1.1.2.1.1)}

/-- The genuinely outer part of the full projective-source corner: at
least one source is injective. -/
abbrev NonprojectiveTargetProjectiveInjectiveSourcePair :=
  {p : NonprojectiveTargetProjectiveSourcePair sigma //
    Injective (sigma.obj p.1.1.1.1.1) ∨
      Injective (sigma.obj p.1.1.2.1.1)}

noncomputable instance
    nonprojectiveTargetProjectiveSourceNoninjectivePairFintype :
    Fintype (NonprojectiveTargetProjectiveSourceNoninjectivePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    nonprojectiveTargetProjectiveInjectiveSourcePairFintype :
    Fintype (NonprojectiveTargetProjectiveInjectiveSourcePair sigma) :=
  Fintype.ofFinite _

/-- The full-orbit different-component refinement of the trimmed literal
source layer.  The predicate is deliberately measured before trimming. -/
abbrev FullOrbitDifferentInteriorLiteralSourceCommonTargetPair :=
  {p : AR.InteriorLiteralSourceCommonTargetPair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.2.1}

/-- Different-component part of the outer projective/injective-source
intersection. -/
abbrev DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair :=
  {p : NonprojectiveTargetProjectiveInjectiveSourcePair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2}

noncomputable instance
    fullOrbitDifferentInteriorLiteralSourceCommonTargetPairFintype :
    Fintype
      (AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitNonprojectiveTargetProjectiveInjectiveSourcePairFintype :
    Fintype
      (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
        sigma) :=
  Fintype.ofFinite _

/-- Split the full projective-source corner according to whether an arrow
source is injective. -/
def nonprojectiveTargetProjectiveSourceEquivNoninjectiveSumInjective :
    NonprojectiveTargetProjectiveSourcePair sigma ≃
      NonprojectiveTargetProjectiveSourceNoninjectivePair sigma ⊕
        NonprojectiveTargetProjectiveInjectiveSourcePair sigma where
  toFun p := by
    classical
    by_cases h : Injective (sigma.obj p.1.1.1.1.1) ∨
        Injective (sigma.obj p.1.1.2.1.1)
    · exact Sum.inr ⟨p, h⟩
    · exact Sum.inl ⟨p, not_or.mp h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h : Injective (sigma.obj p.1.1.1.1.1) ∨
        Injective (sigma.obj p.1.1.2.1.1)
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · have h : ¬ (Injective (sigma.obj p.1.1.1.1.1.1) ∨
          Injective (sigma.obj p.1.1.1.2.1.1)) := not_or.mpr p.2
      simp [h]
    · by_cases hfirst : Injective (sigma.obj p.1.1.1.1.1.1)
      · simp [hfirst]
      · have hsecond := p.2.resolve_left hfirst
        simp [hfirst, hsecond]

omit [DecidableEq iota] in
/-- Forgetting the interior witnesses identifies the noninjective-source
part of the full corner with the trimmed literal source layer. -/
def nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral :
    NonprojectiveTargetProjectiveSourceNoninjectivePair sigma ≃
      AR.InteriorLiteralSourceCommonTargetPair sigma where
  toFun p := by
    let A := toInteriorArrow sigma AR p.1.1.1.1
      ⟨p.1.2.1, p.2.1⟩
    let B := toInteriorArrow sigma AR p.1.1.1.2
      ⟨by
        intro hp
        apply p.1.2.1
        rw [p.1.1.2]
        exact hp,
       p.2.2⟩
    refine ⟨⟨(A, B), p.1.1.2⟩, ?_⟩
    rcases p.1.2.2 with h | h
    · exact Or.inl <|
        ((AR.arMeshRotationData sigma).arrowInterior_source_iff sigma A).2 h
    · exact Or.inr <|
        ((AR.arMeshRotationData sigma).arrowInterior_source_iff sigma B).2 h
  invFun p := by
    let q := forgetInteriorCommonTarget sigma AR p.1
    refine ⟨⟨q, ?_, ?_⟩, ?_, ?_⟩
    · exact p.1.1.1.2.1
    · rcases p.2 with h | h
      · exact Or.inl <|
          ((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.1).1 h
      · exact Or.inr <|
          ((AR.arMeshRotationData sigma).arrowInterior_source_iff
            sigma p.1.1.2).1 h
    · exact p.1.1.1.2.2
    · exact p.1.1.2.2.2
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl

omit [DecidableEq iota] in
/-- Cardinal form of the exact full-to-trim projective-source split. -/
theorem nonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer :
    Fintype.card (NonprojectiveTargetProjectiveSourcePair sigma) =
      Fintype.card (AR.InteriorLiteralSourceCommonTargetPair sigma) +
        Fintype.card
          (NonprojectiveTargetProjectiveInjectiveSourcePair sigma) := by
  have hsplit := Fintype.card_congr
    (nonprojectiveTargetProjectiveSourceEquivNoninjectiveSumInjective sigma)
  have hinterior := Fintype.card_congr
    (AR.nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral
      sigma)
  simp only [Fintype.card_sum] at hsplit
  omega

/-- The full projective-source corner decomposition restricts exactly to
different full arrow components. -/
def differentOrbitNonprojectiveTargetProjectiveSourceEquivInteriorLiteralSumOuter :
    AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma ≃
      AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma ⊕
        AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
          sigma := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let E₀ := nonprojectiveTargetProjectiveSourceEquivNoninjectiveSumInjective
    sigma
  let E₁ := Equiv.sumCongr
    (AR.nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral
      sigma)
    (Equiv.refl (NonprojectiveTargetProjectiveInjectiveSourcePair sigma))
  let E := E₀.trans E₁
  let P : NonprojectiveTargetProjectiveSourcePair sigma → Prop :=
    fun p ↦ ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
  let Q : AR.InteriorLiteralSourceCommonTargetPair sigma ⊕
      NonprojectiveTargetProjectiveInjectiveSourcePair sigma → Prop
    | Sum.inl p =>
        ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.2.1
    | Sum.inr p =>
        ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    by_cases h : Injective (sigma.obj p.1.1.1.1.1) ∨
        Injective (sigma.obj p.1.1.2.1.1)
    · simp [P, Q, E, E₀, E₁,
        nonprojectiveTargetProjectiveSourceEquivNoninjectiveSumInjective,
        h]
    · simp [P, Q, E, E₀, E₁,
        nonprojectiveTargetProjectiveSourceEquivNoninjectiveSumInjective,
        nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral,
        toInteriorArrow, h]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q] using F

omit [DecidableEq iota] in
/-- Cardinal form of the different-component full-to-trim corner split. -/
theorem differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer :
    Fintype.card
        (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair sigma) =
      Fintype.card
          (AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair
            sigma) +
        Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            sigma) := by
  rw [Fintype.card_congr
    (AR.differentOrbitNonprojectiveTargetProjectiveSourceEquivInteriorLiteralSumOuter
      sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
include K in
/-- On the literal first interior boundary, deleting the two old endpoints
does not change whether the two labelled arrows lie in the same intrinsic
component. -/
theorem interiorLiteralSource_full_sameSuccessorOrbit_iff
    (p : AR.InteriorLiteralSourceCommonTargetPair sigma) :
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    let U := (AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma
    O.SameSuccessorOrbit p.1.1.1.1 p.1.1.2.1 ↔
      U.SameSuccessorOrbit p.1.1.1 p.1.1.2 := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let U := (AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma
  let A := p.1.1.1
  let B := p.1.1.2
  have hsourceNotTarget : ∀ a : sigma.IrreduciblePair,
      Projective (sigma.obj a.1.2) → ¬ Injective (sigma.obj a.1.1) :=
    fun a ha ↦ arrowToProjective_source_noninjective
      (K := K) sigma a ha
  rcases p.2 with hA | hB
  · have hiff := O.interior_sameSuccessorOrbit_iff_of_mem_source
      hsourceNotTarget A B hA
    simpa [U, O, ARMeshRotationData.arrowInteriorOrbitData] using hiff.symm
  · have hiff := O.interior_sameSuccessorOrbit_iff_of_mem_source
      hsourceNotTarget B A hB
    constructor
    · intro h
      apply U.sameSuccessorOrbit_symm
      apply hiff.mpr
      exact O.sameSuccessorOrbit_symm h
    · intro h
      apply O.sameSuccessorOrbit_symm
      apply hiff.mp
      exact U.sameSuccessorOrbit_symm h

omit [DecidableEq iota] in
include K in
/-- Thus the full-orbit and trimmed-orbit different-component refinements
of the literal source layer are exactly equivalent. -/
def fullOrbitDifferentInteriorLiteralEquivInteriorDifferentOrbitLiteral :
    AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma := by
  apply (Equiv.refl _).subtypeEquiv
  intro p
  exact not_congr <|
    AR.interiorLiteralSource_full_sameSuccessorOrbit_iff
      (K := K) sigma p

omit [DecidableEq iota] in
include K in
/-- Cardinal identification of the full-orbit and trimmed-orbit literal
different-component layers. -/
theorem fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral :
    Fintype.card
        (AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair sigma) =
      Fintype.card
        (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) :=
  Fintype.card_congr
    (AR.fullOrbitDifferentInteriorLiteralEquivInteriorDifferentOrbitLiteral
      (K := K) sigma)

/-- Full common-target pairs having an injective source. -/
abbrev InjectiveSourceCommonTargetPair :=
  {p : CommonTargetArrowPair sigma //
    Injective (sigma.obj p.1.1.1.1) ∨
      Injective (sigma.obj p.1.2.1.1)}

noncomputable instance injectiveSourceCommonTargetPairFintype :
    Fintype (InjectiveSourceCommonTargetPair sigma) := Fintype.ofFinite _

/-- Injective-source common-target pairs which also have a projective
source. -/
abbrev InjectiveSourceProjectiveSourceCommonTargetPair :=
  {p : InjectiveSourceCommonTargetPair sigma //
    Projective (sigma.obj p.1.1.1.1.1) ∨
      Projective (sigma.obj p.1.1.2.1.1)}

/-- Injective-source common-target pairs with no projective source. -/
abbrev InjectiveSourceNoProjectiveSourceCommonTargetPair :=
  {p : InjectiveSourceCommonTargetPair sigma //
    ¬ (Projective (sigma.obj p.1.1.1.1.1) ∨
      Projective (sigma.obj p.1.1.2.1.1))}

noncomputable instance
    injectiveSourceProjectiveSourceCommonTargetPairFintype :
    Fintype (InjectiveSourceProjectiveSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    injectiveSourceNoProjectiveSourceCommonTargetPairFintype :
    Fintype (InjectiveSourceNoProjectiveSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

/-- Different-component part of the full injective-source endpoint. -/
abbrev DifferentOrbitInjectiveSourceCommonTargetPair :=
  {p : InjectiveSourceCommonTargetPair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Different-component part of the projective/injective-source
intersection, viewed from the injective-source endpoint. -/
abbrev DifferentOrbitInjectiveSourceProjectiveSourceCommonTargetPair :=
  {p : InjectiveSourceProjectiveSourceCommonTargetPair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2}

/-- Different-component injective-source endpoints having no projective
source. -/
abbrev DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair :=
  {p : InjectiveSourceNoProjectiveSourceCommonTargetPair sigma //
    let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
    ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2}

noncomputable instance
    differentOrbitInjectiveSourceCommonTargetPairFintype :
    Fintype (AR.DifferentOrbitInjectiveSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitInjectiveSourceProjectiveSourceCommonTargetPairFintype :
    Fintype
      (AR.DifferentOrbitInjectiveSourceProjectiveSourceCommonTargetPair
        sigma) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPairFintype :
    Fintype
      (AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
        sigma) :=
  Fintype.ofFinite _

/-- Split injective-source pairs according to whether a projective source
also occurs. -/
def injectiveSourceCommonTargetEquivProjectiveSumNoProjective :
    InjectiveSourceCommonTargetPair sigma ≃
      InjectiveSourceProjectiveSourceCommonTargetPair sigma ⊕
        InjectiveSourceNoProjectiveSourceCommonTargetPair sigma where
  toFun p := by
    classical
    by_cases h : Projective (sigma.obj p.1.1.1.1.1) ∨
        Projective (sigma.obj p.1.1.2.1.1)
    · exact Sum.inl ⟨p, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h : Projective (sigma.obj p.1.1.1.1.1) ∨
        Projective (sigma.obj p.1.1.2.1.1)
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · by_cases hfirst : Projective (sigma.obj p.1.1.1.1.1.1)
      · simp [hfirst]
      · have hsecond := p.2.resolve_left hfirst
        simp [hfirst, hsecond]
    · have h : ¬ (Projective (sigma.obj p.1.1.1.1.1.1) ∨
          Projective (sigma.obj p.1.1.1.2.1.1)) := p.2
      simp [h]

/-- The projective/no-projective split of the injective-source endpoint
restricts exactly to different full arrow components. -/
def differentOrbitInjectiveSourceCommonTargetEquivProjectiveSumNoProjective :
    AR.DifferentOrbitInjectiveSourceCommonTargetPair sigma ≃
      AR.DifferentOrbitInjectiveSourceProjectiveSourceCommonTargetPair
          sigma ⊕
        AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
          sigma := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let E := injectiveSourceCommonTargetEquivProjectiveSumNoProjective sigma
  let P : InjectiveSourceCommonTargetPair sigma → Prop :=
    fun p ↦ ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
  let Q : InjectiveSourceProjectiveSourceCommonTargetPair sigma ⊕
      InjectiveSourceNoProjectiveSourceCommonTargetPair sigma → Prop
    | Sum.inl p =>
        ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2
    | Sum.inr p =>
        ¬ O.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    by_cases h : Projective (sigma.obj p.1.1.1.1.1) ∨
        Projective (sigma.obj p.1.1.2.1.1)
    · simp [P, Q, E,
        injectiveSourceCommonTargetEquivProjectiveSumNoProjective, h]
    · simp [P, Q, E,
        injectiveSourceCommonTargetEquivProjectiveSumNoProjective, h]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q] using F

omit [DecidableEq iota] in
include K in
/-- The injective/projective source intersection is exactly the outer
part of the nonprojective-target/projective-source corner. -/
def injectiveSourceProjectiveSourceEquivOuterIntersection :
    InjectiveSourceProjectiveSourceCommonTargetPair sigma ≃
      NonprojectiveTargetProjectiveInjectiveSourcePair sigma where
  toFun p := by
    let q := p.1.1
    have ht : ¬ Projective (sigma.obj q.1.1.1.2) := by
      intro htarget
      rcases p.1.2 with h | h
      · exact arrowToProjective_source_noninjective
          (K := K) sigma q.1.1 htarget h
      · apply arrowToProjective_source_noninjective
          (K := K) sigma q.1.2
        · rw [← q.2]
          exact htarget
        · exact h
    exact ⟨⟨q, ht, p.2⟩, p.1.2⟩
  invFun p :=
    ⟨⟨p.1.1, p.2⟩, p.1.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [DecidableEq iota] in
include K in
/-- The two presentations of the projective/injective-source intersection
remain equivalent after restriction to different full arrow components. -/
def differentOrbitInjectiveSourceProjectiveSourceEquivOuterIntersection :
    AR.DifferentOrbitInjectiveSourceProjectiveSourceCommonTargetPair sigma ≃
      AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
        sigma := by
  let E := injectiveSourceProjectiveSourceEquivOuterIntersection
    (K := K) sigma
  apply E.subtypeEquiv
  intro p
  rfl

omit [DecidableEq iota] in
include K in
/-- Cardinal split of the injective-source endpoint on different full
arrow components. -/
theorem differentOrbitInjectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective :
    Fintype.card
        (AR.DifferentOrbitInjectiveSourceCommonTargetPair sigma) =
      Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            sigma) +
        Fintype.card
          (AR.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            sigma) := by
  have hsplit := Fintype.card_congr
    (AR.differentOrbitInjectiveSourceCommonTargetEquivProjectiveSumNoProjective
      sigma)
  have hintersection := Fintype.card_congr
    (AR.differentOrbitInjectiveSourceProjectiveSourceEquivOuterIntersection
      (K := K) sigma)
  simp only [Fintype.card_sum] at hsplit
  omega

omit [DecidableEq iota] in
include K in
/-- Cardinal split of the full injective-source endpoint family. -/
theorem injectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective :
    Fintype.card (InjectiveSourceCommonTargetPair sigma) =
      Fintype.card
          (NonprojectiveTargetProjectiveInjectiveSourcePair sigma) +
        Fintype.card
          (InjectiveSourceNoProjectiveSourceCommonTargetPair sigma) := by
  have hsplit := Fintype.card_congr
    (injectiveSourceCommonTargetEquivProjectiveSumNoProjective sigma)
  have hintersection := Fintype.card_congr
    (injectiveSourceProjectiveSourceEquivOuterIntersection
      (K := K) sigma)
  simp only [Fintype.card_sum] at hsplit
  omega

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

namespace OpConjecture.IndecomposableSkeleton.AlignedBiduality

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {iota : Type v} {kappa : Type w} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)
  (D : AlignedBiduality sigma tau)

omit [DecidableEq iota] [DecidableEq kappa] in
include D in
/-- Under aligned duality, a projective target on the source becomes an
injective source in the dual common-target pair. -/
def projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget :
    FiniteARTranslationData.ProjectiveTargetCommonSourcePair sigma ≃
      FiniteARTranslationData.InjectiveSourceCommonTargetPair tau := by
  let E := (D.commonTargetEquivCommonSource sigma tau).symm
  apply E.subtypeEquiv
  intro p
  have hfirst := D.forward.projective_iff_injective_image sigma tau
    p.1.1.1.2
  have hsecond := D.forward.projective_iff_injective_image sigma tau
    p.1.2.1.2
  simpa [E, commonTargetEquivCommonSource, pushforwardIrreduciblePair] using
    or_congr hfirst hsecond

/-- Projective-target/injective-source endpoint transport preserves and
reflects the full intrinsic arrow component. -/
def differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    ARsigma.DifferentOrbitProjectiveTargetCommonSourcePair sigma ≃
      ARtau.DifferentOrbitInjectiveSourceCommonTargetPair tau := by
  let E := projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget
    sigma tau D
  apply E.subtypeEquiv
  intro p
  change (¬ ((ARsigma.arMeshRotationData sigma).arrowOrbitData sigma).SameSuccessorOrbit
      p.1.1.1 p.1.1.2) ↔
    ¬ ((ARtau.arMeshRotationData tau).arrowOrbitData tau).SameSuccessorOrbit
      (E p).1.1.1 (E p).1.1.2
  apply not_congr
  have h := D.pullback_arrowOrbit_sameSuccessorOrbit_iff
    sigma tau ARsigma ARtau (E p).1.1.1 (E p).1.1.2
  simpa [E, projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget,
    commonTargetEquivCommonSource, pushforwardIrreduciblePair,
    pullbackIrreduciblePair] using h.symm

include D in
/-- Cardinal form of different-component projective-target endpoint
transport. -/
theorem differentOrbitProjectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
        (ARsigma.DifferentOrbitProjectiveTargetCommonSourcePair sigma) =
      Fintype.card
        (ARtau.DifferentOrbitInjectiveSourceCommonTargetPair tau) :=
  Fintype.card_congr
    (D.differentOrbitProjectiveTargetCommonSourceEquivInjectiveSourceCommonTarget
      sigma tau ARsigma ARtau)

omit [DecidableEq iota] [DecidableEq kappa] in
/-- Cardinal form of the full literal-source dual endpoint transport. -/
theorem projectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget :
    (D : AlignedBiduality sigma tau) →
    Fintype.card
        (FiniteARTranslationData.ProjectiveTargetCommonSourcePair sigma) =
      Fintype.card
        (FiniteARTranslationData.InjectiveSourceCommonTargetPair tau) := by
  intro D
  exact Fintype.card_congr
    (projectiveTargetCommonSourceEquivInjectiveSourceCommonTarget sigma tau D)

include K D in
/-- Endpoint-stratified form of the aligned full different-component
boundary identity. -/
theorem differentOrbitFullEndpoint_strata_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARsigma.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            sigma) +
      Fintype.card
          (ARtau.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair
            tau) +
        Fintype.card
          (ARtau.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            tau) =
      Fintype.card
          (ARsigma.DifferentOrbitInjectiveSourceCommonTargetPair sigma) +
        Fintype.card
          (ARtau.DifferentOrbitInjectiveSourceCommonTargetPair tau) := by
  have hfull := ARsigma.aligned_differentOrbit_fullEndpoint_card_identity
    (K := K) sigma tau ARtau D
  have hsigma :=
    ARsigma.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      sigma
  have htau :=
    ARtau.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      tau
  have hdualsigma :=
    D.differentOrbitProjectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
      sigma tau ARsigma ARtau
  have hdualtau :=
    D.swap.differentOrbitProjectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
      tau sigma ARtau ARsigma
  omega

include K D in
/-- Cancelling the shared projective/injective-source intersection leaves
the exact full-orbit different-component endpoint identity. -/
theorem differentOrbitFullEndpoint_trimmedLiteral_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARtau.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair
            tau) =
      Fintype.card
          (ARsigma.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            tau) := by
  have hstrata := D.differentOrbitFullEndpoint_strata_card_identity
    (K := K) sigma tau ARsigma ARtau
  have hsigma :=
    ARsigma.differentOrbitInjectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective
      (K := K) sigma
  have htau :=
    ARtau.differentOrbitInjectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective
      (K := K) tau
  omega

include K D in
/-- Manuscript-coordinate form of the full different-component endpoint
identity, with the literal layer measured in the trimmed arrow translation. -/
theorem differentOrbitFullEndpoint_interiorLiteral_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARtau.InteriorDifferentOrbitLiteralSourceCommonTargetPair tau) =
      Fintype.card
          (ARsigma.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            tau) := by
  have hfull := D.differentOrbitFullEndpoint_trimmedLiteral_card_identity
    (K := K) sigma tau ARsigma ARtau
  have hsigma :=
    ARsigma.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) sigma
  have htau :=
    ARtau.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) tau
  omega

include K D in
/-- Oriented endpoint-stratified form of the full different-component
incidence identity.  It keeps the two source-boundary terms instead of
cancelling them, and hence preserves the side on which every outer endpoint
correction occurs. -/
theorem differentOrbitFullEndpoint_oneSide_strata_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARsigma.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            sigma) +
        Fintype.card
          (ARtau.DifferentOrbitSourceBoundaryCommonTargetArrowPair tau) =
      Fintype.card
          (ARsigma.DifferentOrbitSourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card
          (ARtau.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            tau) +
        Fintype.card
          (ARtau.DifferentOrbitInjectiveSourceNoProjectiveSourceCommonTargetPair
            tau) := by
  have hone :=
    ARsigma.aligned_differentOrbit_fullEndpoint_oneSide_card_identity
      (K := K) sigma tau ARtau D
  have hsigma :=
    ARsigma.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      sigma
  have hsource :=
    ARsigma.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) sigma
  have hdual :=
    D.differentOrbitProjectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
      sigma tau ARsigma ARtau
  have htau :=
    ARtau.differentOrbitInjectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective
      (K := K) tau
  omega

omit [DecidableEq iota] [DecidableEq kappa] in
include K D in
/-- Endpoint-stratified form of the aligned full boundary identity.  On
each skeleton the projective-source side is the trimmed literal layer plus
its injective-source complement; the opposite full literal layer becomes
the injective-source common-target family under duality. -/
theorem fullEndpoint_strata_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.InteriorLiteralSourceCommonTargetPair sigma) +
        Fintype.card
          (FiniteARTranslationData.NonprojectiveTargetProjectiveInjectiveSourcePair
            sigma) +
      Fintype.card
          (ARtau.InteriorLiteralSourceCommonTargetPair tau) +
        Fintype.card
          (FiniteARTranslationData.NonprojectiveTargetProjectiveInjectiveSourcePair
            tau) =
      Fintype.card
          (FiniteARTranslationData.InjectiveSourceCommonTargetPair sigma) +
        Fintype.card
          (FiniteARTranslationData.InjectiveSourceCommonTargetPair tau) := by
  have hfull := ARsigma.aligned_fullEndpoint_card_identity
    (K := K) sigma tau ARtau D
  have hsigma :=
    ARsigma.nonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      sigma
  have htau :=
    ARtau.nonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      tau
  have hdualsigma :=
    projectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
      sigma tau D
  have hdualtau :=
    projectiveTargetCommonSource_card_eq_injectiveSourceCommonTarget
      tau sigma D.swap
  omega

omit [DecidableEq iota] [DecidableEq kappa] in
include K D in
/-- After cancelling the common projective/injective-source intersection,
the full endpoint identity compares the two trimmed literal layers with the
two injective-source layers having no projective source. -/
theorem fullEndpoint_trimmedLiteral_card_identity
    (ARsigma : sigma.FiniteARTranslationData)
    (ARtau : tau.FiniteARTranslationData) :
    Fintype.card
          (ARsigma.InteriorLiteralSourceCommonTargetPair sigma) +
        Fintype.card
          (ARtau.InteriorLiteralSourceCommonTargetPair tau) =
      Fintype.card
          (FiniteARTranslationData.InjectiveSourceNoProjectiveSourceCommonTargetPair
            sigma) +
        Fintype.card
          (FiniteARTranslationData.InjectiveSourceNoProjectiveSourceCommonTargetPair
            tau) := by
  have hstrata := D.fullEndpoint_strata_card_identity
    (K := K) sigma tau ARsigma ARtau
  have hsigma :=
    FiniteARTranslationData.injectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective
      (K := K) sigma
  have htau :=
    FiniteARTranslationData.injectiveSourceCommonTarget_card_eq_outerIntersection_add_noProjective
      (K := K) tau
  omega

end OpConjecture.IndecomposableSkeleton.AlignedBiduality
