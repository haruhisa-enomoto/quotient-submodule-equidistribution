import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFullBoundaryEndpointStrata

/-!
# Different-orbit target corners of the full four-vertex boundary

The full common-target square shift already restricts to pairs of labelled
arrows in different successor components.  This file refines its target
boundary by the same two endpoint strata used in the unrefined corner
decomposition: injective common target, or noninjective common target with an
injective source.  Combining this with the existing source-corner
classification gives an occurrence-level presentation of the full
different-orbit boundary index.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- Different-component part of the injective-common-target corner. -/
abbrev DifferentOrbitInjectiveTargetCommonTargetPair :=
  {p : InjectiveTargetCommonTargetPair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

/-- Different-component part of the noninjective-target corner having an
injective source. -/
abbrev DifferentOrbitNoninjectiveTargetInjectiveSourcePair :=
  {p : NoninjectiveTargetInjectiveSourcePair σ //
    let O := (AR.arMeshRotationData σ).arrowOrbitData σ
    ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2}

noncomputable instance differentOrbitInjectiveTargetCommonTargetPairFintype :
    Fintype (AR.DifferentOrbitInjectiveTargetCommonTargetPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitNoninjectiveTargetInjectiveSourcePairFintype :
    Fintype (AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ) :=
  Fintype.ofFinite _

/-- The fixed projective-source/injective-source outer intersection,
presented inside the full different-orbit target boundary. -/
abbrev DifferentOrbitTargetBoundaryOuterIntersectionPair :=
  {p : AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ //
    ¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
      (Projective (σ.obj p.1.1.1.1.1.1) ∨
        Projective (σ.obj p.1.1.1.2.1.1)) ∧
      (Injective (σ.obj p.1.1.1.1.1.1) ∨
        Injective (σ.obj p.1.1.1.2.1.1))}

/-- The full different-orbit target boundary after deleting its fixed
projective/injective-source intersection. -/
abbrev DifferentOrbitTargetBoundaryNoOuterIntersectionPair :=
  {p : AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ //
    ¬ (¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
      (Projective (σ.obj p.1.1.1.1.1.1) ∨
        Projective (σ.obj p.1.1.1.2.1.1)) ∧
      (Injective (σ.obj p.1.1.1.1.1.1) ∨
        Injective (σ.obj p.1.1.1.2.1.1)))}

/-- The same outer intersection, presented inside the full
different-orbit source boundary. -/
abbrev DifferentOrbitSourceBoundaryOuterIntersectionPair :=
  {p : AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ //
    ¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
      (Projective (σ.obj p.1.1.1.1.1.1) ∨
        Projective (σ.obj p.1.1.1.2.1.1)) ∧
      (Injective (σ.obj p.1.1.1.1.1.1) ∨
        Injective (σ.obj p.1.1.1.2.1.1))}

/-- The full different-orbit source boundary after deleting its
projective/injective-source intersection. -/
abbrev DifferentOrbitSourceBoundaryNoOuterIntersectionPair :=
  {p : AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ //
    ¬ (¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
      (Projective (σ.obj p.1.1.1.1.1.1) ∨
        Projective (σ.obj p.1.1.1.2.1.1)) ∧
      (Injective (σ.obj p.1.1.1.1.1.1) ∨
        Injective (σ.obj p.1.1.1.2.1.1)))}

noncomputable instance
    differentOrbitTargetBoundaryOuterIntersectionPairFintype :
    Fintype (AR.DifferentOrbitTargetBoundaryOuterIntersectionPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitTargetBoundaryNoOuterIntersectionPairFintype :
    Fintype (AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitSourceBoundaryOuterIntersectionPairFintype :
    Fintype (AR.DifferentOrbitSourceBoundaryOuterIntersectionPair σ) :=
  Fintype.ofFinite _

noncomputable instance
    differentOrbitSourceBoundaryNoOuterIntersectionPairFintype :
    Fintype (AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ) :=
  Fintype.ofFinite _

omit [DecidableEq ι] in
/-- A common-target pair having a projective source and an injective source
already lies on both full boundaries, even when the two witnesses occur on
different arrows.  Hence the full square-shift endpoint map fixes it. -/
theorem commonTargetBoundaryEquiv_apply_of_projectiveSource_injectiveSource
    (p : CommonTargetArrowPair σ)
    (hP : Projective (σ.obj p.1.1.1.1) ∨
      Projective (σ.obj p.1.2.1.1))
    (hI : Injective (σ.obj p.1.1.1.1) ∨
      Injective (σ.obj p.1.2.1.1)) :
    (AR.commonTargetBoundaryEquiv σ
      ⟨p, by
        rcases hP with hP | hP
        · exact Or.inl <|
            ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ p.1.1).2 (Or.inr hP)
        · exact Or.inr <|
            ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ p.1.2).2 (Or.inr hP)⟩).1 = p := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let B := O.twoStepProd O
  apply Subtype.ext
  rw [AR.commonTargetBoundaryEquiv_apply_val σ]
  apply B.targetEndpoint_eq_self_of_mem_target
  rcases hI with hI | hI
  · exact Or.inl <|
      ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
        σ p.1.1).2 (Or.inl hI)
  · exact Or.inr <|
      ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
        σ p.1.2).2 (Or.inl hI)

/-- The intrinsic outer corner is also exactly its source-boundary
presentation. -/
def differentOrbitOuterIntersectionEquivSourceBoundaryOuterIntersection :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair σ ≃
      AR.DifferentOrbitSourceBoundaryOuterIntersectionPair σ where
  toFun p := by
    let q := p.1.1.1
    have hsource :
        ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.1 ∨
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.2 := by
      rcases p.1.1.2.2 with h | h
      · exact Or.inl <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ q.1.1).2 (Or.inr h)
      · exact Or.inr <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ q.1.2).2 (Or.inr h)
    exact ⟨⟨⟨q, hsource⟩, p.2⟩,
      p.1.1.2.1, p.1.1.2.2, p.1.2⟩
  invFun p :=
    ⟨⟨⟨p.1.1.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩, p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [DecidableEq ι] in
/-- On the source-boundary presentation of the outer intersection, the
different-orbit square shift retains the underlying ordered common-target
pair. -/
theorem differentOrbitCommonTargetBoundaryEquiv_apply_outerIntersection
    (p : AR.DifferentOrbitSourceBoundaryOuterIntersectionPair σ) :
    (AR.differentOrbitCommonTargetBoundaryEquiv σ p.1).1.1 =
      p.1.1.1 := by
  simpa [differentOrbitCommonTargetBoundaryEquiv] using
    AR.commonTargetBoundaryEquiv_apply_of_projectiveSource_injectiveSource
      σ p.1.1.1 p.2.2.1 p.2.2.2

omit [DecidableEq ι] in
/-- The different-orbit square shift preserves and reflects membership in
the outer intersection.  The reverse implication uses bijectivity together
with the preceding pointwise fixedness. -/
theorem differentOrbitCommonTargetBoundaryEquiv_outerIntersection_iff
    (p : AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ) :
    (¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
        (Projective (σ.obj p.1.1.1.1.1.1) ∨
          Projective (σ.obj p.1.1.1.2.1.1)) ∧
        (Injective (σ.obj p.1.1.1.1.1.1) ∨
          Injective (σ.obj p.1.1.1.2.1.1))) ↔
      let q := AR.differentOrbitCommonTargetBoundaryEquiv σ p
      ¬ Projective (σ.obj q.1.1.1.1.1.2) ∧
        (Projective (σ.obj q.1.1.1.1.1.1) ∨
          Projective (σ.obj q.1.1.1.2.1.1)) ∧
        (Injective (σ.obj q.1.1.1.1.1.1) ∨
          Injective (σ.obj q.1.1.1.2.1.1)) := by
  let E := AR.differentOrbitCommonTargetBoundaryEquiv σ
  constructor
  · intro hp
    have hfixed :=
      AR.differentOrbitCommonTargetBoundaryEquiv_apply_outerIntersection
        σ (⟨p, hp⟩ :
          AR.DifferentOrbitSourceBoundaryOuterIntersectionPair σ)
    change ¬ Projective (σ.obj (E p).1.1.1.1.1.2) ∧ _
    rw [hfixed]
    exact hp
  · intro hq
    change ¬ Projective (σ.obj (E p).1.1.1.1.1.2) ∧ _ at hq
    let q := (E p).1.1
    have hsource :
        ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.1 ∨
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.2 := by
      rcases hq.2.1 with hP | hP
      · exact Or.inl <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ q.1.1).2 (Or.inr hP)
      · exact Or.inr <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
            σ q.1.2).2 (Or.inr hP)
    let s : AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ :=
      ⟨⟨q, hsource⟩, (E p).2⟩
    have hs :
        ¬ Projective (σ.obj s.1.1.1.1.1.2) ∧
          (Projective (σ.obj s.1.1.1.1.1.1) ∨
            Projective (σ.obj s.1.1.1.2.1.1)) ∧
          (Injective (σ.obj s.1.1.1.1.1.1) ∨
            Injective (σ.obj s.1.1.1.2.1.1)) := by
      simpa [s, q] using hq
    have hfixed :=
      AR.differentOrbitCommonTargetBoundaryEquiv_apply_outerIntersection
        σ (⟨s, hs⟩ :
          AR.DifferentOrbitSourceBoundaryOuterIntersectionPair σ)
    have hEp : E p = E s := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [s, q] using hfixed.symm
    have hps : p = s := E.injective hEp
    rw [hps]
    exact hs

/-- The full different-orbit square shift restricts exactly to the
complements of the fixed outer intersection on its two boundaries. -/
def differentOrbitCommonTargetBoundaryNoOuterIntersectionEquiv :
    AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ ≃
      AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ := by
  let E := AR.differentOrbitCommonTargetBoundaryEquiv σ
  apply E.subtypeEquiv
  intro p
  exact not_congr <|
    AR.differentOrbitCommonTargetBoundaryEquiv_outerIntersection_iff σ p

/-- Exact split of the full different-orbit source boundary into the fixed
outer intersection and its complement. -/
def differentOrbitSourceBoundaryEquivOuterIntersectionSumComplement :
    AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ ≃
      AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair σ ⊕
        AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ := by
  classical
  let P : AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ → Prop :=
    fun p ↦
      ¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
        (Projective (σ.obj p.1.1.1.1.1.1) ∨
          Projective (σ.obj p.1.1.1.2.1.1)) ∧
        (Injective (σ.obj p.1.1.1.1.1.1) ∨
          Injective (σ.obj p.1.1.1.2.1.1))
  let E := (Equiv.sumCompl P).symm
  exact E.trans <|
    Equiv.sumCongr
      (AR.differentOrbitOuterIntersectionEquivSourceBoundaryOuterIntersection
        σ).symm
      (Equiv.refl _)

/-- The complement of the fixed outer intersection on the source boundary
has an exact endpoint decomposition: either the common target is projective,
or the common target is nonprojective and both sources survive the interior
trimming.  The different-component predicate is retained on the full arrow
occurrences in both branches. -/
def differentOrbitSourceBoundaryComplementEquivProjectiveTargetSumFullOrbitLiteral :
    AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ ≃
      AR.DifferentOrbitProjectiveTargetCommonTargetPair σ ⊕
        AR.FullOrbitDifferentInteriorLiteralSourceCommonTargetPair σ where
  toFun p := by
    let q := p.1.1.1
    by_cases ht : Projective (σ.obj q.1.1.1.2)
    · exact Sum.inl ⟨⟨q, ht⟩, p.1.2⟩
    · have hP : Projective (σ.obj q.1.1.1.1) ∨
          Projective (σ.obj q.1.2.1.1) := by
        rcases p.1.1.2 with h | h
        · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ q.1.1).1 h with htarget | hsource
          · exact (ht htarget).elim
          · exact Or.inl hsource
        · rcases ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ q.1.2).1 h with htarget | hsource
          · apply (ht ?_).elim
            rw [q.2]
            exact htarget
          · exact Or.inr hsource
      have hNI : ¬ Injective (σ.obj q.1.1.1.1) ∧
          ¬ Injective (σ.obj q.1.2.1.1) := by
        constructor
        · intro hI
          exact p.2 ⟨ht, hP, Or.inl hI⟩
        · intro hI
          exact p.2 ⟨ht, hP, Or.inr hI⟩
      let n : NonprojectiveTargetProjectiveSourceNoninjectivePair σ :=
        ⟨⟨q, ht, hP⟩, hNI⟩
      let r :=
        AR.nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral
          σ n
      apply Sum.inr
      refine ⟨r, ?_⟩
      simpa [r, n,
        nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral,
        toInteriorArrow] using p.1.2
  invFun p := by
    rcases p with p | p
    · let q := p.1.1
      have hsource :
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.2 :=
        Or.inl <| ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
          σ q.1.1).2 (Or.inl p.1.2)
      exact ⟨⟨⟨q, hsource⟩, p.2⟩, by
        intro houter
        exact houter.1 p.1.2⟩
    · let E :=
        AR.nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral
          σ
      let n := E.symm p.1
      let q := n.1.1
      have hsource :
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.1 ∨
            ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource q.1.2 := by
        rcases n.1.2.2 with h | h
        · exact Or.inl <|
            ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ q.1.1).2 (Or.inr h)
        · exact Or.inr <|
            ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff
              σ q.1.2).2 (Or.inr h)
      have hdiff :
          ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
            q.1.1 q.1.2 := by
        have hq : q = forgetInteriorCommonTarget σ AR p.1.1 := by
          have h := congrArg
            (fun x : AR.InteriorLiteralSourceCommonTargetPair σ ↦
              forgetInteriorCommonTarget σ AR x.1)
            (E.apply_symm_apply p.1)
          change q = forgetInteriorCommonTarget σ AR p.1.1 at h
          exact h
        rw [hq]
        change
          ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
            p.1.1.1.1.1 p.1.1.1.2.1
        exact p.2
      exact ⟨⟨⟨q, hsource⟩, hdiff⟩, by
        intro houter
        rcases houter.2.2 with hI | hI
        · exact n.2.1 hI
        · exact n.2.2 hI⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    by_cases ht : Projective (σ.obj p.1.1.1.1.1.1.2)
    · simp [ht]
    · simp only [ht, ↓reduceDIte]
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv p := by
    rcases p with p | p
    · dsimp
      simp [p.1.2]
    · let E :=
        AR.nonprojectiveTargetProjectiveSourceNoninjectiveEquivInteriorLiteral
          σ
      let n := E.symm p.1
      have ht : ¬ Projective (σ.obj n.1.1.1.1.1.2) := n.1.2.1
      dsimp only
      rw [dif_neg ht]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact E.apply_symm_apply p.1

include K in
/-- Trimmed-orbit form of the exact source-boundary complement
decomposition. -/
def differentOrbitSourceBoundaryComplementEquivProjectiveTargetSumLiteral :
    AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ ≃
      AR.DifferentOrbitProjectiveTargetCommonTargetPair σ ⊕
        AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair σ :=
  (AR.differentOrbitSourceBoundaryComplementEquivProjectiveTargetSumFullOrbitLiteral
      σ).trans <|
    Equiv.sumCongr (Equiv.refl _)
      (AR.fullOrbitDifferentInteriorLiteralEquivInteriorDifferentOrbitLiteral
        (K := K) σ)

/-- The intrinsic outer projective/injective-source corner is exactly its
presentation as a fixed part of the full target boundary. -/
def differentOrbitOuterIntersectionEquivTargetBoundaryOuterIntersection :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair σ ≃
      AR.DifferentOrbitTargetBoundaryOuterIntersectionPair σ where
  toFun p := by
    let q := p.1.1.1
    have htarget :
        ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget q.1.1 ∨
          ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget q.1.2 := by
      rcases p.1.2 with h | h
      · exact Or.inl <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
            σ q.1.1).2 (Or.inl h)
      · exact Or.inr <|
          ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff
            σ q.1.2).2 (Or.inl h)
    exact ⟨⟨⟨q, htarget⟩, p.2⟩,
      p.1.1.2.1, p.1.1.2.2, p.1.2⟩
  invFun p :=
    ⟨⟨⟨p.1.1.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩, p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Exact split of the full different-orbit target boundary into its fixed
outer intersection and the complementary raw endpoint index. -/
def differentOrbitTargetBoundaryEquivOuterIntersectionSumComplement :
    AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ ≃
      AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair σ ⊕
        AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ := by
  classical
  let P : AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ → Prop :=
    fun p ↦
      ¬ Projective (σ.obj p.1.1.1.1.1.2) ∧
        (Projective (σ.obj p.1.1.1.1.1.1) ∨
          Projective (σ.obj p.1.1.1.2.1.1)) ∧
        (Injective (σ.obj p.1.1.1.1.1.1) ∨
          Injective (σ.obj p.1.1.1.2.1.1))
  let E := (Equiv.sumCompl P).symm
  exact E.trans <|
    Equiv.sumCongr
      (AR.differentOrbitOuterIntersectionEquivTargetBoundaryOuterIntersection
        σ).symm
      (Equiv.refl _)

/-- The full target-boundary corner decomposition restricts exactly to
labelled arrows in different successor components. -/
def differentOrbitTargetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource :
    AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ ≃
      AR.DifferentOrbitInjectiveTargetCommonTargetPair σ ⊕
        AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ := by
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let E := targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource σ AR
  let P : AR.TargetBoundaryCommonTargetArrowPair σ → Prop :=
    fun p ↦ ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
  let Q : InjectiveTargetCommonTargetPair σ ⊕
      NoninjectiveTargetInjectiveSourcePair σ → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  let L : {p : InjectiveTargetCommonTargetPair σ // Q (Sum.inl p)} ≃
      AR.DifferentOrbitInjectiveTargetCommonTargetPair σ := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    change P (E.symm (Sum.inl p)) ↔
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
    rfl
  let R : {p : NoninjectiveTargetInjectiveSourcePair σ // Q (Sum.inr p)} ≃
      AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    change (¬ O.SameSuccessorOrbit
        (E.symm (Sum.inr p)).1.1.1 (E.symm (Sum.inr p)).1.1.2) ↔
      ¬ O.SameSuccessorOrbit p.1.1.1 p.1.1.2
    have hval : (E.symm (Sum.inr p)).1 = p.1 := by
      by_cases h : Injective (σ.obj p.1.1.1.1.1)
      · simp [E,
          targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource,
          h]
      · simp [E,
          targetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource,
          h]
    rw [hval]
  exact F.trans (Equiv.sumCongr L R)

/-- Endpoint-corner form of the full different-orbit square shift. -/
def differentOrbitFullCommonTargetBoundaryCornerEquiv :
    AR.DifferentOrbitProjectiveTargetCommonTargetPair σ ⊕
        AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair σ ≃
      AR.DifferentOrbitInjectiveTargetCommonTargetPair σ ⊕
        AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ :=
  (AR.differentOrbitSourceBoundaryCommonTargetEquivProjectiveTargetSumProjectiveSource
      σ).symm |>.trans <|
    (AR.differentOrbitCommonTargetBoundaryEquiv σ).trans
      (AR.differentOrbitTargetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource
        σ)

omit [DecidableEq ι] in
/-- Cardinal corner identity for the full different-orbit square shift. -/
theorem differentOrbitFullCommonTargetBoundary_corner_card_identity :
    Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveSourcePair σ) =
      Fintype.card
          (AR.DifferentOrbitInjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ) := by
  rw [← Fintype.card_sum,
    Fintype.card_congr
      (AR.differentOrbitFullCommonTargetBoundaryCornerEquiv σ),
    Fintype.card_sum]

include K AR in
omit [DecidableEq ι] in
/-- After splitting the nonprojective projective-source corner, the source
side of the full different-orbit boundary consists of the projective-target
index, the trimmed literal-source index, and the outer
projective/injective-source intersection. -/
theorem projectiveTarget_add_literal_add_outerIntersection_card_eq_targetCorners :
    Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair σ) +
        Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            σ) =
      Fintype.card
          (AR.DifferentOrbitInjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.DifferentOrbitNoninjectiveTargetInjectiveSourcePair σ) := by
  have hcorner := AR.differentOrbitFullCommonTargetBoundary_corner_card_identity σ
  have hsplit :=
    AR.differentOrbitNonprojectiveTargetProjectiveSource_card_eq_interiorLiteral_add_outer
      σ
  have htrim :=
    AR.fullOrbitDifferentInteriorLiteral_card_eq_interiorDifferentOrbitLiteral
      (K := K) σ
  omega

omit [DecidableEq ι] in
/-- Cardinal split of the different-orbit target boundary into its fixed
outer intersection and complementary endpoint index. -/
theorem differentOrbitTargetBoundary_card_eq_outerIntersection_add_complement :
    Fintype.card
          (AR.DifferentOrbitTargetBoundaryCommonTargetArrowPair σ) =
      Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            σ) +
        Fintype.card
          (AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) := by
  rw [Fintype.card_congr
    (AR.differentOrbitTargetBoundaryEquivOuterIntersectionSumComplement σ)]
  exact Fintype.card_sum

omit [DecidableEq ι] in
/-- Cardinal split of the different-orbit source boundary into the same
fixed outer intersection and its complement. -/
theorem differentOrbitSourceBoundary_card_eq_outerIntersection_add_complement :
    Fintype.card
          (AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ) =
      Fintype.card
          (AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair
            σ) +
        Fintype.card
          (AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ) := by
  rw [Fintype.card_congr
    (AR.differentOrbitSourceBoundaryEquivOuterIntersectionSumComplement σ)]
  exact Fintype.card_sum

omit [DecidableEq ι] in
/-- The square shift identifies the complementary source and target
boundary occurrences exactly. -/
theorem differentOrbitSourceBoundaryComplement_card_eq_targetBoundaryComplement :
    Fintype.card
          (AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ) =
      Fintype.card
          (AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) :=
  Fintype.card_congr
    (AR.differentOrbitCommonTargetBoundaryNoOuterIntersectionEquiv σ)

include K AR in
omit [DecidableEq ι] in
/-- The invariant local boundary index `projective target + trimmed literal
source` is exactly the complement of the fixed outer intersection in the
full different-orbit target boundary. -/
theorem projectiveTarget_add_literal_card_eq_targetBoundaryComplement :
    Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair σ) =
      Fintype.card
          (AR.DifferentOrbitTargetBoundaryNoOuterIntersectionPair σ) := by
  have hcorners :=
    AR.projectiveTarget_add_literal_add_outerIntersection_card_eq_targetCorners
      (K := K) σ
  have htarget := Fintype.card_congr
    (AR.differentOrbitTargetBoundaryCommonTargetEquivInjectiveTargetSumInjectiveSource
      σ)
  have hsplit :=
    AR.differentOrbitTargetBoundary_card_eq_outerIntersection_add_complement
      σ
  simp only [Fintype.card_sum] at htarget
  omega

include K AR in
omit [DecidableEq ι] in
/-- The invariant local boundary index also has the exact source-boundary
complement coordinate. -/
theorem projectiveTarget_add_literal_card_eq_sourceBoundaryComplement :
    Fintype.card
          (AR.DifferentOrbitProjectiveTargetCommonTargetPair σ) +
        Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair σ) =
      Fintype.card
          (AR.DifferentOrbitSourceBoundaryNoOuterIntersectionPair σ) := by
  rw [AR.differentOrbitSourceBoundaryComplement_card_eq_targetBoundaryComplement
    σ]
  exact AR.projectiveTarget_add_literal_card_eq_targetBoundaryComplement
    (K := K) σ

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData
