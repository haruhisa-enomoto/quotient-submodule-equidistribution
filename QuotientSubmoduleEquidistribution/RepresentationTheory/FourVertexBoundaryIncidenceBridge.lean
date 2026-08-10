import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexBoundaryChannelClassification
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexDualArrowOccurrences

/-!
# One-step incidence bridge on the trimmed arrow boundary

Mesh rotation changes a pair of arrows with a common source into a pair
of predecessor arrows with a common target.  On the trimmed boundary this
identifies the genuine second source layer with the nonterminal part of the
literal first source layer.  The omitted terminal part is the endpoint
correction which remains in signed strip reversal.
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

/-- Common-target pairs with at least one coordinate literally in the
first trimmed source layer. -/
abbrev InteriorLiteralSourceCommonTargetPair :=
  {p : AR.InteriorCommonTargetArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.1 ∨
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.2}

/-- Common-target pairs on the shifted source boundary for which neither
coordinate is literally in the first source layer. -/
abbrev InteriorSecondOnlySourceCommonTargetPair :=
  {p : AR.InteriorSourceBoundaryCommonTargetArrowPair sigma //
    ¬ (((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.1 ∨
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.2)}

/-- Common-source pairs with at least one coordinate literally in the
first trimmed source layer. -/
abbrev InteriorLiteralSourceCommonSourcePair :=
  {p : AR.InteriorCommonSourceArrowPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.1 ∨
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
        p.1.2}

/-- Common-source pairs on the shifted source boundary for which neither
coordinate is literally in the first source layer. -/
abbrev InteriorSecondOnlySourceCommonSourcePair :=
  {p : AR.InteriorSourceBoundaryCommonSourceArrowPair sigma //
    ¬ (((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.1 ∨
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.2)}

/-- Literal-source common-target pairs whose two coordinates can both be
advanced inside the trimmed arrow translation. -/
abbrev InteriorLiteralSourceNonterminalCommonTargetPair :=
  {p : AR.InteriorLiteralSourceCommonTargetPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.1 ∧
      ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.2}

/-- Literal-source common-target pairs for which at least one coordinate is
already at the terminal end of its trimmed arrow chain. -/
abbrev InteriorLiteralSourceTerminalCommonTargetPair :=
  {p : AR.InteriorLiteralSourceCommonTargetPair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.1 ∨
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.2}

/-- Different-orbit part of the literal common-target source layer. -/
abbrev InteriorDifferentOrbitLiteralSourceCommonTargetPair :=
  {p : AR.InteriorLiteralSourceCommonTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1}

/-- Different-orbit part of the genuine second common-target source layer. -/
abbrev InteriorDifferentOrbitSecondOnlySourceCommonTargetPair :=
  {p : AR.InteriorSecondOnlySourceCommonTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1}

/-- Different-orbit part of the literal common-source source layer. -/
abbrev InteriorDifferentOrbitLiteralSourceCommonSourcePair :=
  {p : AR.InteriorLiteralSourceCommonSourcePair sigma //
    InteriorCommonSourceArrowPair.DifferentOrbit sigma AR p.1}

/-- Different-orbit part of the genuine second common-source source layer. -/
abbrev InteriorDifferentOrbitSecondOnlySourceCommonSourcePair :=
  {p : AR.InteriorSecondOnlySourceCommonSourcePair sigma //
    InteriorCommonSourceArrowPair.DifferentOrbit sigma AR p.1.1}

/-- Different-orbit nonterminal part of the literal common-target source
layer. -/
abbrev InteriorDifferentOrbitLiteralSourceNonterminalCommonTargetPair :=
  {p : AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1}

/-- Different-orbit terminal part of the literal common-target source
layer. -/
abbrev InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair :=
  {p : AR.InteriorLiteralSourceTerminalCommonTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1}

noncomputable instance interiorLiteralSourceCommonTargetPairFintype :
    Fintype (AR.InteriorLiteralSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance interiorSecondOnlySourceCommonTargetPairFintype :
    Fintype (AR.InteriorSecondOnlySourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance interiorLiteralSourceCommonSourcePairFintype :
    Fintype (AR.InteriorLiteralSourceCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance interiorSecondOnlySourceCommonSourcePairFintype :
    Fintype (AR.InteriorSecondOnlySourceCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorLiteralSourceNonterminalCommonTargetPairFintype :
    Fintype (AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorLiteralSourceTerminalCommonTargetPairFintype :
    Fintype (AR.InteriorLiteralSourceTerminalCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitLiteralSourceCommonTargetPairFintype :
    Fintype (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitSecondOnlySourceCommonTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitLiteralSourceCommonSourcePairFintype :
    Fintype (AR.InteriorDifferentOrbitLiteralSourceCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitSecondOnlySourceCommonSourcePairFintype :
    Fintype
      (AR.InteriorDifferentOrbitSecondOnlySourceCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitLiteralSourceNonterminalCommonTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitLiteralSourceNonterminalCommonTargetPair
        sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitLiteralSourceTerminalCommonTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair sigma) :=
  Fintype.ofFinite _

/-- Split the common-target shifted source boundary into its literal first
layer and its genuine second-layer remainder. -/
def interiorSourceBoundaryCommonTargetEquivLiteralSumSecondOnly :
    AR.InteriorSourceBoundaryCommonTargetArrowPair sigma ≃
      AR.InteriorLiteralSourceCommonTargetPair sigma ⊕
        AR.InteriorSecondOnlySourceCommonTargetPair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.1 ∨
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.2
    · exact Sum.inl ⟨p.1, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, by
        rcases p.2 with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)⟩
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.1 ∨
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- Split the common-source shifted source boundary into its literal first
layer and its genuine second-layer remainder. -/
def interiorSourceBoundaryCommonSourceEquivLiteralSumSecondOnly :
    AR.InteriorSourceBoundaryCommonSourceArrowPair sigma ≃
      AR.InteriorLiteralSourceCommonSourcePair sigma ⊕
        AR.InteriorSecondOnlySourceCommonSourcePair sigma where
  toFun p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.1 ∨
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.2
    · exact Sum.inl ⟨p.1, h⟩
    · exact Sum.inr ⟨p, h⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨p.1, by
        rcases p.2 with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)⟩
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.1 ∨
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
            p.1.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · simp [p.2]

/-- Split the literal common-target layer according to whether both
coordinates still admit one trimmed successor. -/
def interiorLiteralSourceCommonTargetEquivNonterminalSumTerminal :
    AR.InteriorLiteralSourceCommonTargetPair sigma ≃
      AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma ⊕
        AR.InteriorLiteralSourceTerminalCommonTargetPair sigma where
  toFun p := by
    classical
    by_cases h :
        ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
            p.1.1.1 ∧
          ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
            p.1.1.2
    · exact Sum.inl ⟨p, h⟩
    · exact Sum.inr ⟨p, by
        by_cases hfirst :
            ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
              p.1.1.1
        · exact Or.inl hfirst
        · right
          by_contra hsecond
          exact h ⟨hfirst, hsecond⟩⟩
  invFun p := by
    rcases p with p | p
    · exact p.1
    · exact p.1
  left_inv p := by
    classical
    by_cases h :
        ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
            p.1.1.1 ∧
          ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
            p.1.1.2
    · simp [h]
    · simp [h]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.2]
    · have h : ¬ (¬
          ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
              p.1.1.1.1 ∧
        ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
              p.1.1.1.2) := by
        intro hnonterminal
        exact p.2.elim hnonterminal.1 hnonterminal.2
      simp [h]

omit [DecidableEq iota] in
/-- One predecessor rotation turns a genuine second-layer common-source
pair into a nonterminal literal-source common-target pair, and one successor
rotation is its inverse. -/
def interiorSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget :
    AR.InteriorSecondOnlySourceCommonSourcePair sigma ≃
      AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma where
  toFun p := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    have hA : ¬ O.InteriorSource p.1.1.1.1 :=
      fun h ↦ p.2 (Or.inl h)
    have hB : ¬ O.InteriorSource p.1.1.1.2 :=
      fun h ↦ p.2 (Or.inr h)
    let A := (U.tau ⟨p.1.1.1.1, hA⟩).1
    let B := (U.tau ⟨p.1.1.1.2, hB⟩).1
    have htarget : A.1.1.2 = B.1.1.2 := by
      have hAVal := M.arrowOrbitData_tau_val sigma
        ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩
      have hBVal := M.arrowOrbitData_tau_val sigma
        ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩
      change A.1.1.2 = B.1.1.2
      change
        ((O.tau ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩).1).1.2 =
          ((O.tau ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩).1).1.2
      rw [congrArg Prod.snd hAVal, congrArg Prod.snd hBVal]
      exact p.1.1.2
    refine ⟨⟨⟨(A, B), htarget⟩, ?_⟩, ?_⟩
    · rcases p.1.2 with h | h
      · rcases h with h | h
        · exact (hA h).elim
        · left
          exact h hA
      · rcases h with h | h
        · exact (hB h).elim
        · right
          exact h hB
    · exact ⟨(U.tau ⟨p.1.1.1.1, hA⟩).2,
        (U.tau ⟨p.1.1.1.2, hB⟩).2⟩
  invFun p := by
    let M := AR.arMeshRotationData sigma
    let O := M.arrowOrbitData sigma
    let U := M.arrowInteriorOrbitData sigma
    let A := (U.tau.symm ⟨p.1.1.1.1, p.2.1⟩).1
    let B := (U.tau.symm ⟨p.1.1.1.2, p.2.2⟩).1
    have hsource : A.1.1.1 = B.1.1.1 := by
      have hAVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.1.1, p.1.1.1.1.2.2⟩
      have hBVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.2.1, p.1.1.1.2.2.2⟩
      change A.1.1.1 = B.1.1.1
      change
        ((O.tau.symm ⟨p.1.1.1.1.1, p.1.1.1.1.2.2⟩).1).1.1 =
          ((O.tau.symm ⟨p.1.1.1.2.1, p.1.1.1.2.2.2⟩).1).1.1
      rw [congrArg Prod.fst hAVal, congrArg Prod.fst hBVal]
      exact p.1.1.2
    refine ⟨⟨⟨(A, B), hsource⟩, ?_⟩, ?_⟩
    · rcases p.1.2 with h | h
      · left
        right
        intro hnot
        have hinput :
            (⟨A, hnot⟩ : {x // ¬ O.InteriorSource x}) =
              U.tau.symm ⟨p.1.1.1.1, p.2.1⟩ := by
          apply Subtype.ext
          rfl
        have hforward := congrArg U.tau hinput
        have hback := U.tau.apply_symm_apply
          ⟨p.1.1.1.1, p.2.1⟩
        rw [congrArg Subtype.val (hforward.trans hback)]
        exact h
      · right
        right
        intro hnot
        have hinput :
            (⟨B, hnot⟩ : {x // ¬ O.InteriorSource x}) =
              U.tau.symm ⟨p.1.1.1.2, p.2.2⟩ := by
          apply Subtype.ext
          rfl
        have hforward := congrArg U.tau hinput
        have hback := U.tau.apply_symm_apply
          ⟨p.1.1.1.2, p.2.2⟩
        rw [congrArg Subtype.val (hforward.trans hback)]
        exact h
    · exact fun h ↦ h.elim
        (U.tau.symm ⟨p.1.1.1.1, p.2.1⟩).2
        (U.tau.symm ⟨p.1.1.1.2, p.2.2⟩).2
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).tau.symm_apply_apply
          ⟨p.1.1.1.1, fun h ↦ p.2 (Or.inl h)⟩)
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).tau.symm_apply_apply
          ⟨p.1.1.1.2, fun h ↦ p.2 (Or.inr h)⟩)
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).tau.apply_symm_apply
          ⟨p.1.1.1.1, p.2.1⟩)
    · exact congrArg Subtype.val
        (((AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma).tau.apply_symm_apply
          ⟨p.1.1.1.2, p.2.2⟩)

omit [DecidableEq iota] in
/-- The predecessor rotation in the one-step incidence equivalence preserves
and reflects whether its two labelled occurrences belong to the same
intrinsic component. -/
theorem interiorSecondOnlyCommonSourceEquiv_sameSuccessorOrbit_iff
    (p : AR.InteriorSecondOnlySourceCommonSourcePair sigma) :
    let U := (AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma
    let E := AR.interiorSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget
      sigma
    U.SameSuccessorOrbit (E p).1.1.1.1 (E p).1.1.1.2 ↔
      U.SameSuccessorOrbit p.1.1.1.1 p.1.1.1.2 := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  let E := AR.interiorSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget
    sigma
  let A₀ := p.1.1.1.1
  let B₀ := p.1.1.1.2
  have hA : ¬ O.InteriorSource A₀ := fun h ↦ p.2 (Or.inl h)
  have hB : ¬ O.InteriorSource B₀ := fun h ↦ p.2 (Or.inr h)
  let A := (U.tau ⟨A₀, hA⟩).1
  let B := (U.tau ⟨B₀, hB⟩).1
  have hAstep : U.successor A = A₀ := by
    have hnotTarget : ¬ O.InteriorTarget A := (U.tau ⟨A₀, hA⟩).2
    rw [show U.successor A = (U.tau.symm ⟨A, hnotTarget⟩).1 by
      classical
      unfold QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor
      split
      · rename_i h
        exact (hnotTarget h).elim
      · rfl]
    exact congrArg Subtype.val (U.tau.symm_apply_apply ⟨A₀, hA⟩)
  have hBstep : U.successor B = B₀ := by
    have hnotTarget : ¬ O.InteriorTarget B := (U.tau ⟨B₀, hB⟩).2
    rw [show U.successor B = (U.tau.symm ⟨B, hnotTarget⟩).1 by
      classical
      unfold QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor
      split
      · rename_i h
        exact (hnotTarget h).elim
      · rfl]
    exact congrArg Subtype.val (U.tau.symm_apply_apply ⟨B₀, hB⟩)
  have hAorbit : U.SameSuccessorOrbit A A₀ := by
    exact ⟨1, 0, by simpa only [Function.iterate_one,
      Function.iterate_zero, id_eq] using hAstep⟩
  have hBorbit : U.SameSuccessorOrbit B B₀ := by
    exact ⟨1, 0, by simpa only [Function.iterate_one,
      Function.iterate_zero, id_eq] using hBstep⟩
  change U.SameSuccessorOrbit A B ↔
    U.SameSuccessorOrbit A₀ B₀
  exact U.sameSuccessorOrbit_congr_of_related hAorbit hBorbit

omit [DecidableEq iota] in
/-- The one-step incidence equivalence restricts exactly to different
intrinsic arrow-orbit components. -/
def interiorDifferentOrbitSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget :
    AR.InteriorDifferentOrbitSecondOnlySourceCommonSourcePair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceNonterminalCommonTargetPair
        sigma := by
  let E := AR.interiorSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget
    sigma
  apply E.subtypeEquiv
  intro p
  exact not_congr <|
    (AR.interiorSecondOnlyCommonSourceEquiv_sameSuccessorOrbit_iff sigma p).symm

/-- The literal/second-layer decomposition of the common-target source
boundary restricts to labelled pairs on different intrinsic components. -/
def interiorDifferentOrbitSourceBoundaryCommonTargetEquivLiteralSumSecondOnly :
    AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma ⊕
        AR.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair sigma := by
  let E := AR.interiorSourceBoundaryCommonTargetEquivLiteralSumSecondOnly sigma
  let P : AR.InteriorSourceBoundaryCommonTargetArrowPair sigma → Prop :=
    fun p ↦ InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1
  let Q : AR.InteriorLiteralSourceCommonTargetPair sigma ⊕
      AR.InteriorSecondOnlySourceCommonTargetPair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q, E,
    interiorSourceBoundaryCommonTargetEquivLiteralSumSecondOnly] using F

/-- The literal/second-layer decomposition of the common-source source
boundary restricts to labelled pairs on different intrinsic components. -/
def interiorDifferentOrbitSourceBoundaryCommonSourceEquivLiteralSumSecondOnly :
    AR.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceCommonSourcePair sigma ⊕
        AR.InteriorDifferentOrbitSecondOnlySourceCommonSourcePair sigma := by
  let E := AR.interiorSourceBoundaryCommonSourceEquivLiteralSumSecondOnly sigma
  let P : AR.InteriorSourceBoundaryCommonSourceArrowPair sigma → Prop :=
    fun p ↦ InteriorCommonSourceArrowPair.DifferentOrbit sigma AR p.1
  let Q : AR.InteriorLiteralSourceCommonSourcePair sigma ⊕
      AR.InteriorSecondOnlySourceCommonSourcePair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q, E,
    interiorSourceBoundaryCommonSourceEquivLiteralSumSecondOnly] using F

/-- The terminal/nonterminal decomposition of the literal common-target
layer restricts to labelled pairs on different intrinsic components. -/
def interiorDifferentOrbitLiteralSourceCommonTargetEquivNonterminalSumTerminal :
    AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma ≃
      AR.InteriorDifferentOrbitLiteralSourceNonterminalCommonTargetPair sigma ⊕
        AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair sigma := by
  let E := AR.interiorLiteralSourceCommonTargetEquivNonterminalSumTerminal sigma
  let P : AR.InteriorLiteralSourceCommonTargetPair sigma → Prop :=
    fun p ↦ InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1
  let Q : AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma ⊕
      AR.InteriorLiteralSourceTerminalCommonTargetPair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  simpa [P, Q, E,
    interiorLiteralSourceCommonTargetEquivNonterminalSumTerminal] using F

omit [DecidableEq iota] in
/-- Cardinal one-step incidence balance on the shifted source boundary.
The common-target and common-source counts differ only by the genuine
second common-target layer and the terminal part of the literal layer. -/
theorem interiorSourceBoundary_target_add_literalSource_card_eq :
    Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) +
        Fintype.card (AR.InteriorLiteralSourceCommonSourcePair sigma) =
      Fintype.card (AR.InteriorSourceBoundaryCommonSourceArrowPair sigma) +
        Fintype.card (AR.InteriorSecondOnlySourceCommonTargetPair sigma) +
          Fintype.card
            (AR.InteriorLiteralSourceTerminalCommonTargetPair sigma) := by
  have htarget :
      Fintype.card (AR.InteriorSourceBoundaryCommonTargetArrowPair sigma) =
        Fintype.card (AR.InteriorLiteralSourceCommonTargetPair sigma) +
          Fintype.card
            (AR.InteriorSecondOnlySourceCommonTargetPair sigma) := by
    rw [Fintype.card_congr
      (AR.interiorSourceBoundaryCommonTargetEquivLiteralSumSecondOnly sigma)]
    exact Fintype.card_sum
  have hsource :
      Fintype.card (AR.InteriorSourceBoundaryCommonSourceArrowPair sigma) =
        Fintype.card (AR.InteriorLiteralSourceCommonSourcePair sigma) +
          Fintype.card
            (AR.InteriorSecondOnlySourceCommonSourcePair sigma) := by
    rw [Fintype.card_congr
      (AR.interiorSourceBoundaryCommonSourceEquivLiteralSumSecondOnly sigma)]
    exact Fintype.card_sum
  have hliteral :
      Fintype.card (AR.InteriorLiteralSourceCommonTargetPair sigma) =
        Fintype.card
            (AR.InteriorLiteralSourceNonterminalCommonTargetPair sigma) +
          Fintype.card
            (AR.InteriorLiteralSourceTerminalCommonTargetPair sigma) := by
    rw [Fintype.card_congr
      (AR.interiorLiteralSourceCommonTargetEquivNonterminalSumTerminal sigma)]
    exact Fintype.card_sum
  have hbridge := Fintype.card_congr
    (AR.interiorSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget
      sigma)
  omega

omit [DecidableEq iota] in
/-- Cardinal one-step incidence balance restricted to pairs on different
intrinsic arrow-orbit components.  Thus the raw endpoint correction in the
different-orbit sector consists exactly of the genuine second common-target
layer and the terminal literal common-target layer. -/
theorem interiorDifferentOrbitSourceBoundary_target_add_literalSource_card_eq :
    Fintype.card
          (AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair
            sigma) +
        Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceCommonSourcePair sigma) =
      Fintype.card
          (AR.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair
            sigma) +
        Fintype.card
            (AR.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair
              sigma) +
          Fintype.card
            (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
              sigma) := by
  have htarget :
      Fintype.card
          (AR.InteriorDifferentOrbitSourceBoundaryCommonTargetArrowPair
            sigma) =
        Fintype.card
            (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) +
          Fintype.card
            (AR.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair
              sigma) := by
    rw [Fintype.card_congr
      (AR.interiorDifferentOrbitSourceBoundaryCommonTargetEquivLiteralSumSecondOnly
        sigma)]
    exact Fintype.card_sum
  have hsource :
      Fintype.card
          (AR.InteriorDifferentOrbitSourceBoundaryCommonSourceArrowPair
            sigma) =
        Fintype.card
            (AR.InteriorDifferentOrbitLiteralSourceCommonSourcePair sigma) +
          Fintype.card
            (AR.InteriorDifferentOrbitSecondOnlySourceCommonSourcePair
              sigma) := by
    rw [Fintype.card_congr
      (AR.interiorDifferentOrbitSourceBoundaryCommonSourceEquivLiteralSumSecondOnly
        sigma)]
    exact Fintype.card_sum
  have hliteral :
      Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceCommonTargetPair sigma) =
        Fintype.card
            (AR.InteriorDifferentOrbitLiteralSourceNonterminalCommonTargetPair
              sigma) +
          Fintype.card
            (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
              sigma) := by
    rw [Fintype.card_congr
      (AR.interiorDifferentOrbitLiteralSourceCommonTargetEquivNonterminalSumTerminal
        sigma)]
    exact Fintype.card_sum
  have hbridge := Fintype.card_congr
    (AR.interiorDifferentOrbitSecondOnlyCommonSourceEquivLiteralNonterminalCommonTarget
      sigma)
  omega

end FiniteARTranslationData

universe w

variable {S : Type u}
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing S]
  {kappa : Type w} [Fintype kappa] [DecidableEq kappa]
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

/-- The endpoint identity obtained by applying one-step incidence on both
sides of an aligned duality and retaining only pairs on different intrinsic
arrow-orbit components. -/
def TrimmedDifferentOrbitEndpointReversalBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card
          (ARsigma.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
            sigma) +
      Fintype.card
          (ARtau.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair tau) +
        Fintype.card
          (ARtau.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
            tau) =
    Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceCommonSourcePair sigma) +
      Fintype.card
        (ARtau.InteriorDifferentOrbitLiteralSourceCommonSourcePair tau)

include k in
/-- Aligned reversal and the restricted one-step incidence bijection prove
the two-sided different-orbit endpoint balance unconditionally. -/
theorem trimmedDifferentOrbitEndpointReversalBalance
    (D : AlignedBiduality sigma tau) :
    TrimmedDifferentOrbitEndpointReversalBalance
      (k := k) (R := R) (S := S) sigma tau := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hincidenceSigma :=
    ARsigma.interiorDifferentOrbitSourceBoundary_target_add_literalSource_card_eq
      sigma
  have hincidenceTau :=
    ARtau.interiorDifferentOrbitSourceBoundary_target_add_literalSource_card_eq
      tau
  have hdualTauSigma :=
    D.interiorDifferentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      sigma tau ARsigma ARtau
  have hdualSigmaTau :=
    (D.swap sigma tau).interiorDifferentOrbitSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      tau sigma ARtau ARsigma
  unfold TrimmedDifferentOrbitEndpointReversalBalance
  dsimp only [ARsigma, ARtau] at hincidenceSigma hincidenceTau hdualTauSigma hdualSigmaTau ⊢
  omega

/-- The remaining endpoint equation after the one-step incidence bridge.
It is subtraction-free: the genuine second common-target layer and the
terminal literal layer on `sigma`, together with the three dual correction
families, balance the literal common-source layer and the three source-side
correction families. -/
def TrimmedBoundaryEndpointReversalBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card (ARsigma.InteriorSecondOnlySourceCommonTargetPair sigma) +
        Fintype.card
          (ARsigma.InteriorLiteralSourceTerminalCommonTargetPair sigma) +
      Fintype.card
          {T : ARtau.StripAdmissibleTriple tau //
            Projective (tau.obj T.a)} +
        Fintype.card (ARtau.BoundaryM6InjectiveTargetPair tau) +
          Fintype.card (ARtau.BoundaryM6ReverseLastPair tau) =
    Fintype.card (ARsigma.InteriorLiteralSourceCommonSourcePair sigma) +
      Fintype.card
          {T : ARsigma.StripAdmissibleTriple sigma //
            Projective (sigma.obj T.a)} +
        Fintype.card (ARsigma.BoundaryM6InjectiveTargetPair sigma) +
          Fintype.card (ARsigma.BoundaryM6ReverseLastPair sigma)

/-- The genuinely uncancelled endpoint equation.  The projective-strip
terms have been removed, since their cardinality is already invariant under
aligned reversal. -/
def TrimmedBoundaryResidualReversalBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card (ARsigma.InteriorSecondOnlySourceCommonTargetPair sigma) +
        Fintype.card
          (ARsigma.InteriorLiteralSourceTerminalCommonTargetPair sigma) +
      Fintype.card (ARtau.BoundaryM6InjectiveTargetPair tau) +
        Fintype.card (ARtau.BoundaryM6ReverseLastPair tau) =
    Fintype.card (ARsigma.InteriorLiteralSourceCommonSourcePair sigma) +
      Fintype.card (ARsigma.BoundaryM6InjectiveTargetPair sigma) +
        Fintype.card (ARsigma.BoundaryM6ReverseLastPair sigma)

omit [DecidableEq iota] [DecidableEq kappa] in
include k in
/-- Projective-strip reversal upgrades the residual endpoint equation to
the endpoint equation used by the trimmed channel reduction. -/
theorem trimmedBoundaryEndpointReversalBalance_of_residual
    (D : AlignedBiduality sigma tau)
    (h : TrimmedBoundaryResidualReversalBalance
      (k := k) (R := R) (S := S) sigma tau) :
    TrimmedBoundaryEndpointReversalBalance
      (k := k) (R := R) (S := S) sigma tau := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hprojective := FiniteARTranslationData.projectiveStrip_card_eq
    (K := k) sigma tau ARsigma ARtau D
  unfold TrimmedBoundaryResidualReversalBalance at h
  unfold TrimmedBoundaryEndpointReversalBalance
  dsimp only [ARsigma, ARtau] at *
  omega

/-- The trimmed form of the preliminary four-channel reversal balance. -/
def TrimmedPreliminaryHookChannelReversalBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InteriorChannel
          sigma ARsigma) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel
          sigma ARsigma) +
      Fintype.card (ARtau.HookWallInteriorSum tau) =
    Fintype.card
        (FiniteARTranslationData.HookM5Preliminary.InteriorChannel
          tau ARtau) +
      Fintype.card
        (FiniteARTranslationData.HookM6Channel.InteriorChannel tau ARtau) +
      Fintype.card (ARsigma.HookWallInteriorSum sigma)

include k in
/-- The clean local channel identities, aligned dual boundary transport,
and the one-step incidence bridge reduce the entire trimmed preliminary
balance to `TrimmedBoundaryEndpointReversalBalance`. -/
theorem trimmedPreliminaryHookChannelReversalBalance_of_endpoint
    (D : AlignedBiduality sigma tau)
    (h : TrimmedBoundaryEndpointReversalBalance
      (k := k) (R := R) (S := S) sigma tau) :
    TrimmedPreliminaryHookChannelReversalBalance
      (k := k) (R := R) (S := S) sigma tau := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hlocalSigma :=
    ARsigma.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) sigma
  have hlocalTau :=
    ARtau.interiorSourceBoundary_clean_local_channel_card_identity
      (k := k) tau
  have hincidence :=
    ARsigma.interiorSourceBoundary_target_add_literalSource_card_eq sigma
  have hduality :=
    D.interiorSourceBoundaryCommonTarget_card_eq_sourceBoundaryCommonSource
      sigma tau ARsigma ARtau
  unfold TrimmedBoundaryEndpointReversalBalance at h
  unfold TrimmedPreliminaryHookChannelReversalBalance
  dsimp only [ARsigma, ARtau] at h hlocalSigma hlocalTau hincidence hduality ⊢
  omega

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
