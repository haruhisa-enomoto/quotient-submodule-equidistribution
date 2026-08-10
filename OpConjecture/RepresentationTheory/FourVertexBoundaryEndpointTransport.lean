import OpConjecture.RepresentationTheory.FourVertexBoundaryIncidenceBridge

/-!
# Endpoint transport for the trimmed four-vertex boundary

A predecessor mesh rotation identifies the genuine second common-target
source layer with the nonterminal part of the literal common-source layer.
Aligned duality transports the remaining terminal common-source part to the
terminal common-target part on the opposite skeleton.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

namespace FiniteARTranslationData

variable (AR : sigma.FiniteARTranslationData)

/-- Literal-source common-source pairs whose two occurrences can still be
advanced in the trimmed arrow translation. -/
abbrev InteriorLiteralSourceNonterminalCommonSourcePair :=
  {p : AR.InteriorLiteralSourceCommonSourcePair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.1 ∧
      ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.2}

/-- Literal-source common-source pairs for which at least one occurrence is
already terminal in the trimmed arrow translation. -/
abbrev InteriorLiteralSourceTerminalCommonSourcePair :=
  {p : AR.InteriorLiteralSourceCommonSourcePair sigma //
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.1 ∨
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorTarget
        p.1.1.2}

noncomputable instance
    interiorLiteralSourceNonterminalCommonSourcePairFintype :
    Fintype (AR.InteriorLiteralSourceNonterminalCommonSourcePair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorLiteralSourceTerminalCommonSourcePairFintype :
    Fintype (AR.InteriorLiteralSourceTerminalCommonSourcePair sigma) :=
  Fintype.ofFinite _

/-- Split the literal common-source layer into the part that advances and
its terminal endpoint complement. -/
def interiorLiteralSourceCommonSourceEquivNonterminalSumTerminal :
    AR.InteriorLiteralSourceCommonSourcePair sigma ≃
      AR.InteriorLiteralSourceNonterminalCommonSourcePair sigma ⊕
        AR.InteriorLiteralSourceTerminalCommonSourcePair sigma where
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
/-- One predecessor rotation turns a genuine second-layer common-target
pair into a nonterminal literal-source common-source pair. -/
def interiorSecondOnlyCommonTargetEquivLiteralNonterminalCommonSource :
    AR.InteriorSecondOnlySourceCommonTargetPair sigma ≃
      AR.InteriorLiteralSourceNonterminalCommonSourcePair sigma where
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
    have hsource : A.1.1.1 = B.1.1.1 := by
      have hAVal := M.arrowOrbitData_tau_val sigma
        ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩
      have hBVal := M.arrowOrbitData_tau_val sigma
        ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩
      change A.1.1.1 = B.1.1.1
      change
        ((O.tau ⟨p.1.1.1.1.1, p.1.1.1.1.2.1⟩).1).1.1 =
          ((O.tau ⟨p.1.1.1.2.1, p.1.1.1.2.2.1⟩).1).1.1
      rw [congrArg Prod.fst hAVal, congrArg Prod.fst hBVal]
      apply congrArg Subtype.val
      apply congrArg M.tau
      apply Subtype.ext
      exact p.1.1.2
    refine ⟨⟨⟨(A, B), hsource⟩, ?_⟩, ?_⟩
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
    have htarget : A.1.1.2 = B.1.1.2 := by
      have hAVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.1.1, p.1.1.1.1.2.2⟩
      have hBVal := M.arrowOrbitData_tau_symm_val sigma
        ⟨p.1.1.1.2.1, p.1.1.1.2.2.2⟩
      change A.1.1.2 = B.1.1.2
      change
        ((O.tau.symm ⟨p.1.1.1.1.1, p.1.1.1.1.2.2⟩).1).1.2 =
          ((O.tau.symm ⟨p.1.1.1.2.1, p.1.1.1.2.2.2⟩).1).1.2
      rw [congrArg Prod.snd hAVal, congrArg Prod.snd hBVal]
      apply congrArg Subtype.val
      apply congrArg M.tau.symm
      apply Subtype.ext
      exact p.1.1.2
    refine ⟨⟨⟨(A, B), htarget⟩, ?_⟩, ?_⟩
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

/-- Terminal literal common-target pairs whose first occurrence is not in
the literal source layer.  Their second occurrence is therefore the
distinguished projective-source occurrence. -/
abbrev InteriorTerminalFirstNotSourceCommonTargetPair :=
  {p : AR.InteriorLiteralSourceTerminalCommonTargetPair sigma //
    ¬ ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
      p.1.1.1.1}

/-- Different-component part of the oriented injective-target first
boundary. -/
abbrev DifferentOrbitBoundaryM6InjectiveTargetPair :=
  {p : AR.BoundaryM6InjectiveTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.pair}

/-- Same-component part of the oriented injective-target first boundary. -/
abbrev SameOrbitBoundaryM6InjectiveTargetPair :=
  {p : AR.BoundaryM6InjectiveTargetPair sigma //
    let U := (AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma
    U.SameSuccessorOrbit p.pair.1.1 p.pair.1.2}

/-- Different-component part of the terminal branch whose first occurrence
is not on the literal source boundary. -/
abbrev InteriorDifferentOrbitTerminalFirstNotSourceCommonTargetPair :=
  {p : AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma //
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1.1}

noncomputable instance
    interiorTerminalFirstNotSourceCommonTargetPairFintype :
    Fintype (AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance differentOrbitBoundaryM6InjectiveTargetPairFintype :
    Fintype (AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance sameOrbitBoundaryM6InjectiveTargetPairFintype :
    Fintype (AR.SameOrbitBoundaryM6InjectiveTargetPair sigma) :=
  Fintype.ofFinite _

noncomputable instance
    interiorDifferentOrbitTerminalFirstNotSourceCommonTargetPairFintype :
    Fintype
      (AR.InteriorDifferentOrbitTerminalFirstNotSourceCommonTargetPair
        sigma) :=
  Fintype.ofFinite _

omit [DecidableEq iota] in
/-- A terminal common-target pair has an injective common target. -/
theorem interiorLiteralSourceTerminalCommonTarget_target_injective
    (p : AR.InteriorLiteralSourceTerminalCommonTargetPair sigma) :
    Injective (sigma.obj p.1.1.1.2.1.1.2) := by
  rcases p.2 with h | h
  · have hi := ((AR.arMeshRotationData sigma).arrowInterior_target_iff
      sigma p.1.1.1.1).1 h
    rw [← p.1.1.2]
    exact hi
  · exact ((AR.arMeshRotationData sigma).arrowInterior_target_iff
      sigma p.1.1.1.2).1 h

omit [DecidableEq iota] in
/-- The first-not-source terminal branch is automatically on two different
intrinsic successor components.  Its second occurrence is a source, both
occurrences are targets, and a component which is simultaneously at its
source and target boundary is a singleton. -/
theorem interiorTerminalFirstNotSourceCommonTarget_differentOrbit
    (p : AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) :
    InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1.1 := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  let A := p.1.1.1.1.1
  let B := p.1.1.1.1.2
  change ¬ U.SameSuccessorOrbit A B
  intro hsame
  have hBSource : O.InteriorSource B := p.1.1.2.resolve_left p.2
  have hTargetInjective : Injective (sigma.obj B.1.1.2) :=
    AR.interiorLiteralSourceTerminalCommonTarget_target_injective sigma p.1
  have hBTarget : O.InteriorTarget B :=
    (M.arrowInterior_target_iff sigma B).2 hTargetInjective
  have hAB : A = B :=
    U.eq_of_mem_source_of_mem_target_of_sameSuccessorOrbit
      hBSource hBTarget (U.sameSuccessorOrbit_symm hsame)
  apply p.2
  change O.InteriorSource A
  rw [hAB]
  exact hBSource

omit [DecidableEq iota] in
/-- For an injective-target first-boundary pair, belonging to one successor
component is equivalent to equality of the two labelled arrow occurrences. -/
theorem boundaryM6InjectiveTarget_sameSuccessorOrbit_iff
    (p : AR.BoundaryM6InjectiveTargetPair sigma) :
    let U := (AR.arMeshRotationData sigma).arrowInteriorOrbitData sigma
    U.SameSuccessorOrbit p.pair.1.1 p.pair.1.2 ↔
      p.pair.1.1 = p.pair.1.2 := by
  let M := AR.arMeshRotationData sigma
  let O := M.arrowOrbitData sigma
  let U := M.arrowInteriorOrbitData sigma
  let A := p.pair.1.1
  let B := p.pair.1.2
  have hATargetInjective : Injective (sigma.obj A.1.1.2) := by
    rw [p.pair.2]
    exact p.target_injective
  have hATarget : O.InteriorTarget A :=
    (M.arrowInterior_target_iff sigma A).2 hATargetInjective
  constructor
  · intro hsame
    exact (U.eq_of_mem_source_of_mem_target_of_sameSuccessorOrbit
      p.first_source hATarget hsame).symm
  · intro hEq
    rw [hEq]
    exact U.sameSuccessorOrbit_refl B

omit [DecidableEq iota] in
/-- A same-component injective-target first-boundary pair is precisely a
diagonal second-source pair. -/
def sameOrbitBoundaryM6InjectiveTargetEquivSecondSourceDiagonal :
    AR.SameOrbitBoundaryM6InjectiveTargetPair sigma ≃
      AR.BoundaryM6InjectiveTargetSecondSourceDiagonalPair sigma where
  toFun p := by
    have hEq :=
      (AR.boundaryM6InjectiveTarget_sameSuccessorOrbit_iff sigma p.1).1 p.2
    have hSecondSource :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.pair.1.2 := by
      rw [← hEq]
      exact p.1.first_source
    exact ⟨⟨p.1, Or.inl hSecondSource⟩, hEq⟩
  invFun p :=
    ⟨p.1.1,
      (AR.boundaryM6InjectiveTarget_sameSuccessorOrbit_iff sigma p.1.1).2
        p.2⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [DecidableEq iota] in
include k AR in
/-- Same-component injective-target first-boundary pairs are exactly the
diagonal short projective strips. -/
def sameOrbitBoundaryM6InjectiveTargetEquivHookShortStrip :
    AR.SameOrbitBoundaryM6InjectiveTargetPair sigma ≃
      AR.HookShortStrip sigma :=
  (AR.sameOrbitBoundaryM6InjectiveTargetEquivSecondSourceDiagonal sigma).trans
    (AR.hookShortStripEquivM6InjectiveTargetSecondSourceDiagonal
      (k := k) sigma).symm

/-- The full injective-target first boundary splits exactly into its
different-component part and the diagonal short-strip correction. -/
def boundaryM6InjectiveTargetPairEquivDifferentOrbitSumShort
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R] :
    AR.BoundaryM6InjectiveTargetPair sigma ≃
      AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma ⊕
        AR.HookShortStrip sigma := by
  classical
  let P : AR.BoundaryM6InjectiveTargetPair sigma → Prop :=
    fun p ↦ InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.pair
  let E := (Equiv.sumCompl P).symm
  let S : {p : AR.BoundaryM6InjectiveTargetPair sigma // ¬ P p} ≃
      AR.SameOrbitBoundaryM6InjectiveTargetPair sigma := by
    apply (Equiv.refl _).subtypeEquiv
    intro p
    simp [P, InteriorCommonTargetArrowPair.DifferentOrbit]
  exact E.trans <| Equiv.sumCongr (Equiv.refl _)
    (S.trans <| AR.sameOrbitBoundaryM6InjectiveTargetEquivHookShortStrip
      (k := k) sigma)

omit [DecidableEq iota] in
/-- Cardinal form of the different-component/short-strip split of the full
injective-target first boundary. -/
theorem boundaryM6InjectiveTargetPair_card_eq_differentOrbit_add_short
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) =
      Fintype.card (AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma) +
        Fintype.card (AR.HookShortStrip sigma) := by
  rw [Fintype.card_congr
    (AR.boundaryM6InjectiveTargetPairEquivDifferentOrbitSumShort
      (k := k) sigma)]
  exact Fintype.card_sum

/-- Removing the diagonal short-strip fiber from the existing exhaustive
injective-target classification leaves exactly the different-component
first-only and off-diagonal wall strata. -/
theorem differentOrbitBoundaryM6InjectiveTargetPair_card_eq_firstOnly_add_wall
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Fintype.card (AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma) =
      Fintype.card (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
        Fintype.card
          (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) := by
  have hall :=
    AR.boundaryM6InjectiveTargetPair_card_eq_firstOnly_add_short_add_wall
      (k := k) sigma
  have hsplit :=
    AR.boundaryM6InjectiveTargetPair_card_eq_differentOrbit_add_short
      (k := k) sigma
  omega

omit [DecidableEq iota] in
/-- Forgetting the redundant different-component witness is an exact
equivalence on the first-not-source terminal branch. -/
def interiorDifferentOrbitTerminalFirstNotSourceEquiv :
    AR.InteriorDifferentOrbitTerminalFirstNotSourceCommonTargetPair sigma ≃
      AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma where
  toFun p := p.1
  invFun p :=
    ⟨p, AR.interiorTerminalFirstNotSourceCommonTarget_differentOrbit sigma p⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq iota] in
/-- Choosing the first occurrence when possible splits a terminal literal
common-target pair into the oriented injective-target family and the
first-not-source remainder. -/
def interiorLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource :
    AR.InteriorLiteralSourceTerminalCommonTargetPair sigma ≃
      AR.BoundaryM6InjectiveTargetPair sigma ⊕
        AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma where
  toFun p := by
    classical
    by_cases hfirst :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.1.1
    · exact Sum.inl
        { pair := p.1.1
          first_source := hfirst
          target_injective :=
            AR.interiorLiteralSourceTerminalCommonTarget_target_injective
              sigma p }
    · exact Sum.inr ⟨p, hfirst⟩
  invFun p := by
    rcases p with p | p
    · exact ⟨⟨p.pair, Or.inl p.first_source⟩, Or.inr <|
        ((AR.arMeshRotationData sigma).arrowInterior_target_iff
          sigma p.pair.1.2).2 p.target_injective⟩
    · exact p.1
  left_inv p := by
    classical
    by_cases hfirst :
        ((AR.arMeshRotationData sigma).arrowOrbitData sigma).InteriorSource
          p.1.1.1.1
    · simp [hfirst]
    · simp [hfirst]
  right_inv p := by
    classical
    rcases p with p | p
    · simp [p.first_source]
    · simp [p.2]

omit [DecidableEq iota] in
/-- Cardinal form of the oriented terminal-corner split. -/
theorem interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource :
    Fintype.card
        (AR.InteriorLiteralSourceTerminalCommonTargetPair sigma) =
      Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) +
        Fintype.card
          (AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) := by
  rw [Fintype.card_congr
    (AR.interiorLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource
      sigma)]
  exact Fintype.card_sum

/-- The oriented terminal split restricts exactly to different components.
The first-not-source branch needs no extra restriction because its
different-component property is automatic. -/
def interiorDifferentOrbitLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource :
    AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair sigma ≃
      AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma ⊕
        AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma := by
  let E :=
    AR.interiorLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource
      sigma
  let P : AR.InteriorLiteralSourceTerminalCommonTargetPair sigma → Prop :=
    fun p ↦ InteriorCommonTargetArrowPair.DifferentOrbit sigma AR p.1.1
  let Q : AR.BoundaryM6InjectiveTargetPair sigma ⊕
      AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma → Prop :=
    fun p ↦ P (E.symm p)
  have hPQ : ∀ p, P p ↔ Q (E p) := by
    intro p
    change P p ↔ P (E.symm (E p))
    rw [E.symm_apply_apply]
  let F := (E.subtypeEquiv hPQ).trans (Equiv.subtypeSum (p := Q))
  have F' :
      AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair sigma ≃
        AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma ⊕
          AR.InteriorDifferentOrbitTerminalFirstNotSourceCommonTargetPair
            sigma := by
    simpa [P, Q, E,
      interiorLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource]
      using F
  exact F'.trans <| Equiv.sumCongr (Equiv.refl _)
    (AR.interiorDifferentOrbitTerminalFirstNotSourceEquiv sigma)

omit [DecidableEq iota] in
/-- Cardinal form of the different-component oriented terminal split. -/
theorem interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource :
    Fintype.card
        (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
          sigma) =
      Fintype.card (AR.DifferentOrbitBoundaryM6InjectiveTargetPair sigma) +
        Fintype.card
          (AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) := by
  rw [Fintype.card_congr
    (AR.interiorDifferentOrbitLiteralSourceTerminalCommonTargetEquivInjectiveSumFirstNotSource
      sigma)]
  exact Fintype.card_sum

omit [DecidableEq iota] in
/-- Eliminating the common different-orbit injective-target summand relates
the manuscript's terminal correction directly to the unrestricted oriented
terminal split and the diagonal short-strip term. -/
theorem interiorDifferentOrbitTerminal_add_short_card_eq_injective_add_firstNotSource
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Fintype.card
          (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
            sigma) +
        Fintype.card (AR.HookShortStrip sigma) =
      Fintype.card (AR.BoundaryM6InjectiveTargetPair sigma) +
        Fintype.card
          (AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) := by
  have hterminal :=
    AR.interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      sigma
  have hinjective :=
    AR.boundaryM6InjectiveTargetPair_card_eq_differentOrbit_add_short
      (k := k) sigma
  omega

/-- Fully expanded terminal different-orbit boundary: first-not-source
terms, first-only injective-target terms, and off-diagonal wall terms. -/
theorem interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_firstNotSource_add_firstOnly_add_wall
    (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R] :
    Fintype.card
        (AR.InteriorDifferentOrbitLiteralSourceTerminalCommonTargetPair
          sigma) =
      Fintype.card
          (AR.InteriorTerminalFirstNotSourceCommonTargetPair sigma) +
        Fintype.card (AR.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
          Fintype.card
            (AR.HookWallInteriorInjectiveTargetOffDiagonal sigma) := by
  have hterminal :=
    AR.interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      sigma
  have hinjective :=
    AR.differentOrbitBoundaryM6InjectiveTargetPair_card_eq_firstOnly_add_wall
      (k := k) sigma
  omega

end FiniteARTranslationData

namespace AlignedBiduality

universe w

variable {S : Type u}
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing S]
  {kappa : Type w} [Fintype kappa] [DecidableEq kappa]
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)
  (D : AlignedBiduality sigma tau)
  (ARsigma : sigma.FiniteARTranslationData)
  (ARtau : tau.FiniteARTranslationData)

/-- Duality identifies terminal literal common-target pairs on the dual
skeleton with terminal literal common-source pairs on the source skeleton. -/
def interiorLiteralSourceTerminalCommonTargetEquivCommonSource :
    ARtau.InteriorLiteralSourceTerminalCommonTargetPair tau ≃
      ARsigma.InteriorLiteralSourceTerminalCommonSourcePair sigma where
  toFun p := by
    let E := D.interiorCommonTargetEquivCommonSource
      sigma tau ARsigma ARtau
    refine ⟨⟨E p.1.1, ?_⟩, ?_⟩
    · rcases p.2 with h | h
      · exact Or.inl
          ((AlignedBiduality.pullbackInterior_target_iff_source
            sigma tau D ARsigma ARtau p.1.1.1.1).1 h)
      · exact Or.inr
          ((AlignedBiduality.pullbackInterior_target_iff_source
            sigma tau D ARsigma ARtau p.1.1.1.2).1 h)
    · rcases p.1.2 with h | h
      · exact Or.inl ((D.pullbackInterior_source_iff_target
          sigma tau ARsigma ARtau p.1.1.1.1).1 h)
      · exact Or.inr ((D.pullbackInterior_source_iff_target
          sigma tau ARsigma ARtau p.1.1.1.2).1 h)
  invFun p := by
    let E := D.interiorCommonTargetEquivCommonSource
      sigma tau ARsigma ARtau
    let q := E.symm p.1.1
    have hq : E q = p.1.1 := E.apply_symm_apply p.1.1
    have hfirst :
        D.pullbackInteriorArrow sigma tau ARsigma ARtau q.1.1 =
          p.1.1.1.1 := congrArg
      (fun r : ARsigma.InteriorCommonSourceArrowPair sigma ↦ r.1.1) hq
    have hsecond :
        D.pullbackInteriorArrow sigma tau ARsigma ARtau q.1.2 =
          p.1.1.1.2 := congrArg
      (fun r : ARsigma.InteriorCommonSourceArrowPair sigma ↦ r.1.2) hq
    refine ⟨⟨q, ?_⟩, ?_⟩
    · rcases p.2 with h | h
      · left
        apply (D.pullbackInterior_source_iff_target
          sigma tau ARsigma ARtau q.1.1).2
        rw [hfirst]
        exact h
      · right
        apply (D.pullbackInterior_source_iff_target
          sigma tau ARsigma ARtau q.1.2).2
        rw [hsecond]
        exact h
    · rcases p.1.2 with h | h
      · left
        apply (AlignedBiduality.pullbackInterior_target_iff_source
          sigma tau D ARsigma ARtau q.1.1).2
        rw [hfirst]
        exact h
      · right
        apply (AlignedBiduality.pullbackInterior_target_iff_source
          sigma tau D ARsigma ARtau q.1.2).2
        rw [hsecond]
        exact h
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (D.interiorCommonTargetEquivCommonSource
      sigma tau ARsigma ARtau).symm_apply_apply p.1.1
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (D.interiorCommonTargetEquivCommonSource
      sigma tau ARsigma ARtau).apply_symm_apply p.1.1

end AlignedBiduality

universe w

variable {S : Type u}
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing S]
  {kappa : Type w} [Fintype kappa] [DecidableEq kappa]
  (tau : IndecomposableSkeleton.{u, w, u} S kappa)

omit [DecidableEq iota] [DecidableEq kappa] in
/-- The literal common-source layer is the disjoint sum of the genuine
second common-target layer and the dual terminal common-target layer. -/
theorem interiorLiteralSourceCommonSource_card_eq_secondOnly_add_dualTerminal
    (D : AlignedBiduality sigma tau) :
    let ARsigma := sigma.finiteDimensionalARTranslationData k R
    let ARtau := tau.finiteDimensionalARTranslationData k S
    Fintype.card (ARsigma.InteriorLiteralSourceCommonSourcePair sigma) =
      Fintype.card
          (ARsigma.InteriorSecondOnlySourceCommonTargetPair sigma) +
        Fintype.card
          (ARtau.InteriorLiteralSourceTerminalCommonTargetPair tau) := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hsplit := Fintype.card_congr
    (ARsigma.interiorLiteralSourceCommonSourceEquivNonterminalSumTerminal
      sigma)
  have hrotate := Fintype.card_congr
    (ARsigma.interiorSecondOnlyCommonTargetEquivLiteralNonterminalCommonSource
      sigma)
  have hdual := Fintype.card_congr
    (D.interiorLiteralSourceTerminalCommonTargetEquivCommonSource
      sigma tau ARsigma ARtau)
  simp only [Fintype.card_sum] at hsplit
  dsimp only [ARsigma, ARtau] at *
  omega

include k in
/-- Manuscript-facing expansion of the unconditional different-orbit
endpoint balance.  The terminal boundary is written in the three actual
oriented strata which remain after the diagonal short strip is removed. -/
theorem trimmedDifferentOrbitEndpointReversalBalance_expanded
    (D : AlignedBiduality sigma tau) :
    let ARsigma := sigma.finiteDimensionalARTranslationData k R
    let ARtau := tau.finiteDimensionalARTranslationData k S
    Fintype.card
          (ARsigma.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair
            sigma) +
        Fintype.card
          (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair sigma) +
        Fintype.card
          (ARsigma.BoundaryM6InjectiveTargetFirstOnlyPair sigma) +
        Fintype.card
          (ARsigma.HookWallInteriorInjectiveTargetOffDiagonal sigma) +
      Fintype.card
          (ARtau.InteriorDifferentOrbitSecondOnlySourceCommonTargetPair tau) +
        Fintype.card
          (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair tau) +
        Fintype.card
          (ARtau.BoundaryM6InjectiveTargetFirstOnlyPair tau) +
        Fintype.card
          (ARtau.HookWallInteriorInjectiveTargetOffDiagonal tau) =
    Fintype.card
          (ARsigma.InteriorDifferentOrbitLiteralSourceCommonSourcePair
            sigma) +
      Fintype.card
        (ARtau.InteriorDifferentOrbitLiteralSourceCommonSourcePair tau) := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hbalance := trimmedDifferentOrbitEndpointReversalBalance
    (k := k) (R := R) (S := S) sigma tau D
  have hsigma :=
    ARsigma.interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_firstNotSource_add_firstOnly_add_wall
      (k := k) sigma
  have htau :=
    ARtau.interiorDifferentOrbitLiteralSourceTerminalCommonTarget_card_eq_firstNotSource_add_firstOnly_add_wall
      (k := k) tau
  unfold TrimmedDifferentOrbitEndpointReversalBalance at hbalance
  dsimp only [ARsigma, ARtau] at *
  omega

/-- After second-layer incidence and dual terminal transport, the residual
trimmed endpoint equation reduces to the symmetric terminal-corner equation. -/
def TrimmedTerminalCornerReversalBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorLiteralSourceTerminalCommonTargetPair sigma) +
      Fintype.card (ARtau.BoundaryM6InjectiveTargetPair tau) +
        Fintype.card (ARtau.BoundaryM6ReverseLastPair tau) =
    Fintype.card
        (ARtau.InteriorLiteralSourceTerminalCommonTargetPair tau) +
      Fintype.card (ARsigma.BoundaryM6InjectiveTargetPair sigma) +
        Fintype.card (ARsigma.BoundaryM6ReverseLastPair sigma)

/-- After the oriented injective-target summands cancel, the terminal
corner equation compares only the first-not-source terminal remainder and
the reverse-last exception. -/
def TrimmedTerminalReverseExceptionBalance : Prop :=
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  Fintype.card
        (ARsigma.InteriorTerminalFirstNotSourceCommonTargetPair sigma) +
      Fintype.card (ARtau.BoundaryM6ReverseLastPair tau) =
    Fintype.card
        (ARtau.InteriorTerminalFirstNotSourceCommonTargetPair tau) +
      Fintype.card (ARsigma.BoundaryM6ReverseLastPair sigma)

omit [DecidableEq iota] [DecidableEq kappa] in
include k in
/-- The terminal/reverse-exception equation implies the terminal-corner
balance after the two injective-target summands cancel. -/
theorem trimmedTerminalCornerReversalBalance_of_reverseException
    (h : TrimmedTerminalReverseExceptionBalance
      (k := k) (R := R) (S := S) sigma tau) :
    TrimmedTerminalCornerReversalBalance
      (k := k) (R := R) (S := S) sigma tau := by
  let ARsigma := sigma.finiteDimensionalARTranslationData k R
  let ARtau := tau.finiteDimensionalARTranslationData k S
  have hsigma :=
    ARsigma.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      sigma
  have htau :=
    ARtau.interiorLiteralSourceTerminalCommonTarget_card_eq_injective_add_firstNotSource
      tau
  unfold TrimmedTerminalReverseExceptionBalance at h
  unfold TrimmedTerminalCornerReversalBalance
  dsimp only [ARsigma, ARtau] at *
  omega

omit [DecidableEq iota] [DecidableEq kappa] in
include k in
/-- The terminal-corner balance implies the residual trimmed endpoint
balance. -/
theorem trimmedBoundaryResidualReversalBalance_of_terminalCorner
    (D : AlignedBiduality sigma tau)
    (h : TrimmedTerminalCornerReversalBalance
      (k := k) (R := R) (S := S) sigma tau) :
    TrimmedBoundaryResidualReversalBalance
      (k := k) (R := R) (S := S) sigma tau := by
  have hliteral :=
    interiorLiteralSourceCommonSource_card_eq_secondOnly_add_dualTerminal
      (k := k) sigma tau D
  unfold TrimmedTerminalCornerReversalBalance at h
  unfold TrimmedBoundaryResidualReversalBalance
  omega

end OpConjecture.IndecomposableSkeleton
