import OpConjecture.RepresentationTheory.FourVertexOuterEndpointTwoSourceTransport
import OpConjecture.RepresentationTheory.FourVertexDifferentOrbitTargetCorners

/-!
# Short-chain boundary position of outer first arrows

For an oriented outer pair the first source is simultaneously projective
and injective.  In the manuscript's chain coordinates this forces the
first arrow's mesh orbit to be a length-two chain: the arrow itself lies
on the injective-source boundary layer, and its mesh translate lies on
the projective-target boundary layer.  These membership facts are the
boundary-position input for the index-range reading of the two
preliminary sums in the strip-conservation proof.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {K R : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

omit [DecidableEq ι] in
/-- The successor orbit of any arrow with projective-injective source and
nonprojective target is exactly the length-two chain consisting of the
arrow and its mesh translate. -/
theorem piSourceArrow_sameSuccessorOrbit_iff
    (α x : σ.IrreduciblePair)
    (hP : Projective (σ.obj α.1.1))
    (hI : Injective (σ.obj α.1.1))
    (ht : ¬ Projective (σ.obj α.1.2)) :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit α x ↔
      x = α ∨
        x = (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
          ⟨α, ht⟩).1 := by
  classical
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let sa := (O.tau ⟨α, ht⟩).1
  have hPs : Projective (σ.obj sa.1.2) := by
    have h := (AR.arMeshRotationData σ).arrowOrbitData_tau_val σ ⟨α, ht⟩
    have htarget : sa.1.2 = α.1.1 := congrArg Prod.snd h
    rw [htarget]
    exact hP
  have hIs : ¬ Injective (σ.obj sa.1.1) := (O.tau ⟨α, ht⟩).2
  have hsucc1 : O.successor α = α :=
    O.successor_eq_self_of_mem_target hI
  have hsuccs : O.successor sa = α := by
    have hval : (O.tau.symm ⟨sa, hIs⟩).1 = α := by
      have : O.tau.symm ⟨sa, hIs⟩ = ⟨α, ht⟩ := by
        apply O.tau.symm_apply_eq.2
        apply Subtype.ext
        rfl
      exact congrArg Subtype.val this
    simpa [BoundaryTranslationChains.Data.successor, hIs] using hval
  have key : ∀ m (x : σ.IrreduciblePair),
      (O.successor^[m]) x = α → x = α ∨ x = sa := by
    intro m
    induction m with
    | zero => exact fun x hx ↦ Or.inl hx
    | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply] at hx
      rcases ih (O.successor x) hx with hx1 | hxs
      · by_cases hIx : Injective (σ.obj x.1.1)
        · left
          rw [← O.successor_eq_self_of_mem_target hIx]
          exact hx1
        · right
          have hval : (O.tau.symm ⟨x, hIx⟩).1 = α := by
            simpa [BoundaryTranslationChains.Data.successor, hIx]
              using hx1
          have hsub : O.tau.symm ⟨x, hIx⟩ = ⟨α, ht⟩ := Subtype.ext hval
          have hx2 : (⟨x, hIx⟩ : {a : σ.IrreduciblePair //
              ¬ Injective (σ.obj a.1.1)}) = O.tau ⟨α, ht⟩ :=
            O.tau.symm_apply_eq.1 hsub
          exact congrArg Subtype.val hx2
      · exfalso
        by_cases hIx : Injective (σ.obj x.1.1)
        · have hxeq : x = sa := by
            rw [← O.successor_eq_self_of_mem_target hIx]
            exact hxs
          exact hIs (hxeq ▸ hIx)
        · have hprop : ¬ Projective (σ.obj (O.successor x).1.2) := by
            simpa [BoundaryTranslationChains.Data.successor, hIx] using
              (O.tau.symm ⟨x, hIx⟩).2
          exact hprop (hxs ▸ hPs)
  constructor
  · rintro ⟨m, n, h⟩
    exact key n x (by rw [← h, Function.iterate_fixed hsucc1 m])
  · rintro (rfl | rfl)
    · exact ⟨0, 0, rfl⟩
    · exact ⟨0, 1, by simpa using hsuccs.symm⟩

namespace FirstProjectiveInjectiveDifferentOrbitOuterPair

variable {σ AR} (p : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ)

omit [DecidableEq ι] in
/-- The first arrow of an outer pair lies on the source boundary of the
global mesh rotation: its mesh translate ends at the projective first
source. -/
theorem first_twoSource :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoSource p.pair.1.1 :=
  ((AR.arMeshRotationData σ).arrowOrbit_twoSource_iff σ p.pair.1.1).2
    (Or.inr p.first_projective)

omit [DecidableEq ι] in
/-- The first arrow of an outer pair lies on the target boundary of the
global mesh rotation: it literally starts at the injective first
source. -/
theorem first_twoTarget :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget p.pair.1.1 :=
  ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff σ p.pair.1.1).2
    (Or.inl p.first_injective)

omit [DecidableEq ι] in
/-- The first arrow of an outer pair is deleted by the interior
trimming. -/
theorem first_not_interiorArrow :
    ¬ IsInteriorArrow σ p.pair.1.1 := by
  intro h
  exact h.2 p.first_injective

/-- The mesh translate of the first arrow: the terminal occurrence of its
length-two chain. -/
def firstMeshTranslate : σ.IrreduciblePair :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨p.pair.1.1, p.target_nonprojective⟩).1

omit [DecidableEq ι] in
/-- The mesh translate of the first arrow ends at the projective first
source. -/
theorem firstMeshTranslate_mem_source :
    Projective (σ.obj (p.firstMeshTranslate).1.2) := by
  have h := ((AR.arMeshRotationData σ)).arrowOrbitData_tau_val σ
    ⟨p.pair.1.1, p.target_nonprojective⟩
  have htarget : (p.firstMeshTranslate).1.2 = p.pair.1.1.1.1 :=
    congrArg Prod.snd h
  rw [htarget]
  exact p.first_projective

omit [DecidableEq ι] in
/-- The mesh translate of the first arrow starts at a noninjective
label. -/
theorem firstMeshTranslate_not_mem_target :
    ¬ Injective (σ.obj (p.firstMeshTranslate).1.1) :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨p.pair.1.1, p.target_nonprojective⟩).2

omit [DecidableEq ι] in
/-- The successor orbit of an outer first arrow is exactly its own
length-two mesh chain: the arrow itself and its mesh translate.  This is
the manuscript's `L = 2` recognition for the chain through a
projective-injective source. -/
theorem sameSuccessorOrbit_first_iff (x : σ.IrreduciblePair) :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
        p.pair.1.1 x ↔
      x = p.pair.1.1 ∨ x = p.firstMeshTranslate := by
  classical
  let O := (AR.arMeshRotationData σ).arrowOrbitData σ
  let a1 := p.pair.1.1
  let sa1 := p.firstMeshTranslate
  have hI1 : Injective (σ.obj a1.1.1) := p.first_injective
  have hPs : Projective (σ.obj sa1.1.2) :=
    p.firstMeshTranslate_mem_source
  have hIs : ¬ Injective (σ.obj sa1.1.1) :=
    p.firstMeshTranslate_not_mem_target
  have hsucc1 : O.successor a1 = a1 :=
    O.successor_eq_self_of_mem_target hI1
  have hsuccs : O.successor sa1 = a1 := by
    have hval : (O.tau.symm ⟨sa1, hIs⟩).1 = a1 := by
      have : O.tau.symm ⟨sa1, hIs⟩ = ⟨a1, p.target_nonprojective⟩ := by
        apply O.tau.symm_apply_eq.2
        apply Subtype.ext
        rfl
      exact congrArg Subtype.val this
    simpa [BoundaryTranslationChains.Data.successor, hIs] using hval
  have key : ∀ m (x : σ.IrreduciblePair),
      (O.successor^[m]) x = a1 → x = a1 ∨ x = sa1 := by
    intro m
    induction m with
    | zero => exact fun x hx ↦ Or.inl hx
    | succ m ih =>
      intro x hx
      rw [Function.iterate_succ_apply] at hx
      rcases ih (O.successor x) hx with hx1 | hxs
      · by_cases hIx : Injective (σ.obj x.1.1)
        · left
          rw [← O.successor_eq_self_of_mem_target hIx]
          exact hx1
        · right
          have hval : (O.tau.symm ⟨x, hIx⟩).1 = a1 := by
            simpa [BoundaryTranslationChains.Data.successor, hIx]
              using hx1
          have hsub : O.tau.symm ⟨x, hIx⟩ =
              ⟨a1, p.target_nonprojective⟩ := Subtype.ext hval
          have hx2 : (⟨x, hIx⟩ : {a : σ.IrreduciblePair //
              ¬ Injective (σ.obj a.1.1)}) =
              O.tau ⟨a1, p.target_nonprojective⟩ :=
            O.tau.symm_apply_eq.1 hsub
          exact congrArg Subtype.val hx2
      · exfalso
        by_cases hIx : Injective (σ.obj x.1.1)
        · have hxeq : x = sa1 := by
            rw [← O.successor_eq_self_of_mem_target hIx]
            exact hxs
          exact hIs (hxeq ▸ hIx)
        · have hprop : ¬ Projective (σ.obj (O.successor x).1.2) := by
            simpa [BoundaryTranslationChains.Data.successor, hIx] using
              (O.tau.symm ⟨x, hIx⟩).2
          exact hprop (hxs ▸ hPs)
  constructor
  · rintro ⟨m, n, h⟩
    have hn : (O.successor^[n]) x = a1 → x = a1 ∨ x = sa1 := key n x
    exact hn (by rw [← h, Function.iterate_fixed hsucc1 m])
  · rintro (rfl | rfl)
    · exact ⟨0, 0, rfl⟩
    · exact ⟨0, 1, by simpa using hsuccs.symm⟩

omit [DecidableEq ι] in
/-- The second arrow of an outer pair is not the first arrow. -/
theorem second_ne_first : p.pair.1.2 ≠ p.pair.1.1 := fun h ↦
  p.differentOrbit
    ((p.sameSuccessorOrbit_first_iff p.pair.1.2).2 (Or.inl h))

omit [DecidableEq ι] in
/-- The second arrow of an outer pair is not the mesh translate of the
first arrow either: by the length-two orbit recognition, these two
exclusions are exactly the different-orbit condition. -/
theorem second_ne_firstMeshTranslate :
    p.pair.1.2 ≠ p.firstMeshTranslate := fun h ↦
  p.differentOrbit
    ((p.sameSuccessorOrbit_first_iff p.pair.1.2).2 (Or.inr h))

omit [DecidableEq ι] in
/-- No admissible strip triple has its first arrow on the length-two
mesh chain of an outer first arrow: the manuscript's statement that
chains with `L ≤ 2` contribute no admissible triples. -/
theorem not_sameSuccessorOrbit_stripTriple_firstArrow
    (H : AR.StripAdmissibleTriple σ) :
    ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
        p.pair.1.1 ⟨(H.a, H.u), H.a_to_u⟩ := by
  intro h
  rcases (p.sameSuccessorOrbit_first_iff _).1 h with h1 | h2
  · have hni : ¬ Injective (σ.obj H.a) := by
      have htau := (AR.arTranslation σ ⟨H.b, H.b_nonprojective⟩).2
      rw [H.tau_b] at htau
      exact htau
    apply hni
    have hval : H.a = p.pair.1.1.1.1 := congrArg (fun q ↦ q.1.1) h1
    rw [hval]
    exact p.first_injective
  · apply H.u_nonprojective
    have hval : H.u = (p.firstMeshTranslate).1.2 :=
      congrArg (fun q ↦ q.1.2) h2
    rw [hval]
    exact p.firstMeshTranslate_mem_source

/-- Every outer pair lies in the fixed projective/injective-source
corner of the full different-orbit boundary: its first source witnesses
both status conditions at once.  In the manuscript's coordinates the
surviving outer strata are therefore corner terms of the boundary
reading, fixed pointwise by the full square shift. -/
def toOuterIntersection :
    AR.DifferentOrbitNonprojectiveTargetProjectiveInjectiveSourcePair σ :=
  ⟨⟨⟨p.pair, p.target_nonprojective, Or.inl p.first_projective⟩,
    Or.inl p.first_injective⟩, p.differentOrbit⟩

omit [DecidableEq ι] in
/-- The corner presentation of outer pairs is injective. -/
theorem toOuterIntersection_injective :
    Function.Injective
      (toOuterIntersection (σ := σ) (AR := AR)) := by
  intro p q h
  apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
  exact congrArg (fun x ↦ x.1.1.1) h

/-- Source-boundary presentation of an outer pair: its first arrow lies
on the source boundary layer. -/
def toSourceBoundary :
    AR.DifferentOrbitSourceBoundaryCommonTargetArrowPair σ :=
  ⟨⟨p.pair, Or.inl p.first_twoSource⟩, p.differentOrbit⟩

omit [DecidableEq ι] in
/-- The full different-orbit square shift fixes every outer pair
pointwise: outer pairs are corner terms of the manuscript's boundary
reading. -/
theorem squareShift_toSourceBoundary_fixed :
    (AR.differentOrbitCommonTargetBoundaryEquiv σ
      p.toSourceBoundary).1.1 = p.pair :=
  AR.differentOrbitCommonTargetBoundaryEquiv_apply_outerIntersection σ
    ⟨p.toSourceBoundary,
      p.target_nonprojective, Or.inl p.first_projective,
      Or.inl p.first_injective⟩

end FirstProjectiveInjectiveDifferentOrbitOuterPair

omit [DecidableEq ι] in
/-- In the injective-target outer stratum the second arrow survives the
interior trimming: its source is nonprojective and noninjective and its
target is the nonprojective common target. -/
theorem firstPISecondNonprojectiveNoninjectiveTargetInjective_second_interior
    (q : AR.FirstPISecondNonprojectiveNoninjectiveTargetInjectiveOuterPair
      σ) :
    IsInteriorArrow σ q.1.pair.1.2 := by
  constructor
  · rw [← q.1.pair.2]
    exact q.1.target_nonprojective
  · exact q.2.2.1

omit [DecidableEq ι] in
/-- In the injective-second outer stratum the second arrow is deleted by
the interior trimming: it literally starts at an injective label. -/
theorem firstPISecondInjectiveTranslatedTargetNonprojective_second_not_interior
    (q : AR.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
      σ) :
    ¬ IsInteriorArrow σ q.1.pair.1.2 := fun h ↦
  h.2 q.2.2.1

omit [DecidableEq ι] in
/-- In the injective-second outer stratum the second arrow lies on the
target boundary layer of the mesh rotation. -/
theorem firstPISecondInjectiveTranslatedTargetNonprojective_second_twoTarget
    (q : AR.FirstPISecondInjectiveTranslatedTargetNonprojectiveOuterPair
      σ) :
    ((AR.arMeshRotationData σ).arrowOrbitData σ).TwoTarget
      q.1.pair.1.2 :=
  ((AR.arMeshRotationData σ).arrowOrbit_twoTarget_iff σ q.1.pair.1.2).2
    (Or.inl q.2.2.1)

/-- Every injective-fourth `M6` term reads off as an outer pair: the
fourth label is a projective-injective vertex with an arrow to the hook
source, and the mesh translate of the triple's first arrow provides the
second occurrence at the same common target.  This is the manuscript's
assignment of an `M4`-term to the pair of its chain orbit and the short
orbit of its associated arrow. -/
def hookM6InjectiveFourthToOuterPair
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ := by
  classical
  let E := M.1.1
  have hza := HookFourthExtension.z_projective_and_z_to_a_of_a_nonprojective
    (σ := σ) (AR := AR) (E := E) M.1.2
  let first : σ.IrreduciblePair := ⟨(E.z, E.triple.a), hza.2⟩
  let secondSub := ((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨⟨(E.triple.a, E.triple.u), E.triple.a_to_u⟩,
      E.triple.u_nonprojective⟩
  have hsecondTarget : secondSub.1.1.2 = E.triple.a := by
    have h := (AR.arMeshRotationData σ).arrowOrbitData_tau_val σ
      ⟨⟨(E.triple.a, E.triple.u), E.triple.a_to_u⟩,
        E.triple.u_nonprojective⟩
    exact congrArg Prod.snd h
  refine ⟨⟨(first, secondSub.1), hsecondTarget.symm⟩,
    M.1.2, hza.1, M.2, ?_⟩
  show ¬ ((AR.arMeshRotationData σ).arrowOrbitData σ).SameSuccessorOrbit
      first secondSub.1
  intro hsame
  rcases (piSourceArrow_sameSuccessorOrbit_iff σ AR first secondSub.1
      hza.1 M.2 M.1.2).1 hsame with h1 | h2
  · have hsrc : secondSub.1.1.1 = E.z := congrArg (fun q ↦ q.1.1) h1
    have hni : ¬ Injective (σ.obj secondSub.1.1.1) := secondSub.2
    rw [hsrc] at hni
    exact hni M.2
  · have htar : secondSub.1.1.2 =
        (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
          ⟨first, M.1.2⟩).1.1.2 := congrArg (fun q ↦ q.1.2) h2
    have hz : (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
        ⟨first, M.1.2⟩).1.1.2 = E.z := by
      have hval := (AR.arMeshRotationData σ).arrowOrbitData_tau_val σ
        ⟨first, M.1.2⟩
      exact congrArg Prod.snd hval
    rw [hz, hsecondTarget] at htar
    exact E.z_not_mem (htar ▸ E.triple.mem_support_a)

/-- The outer-pair reading of injective-fourth `M6` terms is injective:
the pair determines the fourth label, the hook source, and by mesh
injectivity the middle and third labels. -/
theorem hookM6InjectiveFourthToOuterPair_injective :
    Function.Injective
      (hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)) := by
  intro M N h
  have hz : M.1.1.z = N.1.1.z :=
    congrArg (fun q ↦ q.pair.1.1.1.1) h
  have ha : M.1.1.triple.a = N.1.1.triple.a :=
    congrArg (fun q ↦ q.pair.1.1.1.2) h
  have hsrc : (AR.arTranslation σ
      ⟨M.1.1.triple.u, M.1.1.triple.u_nonprojective⟩).1 =
      (AR.arTranslation σ
        ⟨N.1.1.triple.u, N.1.1.triple.u_nonprojective⟩).1 :=
    congrArg (fun q ↦ q.pair.1.2.1.1) h
  have hu : M.1.1.triple.u = N.1.1.triple.u := by
    have h2 := AR.arTranslation_injective σ (Subtype.ext hsrc)
    exact congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) h2
  have hb : M.1.1.triple.b = N.1.1.triple.b := by
    have hval : (AR.arTranslation σ
        ⟨M.1.1.triple.b, M.1.1.triple.b_nonprojective⟩).1 =
        (AR.arTranslation σ
          ⟨N.1.1.triple.b, N.1.1.triple.b_nonprojective⟩).1 := by
      rw [M.1.1.triple.tau_b, N.1.1.triple.tau_b]
      exact ha
    have h2 := AR.arTranslation_injective σ (Subtype.ext hval)
    exact congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) h2
  apply Subtype.ext
  apply Subtype.ext
  apply HookFourthExtension.ext
  · exact StripAdmissibleTriple.ext ha hu hb
  · exact hz

/-- The second arrow of an `M6` outer-pair reading is a mesh translate,
so its source is never injective.  Hence the `M6` reading is disjoint
from the injective-second outer stratum. -/
theorem hookM6InjectiveFourthToOuterPair_second_noninjective
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    ¬ Injective (σ.obj
      ((hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        M).pair.1.2.1.1)) :=
  (((AR.arMeshRotationData σ).arrowOrbitData σ).tau
    ⟨⟨(M.1.1.triple.a, M.1.1.triple.u), M.1.1.triple.a_to_u⟩,
      M.1.1.triple.u_nonprojective⟩).2

/-- The common target of an `M6` outer-pair reading is the mesh
translate of the third label, so it is never injective.  Hence the `M6`
reading is also disjoint from the injective-target outer stratum: the
three surviving outer strata embed pairwise disjointly into the single
outer-pair family. -/
theorem hookM6InjectiveFourthToOuterPair_target_noninjective
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    ¬ Injective (σ.obj
      ((hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        M).pair.1.1.1.2)) := by
  have h := (AR.arTranslation σ
    ⟨M.1.1.triple.b, M.1.1.triple.b_nonprojective⟩).2
  rw [M.1.1.triple.tau_b] at h
  exact h

/-- The noninjective-second, noninjective-target cell of the outer-pair
family: the exact home of the `M6` reading. -/
abbrev SecondNoninjectiveTargetNoninjectiveOuterPair :=
  {q : AR.FirstProjectiveInjectiveDifferentOrbitOuterPair σ //
    ¬ Injective (σ.obj q.pair.1.2.1.1) ∧
      ¬ Injective (σ.obj q.pair.1.1.1.2)}

noncomputable instance secondNoninjectiveTargetNoninjectiveOuterPairFintype :
    Fintype (AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) :=
  Fintype.ofFinite _

/-- The `M6` reading, packaged into its exact status cell. -/
def hookM6InjectiveFourthToTargetNoninjectiveCell
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ :=
  ⟨hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR) M,
    hookM6InjectiveFourthToOuterPair_second_noninjective σ AR M,
    hookM6InjectiveFourthToOuterPair_target_noninjective σ AR M⟩

/-- The cell-typed `M6` reading remains injective. -/
theorem hookM6InjectiveFourthToTargetNoninjectiveCell_injective :
    Function.Injective
      (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)) :=
  fun _ _ h ↦
    hookM6InjectiveFourthToOuterPair_injective σ AR
      (congrArg Subtype.val h)

/-- The reconstructed middle label of a cell element: the inverse mesh
translate of its noninjective second source. -/
def outerCellMiddle
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) : ι :=
  ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.2.1.1, q.2.1⟩).1

/-- The reconstructed last label of a cell element: the inverse mesh
translate of its noninjective common target. -/
def outerCellLast
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) : ι :=
  ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.1.1.2, q.2.2⟩).1

/-- Lift a cell element to an injective-fourth `M6` term under the
manuscript's residual fourth-hook-vertex conditions.  The two mesh
arrows `a → u` and `u → b` are automatic by mesh incidence; the four
residual clauses are exactly the triple and extension exclusions that an
injective fourth label does not force. -/
def injectiveFourthOfOuterCell
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (ha_ne_b : q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q)
    (hb_not_to_u : ¬ HasIrreducibleMorphism
      (σ.obj (outerCellLast σ AR q)) (σ.obj (outerCellMiddle σ AR q)))
    (hz_not_to_u : ¬ HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellMiddle σ AR q)))
    (hz_not_to_b : ¬ HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellLast σ AR q))) :
    HookM6Channel.InjectiveFourthEndpoint σ AR := by
  classical
  let a := q.1.pair.1.1.1.2
  let z := q.1.pair.1.1.1.1
  let w := q.1.pair.1.2.1.1
  have haNI : ¬ Injective (σ.obj a) := q.2.2
  let uLabel : σ.NonprojectiveLabel :=
    (AR.arTranslationEquiv σ).symm ⟨w, q.2.1⟩
  have htauU : (AR.arTranslation σ uLabel).1 = w :=
    congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply ⟨w, q.2.1⟩)
  have hwa : HasIrreducibleMorphism (σ.obj w) (σ.obj a) := by
    have h := q.1.pair.1.2.2
    have ht : q.1.pair.1.2.1.2 = a := q.1.pair.2.symm
    rw [ht] at h
    exact h
  have haU : HasIrreducibleMorphism (σ.obj a) (σ.obj uLabel.1) := by
    apply (AR.arTranslation_incidence σ uLabel a).2
    rw [htauU]
    exact hwa
  let qA : σ.IrreduciblePair := ⟨(a, uLabel.1), haU⟩
  let T := stripTripleOfNoninjectiveArrow (k := K) σ AR qA
    haNI uLabel.2 ha_ne_b hb_not_to_u
  have hzP : Projective (σ.obj z) := q.1.first_projective
  have hza : HasIrreducibleMorphism (σ.obj z) (σ.obj T.a) :=
    q.1.pair.1.1.2
  have hzNot : z ∉ T.support := by
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact σ.hasNoIrreducibleEndomorphism_obj z (by
        simpa only [h] using hza)
    · intro h
      have hu : Projective (σ.obj T.u) := h ▸ hzP
      exact uLabel.2 hu
    · intro h
      exact T.b_nonprojective (h ▸ hzP)
  have hzMem : z ∈ insert z T.support :=
    Finset.mem_insert_self z T.support
  have haMem : T.a ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_a
  have huMem : T.u ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_u
  have hbMem : T.b ∈ insert z T.support :=
    Finset.mem_insert_of_mem T.mem_support_b
  have eZA : OpConjecture.RootedDigraph.InsideEdge
      σ.irreducibleEdge (insert z T.support) z T.a :=
    ⟨hzMem, haMem, hza⟩
  have eAU : OpConjecture.RootedDigraph.InsideEdge
      σ.irreducibleEdge (insert z T.support) T.a T.u :=
    ⟨haMem, huMem, T.a_to_u⟩
  have eUB : OpConjecture.RootedDigraph.InsideEdge
      σ.irreducibleEdge (insert z T.support) T.u T.b :=
    ⟨huMem, hbMem, T.u_to_b⟩
  have hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset
        (insert z T.support) := by
    intro x hx
    change x ∈ insert z ({T.a, T.u, T.b} : Finset ι) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨z, by simpa using hzP, hzMem,
        Relation.ReflTransGen.refl⟩
    · exact ⟨z, by simpa using hzP, hzMem,
        Relation.ReflTransGen.single eZA⟩
    · refine ⟨z, by simpa using hzP, hzMem, ?_⟩
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single eZA) eAU
    · refine ⟨z, by simpa using hzP, hzMem, ?_⟩
      apply Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single eZA) eAU)
      exact eUB
  exact ⟨⟨{ triple := T
            z := z
            z_not_mem := hzNot
            rooted := hroot
            z_not_to_u := hz_not_to_u
            z_not_to_b := hz_not_to_b },
      q.1.target_nonprojective⟩,
    q.1.first_injective⟩

/-- The outer-pair reading undoes the cell lift: on a cell element the
reconstruction and the `M6` reading are mutually inverse. -/
theorem hookM6InjectiveFourthToOuterPair_injectiveFourthOfOuterCell
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (ha_ne_b : q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q)
    (hb_not_to_u : ¬ HasIrreducibleMorphism
      (σ.obj (outerCellLast σ AR q)) (σ.obj (outerCellMiddle σ AR q)))
    (hz_not_to_u : ¬ HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellMiddle σ AR q)))
    (hz_not_to_b : ¬ HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellLast σ AR q))) :
    hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        (injectiveFourthOfOuterCell (K := K) σ AR q ha_ne_b hb_not_to_u
          hz_not_to_u hz_not_to_b) = q.1 := by
  apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((AR.arTranslationEquiv σ).apply_symm_apply
          ⟨q.1.pair.1.2.1.1, q.2.1⟩)
    · exact q.1.pair.2

/-- On an `M6` reading the reconstructed middle label recovers the
displayed middle label. -/
theorem outerCellMiddle_hookM6InjectiveFourth
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    outerCellMiddle σ AR
        (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)
          M) =
      M.1.1.triple.u := by
  have h : (⟨(hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).1.pair.1.2.1.1,
        (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).2.1⟩ : σ.NoninjectiveLabel) =
      AR.arTranslationEquiv σ
        ⟨M.1.1.triple.u, M.1.1.triple.u_nonprojective⟩ :=
    Subtype.ext rfl
  simp only [outerCellMiddle]
  rw [h]
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv σ).symm_apply_apply
      ⟨M.1.1.triple.u, M.1.1.triple.u_nonprojective⟩)

/-- On an `M6` reading the reconstructed last label recovers the
displayed last label. -/
theorem outerCellLast_hookM6InjectiveFourth
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    outerCellLast σ AR
        (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)
          M) =
      M.1.1.triple.b := by
  have h : (⟨(hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).1.pair.1.1.1.2,
        (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).2.2⟩ : σ.NoninjectiveLabel) =
      AR.arTranslationEquiv σ
        ⟨M.1.1.triple.b, M.1.1.triple.b_nonprojective⟩ :=
    Subtype.ext M.1.1.triple.tau_b.symm
  simp only [outerCellLast]
  rw [h]
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv σ).symm_apply_apply
      ⟨M.1.1.triple.b, M.1.1.triple.b_nonprojective⟩)

/-- Every `M6` reading satisfies the four residual fourth-hook-vertex
clauses. -/
theorem hookM6InjectiveFourthToTargetNoninjectiveCell_residuals
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)
          M).1.pair.1.1.1.2 ≠
        outerCellLast σ AR
          (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
            (AR := AR) M) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj (outerCellLast σ AR
          (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
            (AR := AR) M)))
        (σ.obj (outerCellMiddle σ AR
          (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
            (AR := AR) M))) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).1.pair.1.1.1.1)
        (σ.obj (outerCellMiddle σ AR
          (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
            (AR := AR) M))) ∧
      ¬ HasIrreducibleMorphism
        (σ.obj (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
          (AR := AR) M).1.pair.1.1.1.1)
        (σ.obj (outerCellLast σ AR
          (hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ)
            (AR := AR) M))) := by
  rw [outerCellMiddle_hookM6InjectiveFourth,
    outerCellLast_hookM6InjectiveFourth]
  exact ⟨M.1.1.triple.a_ne_b, M.1.1.triple.b_not_to_u,
    M.1.1.z_not_to_u, M.1.1.z_not_to_b⟩

include K in
/-- Exact image of the `M6` reading inside its status cell: a cell
element arises from an injective-fourth `M6` term precisely when it
satisfies the four residual fourth-hook-vertex clauses.  This is the
manuscript's identification of the discarded `M4` terms with their
short-chain boundary readings. -/
theorem mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) :
    (∃ M : HookM6Channel.InjectiveFourthEndpoint σ AR,
        hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)
          M = q) ↔
      (q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ∧
        ¬ HasIrreducibleMorphism
          (σ.obj (outerCellLast σ AR q))
          (σ.obj (outerCellMiddle σ AR q)) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.1)
          (σ.obj (outerCellMiddle σ AR q)) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.1)
          (σ.obj (outerCellLast σ AR q))) := by
  constructor
  · rintro ⟨M, rfl⟩
    exact hookM6InjectiveFourthToTargetNoninjectiveCell_residuals σ AR M
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨injectiveFourthOfOuterCell (K := K) σ AR q h1 h2 h3 h4,
      Subtype.ext
        (hookM6InjectiveFourthToOuterPair_injectiveFourthOfOuterCell
          (K := K) σ AR q h1 h2 h3 h4)⟩

/-- The outer-pair reading of an injective-fourth `M6` term is the
channel's assigned common-target pair. -/
theorem hookM6InjectiveFourthToOuterPair_pair_eq
    (M : HookM6Channel.InjectiveFourthEndpoint σ AR) :
    (hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR) M).pair =
      M.1.commonTargetPair σ AR := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- The deep-anchor endpoint reading is the plain outer-pair reading of
the underlying `M6` term. -/
theorem deepAnchor_outerPair_eq
    (M : HookM6Channel.InjectiveFourthDeepAnchor σ AR) :
    HookM6Channel.InjectiveFourthDeepAnchor.firstProjectiveInjectiveDifferentOrbitOuterPair
        σ AR M =
      hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR) M.1.1 := by
  apply FirstProjectiveInjectiveDifferentOrbitOuterPair.ext
  exact (hookM6InjectiveFourthToOuterPair_pair_eq σ AR M.1.1).symm

include K in
/-- Clause characterization of the deep `M6` image: a cell element with
nonprojective second source and deep second arrow lies in the deep image
exactly when it satisfies the four residual fourth-hook-vertex
clauses. -/
theorem mem_firstPIDeepM6Image_iff
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ)
    (hP : ¬ Projective (σ.obj q.1.pair.1.2.1.1))
    (hTS : ¬ ((AR.arMeshRotationData σ).arrowInteriorOrbitData
        σ).TwoSource
      (toInteriorArrow σ AR q.1.pair.1.2
        ⟨by
          rw [← q.1.pair.2]
          exact q.1.target_nonprojective,
        q.2.1⟩)) :
    q.1 ∈ AR.FirstPIDeepM6Image σ ↔
      (q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ∧
        ¬ HasIrreducibleMorphism
          (σ.obj (outerCellLast σ AR q))
          (σ.obj (outerCellMiddle σ AR q)) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.1)
          (σ.obj (outerCellMiddle σ AR q)) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.1)
          (σ.obj (outerCellLast σ AR q))) := by
  constructor
  · rintro ⟨M, hM⟩
    have hread : hookM6InjectiveFourthToOuterPair (σ := σ) (AR := AR)
        M.1.1 = q.1 :=
      (deepAnchor_outerPair_eq σ AR M).symm.trans hM
    have hcell : hookM6InjectiveFourthToTargetNoninjectiveCell
        (σ := σ) (AR := AR) M.1.1 = q :=
      Subtype.ext hread
    subst hcell
    exact
      hookM6InjectiveFourthToTargetNoninjectiveCell_residuals σ AR M.1.1
  · intro hclauses
    obtain ⟨M₀, hM₀⟩ :=
      (mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff
        (K := K) σ AR q).2 hclauses
    subst hM₀
    exact ⟨⟨⟨M₀, hP⟩, hTS⟩, deepAnchor_outerPair_eq σ AR ⟨⟨M₀, hP⟩, hTS⟩⟩

include K in
/-- Normalized form of the exact-image characterization: by mesh
incidence the four residual clauses are the absence of the three return
arrows `w -> z`, `t -> z`, `t -> w` together with the translate
inequality. -/
theorem mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff_normalized
    (q : AR.SecondNoninjectiveTargetNoninjectiveOuterPair σ) :
    (∃ M : HookM6Channel.InjectiveFourthEndpoint σ AR,
        hookM6InjectiveFourthToTargetNoninjectiveCell (σ := σ) (AR := AR)
          M = q) ↔
      (q.1.pair.1.1.1.2 ≠ outerCellLast σ AR q ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.2.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.1) ∧
        ¬ HasIrreducibleMorphism
          (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.1.1.1)) := by
  rw [mem_range_hookM6InjectiveFourthToTargetNoninjectiveCell_iff
    (K := K) σ AR q]
  have huval : (AR.arTranslation σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.2.1.1, q.2.1⟩)).1 =
      q.1.pair.1.2.1.1 :=
    congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply
        ⟨q.1.pair.1.2.1.1, q.2.1⟩)
  have hbval : (AR.arTranslation σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.1.1.2, q.2.2⟩)).1 =
      q.1.pair.1.1.1.2 :=
    congrArg Subtype.val
      ((AR.arTranslationEquiv σ).apply_symm_apply
        ⟨q.1.pair.1.1.1.2, q.2.2⟩)
  have h2 : HasIrreducibleMorphism
      (σ.obj (outerCellLast σ AR q)) (σ.obj (outerCellMiddle σ AR q)) ↔
      HasIrreducibleMorphism
        (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.2.1.1) := by
    have i1 := AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.2.1.1, q.2.1⟩)
      (outerCellLast σ AR q)
    have i2 := AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.1.1.2, q.2.2⟩)
      q.1.pair.1.2.1.1
    rw [huval] at i1
    rw [hbval] at i2
    simp only [outerCellLast, outerCellMiddle]
    exact i1.trans i2
  have h3 : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellMiddle σ AR q)) ↔
      HasIrreducibleMorphism
        (σ.obj q.1.pair.1.2.1.1) (σ.obj q.1.pair.1.1.1.1) := by
    have i1 := AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.2.1.1, q.2.1⟩)
      q.1.pair.1.1.1.1
    rw [huval] at i1
    simp only [outerCellMiddle]
    exact i1
  have h4 : HasIrreducibleMorphism
      (σ.obj q.1.pair.1.1.1.1) (σ.obj (outerCellLast σ AR q)) ↔
      HasIrreducibleMorphism
        (σ.obj q.1.pair.1.1.1.2) (σ.obj q.1.pair.1.1.1.1) := by
    have i1 := AR.arTranslation_incidence σ
      ((AR.arTranslationEquiv σ).symm ⟨q.1.pair.1.1.1.2, q.2.2⟩)
      q.1.pair.1.1.1.1
    rw [hbval] at i1
    simp only [outerCellLast]
    exact i1
  exact and_congr Iff.rfl
    (and_congr (not_congr h2) (and_congr (not_congr h3) (not_congr h4)))

end OpConjecture.IndecomposableSkeleton.FiniteARTranslationData
