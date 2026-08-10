import QuotientSubmoduleEquidistribution.RepresentationTheory.ARNoTransitiveTriangles
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexHookExtensions

/-!
# Fourth-vertex channels for the strip count

This file begins the subtraction-free version of the manuscript's
`M₂,M₃,M₅,M₆` decomposition.  It proves the two rootedness facts which
determine the positive fourth-vertex channels: a nonprojective fourth label
beside a projective hook source is reached from the middle or last hook
label, while a nonprojective hook source forces the fourth label to be a
projective predecessor of that source.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

namespace StripAdmissibleTriple

variable (T : AR.StripAdmissibleTriple σ)

omit [DecidableEq ι] in
include k in
/-- The two predecessor sets in an admissible hook triple are disjoint.
Otherwise `z → u → b` would be a length-two bypass of `z → b`. -/
theorem not_to_b_of_to_u
    {z : ι}
    (hzu : HasIrreducibleMorphism (σ.obj z) (σ.obj T.u)) :
    ¬ HasIrreducibleMorphism (σ.obj z) (σ.obj T.b) :=
  AR.no_irreducible_transitiveTriangle (K := k) σ hzu T.u_to_b

end StripAdmissibleTriple

namespace HookFourthExtension

variable (E : AR.HookFourthExtension σ)

/-- If the fourth label is nonprojective, rootedness forces an arrow from
the hook middle or last label to it.  (The complementary lemma below then
shows that the hook source is necessarily projective.) -/
theorem outgoing_to_z_of_z_nonprojective
    (hz : ¬ Projective (σ.obj E.z)) :
    HasIrreducibleMorphism (σ.obj E.triple.u) (σ.obj E.z) ∨
      HasIrreducibleMorphism (σ.obj E.triple.b) (σ.obj E.z) := by
  have hzSupport : E.z ∈ E.support := by
    simp [HookFourthExtension.support]
  obtain ⟨p, hpProjective, _hpSupport, hpz⟩ :=
    E.rooted E.z hzSupport
  have hpProjective' : Projective (σ.obj p) := by
    simpa using hpProjective
  have hp_ne_z : p ≠ E.z := by
    intro hpz'
    exact hz (hpz' ▸ hpProjective')
  rcases hpz.cases_tail with hpz' | ⟨c, _hpc, hcz⟩
  · exact (hp_ne_z hpz'.symm).elim
  · have hcSupport : c ∈ E.support := hcz.1
    have hcEdge : HasIrreducibleMorphism (σ.obj c) (σ.obj E.z) :=
      hcz.2.2
    change c ∈ insert E.z
      ({E.triple.a, E.triple.u, E.triple.b} : Finset ι) at hcSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcSupport
    rcases hcSupport with hcz' | hca | hcu | hcb
    · exact (σ.hasNoIrreducibleEndomorphism_obj E.z
        (by simpa [hcz'] using hcEdge)).elim
    · have hzb : HasIrreducibleMorphism
          (σ.obj E.z) (σ.obj E.triple.b) := by
        apply (AR.arTranslation_incidence σ
          ⟨E.triple.b, E.triple.b_nonprojective⟩ E.z).2
        simpa [E.triple.tau_b, hca] using hcEdge
      exact (E.z_not_to_b hzb).elim
    · exact Or.inl (by simpa [hcu] using hcEdge)
    · exact Or.inr (by simpa [hcb] using hcEdge)

/-- If the hook source is nonprojective, the fourth label is the unique
possible projective root and its first path step is an arrow to the hook
source. -/
theorem z_projective_and_z_to_a_of_a_nonprojective
    (ha : ¬ Projective (σ.obj E.triple.a)) :
    Projective (σ.obj E.z) ∧
      HasIrreducibleMorphism (σ.obj E.z) (σ.obj E.triple.a) := by
  have haSupport : E.triple.a ∈ E.support := by
    simp [HookFourthExtension.support]
  obtain ⟨p, hpProjective, hpSupport, hpa⟩ :=
    E.rooted E.triple.a haSupport
  have hpProjective' : Projective (σ.obj p) := by
    simpa using hpProjective
  change p ∈ insert E.z
    ({E.triple.a, E.triple.u, E.triple.b} : Finset ι) at hpSupport
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpSupport
  have hpz : p = E.z := by
    rcases hpSupport with hpz | hpa' | hpu | hpb
    · exact hpz
    · exact (ha (hpa' ▸ hpProjective')).elim
    · exact (E.triple.u_nonprojective (hpu ▸ hpProjective')).elim
    · exact (E.triple.b_nonprojective (hpb ▸ hpProjective')).elim
  have hzProjective : Projective (σ.obj E.z) := hpz ▸ hpProjective'
  have hreach : QuotientSubmoduleEquidistribution.RootedDigraph.ReachInside
      σ.irreducibleEdge E.support E.z E.triple.a := by
    change QuotientSubmoduleEquidistribution.RootedDigraph.ReachInside
      σ.irreducibleEdge (insert E.z E.triple.support)
        E.z E.triple.a
    simpa [hpz] using hpa
  have hz_ne_a : E.z ≠ E.triple.a := by
    intro hza
    exact ha (hza ▸ hzProjective)
  rcases hreach.cases_head with hza | ⟨c, hzc, _hca⟩
  · exact (hz_ne_a hza).elim
  · have hcSupport : c ∈ E.support := hzc.2.1
    have hEdge : HasIrreducibleMorphism (σ.obj E.z) (σ.obj c) :=
      hzc.2.2
    change c ∈ insert E.z
      ({E.triple.a, E.triple.u, E.triple.b} : Finset ι) at hcSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcSupport
    rcases hcSupport with hcz | hca | hcu | hcb
    · exact (σ.hasNoIrreducibleEndomorphism_obj E.z
        (by simpa [hcz] using hEdge)).elim
    · exact ⟨hzProjective, by simpa [hca] using hEdge⟩
    · exact (E.z_not_to_u (by simpa [hcu] using hEdge)).elim
    · exact (E.z_not_to_b (by simpa [hcb] using hEdge)).elim

end HookFourthExtension

/-- The wall term attached to a projectively based admissible triple: the
fourth label ranges over all projective labels before the two incoming-arrow
exclusions are imposed. -/
@[ext]
structure HookWallChoice where
  triple : AR.StripAdmissibleTriple σ
  a_projective : Projective (σ.obj triple.a)
  z : ι
  z_projective : Projective (σ.obj z)

noncomputable instance hookWallChoiceFinite :
    Finite (AR.HookWallChoice σ) :=
  Finite.of_injective
    (fun W ↦ (W.triple, W.z)) (by
      intro W₁ W₂ h
      apply HookWallChoice.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

noncomputable instance hookWallChoiceFintype :
    Fintype (AR.HookWallChoice σ) := Fintype.ofFinite _

/-- Wall choices which preserve both singleton predecessor conditions. -/
abbrev HookWallGood :=
  {W : AR.HookWallChoice σ //
    ¬ HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.u) ∧
      ¬ HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.b)}

/-- The first negative wall channel, corresponding to `M₂`. -/
abbrev HookWallBadU :=
  {W : AR.HookWallChoice σ //
    HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.u)}

/-- The second negative wall channel after removing `M₂`, corresponding
to `M₃`.  The later no-sectional-bypass lemma identifies this sequential
version with the manuscript's unrestricted `M₃` set. -/
abbrev HookWallBadB :=
  {W : AR.HookWallChoice σ //
    ¬ HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.u) ∧
      HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.b)}

/-- The manuscript's unrestricted `M₃` channel.  The no-transitive-triangle
theorem makes its missing `z → u` exclusion automatic. -/
abbrev HookWallBadBUnrestricted :=
  {W : AR.HookWallChoice σ //
    HasIrreducibleMorphism (σ.obj W.z) (σ.obj W.triple.b)}

/-- Positive `M₅` extensions.  Rootedness proves that their fourth label
is reached by an arrow from `u` or `b`. -/
abbrev HookM5Channel :=
  {E : AR.HookFourthExtension σ //
    ¬ Projective (σ.obj E.z)}

/-- Positive `M₆` extensions.  Their fourth label is automatically a
projective predecessor of `a`. -/
abbrev HookM6Channel :=
  {E : AR.HookFourthExtension σ //
    ¬ Projective (σ.obj E.triple.a)}

/-- Extensions in the projective-source/projective-fourth-label chamber. -/
abbrev HookProjectivePairExtension :=
  {E : AR.HookFourthExtension σ //
    Projective (σ.obj E.triple.a) ∧ Projective (σ.obj E.z)}

namespace HookWallGood

variable (W : AR.HookWallGood σ)

/-- A good wall choice is precisely a rooted hook extension with both its
source and fourth label projective. -/
def toExtension : AR.HookFourthExtension σ := by
  classical
  let T := W.1.triple
  let z := W.1.z
  have hzNot : z ∉ T.support := by
    intro hz
    change z ∈ ({T.a, T.u, T.b} : Finset ι) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hza | hzu | hzb
    · apply W.2.1
      change HasIrreducibleMorphism (σ.obj z) (σ.obj T.u)
      rw [hza]
      exact T.a_to_u
    · exact T.u_nonprojective (hzu ▸ W.1.z_projective)
    · exact T.b_nonprojective (hzb ▸ W.1.z_projective)
  exact
    { triple := T
      z := z
      z_not_mem := hzNot
      rooted := by
        intro x hx
        change x ∈ insert z ({T.a, T.u, T.b} : Finset ι) at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · refine ⟨z, ?_, by simp, Relation.ReflTransGen.refl⟩
          simpa using W.1.z_projective
        · refine ⟨T.a, ?_, by simp, Relation.ReflTransGen.refl⟩
          simpa using W.1.a_projective
        · refine ⟨T.a, ?_, by simp, ?_⟩
          · simpa using W.1.a_projective
          · exact Relation.ReflTransGen.single ⟨by simp, by simp,
              T.a_to_u⟩
        · refine ⟨T.a, ?_, by simp, ?_⟩
          · simpa using W.1.a_projective
          · apply Relation.ReflTransGen.tail
              (Relation.ReflTransGen.single ⟨by simp, by simp,
                T.a_to_u⟩)
            exact ⟨by simp, by simp, T.u_to_b⟩
      z_not_to_u := W.2.1
      z_not_to_b := W.2.2 }

end HookWallGood

/-- Projective-pair extensions and good wall choices carry exactly the
same data. -/
def hookProjectivePairExtensionEquivWallGood :
    AR.HookProjectivePairExtension σ ≃ AR.HookWallGood σ where
  toFun E :=
    ⟨{ triple := E.1.triple
       a_projective := E.2.1
       z := E.1.z
       z_projective := E.2.2 },
      E.1.z_not_to_u, E.1.z_not_to_b⟩
  invFun W := ⟨W.toExtension σ AR,
    W.1.a_projective, W.1.z_projective⟩
  left_inv E := by
    apply Subtype.ext
    apply HookFourthExtension.ext
    · rfl
    · rfl
  right_inv W := by
    apply Subtype.ext
    apply HookWallChoice.ext
    · rfl
    · rfl

noncomputable instance hookWallGoodFintype :
    Fintype (AR.HookWallGood σ) := Fintype.ofFinite _

noncomputable instance hookWallBadUFintype :
    Fintype (AR.HookWallBadU σ) := Fintype.ofFinite _

noncomputable instance hookWallBadBFintype :
    Fintype (AR.HookWallBadB σ) := Fintype.ofFinite _

noncomputable instance hookWallBadBUnrestrictedFintype :
    Fintype (AR.HookWallBadBUnrestricted σ) := Fintype.ofFinite _

noncomputable instance hookM5ChannelFintype :
    Fintype (AR.HookM5Channel σ) := Fintype.ofFinite _

noncomputable instance hookM6ChannelFintype :
    Fintype (AR.HookM6Channel σ) := Fintype.ofFinite _

noncomputable instance hookProjectivePairExtensionFintype :
    Fintype (AR.HookProjectivePairExtension σ) := Fintype.ofFinite _

namespace HookM5Channel

variable (M : AR.HookM5Channel σ)

/-- An `M₅` extension has projective hook source. -/
theorem a_projective : Projective (σ.obj M.1.triple.a) := by
  by_contra ha
  exact M.2 (M.1.z_projective_and_z_to_a_of_a_nonprojective
    σ AR ha).1

/-- The associated positive arrow in an `M₅` channel starts at `u` or
`b`. -/
theorem outgoing_to_z :
    HasIrreducibleMorphism (σ.obj M.1.triple.u) (σ.obj M.1.z) ∨
      HasIrreducibleMorphism (σ.obj M.1.triple.b) (σ.obj M.1.z) :=
  M.1.outgoing_to_z_of_z_nonprojective σ AR M.2

include k in
/-- The associated `M₅` arrow is unique: simultaneous arrows from `u`
and `b` would make `u → b → z` a length-two bypass of `u → z`. -/
theorem outgoing_to_z_exclusive :
    ¬ (HasIrreducibleMorphism (σ.obj M.1.triple.u) (σ.obj M.1.z) ∧
      HasIrreducibleMorphism (σ.obj M.1.triple.b) (σ.obj M.1.z)) := by
  rintro ⟨huz, hbz⟩
  exact AR.no_irreducible_transitiveTriangle
    (K := k) σ M.1.triple.u_to_b hbz huz

end HookM5Channel

namespace HookM6Channel

variable (M : AR.HookM6Channel σ)

/-- The projective-predecessor description of `M₆`. -/
theorem z_projective_and_z_to_a :
    Projective (σ.obj M.1.z) ∧
      HasIrreducibleMorphism (σ.obj M.1.z) (σ.obj M.1.triple.a) :=
  M.1.z_projective_and_z_to_a_of_a_nonprojective
    σ AR M.2

end HookM6Channel

include k in
/-- The sequential `M₃` channel used to form a disjoint partition is
equivalent to the manuscript's unrestricted `M₃` channel. -/
def hookWallBadBEquivUnrestricted :
    AR.HookWallBadB σ ≃ AR.HookWallBadBUnrestricted σ where
  toFun W := ⟨W.1, W.2.2⟩
  invFun W := ⟨W.1, by
    intro hzu
    exact W.1.triple.not_to_b_of_to_u
      (k := k) σ AR hzu W.2, W.2⟩
  left_inv W := by rfl
  right_inv W := by rfl

/-- Split hook extensions into the good wall chamber and the two positive
channels. -/
def hookExtensionEquivProjectivePairSumM5SumM6 :
    AR.HookFourthExtension σ ≃
      AR.HookProjectivePairExtension σ ⊕
        (AR.HookM5Channel σ ⊕ AR.HookM6Channel σ) where
  toFun E := by
    classical
    by_cases ha : Projective (σ.obj E.triple.a)
    · by_cases hz : Projective (σ.obj E.z)
      · exact Sum.inl ⟨E, ha, hz⟩
      · exact Sum.inr (Sum.inl ⟨E, hz⟩)
    · exact Sum.inr (Sum.inr ⟨E, ha⟩)
  invFun X := by
    rcases X with E | E | E
    · exact E.1
    · exact E.1
    · exact E.1
  left_inv E := by
    classical
    by_cases ha : Projective (σ.obj E.triple.a)
    · by_cases hz : Projective (σ.obj E.z)
      · simp [ha, hz]
      · simp [ha, hz]
    · simp [ha]
  right_inv X := by
    classical
    rcases X with E | E | E
    · simp [E.2.1, E.2.2]
    · have ha := E.a_projective σ AR
      simp [ha, E.2]
    · simp [E.2]

/-- Replace the projective-pair chamber by its equivalent good wall
coordinates. -/
def hookExtensionEquivWallGoodSumM5SumM6 :
    AR.HookFourthExtension σ ≃
      AR.HookWallGood σ ⊕
        (AR.HookM5Channel σ ⊕ AR.HookM6Channel σ) :=
  (hookExtensionEquivProjectivePairSumM5SumM6
    σ AR).trans <|
      Equiv.sumCongr (hookProjectivePairExtensionEquivWallGood σ AR)
        (Equiv.refl _)

/-- Partition the unrestricted projective wall into good choices, `M₂`,
and then `M₃`.  The sequential definition makes this disjoint without yet
using the no-sectional-bypass theorem. -/
def hookWallChoiceEquivGoodSumBadUSumBadB :
    AR.HookWallChoice σ ≃
      AR.HookWallGood σ ⊕
        (AR.HookWallBadU σ ⊕ AR.HookWallBadB σ) where
  toFun W := by
    classical
    by_cases hu : HasIrreducibleMorphism
        (σ.obj W.z) (σ.obj W.triple.u)
    · exact Sum.inr (Sum.inl ⟨W, hu⟩)
    · by_cases hb : HasIrreducibleMorphism
          (σ.obj W.z) (σ.obj W.triple.b)
      · exact Sum.inr (Sum.inr ⟨W, hu, hb⟩)
      · exact Sum.inl ⟨W, hu, hb⟩
  invFun X := by
    rcases X with W | W | W
    · exact W.1
    · exact W.1
    · exact W.1
  left_inv W := by
    classical
    by_cases hu : HasIrreducibleMorphism
        (σ.obj W.z) (σ.obj W.triple.u)
    · simp [hu]
    · by_cases hb : HasIrreducibleMorphism
          (σ.obj W.z) (σ.obj W.triple.b)
      · simp [hu, hb]
      · simp [hu, hb]
  right_inv X := by
    classical
    rcases X with W | W | W
    · simp [W.2.1, W.2.2]
    · simp [W.2]
    · simp [W.2.1, W.2.2]

/-- Subtraction-free fourth-vertex channel identity
`W + M₂ + M₃ = wall + M₅ + M₆`. -/
theorem hookExtension_channel_card_identity :
    Fintype.card (AR.HookFourthExtension σ) +
        Fintype.card (AR.HookWallBadU σ) +
      Fintype.card (AR.HookWallBadB σ) =
    Fintype.card (AR.HookWallChoice σ) +
        Fintype.card (AR.HookM5Channel σ) +
      Fintype.card (AR.HookM6Channel σ) := by
  have hExtension := Fintype.card_congr
    (hookExtensionEquivWallGoodSumM5SumM6 σ AR)
  have hWall := Fintype.card_congr
    (hookWallChoiceEquivGoodSumBadUSumBadB σ AR)
  simp only [Fintype.card_sum] at hExtension hWall
  omega

include k in
/-- Exact manuscript form of the subtraction-free fourth-vertex channel
identity, with the unrestricted `M₃` term. -/
theorem hookExtension_channel_card_identity_unrestricted :
    Fintype.card (AR.HookFourthExtension σ) +
        Fintype.card (AR.HookWallBadU σ) +
      Fintype.card (AR.HookWallBadBUnrestricted σ) =
    Fintype.card (AR.HookWallChoice σ) +
        Fintype.card (AR.HookM5Channel σ) +
      Fintype.card (AR.HookM6Channel σ) := by
  rw [← Fintype.card_congr (hookWallBadBEquivUnrestricted
    (k := k) σ AR)]
  exact hookExtension_channel_card_identity σ AR

/-- Actual quotient hook occurrences satisfy the subtraction-free wall
channel formula. -/
theorem quotientHookOccurrenceFour_channel_card_identity :
    Fintype.card (QuotientHookOccurrenceFour (k := k) (R := R) σ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallBadU σ) +
      Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallBadB σ) =
    Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallChoice σ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5Channel σ) +
      Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM6Channel σ) := by
  rw [Fintype.card_congr
    (quotientHookOccurrenceFourEquivExtension
      (k := k) (R := R) σ)]
  exact hookExtension_channel_card_identity σ
    (σ.finiteDimensionalARTranslationData k R)

/-- Actual quotient hook occurrences satisfy the manuscript's channel
formula with unrestricted `M₃`. -/
theorem quotientHookOccurrenceFour_channel_card_identity_unrestricted :
    Fintype.card (QuotientHookOccurrenceFour (k := k) (R := R) σ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallBadU σ) +
      Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallBadBUnrestricted σ) =
    Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookWallChoice σ) +
        Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5Channel σ) +
      Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM6Channel σ) := by
  rw [Fintype.card_congr
    (quotientHookOccurrenceFourEquivExtension
      (k := k) (R := R) σ)]
  exact hookExtension_channel_card_identity_unrestricted
    (k := k) (R := R) σ
    (σ.finiteDimensionalARTranslationData k R)

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
