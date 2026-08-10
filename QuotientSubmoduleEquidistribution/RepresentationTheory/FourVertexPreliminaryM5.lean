import QuotientSubmoduleEquidistribution.RepresentationTheory.ARNoSectionalCycles
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexSignedChannelOccurrences

/-!
# Preliminary positive channel and its return correction

The square-shift strip first counts outgoing fourth vertices before it
excludes arrows returning from the fourth vertex to the hook middle or last
label.  This file packages that preliminary `M₅` type and separates it
exactly into the genuine `M₅` channel and the rejected-return correction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {iota : Type v} [Fintype iota] [DecidableEq iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)
  (AR : sigma.FiniteARTranslationData)

/-- A preliminary positive fourth-vertex term.  It has a projective hook
source and a nonprojective fourth label reached from `u` or `b`, but no
return-arrow exclusion has yet been imposed. -/
@[ext]
structure HookM5Preliminary where
  triple : AR.StripAdmissibleTriple sigma
  a_projective : Projective (sigma.obj triple.a)
  z : iota
  z_not_mem : z ∉ triple.support
  z_nonprojective : ¬ Projective (sigma.obj z)
  outgoing_to_z :
    HasIrreducibleMorphism (sigma.obj triple.u) (sigma.obj z) ∨
      HasIrreducibleMorphism (sigma.obj triple.b) (sigma.obj z)

omit [Fintype iota] in
noncomputable instance hookM5PreliminaryFinite :
    Finite (AR.HookM5Preliminary sigma) :=
  Finite.of_injective
    (fun M ↦ (M.triple, M.z)) (by
      intro M N h
      apply HookM5Preliminary.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

noncomputable instance hookM5PreliminaryFintype :
    Fintype (AR.HookM5Preliminary sigma) := Fintype.ofFinite _

namespace HookM5Preliminary

variable (M : AR.HookM5Preliminary sigma)

/-- A preliminary term is rejected precisely when its fourth vertex has a
return arrow to `u` or `b`. -/
def HasReturn : Prop :=
  HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.u) ∨
    HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.b)

/-- The four labels of a preliminary term. -/
def support : Finset iota := insert M.z M.triple.support

omit [Fintype iota] in
@[simp]
theorem support_card : M.support.card = 4 := by
  rw [support, Finset.card_insert_of_notMem M.z_not_mem,
    M.triple.support_card]

include k in
/-- The two possible preliminary outgoing arrows are mutually exclusive. -/
theorem outgoing_to_z_exclusive :
    ¬ (HasIrreducibleMorphism (sigma.obj M.triple.u) (sigma.obj M.z) ∧
      HasIrreducibleMorphism (sigma.obj M.triple.b) (sigma.obj M.z)) := by
  rintro ⟨huz, hbz⟩
  exact AR.no_irreducible_transitiveTriangle
    (K := k) sigma M.triple.u_to_b hbz huz

include k in
/-- A preliminary arrow `u → z` cannot return to `b`, since it would
bypass the displayed hook arrow `u → b`. -/
theorem not_z_to_b_of_u_to_z
    (huz : HasIrreducibleMorphism (sigma.obj M.triple.u) (sigma.obj M.z)) :
    ¬ HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.b) := by
  intro hzb
  exact AR.no_irreducible_transitiveTriangle
    (K := k) sigma huz hzb M.triple.u_to_b

include k in
/-- The `b ↔ z` return branch is impossible.  The local two-cycle lemma
would make `z` fixed; mesh incidence would then give an opposite-arrow pair
at the projective but noninjective hook source. -/
theorem not_b_to_z_and_z_to_b :
    ¬ (HasIrreducibleMorphism (sigma.obj M.triple.b) (sigma.obj M.z) ∧
      HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.b)) := by
  rintro ⟨hbz, hzb⟩
  rcases AR.exists_arTranslation_eq_self_of_two_cycle
      (K := k) sigma M.triple.b M.z hbz hzb with hbfixed | hzfixed
  · rcases hbfixed with ⟨hbNP, hfix⟩
    have hab : M.triple.a = M.triple.b := by
      calc
        M.triple.a =
            (AR.arTranslation sigma
              ⟨M.triple.b, M.triple.b_nonprojective⟩).1 :=
          M.triple.tau_b.symm
        _ = (AR.arTranslation sigma ⟨M.triple.b, hbNP⟩).1 := by
          congr
        _ = M.triple.b := hfix
    exact M.triple.a_ne_b hab
  · rcases hzfixed with ⟨hzNP, hfix⟩
    have haz : HasIrreducibleMorphism
        (sigma.obj M.triple.a) (sigma.obj M.z) := by
      have h := (AR.arTranslation_incidence sigma
        ⟨M.triple.b, M.triple.b_nonprojective⟩ M.z).1 hzb
      simpa only [M.triple.tau_b] using h
    have hza : HasIrreducibleMorphism
        (sigma.obj M.z) (sigma.obj M.triple.a) := by
      have h := (AR.arTranslation_incidence sigma
        ⟨M.z, hzNP⟩ M.triple.a).1 haz
      simpa only [hfix] using h
    have haI := AR.injective_of_projective_two_cycle
      (K := k) sigma M.triple.a M.z M.a_projective haz hza
    exact M.triple.a_noninjective sigma AR haI

/-- Projective rootedness of a preliminary term follows from the displayed
hook path and its selected outgoing arrow. -/
theorem rooted :
    QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      sigma.irreducibleEdge sigma.projectiveLabelFinset
        (insert M.z M.triple.support) := by
  intro x hx
  change x ∈ insert M.z
    ({M.triple.a, M.triple.u, M.triple.b} : Finset iota) at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine ⟨M.triple.a, ?_, by simp, ?_⟩
    · simpa using M.a_projective
    · rcases M.outgoing_to_z with huz | hbz
      · apply Relation.ReflTransGen.tail
          (Relation.ReflTransGen.single ⟨by simp, by simp,
            M.triple.a_to_u⟩)
        exact ⟨by simp, by simp, huz⟩
      · apply Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail
            (Relation.ReflTransGen.single ⟨by simp, by simp,
              M.triple.a_to_u⟩)
            ⟨by simp, by simp, M.triple.u_to_b⟩)
        exact ⟨by simp, by simp, hbz⟩
  · refine ⟨M.triple.a, ?_, by simp, Relation.ReflTransGen.refl⟩
    simpa using M.a_projective
  · refine ⟨M.triple.a, ?_, by simp, ?_⟩
    · simpa using M.a_projective
    · exact Relation.ReflTransGen.single ⟨by simp, by simp,
        M.triple.a_to_u⟩
  · refine ⟨M.triple.a, ?_, by simp, ?_⟩
    · simpa using M.a_projective
    · apply Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single ⟨by simp, by simp,
          M.triple.a_to_u⟩)
      exact ⟨by simp, by simp, M.triple.u_to_b⟩

/-- A preliminary term without a return arrow is a genuine `M₅` hook
extension. -/
def toChannel (hreturn : ¬ M.HasReturn sigma) : AR.HookM5Channel sigma :=
  ⟨{ triple := M.triple
     z := M.z
     z_not_mem := M.z_not_mem
     rooted := M.rooted sigma AR
     z_not_to_u := fun h ↦ hreturn (Or.inl h)
     z_not_to_b := fun h ↦ hreturn (Or.inr h) },
   M.z_nonprojective⟩

end HookM5Preliminary

namespace HookM5Channel

variable (M : AR.HookM5Channel sigma)

/-- Forget the two return-arrow exclusions of a genuine `M₅` channel. -/
def toPreliminary : AR.HookM5Preliminary sigma where
  triple := M.1.triple
  a_projective := M.a_projective sigma AR
  z := M.1.z
  z_not_mem := M.1.z_not_mem
  z_nonprojective := M.2
  outgoing_to_z := M.outgoing_to_z sigma AR

theorem toPreliminary_noReturn :
    ¬ (M.toPreliminary sigma AR).HasReturn sigma := by
  rintro (h | h)
  · exact M.1.z_not_to_u h
  · exact M.1.z_not_to_b h

end HookM5Channel

@[simp]
theorem HookM5Preliminary.toChannel_toPreliminary
    (M : AR.HookM5Preliminary sigma)
    (hreturn : ¬ M.HasReturn sigma) :
    (M.toChannel sigma AR hreturn).toPreliminary sigma AR = M := by
  apply HookM5Preliminary.ext <;> rfl

@[simp]
theorem HookM5Channel.toPreliminary_toChannel
    (M : AR.HookM5Channel sigma) :
    (M.toPreliminary sigma AR).toChannel sigma AR
      (M.toPreliminary_noReturn sigma AR) = M := by
  apply Subtype.ext
  apply HookFourthExtension.ext <;> rfl

/-- Preliminary terms excluded by a return arrow. -/
abbrev HookM5Rejected :=
  {M : AR.HookM5Preliminary sigma // M.HasReturn sigma}

noncomputable instance hookM5RejectedFintype :
    Fintype (AR.HookM5Rejected sigma) := Fintype.ofFinite _

/-- Rejected terms in the opposite-arrow branch `u ↔ z`. -/
abbrev HookM5FixedReturn :=
  {M : AR.HookM5Preliminary sigma //
    HasIrreducibleMorphism (sigma.obj M.triple.u) (sigma.obj M.z) ∧
      HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.u)}

/-- Rejected terms in the oriented-triangle branch
`b → z → u → b`. -/
abbrev HookM5TriangleReturn :=
  {M : AR.HookM5Preliminary sigma //
    HasIrreducibleMorphism (sigma.obj M.triple.b) (sigma.obj M.z) ∧
      HasIrreducibleMorphism (sigma.obj M.z) (sigma.obj M.triple.u)}

noncomputable instance hookM5FixedReturnFintype :
    Fintype (AR.HookM5FixedReturn sigma) := Fintype.ofFinite _

noncomputable instance hookM5TriangleReturnFintype :
    Fintype (AR.HookM5TriangleReturn sigma) := Fintype.ofFinite _

namespace HookM5FixedReturn

variable (M : AR.HookM5FixedReturn sigma)

include k in
/-- The local two-cycle theorem justifies the name: one of `u,z` is fixed
by ordinary AR translation. -/
theorem exists_arTranslation_fixed :
    (∃ hu : ¬ Projective (sigma.obj M.1.triple.u),
      (AR.arTranslation sigma ⟨M.1.triple.u, hu⟩).1 = M.1.triple.u) ∨
    (∃ hz : ¬ Projective (sigma.obj M.1.z),
      (AR.arTranslation sigma ⟨M.1.z, hz⟩).1 = M.1.z) :=
  AR.exists_arTranslation_eq_self_of_two_cycle
    (K := k) sigma M.1.triple.u M.1.z M.2.1 M.2.2

end HookM5FixedReturn

namespace HookM5TriangleReturn

variable (M : AR.HookM5TriangleReturn sigma)

/-- The oriented return triangle is sectional exactly when none of its
three length-two corners is closed by AR translation. -/
def IsSectional : Prop :=
  (AR.arTranslation sigma
      ⟨M.1.triple.b, M.1.triple.b_nonprojective⟩).1 ≠ M.1.z ∧
    (AR.arTranslation sigma
      ⟨M.1.z, M.1.z_nonprojective⟩).1 ≠ M.1.triple.u ∧
    (AR.arTranslation sigma
      ⟨M.1.triple.u, M.1.triple.u_nonprojective⟩).1 ≠ M.1.triple.b

omit [Fintype iota] in
/-- The corner at `b` is automatically sectional: `tau b=a`, while the
fourth label is outside the displayed hook support. -/
theorem tau_b_ne_z :
    (AR.arTranslation sigma
      ⟨M.1.triple.b, M.1.triple.b_nonprojective⟩).1 ≠ M.1.z := by
  rw [M.1.triple.tau_b]
  intro haz
  apply M.1.z_not_mem
  simp [haz, StripAdmissibleTriple.support]

omit [Field k] [Algebra k R] [FiniteDimensional k R] [Fintype iota] in
/-- An oriented return triangle cannot be sectional. -/
theorem not_isSectional : ¬ M.IsSectional sigma AR := by
  rintro hsectional
  obtain ⟨f, hf⟩ := M.2.1
  obtain ⟨g, hg⟩ := M.2.2
  obtain ⟨h, hh⟩ := M.1.triple.u_to_b
  exact NatIrreducibleSequence.not_sectional_irreducibleTriangle
    sigma AR hf hg hh
      M.1.triple.b_nonprojective M.1.z_nonprojective
      M.1.triple.u_nonprojective hsectional

omit [Fintype iota] in
/-- Once a sectional oriented triangle is excluded, the return is either
the diagonal case `tau z=u` or the row-`T` case `tau u=b`. -/
theorem tau_z_eq_u_or_tau_u_eq_b_of_not_sectional
    (hsectional : ¬ M.IsSectional sigma AR) :
    (AR.arTranslation sigma ⟨M.1.z, M.1.z_nonprojective⟩).1 =
        M.1.triple.u ∨
      (AR.arTranslation sigma
        ⟨M.1.triple.u, M.1.triple.u_nonprojective⟩).1 =
          M.1.triple.b := by
  by_cases hz : (AR.arTranslation sigma
      ⟨M.1.z, M.1.z_nonprojective⟩).1 = M.1.triple.u
  · exact Or.inl hz
  · right
    by_contra hu
    exact hsectional ⟨M.tau_b_ne_z sigma AR, hz, hu⟩

end HookM5TriangleReturn

/-- The diagonal part of the oriented return correction. -/
abbrev HookM5DiagonalReturn :=
  {M : AR.HookM5TriangleReturn sigma //
    (AR.arTranslation sigma ⟨M.1.z, M.1.z_nonprojective⟩).1 =
      M.1.triple.u}

/-- The non-diagonal oriented return, in the translation position used by
row `T`. -/
abbrev HookM5RowTReturn :=
  {M : AR.HookM5TriangleReturn sigma //
    (AR.arTranslation sigma ⟨M.1.z, M.1.z_nonprojective⟩).1 ≠
        M.1.triple.u ∧
      (AR.arTranslation sigma
        ⟨M.1.triple.u, M.1.triple.u_nonprojective⟩).1 =
          M.1.triple.b}

noncomputable instance hookM5DiagonalReturnFintype :
    Fintype (AR.HookM5DiagonalReturn sigma) := Fintype.ofFinite _

noncomputable instance hookM5RowTReturnFintype :
    Fintype (AR.HookM5RowTReturn sigma) := Fintype.ofFinite _

namespace HookM5RowTReturn

variable (M : AR.HookM5RowTReturn sigma)

omit [Fintype iota] in
include AR in
/-- Mesh incidence turns `a → u` and `tau u=b` into the row-`T`
arrow `b → a`. -/
theorem b_to_a :
    HasIrreducibleMorphism
      (sigma.obj M.1.1.triple.b) (sigma.obj M.1.1.triple.a) := by
  have h := (AR.arTranslation_incidence sigma
    ⟨M.1.1.triple.u, M.1.1.triple.u_nonprojective⟩
      M.1.1.triple.a).1 M.1.1.triple.a_to_u
  simpa only [M.2.2] using h

include k in
/-- The projective hook source cannot also point to the fourth label,
since `b → a → z` would bypass `b → z`. -/
theorem a_not_to_z :
    ¬ HasIrreducibleMorphism
      (sigma.obj M.1.1.triple.a) (sigma.obj M.1.1.z) := by
  intro haz
  exact AR.no_irreducible_transitiveTriangle
    (K := k) sigma (M.b_to_a sigma AR) haz M.1.2.1

include k in
/-- In the row-`T` branch, `tau z` lies outside the four displayed
labels. -/
theorem tau_z_not_mem_support :
    (AR.arTranslation sigma ⟨M.1.1.z, M.1.1.z_nonprojective⟩).1 ∉
      M.1.1.support := by
  intro hmem
  simp only [HookM5Preliminary.support, StripAdmissibleTriple.support,
    Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hz | ha | hu | hb
  · have hzb : HasIrreducibleMorphism
        (sigma.obj M.1.1.z) (sigma.obj M.1.1.triple.b) := by
      have h := (AR.arTranslation_incidence sigma
        ⟨M.1.1.z, M.1.1.z_nonprojective⟩
          M.1.1.triple.b).1 M.1.2.1
      simpa only [hz] using h
    exact AR.no_irreducible_transitiveTriangle
      (K := k) sigma M.1.2.2 M.1.1.triple.u_to_b hzb
  · have hinputs :
        (⟨M.1.1.z, M.1.1.z_nonprojective⟩ : sigma.NonprojectiveLabel) =
          ⟨M.1.1.triple.b, M.1.1.triple.b_nonprojective⟩ := by
      apply AR.arTranslation_injective sigma
      apply Subtype.ext
      exact ha.trans M.1.1.triple.tau_b.symm
    apply M.1.1.z_not_mem
    have hzb := congrArg Subtype.val hinputs
    have hzb' : M.1.1.z = M.1.1.triple.b := by
      simpa only using hzb
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton]
    exact Or.inr (Or.inr hzb')
  · exact M.2.1 hu
  · have hinputs :
        (⟨M.1.1.z, M.1.1.z_nonprojective⟩ : sigma.NonprojectiveLabel) =
          ⟨M.1.1.triple.u, M.1.1.triple.u_nonprojective⟩ := by
      apply AR.arTranslation_injective sigma
      apply Subtype.ext
      exact hb.trans M.2.2.symm
    apply M.1.1.z_not_mem
    have hzu := congrArg Subtype.val hinputs
    have hzu' : M.1.1.z = M.1.1.triple.u := by
      simpa only using hzu
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton]
    exact Or.inr (Or.inl hzu')

/-- A non-diagonal oriented return supplies the literal row-`T` packet
with `(p,A₁,A₂,x)=(a,b,u,z)`. -/
def trianglePacket :
    AR.TrianglePacket sigma
      ((((M.1.1.support : Finset iota) : Set iota)ᶜ)) := by
  let Deleted := M.1.1.support
  let K : Set iota := ((Deleted : Finset iota) : Set iota)ᶜ
  let p : DeletedLabel K :=
    ⟨M.1.1.triple.a, by simp [K, Deleted, HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let A₁ : DeletedLabel K :=
    ⟨M.1.1.triple.b, by simp [K, Deleted, HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let A₂ : DeletedLabel K :=
    ⟨M.1.1.triple.u, by simp [K, Deleted, HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let x : DeletedLabel K :=
    ⟨M.1.1.z, by simp [K, Deleted, HookM5Preliminary.support]⟩
  refine
    { p := p
      A₁ := A₁
      A₂ := A₂
      x := x
      p_projective := M.1.1.a_projective
      A₁_nonprojective := M.1.1.triple.b_nonprojective
      A₂_nonprojective := M.1.1.triple.u_nonprojective
      x_nonprojective := M.1.1.z_nonprojective
      A₁_to_p := M.b_to_a sigma AR
      predecessor_A₁ := ?_
      predecessor_A₂ := ?_
      predecessor_x := ?_
      tau_A₁ := M.1.1.triple.tau_b
      tau_A₂ := M.2.2
      tau_x_mem := by
        change (AR.arTranslation sigma
          ⟨M.1.1.z, M.1.1.z_nonprojective⟩).1 ∉ Deleted
        exact M.tau_z_not_mem_support (k := k) sigma AR }
  · refine ⟨M.1.1.triple.u_to_b, ?_⟩
    intro q hqb
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqz | hqa | hqu | hqbself
    · exact (M.1.1.triple.not_to_b_of_to_u
        (k := k) sigma AR M.1.2.2 (by simpa only [hqz] using hqb)).elim
    · exact (M.1.1.triple.a_not_to_b
        (by simpa only [hqa] using hqb)).elim
    · exact Subtype.ext hqu
    · exact (sigma.hasNoIrreducibleEndomorphism_obj M.1.1.triple.b
        (by simpa only [hqbself] using hqb)).elim
  · refine ⟨?_, M.1.1.triple.a_to_u, M.1.2.2, ?_⟩
    · intro hpx
      apply M.1.1.z_not_mem
      have haz := congrArg Subtype.val hpx
      have haz' : M.1.1.triple.a = M.1.1.z := by
        simpa only using haz
      simp only [StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl haz'.symm
    · intro q hqu
      have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
      simp only [Deleted, HookM5Preliminary.support,
        StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton] at hqmem
      rcases hqmem with hqz | hqa | hquself | hqb
      · exact Or.inr (Subtype.ext hqz)
      · exact Or.inl (Subtype.ext hqa)
      · exact (sigma.hasNoIrreducibleEndomorphism_obj M.1.1.triple.u
          (by simpa only [hquself] using hqu)).elim
      · exact (M.1.1.triple.b_not_to_u
          (by simpa only [hqb] using hqu)).elim
  · refine ⟨M.1.2.1, ?_⟩
    intro q hqzArrow
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqz | hqa | hqu | hqb
    · exact (sigma.hasNoIrreducibleEndomorphism_obj M.1.1.z
        (by simpa only [hqz] using hqzArrow)).elim
    · exact (M.a_not_to_z (k := k) sigma AR
        (by simpa only [hqa] using hqzArrow)).elim
    · exact (M.1.1.outgoing_to_z_exclusive
        (k := k) sigma AR ⟨by simpa only [hqu] using hqzArrow,
          M.1.2.1⟩).elim
    · exact Subtype.ext hqb

end HookM5RowTReturn

/-- A row-`T` return, specialized to the canonical finite-dimensional AR
translation, determines the corresponding hookless rooted row-`T` support. -/
def hookM5RowTReturnToQuotientTrianglePacketFour
    (M : (sigma.finiteDimensionalARTranslationData k R).HookM5RowTReturn
      sigma) :
    QuotientTrianglePacketFour (k := k) (R := R) sigma := by
  let AR₀ := sigma.finiteDimensionalARTranslationData k R
  let Deleted := M.1.1.support
  let T := M.trianglePacket (k := k) sigma AR₀
  have hcard : Deleted.card = 4 := M.1.1.support_card sigma AR₀
  have hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      sigma.irreducibleEdge sigma.projectiveLabelFinset Deleted :=
    M.1.1.rooted sigma AR₀
  have hEmpty : IsEmpty (AR₀.AdmissibleHook sigma
      (((Deleted : Finset iota) : Set iota)ᶜ)) :=
    T.no_admissibleHook (k := k) (R := R) sigma Deleted hcard
  exact ⟨⟨Deleted, hcard, hroot⟩, ⟨⟨T⟩, hEmpty⟩⟩

/-- Reconstruct the oriented row-`T` return from a hookless quotient
row-`T` packet. -/
def quotientTrianglePacketFourToHookM5RowTReturn
    (Q : QuotientTrianglePacketFour (k := k) (R := R) sigma) :
    (sigma.finiteDimensionalARTranslationData k R).HookM5RowTReturn
      sigma := by
  let AR₀ := sigma.finiteDimensionalARTranslationData k R
  let T := Classical.choice Q.2.1
  let triple : AR₀.StripAdmissibleTriple sigma :=
    { a := T.p.1
      u := T.A₂.1
      b := T.A₁.1
      a_ne_u := by
        intro h
        exact T.A₂_nonprojective (by simpa only [h] using T.p_projective)
      a_ne_b := by
        intro h
        exact T.A₁_nonprojective (by simpa only [h] using T.p_projective)
      u_ne_b := by
        intro h
        exact sigma.hasNoIrreducibleEndomorphism_obj T.A₁.1 (by
          simpa only [h] using T.predecessor_A₁.1)
      u_nonprojective := T.A₂_nonprojective
      b_nonprojective := T.A₁_nonprojective
      a_to_u := T.predecessor_A₂.2.1
      u_to_b := T.predecessor_A₁.1
      b_not_to_u := by
        intro h
        rcases T.predecessor_A₂.2.2.2 T.A₁ h with hp | hx
        · exact T.A₁_nonprojective (hp ▸ T.p_projective)
        · exact sigma.hasNoIrreducibleEndomorphism_obj T.x.1 (by
            simpa only [hx] using T.predecessor_x.1)
      a_not_to_b := by
        intro h
        have hpA₂ := T.predecessor_A₁.2 T.p h
        exact T.A₂_nonprojective (hpA₂ ▸ T.p_projective)
      tau_b := T.tau_A₁ }
  let preliminary : AR₀.HookM5Preliminary sigma :=
    { triple := triple
      a_projective := T.p_projective
      z := T.x.1
      z_not_mem := by
        simp only [triple, StripAdmissibleTriple.support,
          Finset.mem_insert, Finset.mem_singleton]
        intro hmem
        rcases hmem with h | h | h
        ·
          exact T.x_nonprojective (by simpa only [h] using T.p_projective)
        ·
          exact sigma.hasNoIrreducibleEndomorphism_obj T.x.1 (by
              simpa only [h] using T.predecessor_A₂.2.2.1)
        ·
          exact sigma.hasNoIrreducibleEndomorphism_obj T.x.1 (by
              simpa only [h] using T.predecessor_x.1)
      z_nonprojective := T.x_nonprojective
      outgoing_to_z := Or.inr T.predecessor_x.1 }
  let triangle : AR₀.HookM5TriangleReturn sigma :=
    ⟨preliminary, T.predecessor_x.1, T.predecessor_A₂.2.2.1⟩
  refine ⟨triangle, ?_, T.tau_A₂⟩
  change (AR₀.arTranslation sigma ⟨T.x.1, T.x_nonprojective⟩).1 ≠
    T.A₂.1
  intro htau
  exact T.A₂.2 (htau ▸ T.tau_x_mem)

/-- The four values displayed by a triangle packet recover its ambient
four-element deleted support in the row-`T` order. -/
theorem trianglePacket_rowT_support_eq
    (Deleted : Finset iota) (hcard : Deleted.card = 4)
    (T : (sigma.finiteDimensionalARTranslationData k R).TrianglePacket
      sigma ((((Deleted : Finset iota) : Set iota)ᶜ))) :
    insert T.x.1 ({T.p.1, T.A₂.1, T.A₁.1} : Finset iota) =
      Deleted := by
  apply Finset.ext
  intro y
  constructor
  · intro hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · simpa using T.x.2
    · simpa using T.p.2
    · simpa using T.A₂.2
    · simpa using T.A₁.2
  · intro hy
    let q : DeletedLabel ((((Deleted : Finset iota) : Set iota)ᶜ)) :=
      ⟨y, by simpa using hy⟩
    rcases eq_trianglePacket_label (k := k) (R := R) sigma
        Deleted hcard T q with hp | hA₁ | hA₂ | hx
    · have h := congrArg Subtype.val hp
      exact Finset.mem_insert.2 (Or.inr <|
        Finset.mem_insert.2 (Or.inl h))
    · have h := congrArg Subtype.val hA₁
      exact Finset.mem_insert.2 (Or.inr <|
        Finset.mem_insert.2 (Or.inr <|
          Finset.mem_insert.2 (Or.inr <|
            Finset.mem_singleton.2 h)))
    · have h := congrArg Subtype.val hA₂
      exact Finset.mem_insert.2 (Or.inr <|
        Finset.mem_insert.2 (Or.inr <|
          Finset.mem_insert.2 (Or.inl h)))
    · have h := congrArg Subtype.val hx
      exact Finset.mem_insert.2 (Or.inl h)

/-- The reconstructed row-`T` return has exactly the original packet
support. -/
theorem quotientTrianglePacketFourToHookM5RowTReturn_support
    (Q : QuotientTrianglePacketFour (k := k) (R := R) sigma) :
    (quotientTrianglePacketFourToHookM5RowTReturn
      (k := k) (R := R) sigma Q).1.1.support = Q.1.1 := by
  let T := Classical.choice Q.2.1
  change insert T.x.1 ({T.p.1, T.A₂.1, T.A₁.1} : Finset iota) =
    Q.1.1
  exact trianglePacket_rowT_support_eq (k := k) (R := R) sigma
    Q.1.1 Q.1.2.1 T

/-- Reconstructing a row-`T` return after forming its packet recovers the
original labelled return. -/
theorem hookM5RowTReturn_packet_leftInverse :
    Function.LeftInverse
      (quotientTrianglePacketFourToHookM5RowTReturn
        (k := k) (R := R) sigma)
      (hookM5RowTReturnToQuotientTrianglePacketFour
        (k := k) (R := R) sigma) := by
  intro M
  let AR₀ := sigma.finiteDimensionalARTranslationData k R
  let Q := hookM5RowTReturnToQuotientTrianglePacketFour
    (k := k) (R := R) sigma M
  let T := Classical.choice Q.2.1
  have hT : T = M.trianglePacket (k := k) sigma AR₀ := by
    exact trianglePacket_unique (k := k) (R := R) sigma M.1.1.support
      (M.1.1.support_card sigma AR₀) T
      (M.trianglePacket (k := k) sigma AR₀)
  apply Subtype.ext
  apply Subtype.ext
  apply HookM5Preliminary.ext
  · apply StripAdmissibleTriple.ext
    · exact congrArg (fun X ↦ X.p.1) hT
    · exact congrArg (fun X ↦ X.A₂.1) hT
    · exact congrArg (fun X ↦ X.A₁.1) hT
  · exact congrArg (fun X ↦ X.x.1) hT

/-- Forming the packet of a reconstructed row-`T` return recovers the
original rooted support. -/
theorem hookM5RowTReturn_packet_rightInverse :
    Function.RightInverse
      (quotientTrianglePacketFourToHookM5RowTReturn
        (k := k) (R := R) sigma)
      (hookM5RowTReturnToQuotientTrianglePacketFour
        (k := k) (R := R) sigma) := by
  intro Q
  apply Subtype.ext
  apply Subtype.ext
  exact quotientTrianglePacketFourToHookM5RowTReturn_support
    (k := k) (R := R) sigma Q

/-- Exact identification of non-diagonal oriented returns with the
hookless quotient row-`T` correction. -/
def hookM5RowTReturnEquivQuotientTrianglePacketFour :
    (sigma.finiteDimensionalARTranslationData k R).HookM5RowTReturn sigma ≃
      QuotientTrianglePacketFour (k := k) (R := R) sigma :=
  Equiv.mk
    (hookM5RowTReturnToQuotientTrianglePacketFour
      (k := k) (R := R) sigma)
    (quotientTrianglePacketFourToHookM5RowTReturn
      (k := k) (R := R) sigma)
    (hookM5RowTReturn_packet_leftInverse (k := k) (R := R) sigma)
    (hookM5RowTReturn_packet_rightInverse (k := k) (R := R) sigma)

/-- Cardinal form of the row-`T` return identification. -/
theorem card_hookM5RowTReturn_eq_quotientTrianglePacketFour :
    Fintype.card
        ((sigma.finiteDimensionalARTranslationData k R).HookM5RowTReturn
          sigma) =
      Fintype.card
        (QuotientTrianglePacketFour (k := k) (R := R) sigma) :=
  Fintype.card_congr
    (hookM5RowTReturnEquivQuotientTrianglePacketFour
      (k := k) (R := R) sigma)

/-- Exact diagonal/row-`T` split of oriented returns. -/
def hookM5TriangleReturnEquivDiagonalSumRowT :
    AR.HookM5TriangleReturn sigma ≃
      AR.HookM5DiagonalReturn sigma ⊕ AR.HookM5RowTReturn sigma where
  toFun M := by
    classical
    by_cases hz : (AR.arTranslation sigma
        ⟨M.1.z, M.1.z_nonprojective⟩).1 = M.1.triple.u
    · exact Sum.inl ⟨M, hz⟩
    · exact Sum.inr ⟨M, hz,
        (M.tau_z_eq_u_or_tau_u_eq_b_of_not_sectional
          sigma AR (M.not_isSectional sigma AR)).resolve_left hz⟩
  invFun X := by
    rcases X with M | M
    · exact M.1
    · exact M.1
  left_inv M := by
    classical
    by_cases hz : (AR.arTranslation sigma
        ⟨M.1.z, M.1.z_nonprojective⟩).1 = M.1.triple.u
    · simp [hz]
    · simp [hz]
  right_inv X := by
    classical
    rcases X with M | M
    · simp [M.2]
    · simp [M.2.1]

include k in
/-- Every rejected preliminary term is uniquely either a fixed two-cycle
return or the oriented-triangle return.  The other two formal branches are
excluded by no transitive triangles and the projective two-cycle lemma. -/
def hookM5RejectedEquivFixedReturnSumTriangleReturn :
    AR.HookM5Rejected sigma ≃
      AR.HookM5FixedReturn sigma ⊕ AR.HookM5TriangleReturn sigma where
  toFun X := by
    classical
    by_cases huz : HasIrreducibleMorphism
        (sigma.obj X.1.triple.u) (sigma.obj X.1.z)
    · refine Sum.inl ⟨X.1, huz, ?_⟩
      rcases X.2 with hzu | hzb
      · exact hzu
      · exact (X.1.not_z_to_b_of_u_to_z
          (k := k) sigma AR huz hzb).elim
    · have hbz := X.1.outgoing_to_z.resolve_left huz
      refine Sum.inr ⟨X.1, hbz, ?_⟩
      rcases X.2 with hzu | hzb
      · exact hzu
      · exact (X.1.not_b_to_z_and_z_to_b
          (k := k) sigma AR ⟨hbz, hzb⟩).elim
  invFun X := by
    rcases X with X | X
    · exact ⟨X.1, Or.inl X.2.2⟩
    · exact ⟨X.1, Or.inl X.2.2⟩
  left_inv X := by
    classical
    by_cases huz : HasIrreducibleMorphism
        (sigma.obj X.1.triple.u) (sigma.obj X.1.z)
    · apply Subtype.ext
      simp [huz]
    · apply Subtype.ext
      simp [huz]
  right_inv X := by
    classical
    rcases X with X | X
    · simp [X.2.1]
    · have hnuz : ¬ HasIrreducibleMorphism
          (sigma.obj X.1.triple.u) (sigma.obj X.1.z) := by
        intro huz
        exact X.1.outgoing_to_z_exclusive
          (k := k) sigma AR ⟨huz, X.2.1⟩
      simp [hnuz]

include k in
/-- Cardinal form of the exact return-branch classification. -/
theorem hookM5Rejected_card_eq_fixedReturn_add_triangleReturn :
    Fintype.card (AR.HookM5Rejected sigma) =
      Fintype.card (AR.HookM5FixedReturn sigma) +
        Fintype.card (AR.HookM5TriangleReturn sigma) := by
  rw [Fintype.card_congr
    (hookM5RejectedEquivFixedReturnSumTriangleReturn
      (k := k) sigma AR)]
  exact Fintype.card_sum

/-- Rejected preliminary terms split exactly into fixed two-cycle returns,
diagonal returns, and actual quotient row-`T` packets. -/
def hookM5RejectedEquivFixedReturnSumDiagonalSumTrianglePacket :
    (sigma.finiteDimensionalARTranslationData k R).HookM5Rejected sigma ≃
      (sigma.finiteDimensionalARTranslationData k R).HookM5FixedReturn
          sigma ⊕
        ((sigma.finiteDimensionalARTranslationData k R).HookM5DiagonalReturn
            sigma ⊕
          QuotientTrianglePacketFour (k := k) (R := R) sigma) :=
  (hookM5RejectedEquivFixedReturnSumTriangleReturn
      (k := k) sigma (sigma.finiteDimensionalARTranslationData k R)).trans <|
    Equiv.sumCongr (Equiv.refl _) <|
      (hookM5TriangleReturnEquivDiagonalSumRowT sigma
          (sigma.finiteDimensionalARTranslationData k R)).trans <|
        Equiv.sumCongr (Equiv.refl _)
          (hookM5RowTReturnEquivQuotientTrianglePacketFour
            (k := k) (R := R) sigma)

/-- Cardinal form of the complete return correction. -/
theorem hookM5Rejected_card_eq_fixedReturn_add_diagonalReturn_add_trianglePacket :
    Fintype.card
        ((sigma.finiteDimensionalARTranslationData k R).HookM5Rejected
          sigma) =
      Fintype.card
          ((sigma.finiteDimensionalARTranslationData k R).HookM5FixedReturn
            sigma) +
        Fintype.card
          ((sigma.finiteDimensionalARTranslationData k R).HookM5DiagonalReturn
            sigma) +
        Fintype.card
          (QuotientTrianglePacketFour (k := k) (R := R) sigma) := by
  rw [Fintype.card_congr
    (hookM5RejectedEquivFixedReturnSumDiagonalSumTrianglePacket
      (k := k) (R := R) sigma)]
  simp only [Fintype.card_sum]
  omega

/-- Exact form of the manuscript identity `preliminary M₅ = M₅ + R`. -/
def hookM5PreliminaryEquivChannelSumRejected :
    AR.HookM5Preliminary sigma ≃
      AR.HookM5Channel sigma ⊕ AR.HookM5Rejected sigma where
  toFun M := by
    classical
    by_cases h : M.HasReturn sigma
    · exact Sum.inr ⟨M, h⟩
    · exact Sum.inl (M.toChannel sigma AR h)
  invFun X := by
    rcases X with M | M
    · exact M.toPreliminary sigma AR
    · exact M.1
  left_inv M := by
    classical
    by_cases h : M.HasReturn sigma
    · simp [h]
    · simp [h]
  right_inv X := by
    classical
    rcases X with M | M
    · simp [M.toPreliminary_noReturn sigma AR]
    · simp [M.2]

/-- Cardinal form of the preliminary-channel return decomposition. -/
theorem hookM5Preliminary_card_eq_channel_add_rejected :
    Fintype.card (AR.HookM5Preliminary sigma) =
      Fintype.card (AR.HookM5Channel sigma) +
        Fintype.card (AR.HookM5Rejected sigma) := by
  rw [Fintype.card_congr
    (hookM5PreliminaryEquivChannelSumRejected sigma AR)]
  exact Fintype.card_sum

namespace HookM5Preliminary

variable (M : AR.HookM5Preliminary sigma)

/-- The unique preliminary outgoing arrow, selected in the same order as
the genuine `M₅` channel. -/
def associatedArrow : sigma.IrreduciblePair := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · exact ⟨(M.triple.u, M.z), h⟩
  · exact ⟨(M.triple.b, M.z), M.outgoing_to_z.resolve_left h⟩

/-- The displayed hook arrow ending at the source of the selected
preliminary outgoing arrow. -/
def hookArrow : sigma.IrreduciblePair := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · exact M.triple.firstArrow sigma AR
  · exact M.triple.secondArrow sigma AR

omit [Fintype iota] in
@[simp]
theorem associatedArrow_target :
    (M.associatedArrow sigma AR).1.2 = M.z := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · simp [associatedArrow, h]
  · simp [associatedArrow, h]

omit [Fintype iota] in
theorem associatedArrow_source_eq_hookArrow_target :
    (M.associatedArrow sigma AR).1.1 =
      (M.hookArrow sigma AR).1.2 := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · simp [associatedArrow, hookArrow, h,
      StripAdmissibleTriple.firstArrow]
  · simp [associatedArrow, hookArrow, h,
      StripAdmissibleTriple.secondArrow]

/-- Rotate the selected preliminary outgoing arrow once so that it has a
common target with the selected hook arrow. -/
def rotatedAssociatedArrow : sigma.IrreduciblePair :=
  (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau
    ⟨M.associatedArrow sigma AR, by
      simpa only [M.associatedArrow_target sigma AR] using
        M.z_nonprojective⟩).1

theorem rotatedAssociatedArrow_successor :
    ((AR.arMeshRotationData sigma).arrowOrbitData sigma).successor
        (M.rotatedAssociatedArrow sigma AR) =
      M.associatedArrow sigma AR := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  let p : {q : sigma.IrreduciblePair //
      ¬ Projective (sigma.obj q.1.2)} :=
    ⟨M.associatedArrow sigma AR, by
      simpa only [M.associatedArrow_target sigma AR] using
        M.z_nonprojective⟩
  let q := O.tau p
  change O.successor q.1 = p.1
  have hsuccessor : O.successor q.1 = O.tau.symm ⟨q.1, q.2⟩ := by
    simp [QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.successor, q.2]
  rw [hsuccessor]
  exact congrArg Subtype.val (O.tau.symm_apply_apply p)

theorem rotatedAssociatedArrow_target_eq_hookArrow_target :
    (M.rotatedAssociatedArrow sigma AR).1.2 =
      (M.hookArrow sigma AR).1.2 := by
  let O := (AR.arMeshRotationData sigma).arrowOrbitData sigma
  have hrotate := (AR.arMeshRotationData sigma).arrowOrbitData_tau_val sigma
    ⟨M.associatedArrow sigma AR, by
      simpa only [M.associatedArrow_target sigma AR] using
        M.z_nonprojective⟩
  exact (congrArg Prod.snd hrotate).trans
    (M.associatedArrow_source_eq_hookArrow_target sigma AR)

omit [Fintype iota] in
theorem hookArrow_target_nonprojective :
    ¬ Projective (sigma.obj (M.hookArrow sigma AR).1.2) := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
      M.triple.u_nonprojective
  · simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
      M.triple.b_nonprojective

theorem rotatedAssociatedArrow_isInterior :
    IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) := by
  refine ⟨?_, ?_⟩
  · rw [M.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR]
    exact M.hookArrow_target_nonprojective sigma AR
  · exact (((AR.arMeshRotationData sigma).arrowOrbitData sigma).tau
      ⟨M.associatedArrow sigma AR, by
        simpa only [M.associatedArrow_target sigma AR] using
          M.z_nonprojective⟩).2

omit [Fintype iota] in
theorem hookArrow_isInterior_iff :
    IsInteriorArrow sigma (M.hookArrow sigma AR) ↔
      HasIrreducibleMorphism
          (sigma.obj M.triple.u) (sigma.obj M.z) ∨
        ¬ Injective (sigma.obj M.triple.u) := by
  classical
  by_cases h : HasIrreducibleMorphism
      (sigma.obj M.triple.u) (sigma.obj M.z)
  · simp only [h, true_or, iff_true]
    refine ⟨?_, ?_⟩
    · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
        M.triple.u_nonprojective
    · simpa [hookArrow, h, StripAdmissibleTriple.firstArrow] using
        M.triple.a_noninjective sigma AR
  · simp only [h, false_or]
    constructor
    · intro hInterior
      simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
        hInterior.2
    · intro huNI
      exact ⟨by
          simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
            M.triple.b_nonprojective,
        by simpa [hookArrow, h, StripAdmissibleTriple.secondArrow] using
          huNI⟩

/-- Preliminary terms whose two assigned arrow occurrences survive the
outer-boundary trimming. -/
abbrev InteriorChannel :=
  {M : AR.HookM5Preliminary sigma //
    IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.hookArrow sigma AR)}

theorem interiorChannel_iff :
    (IsInteriorArrow sigma (M.rotatedAssociatedArrow sigma AR) ∧
      IsInteriorArrow sigma (M.hookArrow sigma AR)) ↔
        HasIrreducibleMorphism
            (sigma.obj M.triple.u) (sigma.obj M.z) ∨
          ¬ Injective (sigma.obj M.triple.u) := by
  rw [M.hookArrow_isInterior_iff sigma AR]
  simp only [M.rotatedAssociatedArrow_isInterior sigma AR, true_and]

/-- The raw common-target occurrence assigned to a preliminary `M₅`
term. -/
def commonTargetPair : CommonTargetArrowPair sigma :=
  ⟨(M.rotatedAssociatedArrow sigma AR, M.hookArrow sigma AR),
    M.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR⟩

/-- The preliminary occurrence assignment retains the triple and fourth
label. -/
theorem commonTargetPair_injective :
    Function.Injective (commonTargetPair sigma AR) := by
  classical
  intro M₁ M₂ hpair
  have hrotated := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.1) hpair
  have hhook := congrArg
    (fun p : CommonTargetArrowPair sigma ↦ p.1.2) hpair
  change M₁.rotatedAssociatedArrow sigma AR =
    M₂.rotatedAssociatedArrow sigma AR at hrotated
  change M₁.hookArrow sigma AR = M₂.hookArrow sigma AR at hhook
  have hassociated : M₁.associatedArrow sigma AR =
      M₂.associatedArrow sigma AR := by
    have hsucc := congrArg
      ((AR.arMeshRotationData sigma).arrowOrbitData sigma).successor hrotated
    simpa only [M₁.rotatedAssociatedArrow_successor sigma AR,
      M₂.rotatedAssociatedArrow_successor sigma AR] using hsucc
  have hz : M₁.z = M₂.z := by
    simpa only [M₁.associatedArrow_target sigma AR,
      M₂.associatedArrow_target sigma AR] using congrArg
        (fun q : sigma.IrreduciblePair ↦ q.1.2) hassociated
  by_cases h₁ : HasIrreducibleMorphism
      (sigma.obj M₁.triple.u) (sigma.obj M₁.z)
  · by_cases h₂ : HasIrreducibleMorphism
        (sigma.obj M₂.triple.u) (sigma.obj M₂.z)
    · have htriple := StripAdmissibleTriple.firstArrow_injective
          sigma AR (by simpa [hookArrow, h₁, h₂] using hhook)
      exact HookM5Preliminary.ext htriple hz
    · have hau : M₁.triple.a = M₂.triple.u := by
        have hhook' : M₁.triple.firstArrow sigma AR =
            M₂.triple.secondArrow sigma AR := by
          simpa [hookArrow, h₁, h₂] using hhook
        exact congrArg (fun q : sigma.IrreduciblePair ↦ q.1.1) hhook'
      exact (M₂.triple.u_nonprojective
        (hau ▸ M₁.a_projective)).elim
  · by_cases h₂ : HasIrreducibleMorphism
        (sigma.obj M₂.triple.u) (sigma.obj M₂.z)
    · have hua : M₁.triple.u = M₂.triple.a := by
        have hhook' : M₁.triple.secondArrow sigma AR =
            M₂.triple.firstArrow sigma AR := by
          simpa [hookArrow, h₁, h₂] using hhook
        exact congrArg (fun q : sigma.IrreduciblePair ↦ q.1.1) hhook'
      exact (M₁.triple.u_nonprojective
        (hua.symm ▸ M₂.a_projective)).elim
    · have htriple := StripAdmissibleTriple.secondArrow_injective
          sigma AR (by simpa [hookArrow, h₁, h₂] using hhook)
      exact HookM5Preliminary.ext htriple hz

/-- The trimmed raw occurrence assigned to an interior preliminary term. -/
def interiorCommonTargetPair
    (X : HookM5Preliminary.InteriorChannel sigma AR) :
    AR.InteriorCommonTargetArrowPair sigma :=
  ⟨(toInteriorArrow sigma AR
      (X.1.rotatedAssociatedArrow sigma AR) X.2.1,
    toInteriorArrow sigma AR (X.1.hookArrow sigma AR) X.2.2),
    X.1.rotatedAssociatedArrow_target_eq_hookArrow_target sigma AR⟩

/-- Every trimmed preliminary occurrence lies on the shifted source
boundary. -/
def interiorSourceBoundaryPair
    (X : HookM5Preliminary.InteriorChannel sigma AR) :
    AR.InteriorSourceBoundaryCommonTargetArrowPair sigma := by
  classical
  let N := AR.arMeshRotationData sigma
  let O := N.arrowOrbitData sigma
  let U := N.arrowInteriorOrbitData sigma
  let H := toInteriorArrow sigma AR (X.1.hookArrow sigma AR) X.2.2
  refine ⟨HookM5Preliminary.interiorCommonTargetPair sigma AR X,
    Or.inr ?_⟩
  by_cases h : HasIrreducibleMorphism
      (sigma.obj X.1.triple.u) (sigma.obj X.1.z)
  · left
    apply (N.arrowInterior_source_iff sigma H).2
    simpa [H, toInteriorArrow, hookArrow, h,
      StripAdmissibleTriple.firstArrow] using X.1.a_projective
  · right
    intro hnot
    apply (N.arrowInterior_source_iff sigma (U.tau ⟨H, hnot⟩).1).2
    have hval : (U.tau ⟨H, hnot⟩).1.1 =
        X.1.triple.firstArrow sigma AR := by
      have hpred := congrArg Subtype.val
        (X.1.triple.secondArrow_predecessor sigma AR)
      simpa [U, N, O, H, ARMeshRotationData.arrowInteriorOrbitData,
        QuotientSubmoduleEquidistribution.BoundaryTranslationChains.Data.interior,
        toInteriorArrow, hookArrow, h] using hpred
    rw [hval]
    simpa [StripAdmissibleTriple.firstArrow] using X.1.a_projective

theorem interiorCommonTargetPair_injective :
    Function.Injective (interiorCommonTargetPair sigma AR) := by
  intro X Y h
  apply Subtype.ext
  apply commonTargetPair_injective sigma AR
  have hf := congrArg (forgetInteriorCommonTarget sigma AR) h
  simpa [interiorCommonTargetPair, forgetInteriorCommonTarget,
    toInteriorArrow, commonTargetPair] using hf

end HookM5Preliminary

namespace HookM5Channel

variable (M : AR.HookM5Channel sigma)

/-- The preliminary occurrence construction extends the existing genuine
`M₅` occurrence construction without changing its labelled arrow pair. -/
@[simp]
theorem toPreliminary_commonTargetPair :
    (M.toPreliminary sigma AR).commonTargetPair sigma AR =
      M.commonTargetPair sigma AR := by
  apply Subtype.ext
  rfl

end HookM5Channel

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData
