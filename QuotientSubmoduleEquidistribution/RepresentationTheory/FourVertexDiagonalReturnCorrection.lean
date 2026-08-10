import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexPreliminaryM5

/-!
# The diagonal return and the consecutive double-hook correction

At the projective end of a labelled hook orbit, a strip triple whose
middle vertex is noninjective has a canonical fourth vertex
`z = tau^{-1} u`.  The mesh supplies `b → z` and `tau z = u`.  If the
additional arrow `z → u` is present, this is precisely the diagonal
preliminary-`M₅` return.  If it is absent, the four labels carry the two
consecutive admissible hooks.  This file packages that local dichotomy.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (AR : σ.FiniteARTranslationData)

/-- A projective-end admissible strip triple for which the next labelled
arrow occurrence after the displayed hook exists. -/
abbrev HookDiagonalCandidate :=
  {T : AR.StripAdmissibleTriple σ //
    Projective (σ.obj T.a) ∧ ¬ Injective (σ.obj T.u)}

noncomputable instance hookDiagonalCandidateFintype :
    Fintype (AR.HookDiagonalCandidate σ) := Fintype.ofFinite _

namespace HookDiagonalCandidate

variable (C : AR.HookDiagonalCandidate σ)

/-- The target of the occurrence immediately after `u → b`. -/
def z : ι :=
  ((AR.arTranslationEquiv σ).symm ⟨C.1.u, C.2.2⟩).1

omit [DecidableEq ι] in
theorem z_nonprojective : ¬ Projective (σ.obj (C.z σ AR)) :=
  ((AR.arTranslationEquiv σ).symm ⟨C.1.u, C.2.2⟩).2

omit [DecidableEq ι] in
theorem tau_z :
    (AR.arTranslation σ ⟨C.z σ AR, C.z_nonprojective σ AR⟩).1 =
      C.1.u := by
  exact congrArg Subtype.val
    ((AR.arTranslationEquiv σ).apply_symm_apply ⟨C.1.u, C.2.2⟩)

omit [DecidableEq ι] in
theorem b_to_z :
    HasIrreducibleMorphism (σ.obj C.1.b) (σ.obj (C.z σ AR)) := by
  apply (AR.arTranslation_incidence σ
    ⟨C.z σ AR, C.z_nonprojective σ AR⟩ C.1.b).2
  simpa only [C.tau_z σ AR] using C.1.u_to_b

omit [DecidableEq ι] in
theorem z_ne_a : C.z σ AR ≠ C.1.a := by
  intro h
  exact C.z_nonprojective σ AR (h ▸ C.2.1)

omit [DecidableEq ι] in
theorem z_ne_u : C.z σ AR ≠ C.1.u := by
  intro h
  exact C.1.b_not_to_u (by simpa only [h] using C.b_to_z σ AR)

omit [DecidableEq ι] in
theorem z_ne_b : C.z σ AR ≠ C.1.b := by
  intro h
  exact σ.hasNoIrreducibleEndomorphism_obj C.1.b
    (by simpa only [h] using C.b_to_z σ AR)

/-- The canonical fourth vertex gives the preliminary positive term before
the possible diagonal return is removed. -/
def preliminary : AR.HookM5Preliminary σ where
  triple := C.1
  a_projective := C.2.1
  z := C.z σ AR
  z_not_mem := by
    simp only [StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨C.z_ne_a σ AR, C.z_ne_u σ AR, C.z_ne_b σ AR⟩
  z_nonprojective := C.z_nonprojective σ AR
  outgoing_to_z := Or.inr (C.b_to_z σ AR)

include k in
/-- The canonical fourth vertex cannot point back to `b`. -/
theorem z_not_to_b :
    ¬ HasIrreducibleMorphism (σ.obj (C.z σ AR)) (σ.obj C.1.b) := by
  exact fun h ↦ (C.preliminary σ AR).not_b_to_z_and_z_to_b
    (k := k) σ AR ⟨C.b_to_z σ AR, h⟩

omit [DecidableEq ι] in
/-- The arrow `u → z` is forbidden because `u = tau z`. -/
theorem u_not_to_z :
    ¬ HasIrreducibleMorphism (σ.obj C.1.u) (σ.obj (C.z σ AR)) := by
  intro h
  apply AR.no_irreducible_arTranslation_to_endpoint σ
    ⟨C.z σ AR, C.z_nonprojective σ AR⟩
  simpa only [C.tau_z σ AR] using h

omit [DecidableEq ι] in
include k in
/-- The projective first hook label cannot also point to the canonical
fourth vertex. -/
theorem a_not_to_z :
    ¬ HasIrreducibleMorphism (σ.obj C.1.a) (σ.obj (C.z σ AR)) := by
  intro haz
  have hua : HasIrreducibleMorphism (σ.obj C.1.u) (σ.obj C.1.a) := by
    have h := (AR.arTranslation_incidence σ
      ⟨C.z σ AR, C.z_nonprojective σ AR⟩ C.1.a).1 haz
    simpa only [C.tau_z σ AR] using h
  have haI := AR.injective_of_projective_two_cycle
    (K := k) σ C.1.a C.1.u C.2.1 C.1.a_to_u hua
  exact C.1.a_noninjective σ AR haI

/-- The next three consecutive labels again form an admissible strip
triple, now `(u,b,z)`. -/
def nextTriple : AR.StripAdmissibleTriple σ where
  a := C.1.u
  u := C.1.b
  b := C.z σ AR
  a_ne_u := C.1.u_ne_b
  a_ne_b := C.z_ne_u σ AR |>.symm
  u_ne_b := C.z_ne_b σ AR |>.symm
  u_nonprojective := C.1.b_nonprojective
  b_nonprojective := C.z_nonprojective σ AR
  a_to_u := C.1.u_to_b
  u_to_b := C.b_to_z σ AR
  b_not_to_u := C.z_not_to_b (k := k) σ AR
  a_not_to_b := C.u_not_to_z σ AR
  tau_b := C.tau_z σ AR

/-- A candidate carrying the extra arrow `z → u` is exactly a diagonal
preliminary-`M₅` return. -/
def toDiagonalReturn
    (h : HasIrreducibleMorphism (σ.obj (C.z σ AR)) (σ.obj C.1.u)) :
    AR.HookM5DiagonalReturn σ :=
  ⟨⟨C.preliminary σ AR, C.b_to_z σ AR, h⟩, C.tau_z σ AR⟩

end HookDiagonalCandidate

/-- A canonical projective-end candidate with its diagonal-return arrow
absent. -/
abbrev HookDoubleCandidate :=
  {C : AR.HookDiagonalCandidate σ //
    ¬ HasIrreducibleMorphism (σ.obj (C.z σ AR)) (σ.obj C.1.u)}

noncomputable instance hookDoubleCandidateFintype :
    Fintype (AR.HookDoubleCandidate σ) := Fintype.ofFinite _

namespace HookM5DiagonalReturn

variable (M : AR.HookM5DiagonalReturn σ)

/-- Forget a diagonal return down to its canonical projective-end strip
candidate. -/
def toDiagonalCandidate : AR.HookDiagonalCandidate σ :=
  ⟨M.1.1.triple, M.1.1.a_projective, by
    have h := (AR.arTranslation σ
      ⟨M.1.1.z, M.1.1.z_nonprojective⟩).2
    simpa only [M.2] using h⟩

@[simp]
theorem toDiagonalCandidate_z :
    (M.toDiagonalCandidate σ AR).z σ AR = M.1.1.z := by
  have h :
      (⟨(M.toDiagonalCandidate σ AR).z σ AR,
          (M.toDiagonalCandidate σ AR).z_nonprojective σ AR⟩ :
        σ.NonprojectiveLabel) =
      ⟨M.1.1.z, M.1.1.z_nonprojective⟩ := by
    apply AR.arTranslation_injective σ
    apply Subtype.ext
    exact (M.toDiagonalCandidate σ AR).tau_z σ AR |>.trans M.2.symm
  exact congrArg Subtype.val h

end HookM5DiagonalReturn

/-- Canonical projective-end candidates split exactly into diagonal
returns and candidates for consecutive double hooks. -/
def hookDiagonalCandidateEquivDiagonalReturnSumDoubleCandidate :
    AR.HookDiagonalCandidate σ ≃
      AR.HookM5DiagonalReturn σ ⊕
        AR.HookDoubleCandidate σ where
  toFun C := by
    classical
    by_cases h : HasIrreducibleMorphism
        (σ.obj (C.z σ AR)) (σ.obj C.1.u)
    · exact Sum.inl (C.toDiagonalReturn σ AR h)
    · exact Sum.inr ⟨C, h⟩
  invFun X := by
    rcases X with M | C
    · exact M.toDiagonalCandidate σ AR
    · exact C.1
  left_inv C := by
    classical
    by_cases h : HasIrreducibleMorphism
        (σ.obj (C.z σ AR)) (σ.obj C.1.u)
    · simp only [h, dite_true]
      apply Subtype.ext
      rfl
    · simp only [h, dite_false]
  right_inv X := by
    classical
    rcases X with M | C
    · have hz := HookM5DiagonalReturn.toDiagonalCandidate_z σ AR M
      have hreturn : HasIrreducibleMorphism
          (σ.obj ((M.toDiagonalCandidate σ AR).z σ AR))
          (σ.obj (M.toDiagonalCandidate σ AR).1.u) := by
        rw [hz]
        change HasIrreducibleMorphism
          (σ.obj M.1.1.z) (σ.obj M.1.1.triple.u)
        exact M.1.2.2
      simp only [hreturn, dite_true]
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Subtype.ext
      apply HookM5Preliminary.ext
      · rfl
      · exact hz
    · simp only [C.2]
      rfl

/-- Cardinal form of the canonical diagonal/double-candidate split. -/
theorem hookDiagonalCandidate_card_eq_diagonalReturn_add_doubleCandidate :
    Fintype.card (AR.HookDiagonalCandidate σ) =
      Fintype.card (AR.HookM5DiagonalReturn σ) +
        Fintype.card (AR.HookDoubleCandidate σ) := by
  rw [Fintype.card_congr
    (hookDiagonalCandidateEquivDiagonalReturnSumDoubleCandidate σ AR)]
  exact Fintype.card_sum

/-- A rooted four-support carrying at least two admissible hooks for the
chosen AR translation data. -/
abbrev RootedDoubleHook :=
  {D : QuotientRootedFour σ //
    Nontrivial (AR.AdmissibleHook σ
      ((((D.1 : Finset ι) : Set ι)ᶜ)))}

noncomputable instance rootedDoubleHookFintype :
    Fintype (AR.RootedDoubleHook σ) := Fintype.ofFinite _

namespace AdmissibleHook

omit [Field k] [Algebra k R] [FiniteDimensional k R] in
/-- Two admissible hooks on the same rooted four-support cannot both start
at projective labels. -/
theorem eq_of_sources_projective
    (Deleted : Finset ι)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hcard : Deleted.card ≤ 4)
    (H₁ H₂ : AR.AdmissibleHook σ (((Deleted : Finset ι) : Set ι)ᶜ))
    (h₁P : Projective (σ.obj H₁.a.1))
    (h₂P : Projective (σ.obj H₂.a.1)) :
    H₁ = H₂ := by
  by_contra hne
  rcases H₁.doubleHook_shape_of_ne σ AR Deleted hroot hcard hne with
      h₁₂ | h₂₁
  · have h := h₂P
    rw [congrArg Subtype.val h₁₂.2.2] at h
    exact H₁.u_nonprojective h
  · have h := h₁P
    rw [congrArg Subtype.val h₂₁.2.2] at h
    exact H₂.u_nonprojective h

end AdmissibleHook

/-- Two distinct hooks, oriented so that the first one is the unique hook
whose source is projective. -/
structure OrientedDoubleHookWitness (Q : AR.RootedDoubleHook σ) where
  first : AR.AdmissibleHook σ ((((Q.1.1 : Finset ι) : Set ι)ᶜ))
  second : AR.AdmissibleHook σ ((((Q.1.1 : Finset ι) : Set ι)ᶜ))
  ne : first ≠ second
  consecutive : first.b = second.u
  first_projective : Projective (σ.obj first.a.1)
  second_source : second.a = first.u

namespace RootedDoubleHook

variable (Q : AR.RootedDoubleHook σ)

/-- The consecutive-double-hook theorem canonically orients any two
distinct hooks by their projective source. -/
def orientedWitness : AR.OrientedDoubleHookWitness σ Q := by
  apply Classical.choice
  letI : Nontrivial
      (AR.AdmissibleHook σ ((((Q.1.1 : Finset ι) : Set ι)ᶜ))) := Q.2
  obtain ⟨H₁, H₂, hne⟩ := exists_pair_ne
    (AR.AdmissibleHook σ ((((Q.1.1 : Finset ι) : Set ι)ᶜ)))
  rcases H₁.doubleHook_shape_of_ne σ AR Q.1.1 Q.1.2.2
      (by rw [Q.1.2.1]) hne with h₁₂ | h₂₁
  · exact ⟨
      { first := H₁
        second := H₂
        ne := hne
        consecutive := h₁₂.1
        first_projective := h₁₂.2.1
        second_source := h₁₂.2.2 }⟩
  · exact ⟨
      { first := H₂
        second := H₁
        ne := Ne.symm hne
        consecutive := h₂₁.1
        first_projective := h₂₁.2.1
        second_source := h₂₁.2.2 }⟩

/-- The projectively based first hook of a rooted double support, regarded
as the canonical diagonal candidate. -/
def diagonalCandidate : AR.HookDiagonalCandidate σ := by
  let W := Q.orientedWitness σ AR
  let T := W.first.toStripAdmissibleTriple σ AR Q.1.1 Q.1.2.2
  refine ⟨T, W.first_projective, ?_⟩
  let T₂ := W.second.toStripAdmissibleTriple σ AR Q.1.1 Q.1.2.2
  have h₂ := T₂.a_noninjective σ AR
  change ¬ Injective (σ.obj W.first.u.1)
  rw [← congrArg Subtype.val W.second_source]
  exact h₂

theorem diagonalCandidate_z_eq_second_b :
    (Q.diagonalCandidate σ AR).z σ AR =
      (Q.orientedWitness σ AR).second.b.1 := by
  let W := Q.orientedWitness σ AR
  have h :
      (⟨(Q.diagonalCandidate σ AR).z σ AR,
          (Q.diagonalCandidate σ AR).z_nonprojective σ AR⟩ :
        σ.NonprojectiveLabel) =
      ⟨W.second.b.1, W.second.b_nonprojective⟩ := by
    apply AR.arTranslation_injective σ
    apply Subtype.ext
    calc
      (AR.arTranslation σ
          ⟨(Q.diagonalCandidate σ AR).z σ AR,
            (Q.diagonalCandidate σ AR).z_nonprojective σ AR⟩).1 =
          W.first.u.1 := (Q.diagonalCandidate σ AR).tau_z σ AR
      _ = W.second.a.1 := (congrArg Subtype.val W.second_source).symm
      _ = (AR.arTranslation σ
          ⟨W.second.b.1, W.second.b_nonprojective⟩).1 :=
        W.second.tau_b.symm
  exact congrArg Subtype.val h

/-- The selected candidate has no diagonal return: otherwise the unique
predecessor of its middle vertex would identify the nonprojective end of
the second hook with the projective source of the first. -/
def doubleCandidate : AR.HookDoubleCandidate σ := by
  let W := Q.orientedWitness σ AR
  let C := Q.diagonalCandidate σ AR
  refine ⟨C, ?_⟩
  intro hzu
  have hz : C.z σ AR = W.second.b.1 :=
    RootedDoubleHook.diagonalCandidate_z_eq_second_b σ AR Q
  have heq : W.second.b = W.first.a := by
    apply W.first.predecessor_u.2 W.second.b
    rw [← hz]
    simpa [C, RootedDoubleHook.diagonalCandidate,
      AdmissibleHook.toStripAdmissibleTriple] using hzu
  exact W.second.b_nonprojective
    (congrArg Subtype.val heq |>.symm ▸ W.first_projective)

end RootedDoubleHook

namespace HookDoubleCandidate

variable (C : AR.HookDoubleCandidate σ)

/-- The canonical four-label support of a non-diagonal candidate. -/
def deleted : Finset ι := (C.1.preliminary σ AR).support

@[simp]
theorem deleted_card : (C.deleted σ AR).card = 4 :=
  (C.1.preliminary σ AR).support_card σ AR

/-- The original triple gives the first admissible hook on the canonical
four-label support. -/
def firstHook :
    AR.AdmissibleHook σ ((((C.deleted σ AR : Finset ι) : Set ι)ᶜ)) := by
  let T := C.1.1
  let P := C.1.preliminary σ AR
  let Deleted := C.deleted σ AR
  let K : Set ι := (((Deleted : Finset ι) : Set ι)ᶜ)
  let a : DeletedLabel K := ⟨T.a, by
    simp [T, K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let u : DeletedLabel K := ⟨T.u, by
    simp [T, K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let b : DeletedLabel K := ⟨T.b, by
    simp [T, K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  refine
    { a := a
      u := u
      b := b
      u_nonprojective := T.u_nonprojective
      b_nonprojective := T.b_nonprojective
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := T.tau_b }
  · refine ⟨T.a_to_u, ?_⟩
    intro q hqu
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqz | hqa | hquself | hqb
    · exact (C.2 (by simpa only [hqz] using hqu)).elim
    · exact Subtype.ext hqa
    · exact (σ.hasNoIrreducibleEndomorphism_obj T.u
        (by simpa only [hquself] using hqu)).elim
    · exact (T.b_not_to_u (by simpa only [hqb] using hqu)).elim
  · refine ⟨T.u_to_b, ?_⟩
    intro q hqbArrow
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqz | hqa | hqu | hqbself
    · exact (C.1.z_not_to_b (k := k) σ AR
        (by simpa only [hqz] using hqbArrow)).elim
    · exact (T.a_not_to_b (by simpa only [hqa] using hqbArrow)).elim
    · exact Subtype.ext hqu
    · exact (σ.hasNoIrreducibleEndomorphism_obj T.b
        (by simpa only [hqbself] using hqbArrow)).elim

theorem firstHook_source_projective :
    Projective (σ.obj (C.firstHook (k := k) σ AR).a.1) := by
  change Projective (σ.obj C.1.1.a)
  exact C.1.2.1

/-- Converting the constructed first hook back to strip coordinates
recovers the candidate's original triple. -/
@[simp]
theorem firstHook_toStripAdmissibleTriple :
    (C.firstHook (k := k) σ AR).toStripAdmissibleTriple
        σ AR (C.deleted σ AR) (C.1.preliminary σ AR |>.rooted σ AR) =
      C.1.1 := by
  apply StripAdmissibleTriple.ext <;> rfl

/-- The shifted triple `(u,b,z)` gives the second admissible hook on the
same support. -/
def secondHook :
    AR.AdmissibleHook σ ((((C.deleted σ AR : Finset ι) : Set ι)ᶜ)) := by
  let T := C.1.1
  let P := C.1.preliminary σ AR
  let Deleted := C.deleted σ AR
  let K : Set ι := (((Deleted : Finset ι) : Set ι)ᶜ)
  let u : DeletedLabel K := ⟨T.u, by
    simp [T, K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let b : DeletedLabel K := ⟨T.b, by
    simp [T, K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support]⟩
  let z : DeletedLabel K := ⟨C.1.z σ AR, by
    simp [K, Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support]⟩
  refine
    { a := u
      u := b
      b := z
      u_nonprojective := T.b_nonprojective
      b_nonprojective := C.1.z_nonprojective σ AR
      predecessor_u := ?_
      predecessor_b := ?_
      tau_b := C.1.tau_z σ AR }
  · refine ⟨T.u_to_b, ?_⟩
    intro q hqbArrow
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqz | hqa | hqu | hqbself
    · exact (C.1.z_not_to_b (k := k) σ AR
        (by simpa only [hqz] using hqbArrow)).elim
    · exact (T.a_not_to_b (by simpa only [hqa] using hqbArrow)).elim
    · exact Subtype.ext hqu
    · exact (σ.hasNoIrreducibleEndomorphism_obj T.b
        (by simpa only [hqbself] using hqbArrow)).elim
  · refine ⟨C.1.b_to_z σ AR, ?_⟩
    intro q hqzArrow
    have hqmem : q.1 ∈ Deleted := by simpa [K] using q.2
    simp only [Deleted, deleted, HookDiagonalCandidate.preliminary,
      HookM5Preliminary.support,
      StripAdmissibleTriple.support, Finset.mem_insert,
      Finset.mem_singleton] at hqmem
    rcases hqmem with hqzself | hqa | hqu | hqb
    · exact (σ.hasNoIrreducibleEndomorphism_obj (C.1.z σ AR)
        (by simpa only [hqzself] using hqzArrow)).elim
    · exact (C.1.a_not_to_z (k := k) σ AR
        (by simpa only [hqa] using hqzArrow)).elim
    · exact (C.1.u_not_to_z σ AR
        (by simpa only [hqu] using hqzArrow)).elim
    · exact Subtype.ext hqb

theorem firstHook_ne_secondHook :
    C.firstHook (k := k) σ AR ≠ C.secondHook (k := k) σ AR := by
  intro h
  have ha := congrArg
    (fun H : AR.AdmissibleHook σ
        ((((C.deleted σ AR : Finset ι) : Set ι)ᶜ)) ↦ H.a.1) h
  exact C.1.1.a_ne_u ha

/-- A non-diagonal canonical candidate supplies a rooted support carrying
at least two hooks for the chosen AR translation data. -/
def toRootedDoubleHook :
    AR.RootedDoubleHook σ := by
  let Deleted := C.deleted σ AR
  let Rooted : QuotientRootedFour σ :=
    ⟨Deleted, HookDoubleCandidate.deleted_card σ AR C,
      C.1.preliminary σ AR |>.rooted σ AR⟩
  let H₁ := C.firstHook (k := k) σ AR
  let H₂ := C.secondHook (k := k) σ AR
  letI : Nontrivial
      (AR.AdmissibleHook σ ((((Deleted : Finset ι) : Set ι)ᶜ)) ) :=
    ⟨⟨H₁, H₂,
      HookDoubleCandidate.firstHook_ne_secondHook (k := k) σ AR C⟩⟩
  refine ⟨Rooted, ?_⟩
  change Nontrivial
    (AR.AdmissibleHook σ ((((Deleted : Finset ι) : Set ι)ᶜ)))
  exact inferInstance

end HookDoubleCandidate

/-- Specialization of the consecutive-hook construction to the canonical
finite-dimensional AR data used by the quotient packet type. -/
def hookDoubleCandidateToQuotientDoubleHookFour
    (C : (σ.finiteDimensionalARTranslationData k R).HookDoubleCandidate σ) :
    QuotientDoubleHookFour (k := k) (R := R) σ :=
  C.toRootedDoubleHook (k := k) σ
    (σ.finiteDimensionalARTranslationData k R)

/-- The non-diagonal canonical candidates are exactly the unpointed rooted
double-hook supports.  The apparently forgotten first hook is recoverable
because a rooted four-support has a unique hook with projective source. -/
def hookDoubleCandidateEquivRootedDoubleHook :
    AR.HookDoubleCandidate σ ≃ AR.RootedDoubleHook σ where
  toFun C := C.toRootedDoubleHook (k := k) σ AR
  invFun Q := Q.doubleCandidate σ AR
  left_inv C := by
    let Q := C.toRootedDoubleHook (k := k) σ AR
    let W := Q.orientedWitness σ AR
    have hfirst : W.first = C.firstHook (k := k) σ AR := by
      apply AdmissibleHook.eq_of_sources_projective σ AR
        (C.deleted σ AR)
        (C.1.preliminary σ AR |>.rooted σ AR)
        (by rw [HookDoubleCandidate.deleted_card σ AR C])
      · exact W.first_projective
      · exact C.firstHook_source_projective (k := k) σ AR
    apply Subtype.ext
    apply Subtype.ext
    change W.first.toStripAdmissibleTriple σ AR
        (C.deleted σ AR) (C.1.preliminary σ AR |>.rooted σ AR) = C.1.1
    rw [hfirst]
    exact C.firstHook_toStripAdmissibleTriple (k := k) σ AR
  right_inv Q := by
    let W := Q.orientedWitness σ AR
    let C := Q.doubleCandidate σ AR
    have hz : C.1.z σ AR = W.second.b.1 :=
      RootedDoubleHook.diagonalCandidate_z_eq_second_b σ AR Q
    apply Subtype.ext
    apply Subtype.ext
    change C.deleted σ AR = Q.1.1
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      change x ∈ (C.1.preliminary σ AR).support at hx
      simp only [HookM5Preliminary.support,
        StripAdmissibleTriple.support, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with hxz | hxa | hxu | hxb
      · subst x
        change C.1.z σ AR ∈ Q.1.1
        rw [hz]
        simpa using W.second.b.2
      · subst x
        change C.1.1.a ∈ Q.1.1
        simpa [C, RootedDoubleHook.doubleCandidate,
          RootedDoubleHook.diagonalCandidate,
          AdmissibleHook.toStripAdmissibleTriple] using W.first.a.2
      · subst x
        change C.1.1.u ∈ Q.1.1
        simpa [C, RootedDoubleHook.doubleCandidate,
          RootedDoubleHook.diagonalCandidate,
          AdmissibleHook.toStripAdmissibleTriple] using W.first.u.2
      · subst x
        change C.1.1.b ∈ Q.1.1
        simpa [C, RootedDoubleHook.doubleCandidate,
          RootedDoubleHook.diagonalCandidate,
          AdmissibleHook.toStripAdmissibleTriple] using W.first.b.2
    · rw [HookDoubleCandidate.deleted_card σ AR C, Q.1.2.1]

/-- Consequently a diagonal return plus an actual double-hook support is
exactly one canonical projective-end candidate. -/
def hookDiagonalCandidateEquivDiagonalReturnSumRootedDoubleHook :
    AR.HookDiagonalCandidate σ ≃
      AR.HookM5DiagonalReturn σ ⊕ AR.RootedDoubleHook σ :=
  (hookDiagonalCandidateEquivDiagonalReturnSumDoubleCandidate σ AR).trans <|
    Equiv.sumCongr (Equiv.refl _)
      (hookDoubleCandidateEquivRootedDoubleHook (k := k) σ AR)

include k in
/-- Cardinal form of the diagonal-return/double-hook correction. -/
theorem hookDiagonalCandidate_card_eq_diagonalReturn_add_rootedDoubleHook :
    Fintype.card (AR.HookDiagonalCandidate σ) =
      Fintype.card (AR.HookM5DiagonalReturn σ) +
        Fintype.card (AR.RootedDoubleHook σ) := by
  rw [Fintype.card_congr
    (hookDiagonalCandidateEquivDiagonalReturnSumRootedDoubleHook
      (k := k) σ AR)]
  exact Fintype.card_sum

/-- Canonical-data specialization in the exact packet vocabulary used by
the signed colevel-four identity. -/
theorem hookDiagonalCandidate_card_eq_diagonalReturn_add_doubleHookFour :
    Fintype.card
        ((σ.finiteDimensionalARTranslationData k R).HookDiagonalCandidate
          σ) =
      Fintype.card
          ((σ.finiteDimensionalARTranslationData k R).HookM5DiagonalReturn
            σ) +
        Fintype.card (QuotientDoubleHookFour (k := k) (R := R) σ) :=
  hookDiagonalCandidate_card_eq_diagonalReturn_add_rootedDoubleHook
    (k := k) σ (σ.finiteDimensionalARTranslationData k R)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.FiniteARTranslationData
