import OpConjecture.RepresentationTheory.FourVertexFactorLadderPackets

/-!
# Global coordinates for four-vertex hook occurrences

The strip argument counts a pair consisting of an admissible hook triple
and a fourth vertex.  The existing packet type stores the four-element
support first and the hook inside its deleted-label subtype.  This file
extracts the manuscript's global `(a,u,b;z)` coordinates and records the
exact induced-support conditions.  It is the first reindexing step for the
signed channel count.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {k R : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- An admissible hook triple before a fourth vertex is selected.  The two
negative edge clauses say exactly that the predecessor sets induced on the
three displayed labels are singletons. -/
@[ext]
structure StripAdmissibleTriple where
  a : ι
  u : ι
  b : ι
  a_ne_u : a ≠ u
  a_ne_b : a ≠ b
  u_ne_b : u ≠ b
  u_nonprojective : ¬ Projective (σ.obj u)
  b_nonprojective : ¬ Projective (σ.obj b)
  a_to_u : HasIrreducibleMorphism (σ.obj a) (σ.obj u)
  u_to_b : HasIrreducibleMorphism (σ.obj u) (σ.obj b)
  b_not_to_u : ¬ HasIrreducibleMorphism (σ.obj b) (σ.obj u)
  a_not_to_b : ¬ HasIrreducibleMorphism (σ.obj a) (σ.obj b)
  tau_b : (AR.arTranslation σ ⟨b, b_nonprojective⟩).1 = a

omit [Fintype ι] in
noncomputable instance stripAdmissibleTripleFinite :
    Finite (AR.StripAdmissibleTriple σ) :=
  Finite.of_injective
    (fun H ↦ (H.a, H.u, H.b)) (by
      intro H₁ H₂ h
      ext
      · exact congrArg (fun q ↦ q.1) h
      · exact congrArg (fun q ↦ q.2.1) h
      · exact congrArg (fun q ↦ q.2.2) h)

omit [Fintype ι] in
noncomputable instance stripAdmissibleTripleFintype :
    Fintype (AR.StripAdmissibleTriple σ) := Fintype.ofFinite _

namespace StripAdmissibleTriple

variable {AR : σ.FiniteARTranslationData}
  (H : AR.StripAdmissibleTriple σ)

/-- The three labels displayed by an admissible strip triple. -/
def support : Finset ι := {H.a, H.u, H.b}

omit [Fintype ι] in
@[simp]
theorem mem_support_a : H.a ∈ H.support := by
  simp [support]

omit [Fintype ι] in
@[simp]
theorem mem_support_u : H.u ∈ H.support := by
  simp [support]

omit [Fintype ι] in
@[simp]
theorem mem_support_b : H.b ∈ H.support := by
  simp [support]

omit [Fintype ι] in
@[simp]
theorem support_card : H.support.card = 3 := by
  simp [support, H.a_ne_u, H.a_ne_b, H.u_ne_b]

end StripAdmissibleTriple

/-- A global hook triple together with a fourth label which makes its
four-label support projectively rooted and preserves the two singleton
predecessor conditions. -/
@[ext]
structure HookFourthExtension where
  triple : AR.StripAdmissibleTriple σ
  z : ι
  z_not_mem : z ∉ triple.support
  rooted : OpConjecture.RootedDigraph.IsProjectivelyRooted
    σ.irreducibleEdge σ.projectiveLabelFinset
      (insert z triple.support)
  z_not_to_u :
    ¬ HasIrreducibleMorphism (σ.obj z) (σ.obj triple.u)
  z_not_to_b :
    ¬ HasIrreducibleMorphism (σ.obj z) (σ.obj triple.b)

noncomputable instance hookFourthExtensionFinite :
    Finite (AR.HookFourthExtension σ) :=
  Finite.of_injective
    (fun E ↦ (E.triple, E.z)) (by
      intro E₁ E₂ h
      apply HookFourthExtension.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

noncomputable instance hookFourthExtensionFintype :
    Fintype (AR.HookFourthExtension σ) := Fintype.ofFinite _

namespace HookFourthExtension

variable {AR : σ.FiniteARTranslationData}
  (E : AR.HookFourthExtension σ)

/-- The four-element support associated to a hook extension. -/
def support : Finset ι := insert E.z E.triple.support

include σ in
@[simp]
theorem support_card : E.support.card = 4 := by
  rw [support, Finset.card_insert_of_notMem E.z_not_mem,
    E.triple.support_card]

end HookFourthExtension

/-- The three raw labels of an actual hook occurrence form an admissible
strip triple. -/
def AdmissibleHook.toStripAdmissibleTriple
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : AR.AdmissibleHook σ (((Deleted : Finset ι) : Set ι)ᶜ)) :
    AR.StripAdmissibleTriple σ := by
  let G := AR.fourVertexHookData σ Deleted hroot
  let Q := H.toFourVertexHook σ AR Deleted hroot
  exact
    { a := H.a.1
      u := H.u.1
      b := H.b.1
      a_ne_u := by
        intro h
        exact Q.a_ne_u (Subtype.ext h)
      a_ne_b := by
        intro h
        exact Q.a_ne_b G (Subtype.ext h)
      u_ne_b := by
        intro h
        exact Q.u_ne_b (Subtype.ext h)
      u_nonprojective := H.u_nonprojective
      b_nonprojective := H.b_nonprojective
      a_to_u := H.predecessor_u.1
      u_to_b := H.predecessor_b.1
      b_not_to_u := by
        intro hbu
        have hba := H.predecessor_u.2 H.b hbu
        exact Q.a_ne_b G hba.symm
      a_not_to_b := by
        intro hab
        have hau := H.predecessor_b.2 H.a hab
        exact Q.a_ne_u hau
      tau_b := H.tau_b }

/-- Every actual four-support hook occurrence has a unique omitted fourth
label. -/
def quotientHookOccurrenceFourTriple
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    (σ.finiteDimensionalARTranslationData k R).StripAdmissibleTriple σ :=
  Q.2.toStripAdmissibleTriple σ
    (σ.finiteDimensionalARTranslationData k R) Q.1.1 Q.1.2.2

omit AR in
theorem quotientHookOccurrenceFourTriple_support_subset
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    (quotientHookOccurrenceFourTriple
      (k := k) (R := R) σ Q).support ⊆ Q.1.1 := by
  intro x hx
  let T := quotientHookOccurrenceFourTriple (k := k) (R := R) σ Q
  let H := Q.2
  change x ∈ T.support at hx
  change x ∈ Q.1.1
  simp only [StripAdmissibleTriple.support, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · change H.a.1 ∈ Q.1.1
    simpa using H.a.2
  · change H.u.1 ∈ Q.1.1
    simpa using H.u.2
  · change H.b.1 ∈ Q.1.1
    simpa using H.b.2

omit AR in
theorem quotientHookOccurrenceFourTriple_support_ssubset
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    (quotientHookOccurrenceFourTriple
      (k := k) (R := R) σ Q).support ⊂ Q.1.1 := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨quotientHookOccurrenceFourTriple_support_subset
    (k := k) (R := R) σ Q, ?_⟩
  intro heq
  have hcard := congrArg Finset.card heq
  rw [(quotientHookOccurrenceFourTriple
    (k := k) (R := R) σ Q).support_card, Q.1.2.1] at hcard
  omega

/-- The fourth raw label of an actual hook occurrence. -/
def quotientHookOccurrenceFourFourthVertex
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) : ι :=
  Classical.choose <| Finset.exists_of_ssubset <|
    quotientHookOccurrenceFourTriple_support_ssubset
      (k := k) (R := R) σ Q

omit AR in
theorem quotientHookOccurrenceFourFourthVertex_mem
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    quotientHookOccurrenceFourFourthVertex
      (k := k) (R := R) σ Q ∈ Q.1.1 :=
  (Classical.choose_spec <| Finset.exists_of_ssubset <|
    quotientHookOccurrenceFourTriple_support_ssubset
      (k := k) (R := R) σ Q).1

omit AR in
theorem quotientHookOccurrenceFourFourthVertex_not_mem
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    quotientHookOccurrenceFourFourthVertex
        (k := k) (R := R) σ Q ∉
      (quotientHookOccurrenceFourTriple
        (k := k) (R := R) σ Q).support :=
  (Classical.choose_spec <| Finset.exists_of_ssubset <|
    quotientHookOccurrenceFourTriple_support_ssubset
      (k := k) (R := R) σ Q).2

omit AR in
theorem quotientHookOccurrenceFour_support_eq
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    insert
        (quotientHookOccurrenceFourFourthVertex
          (k := k) (R := R) σ Q)
        (quotientHookOccurrenceFourTriple
          (k := k) (R := R) σ Q).support =
      Q.1.1 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact quotientHookOccurrenceFourFourthVertex_mem
        (k := k) (R := R) σ Q
    · exact quotientHookOccurrenceFourTriple_support_subset
        (k := k) (R := R) σ Q hx
  · rw [Finset.card_insert_of_notMem
        (quotientHookOccurrenceFourFourthVertex_not_mem
          (k := k) (R := R) σ Q),
      (quotientHookOccurrenceFourTriple
        (k := k) (R := R) σ Q).support_card, Q.1.2.1]

/-- Every actual four-support hook occurrence, in global extension
coordinates. -/
def quotientHookOccurrenceFourToExtension
    (Q : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    (σ.finiteDimensionalARTranslationData k R).HookFourthExtension σ := by
  let T := quotientHookOccurrenceFourTriple (k := k) (R := R) σ Q
  let z := quotientHookOccurrenceFourFourthVertex
    (k := k) (R := R) σ Q
  let H := Q.2
  let zd : DeletedLabel (((Q.1.1 : Finset ι) : Set ι)ᶜ) :=
    ⟨z, by
      simpa [z] using quotientHookOccurrenceFourFourthVertex_mem
        (k := k) (R := R) σ Q⟩
  exact
    { triple := T
      z := z
      z_not_mem := quotientHookOccurrenceFourFourthVertex_not_mem
        (k := k) (R := R) σ Q
      rooted := by
        rw [quotientHookOccurrenceFour_support_eq
          (k := k) (R := R) σ Q]
        exact Q.1.2.2
      z_not_to_u := by
        intro hzu
        have hza := H.predecessor_u.2 zd hzu
        apply quotientHookOccurrenceFourFourthVertex_not_mem
          (k := k) (R := R) σ Q
        change z ∈ ({H.a.1, H.u.1, H.b.1} : Finset ι)
        exact Finset.mem_insert.2 <| Or.inl (congrArg Subtype.val hza)
      z_not_to_b := by
        intro hzb
        have hzu := H.predecessor_b.2 zd hzb
        apply quotientHookOccurrenceFourFourthVertex_not_mem
          (k := k) (R := R) σ Q
        change z ∈ ({H.a.1, H.u.1, H.b.1} : Finset ι)
        exact Finset.mem_insert.2 <| Or.inr <|
          Finset.mem_insert.2 <| Or.inl (congrArg Subtype.val hzu) }

/-- Rebuild the actual rooted four-support and its retained hook from
global extension coordinates. -/
def HookFourthExtension.toQuotientHookOccurrenceFour
    (E : (σ.finiteDimensionalARTranslationData k R).HookFourthExtension σ) :
    QuotientHookOccurrenceFour (k := k) (R := R) σ := by
  classical
  let AR := σ.finiteDimensionalARTranslationData k R
  let Deleted : Finset ι := E.support
  let a : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ) :=
    ⟨E.triple.a, by
      simp [Deleted, HookFourthExtension.support,
        StripAdmissibleTriple.support]⟩
  let u : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ) :=
    ⟨E.triple.u, by
      simp [Deleted, HookFourthExtension.support,
        StripAdmissibleTriple.support]⟩
  let b : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ) :=
    ⟨E.triple.b, by
      simp [Deleted, HookFourthExtension.support,
        StripAdmissibleTriple.support]⟩
  let H : AR.AdmissibleHook σ
      (((Deleted : Finset ι) : Set ι)ᶜ) :=
    { a := a
      u := u
      b := b
      u_nonprojective := E.triple.u_nonprojective
      b_nonprojective := E.triple.b_nonprojective
      predecessor_u := by
        constructor
        · exact E.triple.a_to_u
        · intro x hx
          have hxmem : x.1 ∈ Deleted := by simpa using x.2
          change x.1 ∈ insert E.z
            ({E.triple.a, E.triple.u, E.triple.b} : Finset ι) at hxmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
          rcases hxmem with hxz | hxa | hxu | hxb
          · exfalso
            apply E.z_not_to_u
            simpa [hxz] using hx
          · exact Subtype.ext hxa
          · exact (σ.hasNoIrreducibleEndomorphism_obj E.triple.u
              (by simpa [hxu] using hx)).elim
          · exact (E.triple.b_not_to_u (by simpa [hxb] using hx)).elim
      predecessor_b := by
        constructor
        · exact E.triple.u_to_b
        · intro x hx
          have hxmem : x.1 ∈ Deleted := by simpa using x.2
          change x.1 ∈ insert E.z
            ({E.triple.a, E.triple.u, E.triple.b} : Finset ι) at hxmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
          rcases hxmem with hxz | hxa | hxu | hxb
          · exfalso
            apply E.z_not_to_b
            simpa [hxz] using hx
          · exact (E.triple.a_not_to_b (by simpa [hxa] using hx)).elim
          · exact Subtype.ext hxu
          · exact (σ.hasNoIrreducibleEndomorphism_obj E.triple.b
              (by simpa [hxb] using hx)).elim
      tau_b := E.triple.tau_b }
  exact ⟨⟨Deleted, E.support_card, E.rooted⟩, H⟩

omit [DecidableEq ι] in
private theorem quotientHookOccurrenceFour_eq_of_support_eq_of_vals
    (Q₁ Q₂ : QuotientHookOccurrenceFour (k := k) (R := R) σ)
    (hDeleted : Q₁.1.1 = Q₂.1.1)
    (ha : Q₁.2.a.1 = Q₂.2.a.1)
    (hu : Q₁.2.u.1 = Q₂.2.u.1)
    (hb : Q₁.2.b.1 = Q₂.2.b.1) :
    Q₁ = Q₂ := by
  rcases Q₁ with ⟨D₁, H₁⟩
  rcases Q₂ with ⟨D₂, H₂⟩
  have hbase : D₁ = D₂ := Subtype.ext hDeleted
  subst D₂
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  apply AdmissibleHook.ext
  · exact Subtype.ext ha
  · exact Subtype.ext hu
  · exact Subtype.ext hb

/-- Rebuilding an actual hook occurrence from its global coordinates
recovers the original occurrence. -/
theorem quotientHookOccurrenceFour_extension_leftInverse :
    Function.LeftInverse
      (HookFourthExtension.toQuotientHookOccurrenceFour
        (k := k) (R := R) σ)
      (quotientHookOccurrenceFourToExtension
        (k := k) (R := R) σ) := by
  intro Q
  apply quotientHookOccurrenceFour_eq_of_support_eq_of_vals
      (k := k) (R := R) σ
  · exact quotientHookOccurrenceFour_support_eq
      (k := k) (R := R) σ Q
  · rfl
  · rfl
  · rfl

/-- Extracting global coordinates from a rebuilt extension recovers the
extension. -/
theorem quotientHookOccurrenceFour_extension_rightInverse :
    Function.RightInverse
      (HookFourthExtension.toQuotientHookOccurrenceFour
        (k := k) (R := R) σ)
      (quotientHookOccurrenceFourToExtension
        (k := k) (R := R) σ) := by
  intro E
  let Q := E.toQuotientHookOccurrenceFour (k := k) (R := R) σ
  let E' := quotientHookOccurrenceFourToExtension
    (k := k) (R := R) σ Q
  have htriple : E'.triple = E.triple := by
    apply StripAdmissibleTriple.ext
    · rfl
    · rfl
    · rfl
  have hzmem : E'.z ∈ E.support := by
    have h := quotientHookOccurrenceFourFourthVertex_mem
      (k := k) (R := R) σ Q
    exact h
  have hz : E'.z = E.z := by
    rw [HookFourthExtension.support] at hzmem
    rcases Finset.mem_insert.mp hzmem with hz | hzSupport
    · exact hz
    · exfalso
      apply E'.z_not_mem
      rw [htriple]
      exact hzSupport
  apply HookFourthExtension.ext
  · exact htriple
  · exact hz

/-- Actual quotient hook occurrences are exactly global admissible hook
triples equipped with an allowed fourth vertex. -/
def quotientHookOccurrenceFourEquivExtension :
    QuotientHookOccurrenceFour (k := k) (R := R) σ ≃
      (σ.finiteDimensionalARTranslationData k R).HookFourthExtension σ where
  toFun := quotientHookOccurrenceFourToExtension
    (k := k) (R := R) σ
  invFun := HookFourthExtension.toQuotientHookOccurrenceFour
    (k := k) (R := R) σ
  left_inv := quotientHookOccurrenceFour_extension_leftInverse
    (k := k) (R := R) σ
  right_inv := quotientHookOccurrenceFour_extension_rightInverse
    (k := k) (R := R) σ

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
