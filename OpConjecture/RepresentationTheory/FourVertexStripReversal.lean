import OpConjecture.RepresentationTheory.FourVertexArrowOrbitBoundaries

/-!
# Reversal of admissible strip triples

Aligned duality identifies ordinary admissible triples on the dual skeleton
with reverse-admissible triples on the source skeleton.  Combining this
identification with the injective projective-end/injective-end arrow-chain
map in both directions proves equality of the two projective wall-triple
counts used in the signed colevel-four strip.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {K R S : Type u} [Field K]
  [Ring R] [Algebra K R] [FiniteDimensional K R]
  [Ring S] [Algebra K S] [FiniteDimensional K S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- Exchange the two aligned halves of a biduality. -/
def AlignedBiduality.swap (D : AlignedBiduality σ τ) :
    AlignedBiduality τ σ where
  forward := D.backward
  backward := D.forward
  backward_label := by
    rw [D.backward_label]
    exact D.forward.labelEquiv.symm_symm

namespace FiniteARTranslationData

variable (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)
  (D : AlignedBiduality σ τ)

noncomputable instance projectiveStripAdmissibleTripleFintype :
    Fintype {T : ARσ.StripAdmissibleTriple σ //
      Projective (σ.obj T.a)} := Fintype.ofFinite _

noncomputable instance injectiveReverseStripAdmissibleTripleFintype :
    Fintype {T : ARσ.ReverseStripAdmissibleTriple σ //
      Injective (σ.obj T.a)} := Fintype.ofFinite _

noncomputable instance projectiveLabelFintype :
    Fintype {p : ι // Projective (σ.obj p)} := Fintype.ofFinite _

/-- Pull an ordinary admissible triple on the aligned dual skeleton back
to the corresponding reverse triple on the source skeleton. -/
def pullbackStripAdmissibleTriple
    (T : ARτ.StripAdmissibleTriple τ) :
    ARσ.ReverseStripAdmissibleTriple σ where
  a := D.forward.labelEquiv.symm T.a
  u := D.forward.labelEquiv.symm T.u
  b := D.forward.labelEquiv.symm T.b
  a_ne_u := fun h ↦ T.a_ne_u (D.forward.labelEquiv.symm.injective h)
  a_ne_b := fun h ↦ T.a_ne_b (D.forward.labelEquiv.symm.injective h)
  u_ne_b := fun h ↦ T.u_ne_b (D.forward.labelEquiv.symm.injective h)
  u_noninjective := by
    intro huI
    apply T.u_nonprojective
    simpa using (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm T.u)).1 huI
  b_noninjective := by
    intro hbI
    apply T.b_nonprojective
    simpa using (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm T.b)).1 hbI
  u_to_a := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := D.forward.labelEquiv.symm T.u)
      (y := D.forward.labelEquiv.symm T.a)).1 (by
        simpa using T.a_to_u)
  b_to_u := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := D.forward.labelEquiv.symm T.b)
      (y := D.forward.labelEquiv.symm T.u)).1 (by
        simpa using T.u_to_b)
  u_not_to_b := by
    intro hub
    apply T.b_not_to_u
    simpa using (D.hasIrreducibleMorphism_image_iff σ τ
      (x := D.forward.labelEquiv.symm T.u)
      (y := D.forward.labelEquiv.symm T.b)).2 hub
  b_not_to_a := by
    intro hba
    apply T.a_not_to_b
    simpa using (D.hasIrreducibleMorphism_image_iff σ τ
      (x := D.forward.labelEquiv.symm T.b)
      (y := D.forward.labelEquiv.symm T.a)).2 hba
  inverseTau_b := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨T.b, T.b_nonprojective⟩
    simpa [T.tau_b] using h.symm

/-- Push a reverse source triple to the corresponding ordinary admissible
triple on the aligned dual skeleton. -/
def pushforwardReverseStripAdmissibleTriple
    (T : ARσ.ReverseStripAdmissibleTriple σ) :
    ARτ.StripAdmissibleTriple τ where
  a := D.forward.labelEquiv T.a
  u := D.forward.labelEquiv T.u
  b := D.forward.labelEquiv T.b
  a_ne_u := fun h ↦ T.a_ne_u (D.forward.labelEquiv.injective h)
  a_ne_b := fun h ↦ T.a_ne_b (D.forward.labelEquiv.injective h)
  u_ne_b := fun h ↦ T.u_ne_b (D.forward.labelEquiv.injective h)
  u_nonprojective := by
    intro huP
    apply T.u_noninjective
    exact (D.forward.injective_iff_projective_image σ τ T.u).2 huP
  b_nonprojective := by
    intro hbP
    apply T.b_noninjective
    exact (D.forward.injective_iff_projective_image σ τ T.b).2 hbP
  a_to_u := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := T.u) (y := T.a)).2 T.u_to_a
  u_to_b := by
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := T.b) (y := T.u)).2 T.b_to_u
  b_not_to_u := by
    intro hbu
    apply T.u_not_to_b
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := T.u) (y := T.b)).1 hbu
  a_not_to_b := by
    intro hab
    apply T.b_not_to_a
    exact (D.hasIrreducibleMorphism_image_iff σ τ
      (x := T.b) (y := T.a)).1 hab
  tau_b := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨D.forward.labelEquiv T.b, by
        intro hbP
        exact T.b_noninjective
          ((D.forward.injective_iff_projective_image σ τ T.b).2 hbP)⟩
    simpa [T.inverseTau_b] using h

/-- Ordinary dual triples and source-coordinate reverse triples contain
exactly the same data. -/
def stripAdmissibleTripleEquivReverse :
    ARτ.StripAdmissibleTriple τ ≃
      ARσ.ReverseStripAdmissibleTriple σ where
  toFun := pullbackStripAdmissibleTriple σ τ ARσ ARτ D
  invFun := pushforwardReverseStripAdmissibleTriple σ τ ARσ ARτ D
  left_inv T := by
    ext <;> simp [pullbackStripAdmissibleTriple,
      pushforwardReverseStripAdmissibleTriple]
  right_inv T := by
    ext <;> simp [pullbackStripAdmissibleTriple,
      pushforwardReverseStripAdmissibleTriple]

/-- Projective-based triples on the dual skeleton are the same as
injective-based reverse triples on the source skeleton. -/
def projectiveStripEquivInjectiveReverse :
    {T : ARτ.StripAdmissibleTriple τ // Projective (τ.obj T.a)} ≃
      {T : ARσ.ReverseStripAdmissibleTriple σ //
        Injective (σ.obj T.a)} where
  toFun T := ⟨pullbackStripAdmissibleTriple σ τ ARσ ARτ D T.1, by
    exact (D.forward.injective_iff_projective_image σ τ
      (D.forward.labelEquiv.symm T.1.a)).2 (by simpa using T.2)⟩
  invFun T :=
    ⟨pushforwardReverseStripAdmissibleTriple σ τ ARσ ARτ D T.1,
      (D.forward.injective_iff_projective_image σ τ T.1.a).1 T.2⟩
  left_inv T := by
    apply Subtype.ext
    ext <;> simp [pullbackStripAdmissibleTriple,
      pushforwardReverseStripAdmissibleTriple]
  right_inv T := by
    apply Subtype.ext
    ext <;> simp [pullbackStripAdmissibleTriple,
      pushforwardReverseStripAdmissibleTriple]

include K D in
/-- The projective wall-triple count is invariant under aligned reversal.
This is the manuscript's equality `q₀(q)=q₀(s)`. -/
theorem projectiveStrip_card_eq :
    Fintype.card
        {T : ARσ.StripAdmissibleTriple σ // Projective (σ.obj T.a)} =
      Fintype.card
        {T : ARτ.StripAdmissibleTriple τ // Projective (τ.obj T.a)} := by
  let D' : AlignedBiduality τ σ := D.swap σ τ
  let Eστ := projectiveStripEquivInjectiveReverse σ τ ARσ ARτ D
  let Eτσ := projectiveStripEquivInjectiveReverse τ σ ARτ ARσ D'
  have hστ : Fintype.card
        {T : ARσ.StripAdmissibleTriple σ // Projective (σ.obj T.a)} ≤
      Fintype.card
        {T : ARτ.StripAdmissibleTriple τ // Projective (τ.obj T.a)} := by
    rw [Fintype.card_congr Eστ]
    exact Fintype.card_le_of_injective _
      (FiniteARTranslationData.StripAdmissibleTriple.projectiveChainEndReverseTriple_injective
        (K := K) σ ARσ τ D ARτ)
  have hτσ : Fintype.card
        {T : ARτ.StripAdmissibleTriple τ // Projective (τ.obj T.a)} ≤
      Fintype.card
        {T : ARσ.StripAdmissibleTriple σ // Projective (σ.obj T.a)} := by
    rw [Fintype.card_congr Eτσ]
    exact Fintype.card_le_of_injective _
      (FiniteARTranslationData.StripAdmissibleTriple.projectiveChainEndReverseTriple_injective
        (K := K) τ ARτ σ D' ARσ)
  omega

/-- Aligned duality sends source projectives to target injectives. -/
def dualProjectiveEquivInjective :
    {p : ι // Projective (σ.obj p)} ≃
      {i : κ // Injective (τ.obj i)} where
  toFun p := ⟨D.forward.labelEquiv p.1,
    (D.forward.projective_iff_injective_image σ τ p.1).1 p.2⟩
  invFun i := ⟨D.forward.labelEquiv.symm i.1,
    (D.forward.projective_iff_injective_image σ τ
      (D.forward.labelEquiv.symm i.1)).2 (by simpa using i.2)⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv i := by
    apply Subtype.ext
    simp

/-- Projective boundary labels have the same cardinality on the two aligned
skeletons: duality first reaches target injectives and the AR boundary-chain
equivalence then returns to target projectives. -/
def projectiveLabelEquiv :
    {p : ι // Projective (σ.obj p)} ≃
      {p : κ // Projective (τ.obj p)} :=
  (dualProjectiveEquivInjective σ τ D).trans
    (ARτ.boundaryTranslationChainData τ).boundaryEndpointEquiv.symm

/-- A wall choice is independently a projectively based admissible triple
and a projective fourth label. -/
def hookWallChoiceEquivProduct :
    ARσ.HookWallChoice σ ≃
      ({T : ARσ.StripAdmissibleTriple σ //
          Projective (σ.obj T.a)} ×
        {z : ι // Projective (σ.obj z)}) where
  toFun W := (⟨W.triple, W.a_projective⟩,
    ⟨W.z, W.z_projective⟩)
  invFun X :=
    { triple := X.1.1
      a_projective := X.1.2
      z := X.2.1
      z_projective := X.2.2 }
  left_inv W := by ext <;> rfl
  right_inv X := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

include K D in
/-- The full projective wall term, including its independent fourth
projective label, is invariant under aligned reversal. -/
theorem hookWallChoice_card_eq :
    Fintype.card (ARσ.HookWallChoice σ) =
      Fintype.card (ARτ.HookWallChoice τ) := by
  rw [Fintype.card_congr (hookWallChoiceEquivProduct σ ARσ),
    Fintype.card_congr (hookWallChoiceEquivProduct τ ARτ)]
  simp only [Fintype.card_prod]
  rw [projectiveStrip_card_eq (K := K) σ τ ARσ ARτ D,
    Fintype.card_congr (projectiveLabelEquiv σ τ ARτ D)]

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
