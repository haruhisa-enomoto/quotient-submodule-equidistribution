import QuotientSubmoduleEquidistribution.Combinatorics.FourVertexLadderPackets
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderCofiniteEndpoint
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderEventualVanishing
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderARHooklessPackets
import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexARHooks
import QuotientSubmoduleEquidistribution.RepresentationTheory.NormalizedFourVertexLadderRealization

/-!
# Four-vertex packet interface for actual factor ladders

This file specializes the pure packet assembly to the two finite families
which occur at colevel four: projectively rooted deleted sets with a bad
forward factor ladder, and injectively corooted deleted sets with a bad
reverse factor ladder.  It constructs the quotient-side packet
decomposition; the reverse-side decomposition and the two reversal counts
remain the final translation-quiver argument.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- The actual quotient-side bad rooted family with four deleted labels. -/
def quotientBadRootedFourFamily : Finset (Finset ι) :=
  QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
    (QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset)
    (QuotientFactorLadderBad (k := k) (R := R) σ) 4

/-- The actual reverse/submodule-side bad corooted family with four deleted
labels. -/
def submoduleBadRootedFourFamily
    (D : AlignedBiduality σ τ) : Finset (Finset ι) :=
  QuotientSubmoduleEquidistribution.SetClosure.badRootedDeletions
    (QuotientSubmoduleEquidistribution.RootedDigraph.IsInjectivelyCorooted
      σ.irreducibleEdge σ.injectiveLabelFinset)
    (SubmoduleFactorLadderBad (k := k) (S := S) σ τ D) 4

/-- A quotient-side four-vertex support counted by the bad rooted family. -/
abbrev QuotientBadRootedFour : Type v :=
  {Deleted // Deleted ∈ quotientBadRootedFourFamily
    (k := k) (R := R) σ}

/-- A reverse-side four-vertex support counted by the bad corooted family. -/
abbrev SubmoduleBadRootedFour (D : AlignedBiduality σ τ) : Type v :=
  {Deleted // Deleted ∈ submoduleBadRootedFourFamily
    (k := k) (S := S) σ τ D}

/-- All quotient-side projectively rooted four-vertex supports, before
imposing the bad-ladder condition. -/
abbrev QuotientRootedFour : Type v :=
  {Deleted : Finset ι //
    Deleted.card = 4 ∧
      QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
        σ.irreducibleEdge σ.projectiveLabelFinset Deleted}

/-- Hook occurrences on rooted four-vertex supports.  The support is kept
in the sigma type because `W₄` counts occurrences, not only supports. -/
abbrev QuotientHookOccurrenceFour : Type v :=
  Σ D : QuotientRootedFour σ,
    (σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      (((D.1 : Finset ι) : Set ι)ᶜ)

/-- Rooted four-vertex supports with at least two hook occurrences. -/
abbrev QuotientDoubleHookFour : Type v :=
  {D : QuotientRootedFour σ //
    Nontrivial
      ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
        (((D.1 : Finset ι) : Set ι)ᶜ))}

/-- Hookless rooted supports carrying row `F`.  This is a type of supports,
so proof multiplicity does not affect its cardinality. -/
abbrev QuotientFixedPacketFour : Type v :=
  {D : QuotientRootedFour σ //
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).FixedPacket σ
          (((D.1 : Finset ι) : Set ι)ᶜ)) ∧
      IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
          (((D.1 : Finset ι) : Set ι)ᶜ))}

/-- Hookless rooted supports carrying row `T`. -/
abbrev QuotientTrianglePacketFour : Type v :=
  {D : QuotientRootedFour σ //
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
          (((D.1 : Finset ι) : Set ι)ᶜ)) ∧
      IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
          (((D.1 : Finset ι) : Set ι)ᶜ))}

noncomputable instance quotientRootedFourFintype :
    Fintype (QuotientRootedFour σ) := Fintype.ofFinite _

noncomputable instance quotientHookOccurrenceFourFintype :
    Fintype (QuotientHookOccurrenceFour (k := k) (R := R) σ) :=
  Fintype.ofFinite _

noncomputable instance quotientDoubleHookFourFintype :
    Fintype (QuotientDoubleHookFour (k := k) (R := R) σ) :=
  Fintype.ofFinite _

noncomputable instance quotientFixedPacketFourFintype :
    Fintype (QuotientFixedPacketFour (k := k) (R := R) σ) :=
  Fintype.ofFinite _

noncomputable instance quotientTrianglePacketFourFintype :
    Fintype (QuotientTrianglePacketFour (k := k) (R := R) σ) :=
  Fintype.ofFinite _

/-- The four labelled vertices of a fixed packet exhaust a four-element
deleted support. -/
theorem fixedPacket_labels_eq_univ
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    ({F.p, F.a, F.c, F.z} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) = Finset.univ := by
  classical
  have hpa : F.p ≠ F.a := by
    intro h
    exact F.a_nonprojective (h ▸ F.p_projective)
  have hpc : F.p ≠ F.c := by
    intro h
    exact F.c_nonprojective (h ▸ F.p_projective)
  have hpz : F.p ≠ F.z := by
    intro h
    exact F.z_nonprojective (h ▸ F.p_projective)
  have hac : F.a ≠ F.c := by
    intro h
    exact σ.hasNoIrreducibleEndomorphism_obj F.c.1 (by
      simpa [h] using F.c_to_a)
  have haz : F.a ≠ F.z := F.predecessor_c.1
  have hcz : F.c ≠ F.z := by
    intro h
    exact σ.hasNoIrreducibleEndomorphism_obj F.z.1 (by
      simpa [h] using F.predecessor_z.1)
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteARTranslationData.natCard_deletedLabel_compl Deleted,
    hcard]
  simp [hpa, hpc, hpz, hac, haz, hcz]

/-- The four labelled vertices of a triangle packet exhaust a four-element
deleted support. -/
theorem trianglePacket_labels_eq_univ
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    ({T.p, T.A₁, T.A₂, T.x} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) = Finset.univ := by
  classical
  have hpA₁ : T.p ≠ T.A₁ := by
    intro h
    exact T.A₁_nonprojective (h ▸ T.p_projective)
  have hpA₂ : T.p ≠ T.A₂ := by
    intro h
    exact T.A₂_nonprojective (h ▸ T.p_projective)
  have hpx : T.p ≠ T.x := by
    intro h
    exact T.x_nonprojective (h ▸ T.p_projective)
  have hA₁A₂ : T.A₁ ≠ T.A₂ := by
    intro h
    exact σ.hasNoIrreducibleEndomorphism_obj T.A₁.1 (by
      simpa [h] using T.predecessor_A₁.1)
  have hA₁x : T.A₁ ≠ T.x := by
    intro h
    exact σ.hasNoIrreducibleEndomorphism_obj T.x.1 (by
      simpa [h] using T.predecessor_x.1)
  have hA₂x : T.A₂ ≠ T.x := by
    intro h
    exact σ.hasNoIrreducibleEndomorphism_obj T.A₂.1 (by
      simpa [h] using T.predecessor_A₂.2.2.1)
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    FiniteARTranslationData.natCard_deletedLabel_compl Deleted,
    hcard]
  simp [hpA₁, hpA₂, hpx, hA₁A₂, hA₁x, hA₂x]

/-- Every deleted label in a four-element fixed-packet support is one of
the four displayed packet labels. -/
theorem eq_fixedPacket_label
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ))
    (x : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ)) :
    x = F.p ∨ x = F.a ∨ x = F.c ∨ x = F.z := by
  have hx : x ∈ ({F.p, F.a, F.c, F.z} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) := by
    rw [fixedPacket_labels_eq_univ (k := k) (R := R) σ Deleted hcard F]
    exact Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

/-- Every deleted label in a four-element triangle-packet support is one of
the four displayed packet labels. -/
theorem eq_trianglePacket_label
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ))
    (x : DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ)) :
    x = T.p ∨ x = T.A₁ ∨ x = T.A₂ ∨ x = T.x := by
  have hx : x ∈ ({T.p, T.A₁, T.A₂, T.x} :
      Finset (DeletedLabel (((Deleted : Finset ι) : Set ι)ᶜ))) := by
    rw [trianglePacket_labels_eq_univ (k := k) (R := R) σ Deleted hcard T]
    exact Finset.mem_univ x
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx

/-- A four-element support carries at most one row-`F` packet. -/
theorem fixedPacket_unique
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F₁ F₂ : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    F₁ = F₂ := by
  let AR := σ.finiteDimensionalARTranslationData k R
  have hp : F₁.p = F₂.p := by
    rcases eq_fixedPacket_label (k := k) (R := R) σ Deleted hcard F₁ F₂.p with
      h | h | h | h
    · exact h.symm
    · exact (F₁.a_nonprojective (h ▸ F₂.p_projective)).elim
    · exact (F₁.c_nonprojective (h ▸ F₂.p_projective)).elim
    · exact (F₁.z_nonprojective (h ▸ F₂.p_projective)).elim
  have F₁a_not_fixed :
      (AR.arTranslation σ ⟨F₁.a.1, F₁.a_nonprojective⟩).1 ≠ F₁.a.1 := by
    intro hfixed
    rcases F₁.tau_a_eq_z_or_mem with haz | haKept
    · exact F₁.predecessor_c.1 (Subtype.ext (hfixed.symm.trans haz))
    · exact F₁.a.2 (hfixed ▸ haKept)
  have F₁z_not_fixed :
      (AR.arTranslation σ ⟨F₁.z.1, F₁.z_nonprojective⟩).1 ≠ F₁.z.1 := by
    intro hfixed
    exact F₁.predecessor_c.1 (Subtype.ext (F₁.tau_z.symm.trans hfixed))
  have hc : F₁.c = F₂.c := by
    rcases eq_fixedPacket_label (k := k) (R := R) σ Deleted hcard F₁ F₂.c with
      h | h | h | h
    · exact (F₂.c_nonprojective (h ▸ F₁.p_projective)).elim
    · exfalso
      apply F₁a_not_fixed
      simpa [h] using F₂.tau_c
    · exact h.symm
    · exfalso
      apply F₁z_not_fixed
      simpa [h] using F₂.tau_c
  have ha : F₁.a = F₂.a := by
    rcases eq_fixedPacket_label (k := k) (R := R) σ Deleted hcard F₁ F₂.a with
      h | h | h | h
    · exact (F₂.a_nonprojective (h ▸ F₁.p_projective)).elim
    · exact h.symm
    · have hirr : HasIrreducibleMorphism
          (σ.obj F₂.c.1) (σ.obj F₂.c.1) := by
        simpa [h, hc] using F₂.c_to_a
      exact (σ.hasNoIrreducibleEndomorphism_obj F₂.c.1 hirr).elim
    · exfalso
      apply F₁.p_not_to_z
      simpa [hp, h] using F₂.p_to_a
  have hz : F₁.z = F₂.z := by
    have hzInputs :
        (⟨F₁.z.1, F₁.z_nonprojective⟩ : σ.NonprojectiveLabel) =
          ⟨F₂.z.1, F₂.z_nonprojective⟩ := by
      apply AR.arTranslation_injective σ
      apply Subtype.ext
      exact F₁.tau_z.trans ((congrArg Subtype.val ha).trans F₂.tau_z.symm)
    exact Subtype.ext
      (congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) hzInputs)
  ext
  · exact congrArg Subtype.val hp
  · exact congrArg Subtype.val ha
  · exact congrArg Subtype.val hc
  · exact congrArg Subtype.val hz

/-- A four-element support carries at most one row-`T` packet. -/
theorem trianglePacket_unique
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (T₁ T₂ : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    T₁ = T₂ := by
  let AR := σ.finiteDimensionalARTranslationData k R
  have hp : T₁.p = T₂.p := by
    rcases eq_trianglePacket_label (k := k) (R := R) σ Deleted hcard T₁ T₂.p with
      h | h | h | h
    · exact h.symm
    · exact (T₁.A₁_nonprojective (h ▸ T₂.p_projective)).elim
    · exact (T₁.A₂_nonprojective (h ▸ T₂.p_projective)).elim
    · exact (T₁.x_nonprojective (h ▸ T₂.p_projective)).elim
  have hA₁ : T₁.A₁ = T₂.A₁ := by
    have hinputs :
        (⟨T₁.A₁.1, T₁.A₁_nonprojective⟩ : σ.NonprojectiveLabel) =
          ⟨T₂.A₁.1, T₂.A₁_nonprojective⟩ := by
      apply AR.arTranslation_injective σ
      apply Subtype.ext
      exact T₁.tau_A₁.trans ((congrArg Subtype.val hp).trans T₂.tau_A₁.symm)
    exact Subtype.ext
      (congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) hinputs)
  have hA₂ : T₁.A₂ = T₂.A₂ := by
    have hinputs :
        (⟨T₁.A₂.1, T₁.A₂_nonprojective⟩ : σ.NonprojectiveLabel) =
          ⟨T₂.A₂.1, T₂.A₂_nonprojective⟩ := by
      apply AR.arTranslation_injective σ
      apply Subtype.ext
      exact T₁.tau_A₂.trans
        ((congrArg Subtype.val hA₁).trans T₂.tau_A₂.symm)
    exact Subtype.ext
      (congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) hinputs)
  have hx : T₁.x = T₂.x := by
    have hxPred : HasIrreducibleMorphism
        (σ.obj T₂.x.1) (σ.obj T₁.A₂.1) := by
      simpa [hA₂] using T₂.predecessor_A₂.2.2.1
    rcases T₁.predecessor_A₂.2.2.2 T₂.x hxPred with h | h
    · exact (T₂.x_nonprojective (h ▸ T₁.p_projective)).elim
    · exact h.symm
  ext
  · exact congrArg Subtype.val hp
  · exact congrArg Subtype.val hA₁
  · exact congrArg Subtype.val hA₂
  · exact congrArg Subtype.val hx

/-- Rows `F` and `T` are disjoint on a four-element support.  The fixed
packet has a translation-fixed nonprojective label, whereas none of the
four triangle-packet labels can be such a vertex. -/
theorem fixedPacket_trianglePacket_disjoint
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ))
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    False := by
  let AR := σ.finiteDimensionalARTranslationData k R
  have hA₁_not_fixed :
      (AR.arTranslation σ ⟨T.A₁.1, T.A₁_nonprojective⟩).1 ≠ T.A₁.1 := by
    intro hfixed
    have hpA₁ : T.p = T.A₁ :=
      Subtype.ext (T.tau_A₁.symm.trans hfixed)
    exact T.A₁_nonprojective (hpA₁ ▸ T.p_projective)
  have hA₂_not_fixed :
      (AR.arTranslation σ ⟨T.A₂.1, T.A₂_nonprojective⟩).1 ≠ T.A₂.1 := by
    intro hfixed
    have hA₁A₂ : T.A₁ = T.A₂ :=
      Subtype.ext (T.tau_A₂.symm.trans hfixed)
    exact σ.hasNoIrreducibleEndomorphism_obj T.A₁.1 (by
      simpa [hA₁A₂] using T.predecessor_A₁.1)
  have hx_not_fixed :
      (AR.arTranslation σ ⟨T.x.1, T.x_nonprojective⟩).1 ≠ T.x.1 := by
    intro hfixed
    exact T.x.2 (hfixed ▸ T.tau_x_mem)
  rcases eq_trianglePacket_label (k := k) (R := R) σ Deleted hcard T F.c with
    h | h | h | h
  · exact F.c_nonprojective (h ▸ T.p_projective)
  · apply hA₁_not_fixed
    simpa [h] using F.tau_c
  · apply hA₂_not_fixed
    simpa [h] using F.tau_c
  · apply hx_not_fixed
    simpa [h] using F.tau_c

/-- A four-element support carrying row `T` cannot also carry an
admissible hook.  Thus the hookless field in
`QuotientTrianglePacketFour` is forced by the packet itself. -/
theorem FiniteARTranslationData.TrianglePacket.no_admissibleHook
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((Deleted : Finset ι) : Set ι)ᶜ)) :
    IsEmpty
      ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
        (((Deleted : Finset ι) : Set ι)ᶜ)) := by
  constructor
  intro H
  rcases eq_trianglePacket_label (k := k) (R := R) σ Deleted hcard T H.b with
    hbP | hbA₁ | hbA₂ | hbx
  · exact H.b_nonprojective (hbP ▸ T.p_projective)
  · have hA₂u : T.A₂ = H.u :=
      H.predecessor_b.2 T.A₂ (by
        simpa only [hbA₁] using T.predecessor_A₁.1)
    have hpa : T.p = H.a :=
      H.predecessor_u.2 T.p (by
        simpa only [← hA₂u] using T.predecessor_A₂.2.1)
    have hxa : T.x = H.a :=
      H.predecessor_u.2 T.x (by
        simpa only [← hA₂u] using T.predecessor_A₂.2.2.1)
    exact T.x_nonprojective (hxa.trans hpa.symm ▸ T.p_projective)
  · have hpu : T.p = H.u :=
      H.predecessor_b.2 T.p (by
        simpa only [hbA₂] using T.predecessor_A₂.2.1)
    have hxu : T.x = H.u :=
      H.predecessor_b.2 T.x (by
        simpa only [hbA₂] using T.predecessor_A₂.2.2.1)
    exact T.x_nonprojective (hxu.trans hpu.symm ▸ T.p_projective)
  · have hA₁u : T.A₁ = H.u :=
      H.predecessor_b.2 T.A₁ (by
        simpa only [hbx] using T.predecessor_x.1)
    have hA₂a : T.A₂ = H.a :=
      H.predecessor_u.2 T.A₂ (by
        simpa only [← hA₁u] using T.predecessor_A₁.1)
    have htau :
        ((σ.finiteDimensionalARTranslationData k R).arTranslation σ
          ⟨T.x.1, T.x_nonprojective⟩).1 = T.A₂.1 := by
      simpa only [hbx, hA₂a] using H.tau_b
    apply T.A₂.2
    rw [← htau]
    exact T.tau_x_mem

/-- Bad rooted four-supports retaining the rooted-support certificate in the
ambient subtype. -/
abbrev QuotientBadRootedFourSupport : Type v :=
  {D : QuotientRootedFour σ //
    QuotientFactorLadderBad (k := k) (R := R) σ D.1}

noncomputable instance quotientBadRootedFourSupportFintype :
    Fintype (QuotientBadRootedFourSupport (k := k) (R := R) σ) :=
  Fintype.ofFinite _

/-- The rooted-support and bad-family representations of a bad four-set are
canonically equivalent. -/
def quotientBadRootedFourSupportEquiv :
    QuotientBadRootedFourSupport (k := k) (R := R) σ ≃
      QuotientBadRootedFour (k := k) (R := R) σ where
  toFun D := ⟨D.1.1, by
    rw [quotientBadRootedFourFamily,
      QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
    exact ⟨D.1.2.1, D.1.2.2, D.2⟩⟩
  invFun D := by
    have h :
        D.1.card = 4 ∧
          QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
            σ.irreducibleEdge σ.projectiveLabelFinset D.1 ∧
          QuotientFactorLadderBad (k := k) (R := R) σ D.1 := by
      simpa only [quotientBadRootedFourFamily,
        QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions] using D.2
    exact ⟨⟨D.1, h.1, h.2.1⟩, h.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact remaining supportwise existence statement in the quotient
four-support lemma.  The hookless clauses include their required empty-hook
condition. -/
def QuotientFourSupportClassification : Prop :=
  ∀ D : QuotientRootedFour σ,
    QuotientFactorLadderBad (k := k) (R := R) σ D.1 ↔
      Nonempty
          ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
            (((D.1 : Finset ι) : Set ι)ᶜ)) ∨
        (Nonempty
            ((σ.finiteDimensionalARTranslationData k R).FixedPacket σ
              (((D.1 : Finset ι) : Set ι)ᶜ)) ∧
          IsEmpty
            ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
              (((D.1 : Finset ι) : Set ι)ᶜ))) ∨
        (Nonempty
            ((σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
              (((D.1 : Finset ι) : Set ι)ᶜ)) ∧
          IsEmpty
            ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
              (((D.1 : Finset ι) : Set ι)ᶜ)))

/-- The hookless direction in the quotient-side support classification: a
bad rooted four-support with no admissible hook carries one of the two
hookless AR packets. -/
def QuotientFourHooklessExistence : Prop :=
  ∀ D : QuotientRootedFour σ,
    QuotientFactorLadderBad (k := k) (R := R) σ D.1 →
      IsEmpty
          ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
            (((D.1 : Finset ι) : Set ι)ᶜ)) →
        Nonempty
            ((σ.finiteDimensionalARTranslationData k R).FixedPacket σ
              (((D.1 : Finset ι) : Set ι)ᶜ)) ∨
          Nonempty
            ((σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
              (((D.1 : Finset ι) : Set ι)ᶜ))

/-- The exact quotient-side packet-decomposition target. -/
abbrev QuotientFourPacketDecomposition :=
  QuotientSubmoduleEquidistribution.FourVertexLadderPackets.Decomposition
    (QuotientBadRootedFour (k := k) (R := R) σ)
    (QuotientHookOccurrenceFour (k := k) (R := R) σ)
    (QuotientDoubleHookFour (k := k) (R := R) σ)
    (QuotientFixedPacketFour (k := k) (R := R) σ)
    (QuotientTrianglePacketFour (k := k) (R := R) σ)

/-- Once the supportwise existence classification is proved, all
multiplicity, uniqueness, disjointness, and double-hook bookkeeping
automatically assemble into the manuscript's packet decomposition. -/
noncomputable def quotientFourPacketDecompositionOfClassification
    (C : QuotientFourSupportClassification (k := k) (R := R) σ) :
    QuotientFourPacketDecomposition (k := k) (R := R) σ := by
  let Hook := fun D : QuotientRootedFour σ ↦
    (σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      (((D.1 : Finset ι) : Set ι)ᶜ)
  let Fixed := fun D : QuotientRootedFour σ ↦
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).FixedPacket σ
          (((D.1 : Finset ι) : Set ι)ᶜ)) ∧ IsEmpty (Hook D)
  let Triangle := fun D : QuotientRootedFour σ ↦
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
          (((D.1 : Finset ι) : Set ι)ᶜ)) ∧ IsEmpty (Hook D)
  letI : ∀ D, Fintype (Hook D) := fun _ ↦ Fintype.ofFinite _
  let E := QuotientSubmoduleEquidistribution.FourVertexLadderPackets.decompositionOfFiberClassification
    Hook
    (fun D : QuotientRootedFour σ ↦
      QuotientFactorLadderBad (k := k) (R := R) σ D.1)
    Fixed Triangle
    (fun D ↦ by
      have h := (σ.finiteDimensionalARTranslationData k R).admissibleHook_natCard_le_two
        σ D.1 D.2.2 (by omega)
      simpa only [Nat.card_eq_fintype_card] using h)
    C
    (fun _ h ↦ h.2)
    (fun _ h ↦ h.2)
    (fun D hF hT ↦ by
      exact fixedPacket_trianglePacket_disjoint
        (k := k) (R := R) σ D.1 D.2.1
          (Classical.choice hF.1) (Classical.choice hT.1))
  exact ⟨E.classify.trans
    (Equiv.sumCongr
      (quotientBadRootedFourSupportEquiv (k := k) (R := R) σ)
      (Equiv.refl _))⟩

section AlgebraicallyClosed

variable [IsAlgClosed k]

omit [DecidableEq ι] in
/-- Every admissible hook occurrence, whether or not its cancelling source
is projective, supplies the literal quotient-side bad factor ladder. -/
theorem quotientFactorLadderBad_of_admissibleHook
    (Deleted : Finset ι)
    (H : (σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      ((Deleted : Set ι)ᶜ)) :
    QuotientFactorLadderBad (k := k) (R := R) σ Deleted := by
  refine ⟨H.b, ?_⟩
  simpa [finiteDimensionalFactorLadderData] using
    H.not_reaches_deletedProjective_of_isAlgClosed (k := k) σ

omit [DecidableEq ι] in
/-- Every actual projectively based hook supplies the literal quotient-side
bad factor-ladder witness. -/
theorem quotientFactorLadderBad_of_quotientHook
    (Deleted : Finset ι)
    (H : (σ.finiteDimensionalARTranslationData k R).QuotientHook σ
      ((Deleted : Set ι)ᶜ)) :
    QuotientFactorLadderBad (k := k) (R := R) σ Deleted := by
  exact quotientFactorLadderBad_of_admissibleHook
    (k := k) (R := R) σ Deleted H.toAdmissibleHook

omit [DecidableEq ι] in
/-- Every actual row-`F` packet on a selected support supplies the literal
quotient-side bad factor-ladder witness. -/
theorem quotientFactorLadderBad_of_fixedPacket
    (Deleted : Finset ι)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      ((Deleted : Set ι)ᶜ)) :
    QuotientFactorLadderBad (k := k) (R := R) σ Deleted := by
  refine ⟨F.z, ?_⟩
  simpa [finiteDimensionalFactorLadderData] using
    F.not_reachesBoundary_of_isAlgClosed (k := k) σ

omit [DecidableEq ι] in
/-- Every actual row-`T` packet on a selected support supplies the literal
quotient-side bad factor-ladder witness. -/
theorem quotientFactorLadderBad_of_trianglePacket
    (Deleted : Finset ι)
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      ((Deleted : Set ι)ᶜ)) :
    QuotientFactorLadderBad (k := k) (R := R) σ Deleted := by
  refine ⟨T.x, ?_⟩
  simpa [finiteDimensionalFactorLadderData] using
    T.not_reachesBoundary_of_isAlgClosed (k := k) σ

omit [DecidableEq ι] in
/-- Over an algebraically closed field, the hookless-existence direction
implies the full supportwise classification: the reverse implications are
the already proved packet-to-bad ladder computations. -/
theorem quotientFourSupportClassification_of_hooklessExistence
    (C : QuotientFourHooklessExistence (k := k) (R := R) σ) :
    QuotientFourSupportClassification (k := k) (R := R) σ := by
  intro D
  let Hook :=
    (σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      (((D.1 : Finset ι) : Set ι)ᶜ)
  let Fixed :=
    (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      (((D.1 : Finset ι) : Set ι)ᶜ)
  let Triangle :=
    (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      (((D.1 : Finset ι) : Set ι)ᶜ)
  constructor
  · intro hbad
    by_cases hHook : Nonempty Hook
    · exact Or.inl hHook
    · letI : IsEmpty Hook := not_nonempty_iff.mp hHook
      rcases C D hbad inferInstance with hFixed | hTriangle
      · exact Or.inr (Or.inl ⟨hFixed, inferInstance⟩)
      · exact Or.inr (Or.inr ⟨hTriangle, inferInstance⟩)
  · rintro (hHook | ⟨hFixed, _⟩ | ⟨hTriangle, _⟩)
    · exact quotientFactorLadderBad_of_admissibleHook
        (k := k) (R := R) σ D.1 (Classical.choice hHook)
    · exact quotientFactorLadderBad_of_fixedPacket
        (k := k) (R := R) σ D.1 (Classical.choice hFixed)
    · exact quotientFactorLadderBad_of_trianglePacket
        (k := k) (R := R) σ D.1 (Classical.choice hTriangle)

/-- The normalized four-vertex ladder classification supplies the missing
hookless direction for every actual projectively rooted bad support. -/
theorem quotientFourHooklessExistence :
    QuotientFourHooklessExistence (k := k) (R := R) σ := by
  intro D hbad hEmpty
  letI : IsEmpty
      ((σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
        (((D.1 : Finset ι) : Set ι)ᶜ)) := hEmpty
  rcases
      FiniteARTranslationData.NormalizedFour.hook_or_fixed_or_triangle_of_bad_rooted_four
      (k := k) (R := R) σ D.1 D.2.1 D.2.2 hbad with
    hHook | hFixed | hTriangle
  · exact isEmptyElim (Classical.choice hHook)
  · exact Or.inl hFixed
  · exact Or.inr hTriangle

/-- The actual quotient-side support classification on four deleted
vertices. -/
theorem quotientFourSupportClassification :
    QuotientFourSupportClassification (k := k) (R := R) σ :=
  quotientFourSupportClassification_of_hooklessExistence
    (k := k) (R := R) σ
      (quotientFourHooklessExistence (k := k) (R := R) σ)

omit [DecidableEq ι] in
/-- The exact quotient packet decomposition now depends only on the
hookless-existence theorem. -/
noncomputable def quotientFourPacketDecompositionOfHooklessExistence
    (C : QuotientFourHooklessExistence (k := k) (R := R) σ) :
    QuotientFourPacketDecomposition (k := k) (R := R) σ :=
  quotientFourPacketDecompositionOfClassification
    (k := k) (R := R) σ
      (quotientFourSupportClassification_of_hooklessExistence
        (k := k) (R := R) σ C)

/-- The exact quotient-side packet decomposition on four deleted
vertices. -/
noncomputable def quotientFourPacketDecomposition :
    QuotientFourPacketDecomposition (k := k) (R := R) σ :=
  quotientFourPacketDecompositionOfHooklessExistence
    (k := k) (R := R) σ
      (quotientFourHooklessExistence (k := k) (R := R) σ)

omit [DecidableEq ι] in
/-- A rooted four-set carrying an actual projectively based hook is a
member of the actual bad rooted family. -/
theorem mem_quotientBadRootedFourFamily_of_quotientHook
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : (σ.finiteDimensionalARTranslationData k R).QuotientHook σ
      ((Deleted : Set ι)ᶜ)) :
    Deleted ∈ quotientBadRootedFourFamily (k := k) (R := R) σ := by
  rw [quotientBadRootedFourFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  exact ⟨hcard, hroot,
    quotientFactorLadderBad_of_quotientHook
      (k := k) (R := R) σ Deleted H⟩

omit [DecidableEq ι] in
/-- A rooted four-set carrying any admissible hook occurrence is a member
of the actual bad rooted family. -/
theorem mem_quotientBadRootedFourFamily_of_admissibleHook
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : (σ.finiteDimensionalARTranslationData k R).AdmissibleHook σ
      ((Deleted : Set ι)ᶜ)) :
    Deleted ∈ quotientBadRootedFourFamily (k := k) (R := R) σ := by
  rw [quotientBadRootedFourFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  exact ⟨hcard, hroot,
    quotientFactorLadderBad_of_admissibleHook
      (k := k) (R := R) σ Deleted H⟩

omit [DecidableEq ι] in
/-- A rooted four-set carrying an actual row-`F` packet is a member of the
actual bad rooted family. -/
theorem mem_quotientBadRootedFourFamily_of_fixedPacket
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (F : (σ.finiteDimensionalARTranslationData k R).FixedPacket σ
      ((Deleted : Set ι)ᶜ)) :
    Deleted ∈ quotientBadRootedFourFamily (k := k) (R := R) σ := by
  rw [quotientBadRootedFourFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  exact ⟨hcard, hroot,
    quotientFactorLadderBad_of_fixedPacket
      (k := k) (R := R) σ Deleted F⟩

omit [DecidableEq ι] in
/-- A rooted four-set carrying an actual row-`T` packet is a member of the
actual bad rooted family. -/
theorem mem_quotientBadRootedFourFamily_of_trianglePacket
    (Deleted : Finset ι) (hcard : Deleted.card = 4)
    (hroot : QuotientSubmoduleEquidistribution.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (T : (σ.finiteDimensionalARTranslationData k R).TrianglePacket σ
      ((Deleted : Set ι)ᶜ)) :
    Deleted ∈ quotientBadRootedFourFamily (k := k) (R := R) σ := by
  rw [quotientBadRootedFourFamily,
    QuotientSubmoduleEquidistribution.SetClosure.mem_badRootedDeletions]
  exact ⟨hcard, hroot,
    quotientFactorLadderBad_of_trianglePacket
      (k := k) (R := R) σ Deleted T⟩

/-- Forget a hook occurrence but retain its support as an actual bad rooted
four-set.  This map is deliberately not injective on double hooks. -/
def quotientHookOccurrenceFourToBad
    (H : QuotientHookOccurrenceFour (k := k) (R := R) σ) :
    QuotientBadRootedFour (k := k) (R := R) σ :=
  ⟨H.1.1,
    mem_quotientBadRootedFourFamily_of_admissibleHook
      (k := k) (R := R) σ H.1.1 H.1.2.1 H.1.2.2 H.2⟩

/-- Forget the row-`F` certificate but retain its support as an actual bad
rooted four-set. -/
def quotientFixedPacketFourToBad
    (F : QuotientFixedPacketFour (k := k) (R := R) σ) :
    QuotientBadRootedFour (k := k) (R := R) σ := by
  let packet := Classical.choice F.2.1
  exact ⟨F.1.1,
    mem_quotientBadRootedFourFamily_of_fixedPacket
      (k := k) (R := R) σ F.1.1 F.1.2.1 F.1.2.2 packet⟩

/-- Forget the row-`T` certificate but retain its support as an actual bad
rooted four-set. -/
def quotientTrianglePacketFourToBad
    (T : QuotientTrianglePacketFour (k := k) (R := R) σ) :
    QuotientBadRootedFour (k := k) (R := R) σ := by
  let packet := Classical.choice T.2.1
  exact ⟨T.1.1,
    mem_quotientBadRootedFourFamily_of_trianglePacket
      (k := k) (R := R) σ T.1.1 T.1.2.1 T.1.2.2 packet⟩

end AlgebraicallyClosed

omit [DecidableEq ι] in
/-- Once the four-support packet decompositions and the two reversal counts
have been constructed, the actual bad rooted factor-ladder families have
the same cardinality. -/
theorem badRootedFour_card_eq_of_packetDecompositions
    (D : AlignedBiduality σ τ)
    {QHook QDouble QFixed QTriangle : Type v}
    {SHook SDouble SFixed STriangle : Type w}
    [Fintype QHook] [Fintype QDouble] [Fintype QFixed]
    [Fintype QTriangle] [Fintype SHook] [Fintype SDouble]
    [Fintype SFixed] [Fintype STriangle]
    (QD : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.Decomposition
      (QuotientBadRootedFour (k := k) (R := R) σ)
      QHook QDouble QFixed QTriangle)
    (SD : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.Decomposition
      (SubmoduleBadRootedFour (k := k) (S := S) σ τ D)
      SHook SDouble SFixed STriangle)
    (B : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.ReversalBalance
      QHook QDouble QFixed QTriangle
      SHook SDouble SFixed STriangle) :
    (quotientBadRootedFourFamily (k := k) (R := R) σ).card =
      (submoduleBadRootedFourFamily
        (k := k) (S := S) σ τ D).card := by
  have h :=
    QuotientSubmoduleEquidistribution.FourVertexLadderPackets.killed_card_eq_of_reversalBalance
      QD SD B
  simpa [quotientBadRootedFourFamily,
    submoduleBadRootedFourFamily] using h

/-- The packet proof feeds directly into the colevel-four equality for the
actual quotient and submodule closure geometries. -/
theorem levelCount_card_sub_four_eq_of_packetDecompositions
    (D : AlignedBiduality σ τ) (hfour : 4 ≤ Nat.card ι)
    {QHook QDouble QFixed QTriangle : Type v}
    {SHook SDouble SFixed STriangle : Type w}
    [Fintype QHook] [Fintype QDouble] [Fintype QFixed]
    [Fintype QTriangle] [Fintype SHook] [Fintype SDouble]
    [Fintype SFixed] [Fintype STriangle]
    (QD : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.Decomposition
      (QuotientBadRootedFour (k := k) (R := R) σ)
      QHook QDouble QFixed QTriangle)
    (SD : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.Decomposition
      (SubmoduleBadRootedFour (k := k) (S := S) σ τ D)
      SHook SDouble SFixed STriangle)
    (B : QuotientSubmoduleEquidistribution.FourVertexLadderPackets.ReversalBalance
      QHook QDouble QFixed QTriangle
      SHook SDouble SFixed STriangle) :
    σ.qClosure.levelCount (Nat.card ι - 4) =
      σ.sClosure.levelCount (Nat.card ι - 4) := by
  apply levelCount_card_sub_eq_of_badRootedFactorLadderBalance
    (k := k) (R := R) (S := S) σ τ D 4 hfour
  exact badRootedFour_card_eq_of_packetDecompositions
    (k := k) (R := R) (S := S) σ τ D QD SD B

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
