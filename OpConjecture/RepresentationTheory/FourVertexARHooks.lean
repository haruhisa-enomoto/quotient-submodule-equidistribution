import OpConjecture.Combinatorics.FourVertexHooks
import OpConjecture.RepresentationTheory.FactorLadderARHook
import OpConjecture.RepresentationTheory.FactorLadderRooted

/-!
# Four-vertex hook overlap for actual AR supports

This file transports the pure hook-overlap theorem to a retained set of
vertices in the Auslander--Reiten quiver.  It proves the manuscript bound
`|H(D)| ≤ 2` and the consecutive-double-hook shape for every projectively
rooted support of cardinality at most four.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- Ordinary AR translation restricted only by the selected vertex set.
Unlike the factor-ladder operator, this definition does not inspect whether
the retained middle term is zero. -/
def retainedARTranslationTarget (K : Set ι)
    (x : DeletedLabel K) : Option (DeletedLabel K) := by
  classical
  by_cases hx : Projective (σ.obj x.1)
  · exact none
  · let tx : ι := (AR.arTranslation σ ⟨x.1, hx⟩).1
    by_cases htx : tx ∈ K
    · exact none
    · exact some ⟨tx, htx⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Restricted ordinary AR translation is injective wherever it is
defined. -/
theorem retainedARTranslationTarget_some_injective
    (K : Set ι) {x₁ x₂ y : DeletedLabel K}
    (h₁ : AR.retainedARTranslationTarget σ K x₁ = some y)
    (h₂ : AR.retainedARTranslationTarget σ K x₂ = some y) :
    x₁ = x₂ := by
  classical
  by_cases hp₁ : Projective (σ.obj x₁.1)
  · simp [retainedARTranslationTarget, hp₁] at h₁
  · by_cases hm₁ : (AR.arTranslation σ ⟨x₁.1, hp₁⟩).1 ∈ K
    · simp [retainedARTranslationTarget, hp₁, hm₁] at h₁
    · by_cases hp₂ : Projective (σ.obj x₂.1)
      · simp [retainedARTranslationTarget, hp₂] at h₂
      · by_cases hm₂ :
          (AR.arTranslation σ ⟨x₂.1, hp₂⟩).1 ∈ K
        · simp [retainedARTranslationTarget, hp₂, hm₂] at h₂
        · have hv₁ :
              (AR.arTranslation σ ⟨x₁.1, hp₁⟩).1 = y.1 := by
            have hs := h₁
            simp [retainedARTranslationTarget, hp₁, hm₁] at hs
            exact congrArg Subtype.val hs
          have hv₂ :
              (AR.arTranslation σ ⟨x₂.1, hp₂⟩).1 = y.1 := by
            have hs := h₂
            simp [retainedARTranslationTarget, hp₂, hm₂] at hs
            exact congrArg Subtype.val hs
          have hnp : (⟨x₁.1, hp₁⟩ : σ.NonprojectiveLabel) =
              ⟨x₂.1, hp₂⟩ := by
            apply AR.arTranslation_injective σ
            apply Subtype.ext
            exact hv₁.trans hv₂.symm
          apply Subtype.ext
          exact congrArg (fun q : σ.NonprojectiveLabel ↦ q.1) hnp

/-- Labels retained after deleting the complement of a finset are exactly
the elements of that finset. -/
def deletedLabelComplEquiv (Deleted : Finset ι) :
    DeletedLabel ((Deleted : Set ι)ᶜ) ≃ {x // x ∈ Deleted} where
  toFun x := ⟨x.1, by simpa using x.2⟩
  invFun x := ⟨x.1, by simp at x ⊢⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- Cardinality of the literal retained-label type. -/
theorem natCard_deletedLabel_compl (Deleted : Finset ι) :
    Nat.card (DeletedLabel ((Deleted : Set ι)ᶜ)) = Deleted.card := by
  classical
  letI : Fintype (DeletedLabel ((Deleted : Set ι)ᶜ)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (deletedLabelComplEquiv Deleted)).trans
    (Fintype.card_coe Deleted)

/-- The actual retained AR support, packaged as the pure rooted
translation-quiver data used by the four-hook theorem. -/
def fourVertexHookData (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted) :
    OpConjecture.FourVertexHooks.Data
      (DeletedLabel ((Deleted : Set ι)ᶜ)) where
  edge x y := HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1)
  boundary := deletedProjectiveSet σ ((Deleted : Set ι)ᶜ)
  tau := AR.retainedARTranslationTarget σ ((Deleted : Set ι)ᶜ)
  edge_irrefl := by
    intro x hloop
    exact (σ.hasNoIrreducibleEndomorphism_obj x.1) hloop
  tau_injective := by
    intro x y a hx hy
    exact AR.retainedARTranslationTarget_some_injective
      σ ((Deleted : Set ι)ᶜ) hx hy
  rooted := by
    intro x
    have hxDeleted : x.1 ∈ Deleted := by simpa using x.2
    obtain ⟨p, hpProjective, hpDeleted, hpx⟩ :=
      hroot x.1 hxDeleted
    let pd : DeletedLabel ((Deleted : Set ι)ᶜ) :=
      ⟨p, by simpa using hpDeleted⟩
    refine ⟨pd, ?_, ?_⟩
    · simpa [pd, deletedProjectiveSet] using hpProjective
    · have liftPath : ∀ {a b : ι} (ha : a ∈ Deleted) (hb : b ∈ Deleted),
          Relation.ReflTransGen
              (OpConjecture.RootedDigraph.InsideEdge
                σ.irreducibleEdge Deleted) a b →
            Relation.ReflTransGen
              (fun q r : DeletedLabel ((Deleted : Set ι)ᶜ) ↦
                HasIrreducibleMorphism (σ.obj q.1) (σ.obj r.1))
              ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩ := by
        intro a b ha hb hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | @tail b c hab hbc ih =>
            have hbDeleted : b ∈ Deleted := hbc.1
            have hcDeleted : c ∈ Deleted := hbc.2.1
            have ih' : Relation.ReflTransGen
                (fun q r : DeletedLabel ((Deleted : Set ι)ᶜ) ↦
                  HasIrreducibleMorphism (σ.obj q.1) (σ.obj r.1))
                ⟨a, by simpa using ha⟩ ⟨b, by simpa using hbDeleted⟩ := by
              simpa using ih hbDeleted
            have hedge :
                HasIrreducibleMorphism
                  (σ.obj (⟨b, by simpa using hbDeleted⟩ :
                    DeletedLabel ((Deleted : Set ι)ᶜ)).1)
                  (σ.obj (⟨c, by simpa using hcDeleted⟩ :
                    DeletedLabel ((Deleted : Set ι)ᶜ)).1) := by
              simpa [irreducibleEdge] using hbc.2.2
            have htail := Relation.ReflTransGen.tail ih' hedge
            simpa using htail
      simpa [pd] using liftPath hpDeleted hxDeleted hpx

/-- Every actual admissible AR hook gives a hook in the pure finite
translation-quiver package. -/
def AdmissibleHook.toFourVertexHook
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (H : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) :
    (AR.fourVertexHookData σ Deleted hroot).Hook where
  a := H.a
  u := H.u
  b := H.b
  edge_a_u := by
    simpa [fourVertexHookData] using H.predecessor_u.1
  edge_u_b := by
    simpa [fourVertexHookData] using H.predecessor_b.1
  u_not_boundary := by
    simpa [fourVertexHookData, deletedProjectiveSet] using H.u_nonprojective
  b_not_boundary := by
    simpa [fourVertexHookData, deletedProjectiveSet] using H.b_nonprojective
  predecessor_u := by
    intro x
    change HasIrreducibleMorphism (σ.obj x.1) (σ.obj H.u.1) ↔ x = H.a
    constructor
    · exact H.predecessor_u.2 x
    · intro hx
      subst x
      exact H.predecessor_u.1
  predecessor_b := by
    intro x
    change HasIrreducibleMorphism (σ.obj x.1) (σ.obj H.b.1) ↔ x = H.u
    constructor
    · exact H.predecessor_b.2 x
    · intro hx
      subst x
      exact H.predecessor_b.1
  tau_b := by
    change AR.retainedARTranslationTarget σ ((Deleted : Set ι)ᶜ) H.b =
      some H.a
    simp [retainedARTranslationTarget, H.b_nonprojective,
      H.tau_b, H.a.2]

/-- The transport from actual AR hooks to the pure hook package is
injective. -/
theorem AdmissibleHook.toFourVertexHook_injective
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted) :
    Function.Injective
      (AdmissibleHook.toFourVertexHook σ AR Deleted hroot) := by
  intro H₁ H₂ h
  have ha := congrArg
    (fun Q : (AR.fourVertexHookData σ Deleted hroot).Hook ↦ Q.a) h
  have hu := congrArg
    (fun Q : (AR.fourVertexHookData σ Deleted hroot).Hook ↦ Q.u) h
  have hb := congrArg
    (fun Q : (AR.fourVertexHookData σ Deleted hroot).Hook ↦ Q.b) h
  ext
  · exact congrArg Subtype.val (by
      simpa [AdmissibleHook.toFourVertexHook] using ha)
  · exact congrArg Subtype.val (by
      simpa [AdmissibleHook.toFourVertexHook] using hu)
  · exact congrArg Subtype.val (by
      simpa [AdmissibleHook.toFourVertexHook] using hb)

/-- The actual manuscript hook family has at most two elements on every
projectively rooted support of at most four vertices. -/
theorem admissibleHook_natCard_le_two
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hcard : Deleted.card ≤ 4) :
    Nat.card (AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) ≤ 2 := by
  let G := AR.fourVertexHookData σ Deleted hroot
  calc
    Nat.card (AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)) ≤
        Nat.card G.Hook :=
      Nat.card_le_card_of_injective
        (AdmissibleHook.toFourVertexHook σ AR Deleted hroot)
        (AdmissibleHook.toFourVertexHook_injective σ AR Deleted hroot)
    _ ≤ 2 := G.hook_card_le_two (by
      rw [natCard_deletedLabel_compl Deleted]
      exact hcard)

/-- Two distinct actual hooks overlap in one of the two consecutive
orientations. -/
theorem AdmissibleHook.overlap_of_ne
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hcard : Deleted.card ≤ 4)
    {H₁ H₂ : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)}
    (hne : H₁ ≠ H₂) : H₁.b = H₂.u ∨ H₂.b = H₁.u := by
  let G := AR.fourVertexHookData σ Deleted hroot
  let Q₁ := H₁.toFourVertexHook σ AR Deleted hroot
  let Q₂ := H₂.toFourVertexHook σ AR Deleted hroot
  have hQ : Q₁ ≠ Q₂ := by
    intro h
    exact hne (AdmissibleHook.toFourVertexHook_injective
      σ AR Deleted hroot h)
  have hover := OpConjecture.FourVertexHooks.Data.Hook.overlap_of_ne
    (G := G) (by
      rw [natCard_deletedLabel_compl Deleted]
      exact hcard) hQ
  simpa [Q₁, Q₂, AdmissibleHook.toFourVertexHook] using hover

omit [Fintype ι] [DecidableEq ι] in
/-- In the chosen orientation, singleton predecessor sets force the second
hook source to be the first hook middle vertex. -/
theorem AdmissibleHook.source_eq_of_consecutive
    {K : Set ι} {H₁ H₂ : AR.AdmissibleHook σ K}
    (h : H₁.b = H₂.u) : H₂.a = H₁.u := by
  have hedge :
      HasIrreducibleMorphism (σ.obj H₁.u.1) (σ.obj H₂.u.1) := by
    simpa [h] using H₁.predecessor_b.1
  exact (H₂.predecessor_u.2 H₁.u hedge).symm

/-- In a consecutive pair of actual hooks on a projectively rooted
four-vertex support, the source of the first hook is projective. -/
theorem AdmissibleHook.first_projective_of_consecutive
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hcard : Deleted.card ≤ 4)
    {H₁ H₂ : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)}
    (h : H₁.b = H₂.u) :
    Projective (σ.obj H₁.a.1) := by
  let G := AR.fourVertexHookData σ Deleted hroot
  let Q₁ := H₁.toFourVertexHook σ AR Deleted hroot
  let Q₂ := H₂.toFourVertexHook σ AR Deleted hroot
  have hQ : Q₁.b = Q₂.u := by
    simpa [Q₁, Q₂, AdmissibleHook.toFourVertexHook] using h
  have hboundary :=
    OpConjecture.FourVertexHooks.Data.Hook.first_mem_boundary_of_consecutive
      (G := G) (by
        rw [natCard_deletedLabel_compl Deleted]
        exact hcard) hQ
  simpa [G, Q₁, fourVertexHookData, deletedProjectiveSet,
    AdmissibleHook.toFourVertexHook] using hboundary

/-- Any two distinct hooks on a projectively rooted support of at most
four vertices form the manuscript's double-hook configuration, in one of
the two possible orientations.  In the first alternative the vertices are
`H₁.a → H₁.u → H₁.b → H₂.b`, with `H₂.a = H₁.u`;
the second alternative reverses the roles of the hooks. -/
theorem AdmissibleHook.doubleHook_shape_of_ne
    (Deleted : Finset ι)
    (hroot : OpConjecture.RootedDigraph.IsProjectivelyRooted
      σ.irreducibleEdge σ.projectiveLabelFinset Deleted)
    (hcard : Deleted.card ≤ 4)
    {H₁ H₂ : AR.AdmissibleHook σ ((Deleted : Set ι)ᶜ)}
    (hne : H₁ ≠ H₂) :
    (H₁.b = H₂.u ∧ Projective (σ.obj H₁.a.1) ∧ H₂.a = H₁.u) ∨
      (H₂.b = H₁.u ∧ Projective (σ.obj H₂.a.1) ∧ H₁.a = H₂.u) := by
  rcases H₁.overlap_of_ne σ AR Deleted hroot hcard hne with h₁₂ | h₂₁
  · exact Or.inl ⟨h₁₂,
      H₁.first_projective_of_consecutive σ AR Deleted hroot hcard h₁₂,
      H₁.source_eq_of_consecutive σ AR h₁₂⟩
  · exact Or.inr ⟨h₂₁,
      H₂.first_projective_of_consecutive σ AR Deleted hroot hcard h₂₁,
      H₂.source_eq_of_consecutive σ AR h₂₁⟩

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
