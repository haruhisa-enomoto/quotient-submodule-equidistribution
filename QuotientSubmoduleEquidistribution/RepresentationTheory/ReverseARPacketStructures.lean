import QuotientSubmoduleEquidistribution.RepresentationTheory.ARDualTranslation
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorLadderARHooklessPackets

/-!
# Reverse AR packet structures in source coordinates

The quotient packet structures on an aligned dual skeleton are most useful
for the reversal count after pulling them back to the original labels.  An
irreducible predecessor then becomes an irreducible successor, and target AR
translation becomes inverse source AR translation.  This file records those
source-coordinate structures and the forward pullback maps.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R S : Type u}
  [Ring R] [IsNoetherianRing R]
  [Ring S] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

/-- `y` is the unique retained irreducible successor of `x`. -/
def HasUniqueDeletedSuccessor (K : Set ι)
    (x y : DeletedLabel K) : Prop :=
  HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1) ∧
    ∀ z : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj z.1) → z = y

/-- `y` and `z` are exactly the two retained irreducible successors of
`x`. -/
def HasExactlyTwoDeletedSuccessors (K : Set ι)
    (x y z : DeletedLabel K) : Prop :=
  y ≠ z ∧
    HasIrreducibleMorphism (σ.obj x.1) (σ.obj y.1) ∧
    HasIrreducibleMorphism (σ.obj x.1) (σ.obj z.1) ∧
    ∀ q : DeletedLabel K,
      HasIrreducibleMorphism (σ.obj x.1) (σ.obj q.1) →
        q = y ∨ q = z

namespace FiniteARTranslationData

variable (AR : σ.FiniteARTranslationData)

/-- The reversal of an admissible hook.  Its two singleton predecessor
conditions become singleton successor conditions, and its translation
identity uses inverse AR translation. -/
@[ext]
structure ReverseAdmissibleHook (K : Set ι) where
  a : DeletedLabel K
  u : DeletedLabel K
  b : DeletedLabel K
  u_noninjective : ¬ Injective (σ.obj u.1)
  b_noninjective : ¬ Injective (σ.obj b.1)
  successor_u : HasUniqueDeletedSuccessor σ K u a
  successor_b : HasUniqueDeletedSuccessor σ K b u
  inverseTau_b :
    ((AR.arTranslationEquiv σ).symm
      ⟨b.1, b_noninjective⟩).1 = a.1

noncomputable instance reverseAdmissibleHookFinite (K : Set ι) :
    Finite (AR.ReverseAdmissibleHook σ K) :=
  Finite.of_injective
    (fun H ↦ (H.a, H.u, H.b)) (by
      intro H₁ H₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2) h))

/-- The reversal of row `F`, written entirely in the source skeleton. -/
@[ext]
structure ReverseFixedPacket (K : Set ι) where
  i : DeletedLabel K
  a : DeletedLabel K
  c : DeletedLabel K
  z : DeletedLabel K
  i_injective : Injective (σ.obj i.1)
  a_noninjective : ¬ Injective (σ.obj a.1)
  c_noninjective : ¬ Injective (σ.obj c.1)
  z_noninjective : ¬ Injective (σ.obj z.1)
  a_to_i : HasIrreducibleMorphism (σ.obj a.1) (σ.obj i.1)
  a_to_c : HasIrreducibleMorphism (σ.obj a.1) (σ.obj c.1)
  successor_z : HasUniqueDeletedSuccessor σ K z c
  successor_c : HasExactlyTwoDeletedSuccessors σ K c a z
  inverseTau_z :
    ((AR.arTranslationEquiv σ).symm
      ⟨z.1, z_noninjective⟩).1 = a.1
  inverseTau_c :
    ((AR.arTranslationEquiv σ).symm
      ⟨c.1, c_noninjective⟩).1 = c.1
  inverseTau_a_eq_z_or_mem :
    ((AR.arTranslationEquiv σ).symm
        ⟨a.1, a_noninjective⟩).1 = z.1 ∨
      ((AR.arTranslationEquiv σ).symm
        ⟨a.1, a_noninjective⟩).1 ∈ K
  z_not_to_i : ¬ HasIrreducibleMorphism (σ.obj z.1) (σ.obj i.1)

noncomputable instance reverseFixedPacketFinite (K : Set ι) :
    Finite (AR.ReverseFixedPacket σ K) :=
  Finite.of_injective
    (fun F ↦ (F.i, F.a, F.c, F.z)) (by
      intro F₁ F₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.2) h))

/-- The reversal of row `T`, written entirely in the source skeleton. -/
@[ext]
structure ReverseTrianglePacket (K : Set ι) where
  i : DeletedLabel K
  A₁ : DeletedLabel K
  A₂ : DeletedLabel K
  x : DeletedLabel K
  i_injective : Injective (σ.obj i.1)
  A₁_noninjective : ¬ Injective (σ.obj A₁.1)
  A₂_noninjective : ¬ Injective (σ.obj A₂.1)
  x_noninjective : ¬ Injective (σ.obj x.1)
  i_to_A₁ : HasIrreducibleMorphism (σ.obj i.1) (σ.obj A₁.1)
  successor_A₁ : HasUniqueDeletedSuccessor σ K A₁ A₂
  successor_A₂ : HasExactlyTwoDeletedSuccessors σ K A₂ i x
  successor_x : HasUniqueDeletedSuccessor σ K x A₁
  inverseTau_A₁ :
    ((AR.arTranslationEquiv σ).symm
      ⟨A₁.1, A₁_noninjective⟩).1 = i.1
  inverseTau_A₂ :
    ((AR.arTranslationEquiv σ).symm
      ⟨A₂.1, A₂_noninjective⟩).1 = A₁.1
  inverseTau_x_mem :
    ((AR.arTranslationEquiv σ).symm
      ⟨x.1, x_noninjective⟩).1 ∈ K

noncomputable instance reverseTrianglePacketFinite (K : Set ι) :
    Finite (AR.ReverseTrianglePacket σ K) :=
  Finite.of_injective
    (fun T ↦ (T.i, T.A₁, T.A₂, T.x)) (by
      intro T₁ T₂ h
      ext
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.1) h)
      · exact congrArg Subtype.val (congrArg (fun q ↦ q.2.2.2) h))

end FiniteARTranslationData

namespace AlignedBiduality

variable (D : AlignedBiduality σ τ)

omit [Fintype ι] [Fintype κ] in
/-- Pulling back a dual irreducible arrow reverses its orientation. -/
theorem deleted_irreducible_pullback_iff
    (K : Set ι)
    (x y : DeletedLabel (D.forward.labelEquiv '' K)) :
    HasIrreducibleMorphism
        (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm y).1)
        (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm x).1) ↔
      HasIrreducibleMorphism (τ.obj x.1) (τ.obj y.1) := by
  simpa [AlignedAntiEquivalence.deletedLabelEquiv] using
    (D.hasIrreducibleMorphism_image_iff σ τ
      (x := ((D.forward.deletedLabelEquiv σ τ K).symm y).1)
      (y := ((D.forward.deletedLabelEquiv σ τ K).symm x).1)).symm

omit [Fintype ι] [Fintype κ] in
/-- A nonprojective dual deleted label pulls back to a noninjective source
deleted label. -/
theorem deleted_pullback_noninjective
    (K : Set ι)
    (x : DeletedLabel (D.forward.labelEquiv '' K))
    (hx : ¬ Projective (τ.obj x.1)) :
    ¬ Injective
      (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm x).1) := by
  intro hinj
  apply hx
  have h := (D.forward.injective_iff_projective_image σ τ
    ((D.forward.deletedLabelEquiv σ τ K).symm x).1).1 hinj
  simpa [AlignedAntiEquivalence.deletedLabelEquiv] using h

omit [Fintype ι] [Fintype κ] in
/-- A projective dual deleted label pulls back to an injective source
deleted label. -/
theorem deleted_pullback_injective
    (K : Set ι)
    (x : DeletedLabel (D.forward.labelEquiv '' K))
    (hx : Projective (τ.obj x.1)) :
    Injective
      (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm x).1) := by
  apply (D.forward.injective_iff_projective_image σ τ
    ((D.forward.deletedLabelEquiv σ τ K).symm x).1).2
  simpa [AlignedAntiEquivalence.deletedLabelEquiv] using hx

omit [Fintype ι] [Fintype κ] in
/-- A noninjective source deleted label maps to a nonprojective dual
deleted label. -/
theorem deleted_pushforward_nonprojective
    (K : Set ι) (x : DeletedLabel K)
    (hx : ¬ Injective (σ.obj x.1)) :
    ¬ Projective
      (τ.obj ((D.forward.deletedLabelEquiv σ τ K) x).1) := by
  intro hprojective
  apply hx
  apply (D.forward.injective_iff_projective_image σ τ x.1).2
  simpa [AlignedAntiEquivalence.deletedLabelEquiv] using hprojective

omit [Fintype ι] [Fintype κ] in
/-- An injective source deleted label maps to a projective dual deleted
label. -/
theorem deleted_pushforward_projective
    (K : Set ι) (x : DeletedLabel K)
    (hx : Injective (σ.obj x.1)) :
    Projective
      (τ.obj ((D.forward.deletedLabelEquiv σ τ K) x).1) := by
  have h := (D.forward.injective_iff_projective_image σ τ x.1).1 hx
  simpa [AlignedAntiEquivalence.deletedLabelEquiv] using h

variable (ARσ : σ.FiniteARTranslationData)
  (ARτ : τ.FiniteARTranslationData)

/-- Pull a dual admissible hook back to its source-coordinate reverse
hook. -/
def pullbackAdmissibleHook
    (K : Set ι)
    (H : ARτ.AdmissibleHook τ (D.forward.labelEquiv '' K)) :
    ARσ.ReverseAdmissibleHook σ K where
  a := (D.forward.deletedLabelEquiv σ τ K).symm H.a
  u := (D.forward.deletedLabelEquiv σ τ K).symm H.u
  b := (D.forward.deletedLabelEquiv σ τ K).symm H.b
  u_noninjective := D.deleted_pullback_noninjective σ τ K H.u
    H.u_nonprojective
  b_noninjective := D.deleted_pullback_noninjective σ τ K H.b
    H.b_nonprojective
  successor_u := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K H.a H.u).2
        H.predecessor_u.1
    · intro z hz
      have hzTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) z).1)
          (τ.obj H.u.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) z) H.u).1 (by
            simpa using hz)
      have hza := H.predecessor_u.2
        ((D.forward.deletedLabelEquiv σ τ K) z) hzTarget
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using hza
  successor_b := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K H.u H.b).2
        H.predecessor_b.1
    · intro z hz
      have hzTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) z).1)
          (τ.obj H.b.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) z) H.b).1 (by
            simpa using hz)
      have hzu := H.predecessor_b.2
        ((D.forward.deletedLabelEquiv σ τ K) z) hzTarget
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using hzu
  inverseTau_b := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨H.b.1, H.b_nonprojective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, H.tau_b] using h.symm

/-- Push a source-coordinate reverse hook to the corresponding admissible
hook on the dual skeleton. -/
def pushforwardReverseAdmissibleHook
    (K : Set ι)
    (H : ARσ.ReverseAdmissibleHook σ K) :
    ARτ.AdmissibleHook τ (D.forward.labelEquiv '' K) where
  a := (D.forward.deletedLabelEquiv σ τ K) H.a
  u := (D.forward.deletedLabelEquiv σ τ K) H.u
  b := (D.forward.deletedLabelEquiv σ τ K) H.b
  u_nonprojective := D.deleted_pushforward_nonprojective σ τ K H.u
    H.u_noninjective
  b_nonprojective := D.deleted_pushforward_nonprojective σ τ K H.b
    H.b_noninjective
  predecessor_u := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) H.a)
        ((D.forward.deletedLabelEquiv σ τ K) H.u)).1 (by
          simpa using H.successor_u.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) H.u)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj H.u.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      have hqa := H.successor_u.2
        ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using hqa
  predecessor_b := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) H.u)
        ((D.forward.deletedLabelEquiv σ τ K) H.b)).1 (by
          simpa using H.successor_b.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) H.b)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj H.b.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      have hqu := H.successor_b.2
        ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using hqu
  tau_b := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) H.b).1,
        D.deleted_pushforward_nonprojective σ τ K H.b
          H.b_noninjective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv,
      H.inverseTau_b] using h

/-- Dual admissible hooks are exactly source-coordinate reverse hooks. -/
def admissibleHookEquivReverse
    (K : Set ι) :
    ARτ.AdmissibleHook τ (D.forward.labelEquiv '' K) ≃
      ARσ.ReverseAdmissibleHook σ K where
  toFun := D.pullbackAdmissibleHook σ τ ARσ ARτ K
  invFun := D.pushforwardReverseAdmissibleHook σ τ ARσ ARτ K
  left_inv H := by
    ext <;> simp [pullbackAdmissibleHook,
      pushforwardReverseAdmissibleHook]
  right_inv H := by
    ext <;> simp [pullbackAdmissibleHook,
      pushforwardReverseAdmissibleHook]

/-- Pull a dual fixed packet back to its source-coordinate reverse packet. -/
def pullbackFixedPacket
    (K : Set ι)
    (F : ARτ.FixedPacket τ (D.forward.labelEquiv '' K)) :
    ARσ.ReverseFixedPacket σ K where
  i := (D.forward.deletedLabelEquiv σ τ K).symm F.p
  a := (D.forward.deletedLabelEquiv σ τ K).symm F.a
  c := (D.forward.deletedLabelEquiv σ τ K).symm F.c
  z := (D.forward.deletedLabelEquiv σ τ K).symm F.z
  i_injective := D.deleted_pullback_injective σ τ K F.p F.p_projective
  a_noninjective := D.deleted_pullback_noninjective σ τ K F.a
    F.a_nonprojective
  c_noninjective := D.deleted_pullback_noninjective σ τ K F.c
    F.c_nonprojective
  z_noninjective := D.deleted_pullback_noninjective σ τ K F.z
    F.z_nonprojective
  a_to_i := (D.deleted_irreducible_pullback_iff σ τ K F.p F.a).2
    F.p_to_a
  a_to_c := (D.deleted_irreducible_pullback_iff σ τ K F.c F.a).2
    F.c_to_a
  successor_z := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K F.c F.z).2
        F.predecessor_z.1
    · intro q hq
      have hqTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) q).1)
          (τ.obj F.z.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) q) F.z).1 (by
            simpa using hq)
      have hqc := F.predecessor_z.2
        ((D.forward.deletedLabelEquiv σ τ K) q) hqTarget
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using hqc
  successor_c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply F.predecessor_c.1
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using h
    · exact (D.deleted_irreducible_pullback_iff σ τ K F.a F.c).2
        F.predecessor_c.2.1
    · exact (D.deleted_irreducible_pullback_iff σ τ K F.z F.c).2
        F.predecessor_c.2.2.1
    · intro q hq
      have hqTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) q).1)
          (τ.obj F.c.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) q) F.c).1 (by
            simpa using hq)
      rcases F.predecessor_c.2.2.2
          ((D.forward.deletedLabelEquiv σ τ K) q) hqTarget with h | h
      · left
        apply (D.forward.deletedLabelEquiv σ τ K).injective
        simpa using h
      · right
        apply (D.forward.deletedLabelEquiv σ τ K).injective
        simpa using h
  inverseTau_z := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨F.z.1, F.z_nonprojective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, F.tau_z] using h.symm
  inverseTau_c := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨F.c.1, F.c_nonprojective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, F.tau_c] using h.symm
  inverseTau_a_eq_z_or_mem := by
    rcases F.tau_a_eq_z_or_mem with h | h
    · left
      have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
        ⟨F.a.1, F.a_nonprojective⟩
      simpa [AlignedAntiEquivalence.deletedLabelEquiv, h] using ht.symm
    · right
      have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
        ⟨F.a.1, F.a_nonprojective⟩
      have himage : D.forward.labelEquiv.symm
          (ARτ.arTranslation τ ⟨F.a.1, F.a_nonprojective⟩).1 ∈ K := by
        simpa only [Set.mem_image_equiv] using h
      simpa [AlignedAntiEquivalence.deletedLabelEquiv, ht] using himage
  z_not_to_i := by
    intro h
    apply F.p_not_to_z
    exact (D.deleted_irreducible_pullback_iff σ τ K F.p F.z).1 (by
      simpa using h)

/-- Push a source-coordinate reverse fixed packet to row `F` on the dual
skeleton. -/
def pushforwardReverseFixedPacket
    (K : Set ι)
    (F : ARσ.ReverseFixedPacket σ K) :
    ARτ.FixedPacket τ (D.forward.labelEquiv '' K) where
  p := (D.forward.deletedLabelEquiv σ τ K) F.i
  a := (D.forward.deletedLabelEquiv σ τ K) F.a
  c := (D.forward.deletedLabelEquiv σ τ K) F.c
  z := (D.forward.deletedLabelEquiv σ τ K) F.z
  p_projective := D.deleted_pushforward_projective σ τ K F.i
    F.i_injective
  a_nonprojective := D.deleted_pushforward_nonprojective σ τ K F.a
    F.a_noninjective
  c_nonprojective := D.deleted_pushforward_nonprojective σ τ K F.c
    F.c_noninjective
  z_nonprojective := D.deleted_pushforward_nonprojective σ τ K F.z
    F.z_noninjective
  p_to_a := (D.deleted_irreducible_pullback_iff σ τ K
    ((D.forward.deletedLabelEquiv σ τ K) F.i)
    ((D.forward.deletedLabelEquiv σ τ K) F.a)).1 (by
      simpa using F.a_to_i)
  c_to_a := (D.deleted_irreducible_pullback_iff σ τ K
    ((D.forward.deletedLabelEquiv σ τ K) F.c)
    ((D.forward.deletedLabelEquiv σ τ K) F.a)).1 (by
      simpa using F.a_to_c)
  predecessor_z := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) F.c)
        ((D.forward.deletedLabelEquiv σ τ K) F.z)).1 (by
          simpa using F.successor_z.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) F.z)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj F.z.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      have hqc := F.successor_z.2
        ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using hqc
  predecessor_c := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply F.successor_c.1
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using h
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) F.a)
        ((D.forward.deletedLabelEquiv σ τ K) F.c)).1 (by
          simpa using F.successor_c.2.1)
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) F.z)
        ((D.forward.deletedLabelEquiv σ τ K) F.c)).1 (by
          simpa using F.successor_c.2.2.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) F.c)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj F.c.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      rcases F.successor_c.2.2.2
          ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource with h | h
      · left
        apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
        simpa using h
      · right
        apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
        simpa using h
  tau_z := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) F.z).1,
        D.deleted_pushforward_nonprojective σ τ K F.z
          F.z_noninjective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv,
      F.inverseTau_z] using h
  tau_c := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) F.c).1,
        D.deleted_pushforward_nonprojective σ τ K F.c
          F.c_noninjective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv,
      F.inverseTau_c] using h
  tau_a_eq_z_or_mem := by
    rcases F.inverseTau_a_eq_z_or_mem with h | h
    · left
      apply D.forward.labelEquiv.symm.injective
      have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
        ⟨((D.forward.deletedLabelEquiv σ τ K) F.a).1,
          D.deleted_pushforward_nonprojective σ τ K F.a
            F.a_noninjective⟩
      simpa [AlignedAntiEquivalence.deletedLabelEquiv, h] using ht
    · right
      have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
        ⟨((D.forward.deletedLabelEquiv σ τ K) F.a).1,
          D.deleted_pushforward_nonprojective σ τ K F.a
            F.a_noninjective⟩
      refine ⟨((ARσ.arTranslationEquiv σ).symm
        ⟨F.a.1, F.a_noninjective⟩).1, h, ?_⟩
      apply D.forward.labelEquiv.symm.injective
      simpa [AlignedAntiEquivalence.deletedLabelEquiv] using ht.symm
  p_not_to_z := by
    intro h
    apply F.z_not_to_i
    have hs := (D.deleted_irreducible_pullback_iff σ τ K
      ((D.forward.deletedLabelEquiv σ τ K) F.i)
      ((D.forward.deletedLabelEquiv σ τ K) F.z)).2 (by
        simpa using h)
    simpa using hs

/-- Dual row-`F` packets are exactly source-coordinate reverse row-`F`
packets. -/
def fixedPacketEquivReverse
    (K : Set ι) :
    ARτ.FixedPacket τ (D.forward.labelEquiv '' K) ≃
      ARσ.ReverseFixedPacket σ K where
  toFun := D.pullbackFixedPacket σ τ ARσ ARτ K
  invFun := D.pushforwardReverseFixedPacket σ τ ARσ ARτ K
  left_inv F := by
    ext <;> simp [pullbackFixedPacket, pushforwardReverseFixedPacket]
  right_inv F := by
    ext <;> simp [pullbackFixedPacket, pushforwardReverseFixedPacket]

/-- Pull a dual triangle packet back to its source-coordinate reverse
packet. -/
def pullbackTrianglePacket
    (K : Set ι)
    (T : ARτ.TrianglePacket τ (D.forward.labelEquiv '' K)) :
    ARσ.ReverseTrianglePacket σ K where
  i := (D.forward.deletedLabelEquiv σ τ K).symm T.p
  A₁ := (D.forward.deletedLabelEquiv σ τ K).symm T.A₁
  A₂ := (D.forward.deletedLabelEquiv σ τ K).symm T.A₂
  x := (D.forward.deletedLabelEquiv σ τ K).symm T.x
  i_injective := D.deleted_pullback_injective σ τ K T.p T.p_projective
  A₁_noninjective := D.deleted_pullback_noninjective σ τ K T.A₁
    T.A₁_nonprojective
  A₂_noninjective := D.deleted_pullback_noninjective σ τ K T.A₂
    T.A₂_nonprojective
  x_noninjective := D.deleted_pullback_noninjective σ τ K T.x
    T.x_nonprojective
  i_to_A₁ := (D.deleted_irreducible_pullback_iff σ τ K T.A₁ T.p).2
    T.A₁_to_p
  successor_A₁ := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K T.A₂ T.A₁).2
        T.predecessor_A₁.1
    · intro q hq
      have hqTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) q).1)
          (τ.obj T.A₁.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) q) T.A₁).1 (by
            simpa using hq)
      have hqA₂ := T.predecessor_A₁.2
        ((D.forward.deletedLabelEquiv σ τ K) q) hqTarget
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using hqA₂
  successor_A₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply T.predecessor_A₂.1
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using h
    · exact (D.deleted_irreducible_pullback_iff σ τ K T.p T.A₂).2
        T.predecessor_A₂.2.1
    · exact (D.deleted_irreducible_pullback_iff σ τ K T.x T.A₂).2
        T.predecessor_A₂.2.2.1
    · intro q hq
      have hqTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) q).1)
          (τ.obj T.A₂.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) q) T.A₂).1 (by
            simpa using hq)
      rcases T.predecessor_A₂.2.2.2
          ((D.forward.deletedLabelEquiv σ τ K) q) hqTarget with h | h
      · left
        apply (D.forward.deletedLabelEquiv σ τ K).injective
        simpa using h
      · right
        apply (D.forward.deletedLabelEquiv σ τ K).injective
        simpa using h
  successor_x := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K T.A₁ T.x).2
        T.predecessor_x.1
    · intro q hq
      have hqTarget : HasIrreducibleMorphism
          (τ.obj ((D.forward.deletedLabelEquiv σ τ K) q).1)
          (τ.obj T.x.1) :=
        (D.deleted_irreducible_pullback_iff σ τ K
          ((D.forward.deletedLabelEquiv σ τ K) q) T.x).1 (by
            simpa using hq)
      have hqA₁ := T.predecessor_x.2
        ((D.forward.deletedLabelEquiv σ τ K) q) hqTarget
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using hqA₁
  inverseTau_A₁ := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨T.A₁.1, T.A₁_nonprojective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, T.tau_A₁] using h.symm
  inverseTau_A₂ := by
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨T.A₂.1, T.A₂_nonprojective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, T.tau_A₂] using h.symm
  inverseTau_x_mem := by
    have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨T.x.1, T.x_nonprojective⟩
    have himage : D.forward.labelEquiv.symm
        (ARτ.arTranslation τ ⟨T.x.1, T.x_nonprojective⟩).1 ∈ K := by
      simpa only [Set.mem_image_equiv] using T.tau_x_mem
    simpa [AlignedAntiEquivalence.deletedLabelEquiv, ht] using himage

/-- Push a source-coordinate reverse triangle packet to row `T` on the
dual skeleton. -/
def pushforwardReverseTrianglePacket
    (K : Set ι)
    (T : ARσ.ReverseTrianglePacket σ K) :
    ARτ.TrianglePacket τ (D.forward.labelEquiv '' K) where
  p := (D.forward.deletedLabelEquiv σ τ K) T.i
  A₁ := (D.forward.deletedLabelEquiv σ τ K) T.A₁
  A₂ := (D.forward.deletedLabelEquiv σ τ K) T.A₂
  x := (D.forward.deletedLabelEquiv σ τ K) T.x
  p_projective := D.deleted_pushforward_projective σ τ K T.i
    T.i_injective
  A₁_nonprojective := D.deleted_pushforward_nonprojective σ τ K T.A₁
    T.A₁_noninjective
  A₂_nonprojective := D.deleted_pushforward_nonprojective σ τ K T.A₂
    T.A₂_noninjective
  x_nonprojective := D.deleted_pushforward_nonprojective σ τ K T.x
    T.x_noninjective
  A₁_to_p := (D.deleted_irreducible_pullback_iff σ τ K
    ((D.forward.deletedLabelEquiv σ τ K) T.A₁)
    ((D.forward.deletedLabelEquiv σ τ K) T.i)).1 (by
      simpa using T.i_to_A₁)
  predecessor_A₁ := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) T.A₂)
        ((D.forward.deletedLabelEquiv σ τ K) T.A₁)).1 (by
          simpa using T.successor_A₁.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) T.A₁)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj T.A₁.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      have hqA₂ := T.successor_A₁.2
        ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using hqA₂
  predecessor_A₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply T.successor_A₂.1
      apply (D.forward.deletedLabelEquiv σ τ K).injective
      simpa using h
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) T.i)
        ((D.forward.deletedLabelEquiv σ τ K) T.A₂)).1 (by
          simpa using T.successor_A₂.2.1)
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) T.x)
        ((D.forward.deletedLabelEquiv σ τ K) T.A₂)).1 (by
          simpa using T.successor_A₂.2.2.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) T.A₂)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj T.A₂.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      rcases T.successor_A₂.2.2.2
          ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource with h | h
      · left
        apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
        simpa using h
      · right
        apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
        simpa using h
  predecessor_x := by
    constructor
    · exact (D.deleted_irreducible_pullback_iff σ τ K
        ((D.forward.deletedLabelEquiv σ τ K) T.A₁)
        ((D.forward.deletedLabelEquiv σ τ K) T.x)).1 (by
          simpa using T.successor_x.1)
    · intro q hq
      have hsource' :=
        (D.deleted_irreducible_pullback_iff σ τ K q
          ((D.forward.deletedLabelEquiv σ τ K) T.x)).2 (by
            simpa using hq)
      have hsource : HasIrreducibleMorphism
          (σ.obj T.x.1)
          (σ.obj ((D.forward.deletedLabelEquiv σ τ K).symm q).1) := by
        simpa using hsource'
      have hqA₁ := T.successor_x.2
        ((D.forward.deletedLabelEquiv σ τ K).symm q) hsource
      apply (D.forward.deletedLabelEquiv σ τ K).symm.injective
      simpa using hqA₁
  tau_A₁ := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) T.A₁).1,
        D.deleted_pushforward_nonprojective σ τ K T.A₁
          T.A₁_noninjective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv,
      T.inverseTau_A₁] using h
  tau_A₂ := by
    apply D.forward.labelEquiv.symm.injective
    have h := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) T.A₂).1,
        D.deleted_pushforward_nonprojective σ τ K T.A₂
          T.A₂_noninjective⟩
    simpa [AlignedAntiEquivalence.deletedLabelEquiv,
      T.inverseTau_A₂] using h
  tau_x_mem := by
    have ht := D.forward_symm_arTranslation_eq_inverse σ τ ARσ ARτ
      ⟨((D.forward.deletedLabelEquiv σ τ K) T.x).1,
        D.deleted_pushforward_nonprojective σ τ K T.x
          T.x_noninjective⟩
    refine ⟨((ARσ.arTranslationEquiv σ).symm
      ⟨T.x.1, T.x_noninjective⟩).1, T.inverseTau_x_mem, ?_⟩
    apply D.forward.labelEquiv.symm.injective
    simpa [AlignedAntiEquivalence.deletedLabelEquiv] using ht.symm

/-- Dual row-`T` packets are exactly source-coordinate reverse row-`T`
packets. -/
def trianglePacketEquivReverse
    (K : Set ι) :
    ARτ.TrianglePacket τ (D.forward.labelEquiv '' K) ≃
      ARσ.ReverseTrianglePacket σ K where
  toFun := D.pullbackTrianglePacket σ τ ARσ ARτ K
  invFun := D.pushforwardReverseTrianglePacket σ τ ARσ ARτ K
  left_inv T := by
    ext <;> simp [pullbackTrianglePacket,
      pushforwardReverseTrianglePacket]
  right_inv T := by
    ext <;> simp [pullbackTrianglePacket,
      pushforwardReverseTrianglePacket]

end AlignedBiduality

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
