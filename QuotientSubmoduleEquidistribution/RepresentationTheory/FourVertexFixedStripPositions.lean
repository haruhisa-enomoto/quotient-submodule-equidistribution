import QuotientSubmoduleEquidistribution.RepresentationTheory.FourVertexFixedStripBridge

/-!
# Actual fixed-strip cyclic positions

For a projective boundary vertex `p` and a translation-fixed center `c`,
the positions are the boundary-free vertices joined to `c` in both
directions.  Forward AR translation permutes these positions, and the wall
bit records whether `p` has an irreducible arrow to the current neighbor.
The projective--injective bridge identifies reverse packet walls with the
same binary system after a phase shift.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable {AR : σ.FiniteARTranslationData}
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

/-- One cyclic fixed-strip context: a projective boundary vertex, a fixed
center, and the independent condition excluding the boundary arrow to the
center. -/
@[ext]
structure FixedStripContext where
  p : ι
  p_projective : Projective (σ.obj p)
  center : AR.FixedCenter σ
  p_not_to_center :
    ¬ HasIrreducibleMorphism (σ.obj p) (σ.obj center.c)

noncomputable instance fixedStripContextFintype :
    Fintype (AR.FixedStripContext σ) := by
  letI : Finite (AR.FixedStripContext σ) :=
    Finite.of_injective
      (fun C ↦ (C.p, C.center.c)) (by
        intro C₁ C₂ h
        ext
        · exact congrArg Prod.fst h
        · exact congrArg Prod.snd h)
  exact Fintype.ofFinite _

/-- Positions in one fixed-strip context. -/
abbrev FixedStripPosition (C : AR.FixedStripContext σ) :=
  AR.FixedNeighbor σ C.center

/-- The forward cyclic shift on fixed-strip positions. -/
def fixedStripStep (C : AR.FixedStripContext σ) :
    AR.FixedStripPosition σ C ≃ AR.FixedStripPosition σ C :=
  FixedNeighbor.forwardEquiv
    (AR := AR) (C := C.center) (k := k) σ τ D ARτ

/-- The wall bit at a fixed-strip position records the projective boundary
arrow. -/
def fixedStripBit (C : AR.FixedStripContext σ)
    (X : AR.FixedStripPosition σ C) : Bool := by
  classical
  exact if HasIrreducibleMorphism (σ.obj C.p) (σ.obj X.x) then true else false

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Fintype ι] [DecidableEq ι] in
@[simp]
theorem fixedStripBit_eq_true_iff
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C) :
    fixedStripBit (AR := AR) σ C X = true ↔
      HasIrreducibleMorphism (σ.obj C.p) (σ.obj X.x) := by
  simp [fixedStripBit]

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [Fintype ι] [DecidableEq ι] in
@[simp]
theorem fixedStripBit_eq_false_iff
    (C : AR.FixedStripContext σ) (X : AR.FixedStripPosition σ C) :
    fixedStripBit (AR := AR) σ C X = false ↔
      ¬ HasIrreducibleMorphism (σ.obj C.p) (σ.obj X.x) := by
  simp [fixedStripBit]

namespace FixedPacket

variable {K : Set ι}
  (F : AR.FixedPacket σ K)

/-- The cyclic context determined by a quotient row-`F` packet. -/
def fixedStripContext : AR.FixedStripContext σ where
  p := F.p.1
  p_projective := F.p_projective
  center := F.fixedCenter (k := k) σ τ D ARτ
  p_not_to_center := by
    intro hpc
    have hlabel : F.p = F.a ∨ F.p = F.z :=
      F.predecessor_c.2.2.2 F.p hpc
    rcases hlabel with hpa | hpz
    · exact F.a_nonprojective (hpa ▸ F.p_projective)
    · exact F.z_nonprojective (hpz ▸ F.p_projective)

omit [IsAlgClosed k] [Algebra k R] [FiniteDimensional k R]
  [DecidableEq ι] in
/-- Every quotient row-`F` packet is a rise of its actual projective wall
bit. -/
theorem isRise_aNeighbor :
    QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsRise
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ
        (F.fixedStripContext (k := k) σ τ D ARτ))
      (fixedStripBit (AR := AR) σ
        (F.fixedStripContext (k := k) σ τ D ARτ))
      (F.aNeighbor (k := k) σ τ D ARτ) := by
  let C := F.fixedStripContext (k := k) σ τ D ARτ
  constructor
  · rw [fixedStripBit_eq_false_iff]
    change ¬ HasIrreducibleMorphism (σ.obj F.p.1)
      (σ.obj (((FixedNeighbor.forwardEquiv
        (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
        (k := k) σ τ D ARτ).symm
          (F.aNeighbor (k := k) σ τ D ARτ)).x))
    rw [F.forwardEquiv_symm_aNeighbor (k := k) σ τ D ARτ]
    exact F.p_not_to_z
  · rw [fixedStripBit_eq_true_iff]
    exact F.p_to_a

end FixedPacket

namespace ReverseFixedPacket

variable {K : Set ι}
  (F : AR.ReverseFixedPacket σ K)

/-- The quotient-side projective boundary label canonically paired with
the injective wall of a reverse row-`F` packet. -/
def pairedProjective : {p : ι // Projective (σ.obj p)} :=
  (AR.projectiveLabelEquivInjectiveLabel σ).symm
    ⟨F.i.1, F.i_injective⟩

/-- The common cyclic context determined by a reverse row-`F` packet. -/
def fixedStripContext : AR.FixedStripContext σ where
  p := (F.pairedProjective σ).1
  p_projective := (F.pairedProjective σ).2
  center := F.fixedCenter σ
  p_not_to_center := by
    intro hpc
    have hci : HasIrreducibleMorphism (σ.obj F.c.1) (σ.obj F.i.1) := by
      have hbridge :=
        projective_to_fixedCenter_iff_fixedCenter_to_injective
          (AR := AR) (C := F.fixedCenter σ) σ
          (F.pairedProjective σ).1 (F.pairedProjective σ).2
      have h := hbridge.1 hpc
      change HasIrreducibleMorphism
        (σ.obj F.c.1)
        (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ
          (F.pairedProjective σ)).1)) at h
      simpa [pairedProjective] using h
    rcases F.successor_c.2.2.2 F.i hci with hia | hiz
    · exact F.a_noninjective (hia ▸ F.i_injective)
    · exact F.z_noninjective (hiz ▸ F.i_injective)

/-- The position whose bridge phase is the reverse packet's `a` neighbor. -/
def fallPosition : AR.FixedStripPosition σ
    (F.fixedStripContext σ) :=
  (fixedBridgeEquiv
    (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
    (F.pairedProjective σ).1 (F.pairedProjective σ).2).symm
      (F.aNeighbor σ)

omit [IsAlgClosed k] [DecidableEq ι] in
/-- Every reverse row-`F` packet is a fall in the same projective wall
system after applying the fixed bridge phase. -/
theorem isFall_fallPosition :
    QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
      (fixedStripStep (AR := AR) (k := k) σ τ D ARτ
        (F.fixedStripContext σ))
      (fixedStripBit (AR := AR) σ (F.fixedStripContext σ))
      (F.fallPosition (k := k) σ τ D ARτ) := by
  let C := F.fixedStripContext σ
  let p := F.pairedProjective σ
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
  let B := fixedBridgeEquiv
    (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ p.1 p.2
  have hBX : B (F.fallPosition (k := k) σ τ D ARτ) =
      F.aNeighbor σ := B.apply_symm_apply _
  have hBEX : B (E (F.fallPosition (k := k) σ τ D ARτ)) =
      F.zNeighbor (k := k) σ := by
    calc
      B (E (F.fallPosition (k := k) σ τ D ARτ)) =
          E (B (F.fallPosition (k := k) σ τ D ARτ)) := by
        exact fixedBridgeEquiv_forwardEquiv
          (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
          p.1 p.2 (F.fallPosition (k := k) σ τ D ARτ)
      _ = E (F.aNeighbor σ) := congrArg E hBX
      _ = F.zNeighbor (k := k) σ := by
        change FixedNeighbor.forwardEquiv
          (AR := AR) (C := F.fixedCenter σ)
          (k := k) σ τ D ARτ (F.aNeighbor σ) =
            F.zNeighbor (k := k) σ
        exact F.forwardEquiv_aNeighbor_eq (k := k) σ τ D ARτ
  constructor
  · rw [fixedStripBit_eq_true_iff]
    have hbridge := projective_to_neighbor_iff_bridgeNeighbor_to_injective
      (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
      p.1 p.2 (F.fallPosition (k := k) σ τ D ARτ)
    apply hbridge.2
    rw [← fixedBridgeEquiv_apply
      (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ]
    rw [hBX]
    change HasIrreducibleMorphism (σ.obj F.a.1)
      (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ p).1))
    simpa [p, pairedProjective] using F.a_to_i
  · rw [fixedStripBit_eq_false_iff]
    intro hpz
    have hbridge := projective_to_neighbor_iff_bridgeNeighbor_to_injective
      (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ
      p.1 p.2 (E (F.fallPosition (k := k) σ τ D ARτ))
    apply F.z_not_to_i
    have := hbridge.1 hpz
    rw [← fixedBridgeEquiv_apply
      (AR := AR) (C := F.fixedCenter σ) (k := k) σ τ D ARτ] at this
    rw [hBEX] at this
    change HasIrreducibleMorphism (σ.obj F.z.1)
      (σ.obj ((AR.projectiveLabelEquivInjectiveLabel σ p).1)) at this
    simpa [p, pairedProjective] using this

end ReverseFixedPacket

/-- All rises in the actual fixed-strip binary systems. -/
abbrev FixedStripRise :=
  Σ C : AR.FixedStripContext σ,
    {X : AR.FixedStripPosition σ C //
      QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsRise
        (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
        (fixedStripBit (AR := AR) σ C) X}

/-- All falls in the actual fixed-strip binary systems. -/
abbrev FixedStripFall :=
  Σ C : AR.FixedStripContext σ,
    {X : AR.FixedStripPosition σ C //
      QuotientSubmoduleEquidistribution.FixedStripCyclicBalance.IsFall
        (fixedStripStep (AR := AR) (k := k) σ τ D ARτ C)
        (fixedStripBit (AR := AR) σ C) X}

/-- Forget an actual hookless quotient row-`F` support to its rise in the
common fixed-strip system. -/
def quotientFixedPacketFourToFixedStripRise
    (Q : QuotientFixedPacketFour (k := k) (R := R) σ) :
    FixedStripRise
      (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
      σ τ D (τ.finiteDimensionalARTranslationData k S) := by
  let F := Classical.choice Q.2.1
  exact ⟨F.fixedStripContext (k := k) σ τ D
      (τ.finiteDimensionalARTranslationData k S),
    ⟨F.aNeighbor (k := k) σ τ D
        (τ.finiteDimensionalARTranslationData k S),
      F.isRise_aNeighbor (k := k) σ τ D
        (τ.finiteDimensionalARTranslationData k S)⟩⟩

/-- Forget an actual source-coordinate reverse row-`F` support to its fall
in the same fixed-strip system. -/
def sourceReverseFixedPacketFourToFixedStripFall
    (Q : SourceReverseFixedPacketFour
      (k := k) (R := R) σ τ D) :
    FixedStripFall
      (AR := σ.finiteDimensionalARTranslationData k R) (k := k)
      σ τ D (τ.finiteDimensionalARTranslationData k S) := by
  let F := Classical.choice Q.2.1
  exact ⟨F.fixedStripContext σ,
    ⟨F.fallPosition (k := k) σ τ D
        (τ.finiteDimensionalARTranslationData k S),
      F.isFall_fallPosition (k := k) σ τ D
        (τ.finiteDimensionalARTranslationData k S)⟩⟩

end FiniteARTranslationData

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
