import OpConjecture.RepresentationTheory.ARDualLocalRestrictions
import OpConjecture.RepresentationTheory.FourVertexFixedStripBalance
import OpConjecture.RepresentationTheory.FourVertexArrowOrbits

/-!
# Translation cycles around fixed centers

For the fixed-strip count, a translation-fixed center is joined in both
directions to a finite family of boundary-free neighbors.  Inverse AR
translation permutes those neighbors; its inverse is the manuscript's
forward cyclic shift.  This file constructs that permutation without
choosing or quotienting individual translation orbits.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)

namespace FiniteARTranslationData

variable {AR : σ.FiniteARTranslationData}

/-- A boundary-free translation-fixed center. -/
@[ext]
structure FixedCenter where
  c : ι
  c_nonprojective : ¬ Projective (σ.obj c)
  c_noninjective : ¬ Injective (σ.obj c)
  tau_c : (AR.arTranslation σ ⟨c, c_nonprojective⟩).1 = c

noncomputable instance fixedCenterFintype : Fintype (AR.FixedCenter σ) := by
  letI : Finite (AR.FixedCenter σ) :=
    Finite.of_injective FixedCenter.c (by
      intro C₁ C₂ h
      ext
      exact h)
  exact Fintype.ofFinite _

/-- A boundary-free vertex joined to a fixed center by arrows in both
directions. -/
@[ext]
structure FixedNeighbor (C : AR.FixedCenter σ) where
  x : ι
  x_nonprojective : ¬ Projective (σ.obj x)
  x_noninjective : ¬ Injective (σ.obj x)
  c_to_x : HasIrreducibleMorphism (σ.obj C.c) (σ.obj x)
  x_to_c : HasIrreducibleMorphism (σ.obj x) (σ.obj C.c)

noncomputable instance fixedNeighborFintype (C : AR.FixedCenter σ) :
    Fintype (AR.FixedNeighbor σ C) := by
  letI : Finite (AR.FixedNeighbor σ C) :=
    Finite.of_injective FixedNeighbor.x (by
      intro X₁ X₂ h
      ext
      exact h)
  exact Fintype.ofFinite _

namespace FixedNeighbor

variable {C : AR.FixedCenter σ}
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

/-- Inverse AR translation preserves the boundary-free neighbors of a
fixed center. -/
def successor (X : AR.FixedNeighbor σ C) : AR.FixedNeighbor σ C := by
  let yLabel : σ.NonprojectiveLabel :=
    (AR.arTranslationEquiv σ).symm ⟨X.x, X.x_noninjective⟩
  let y : ι := yLabel.1
  have hyP : ¬ Projective (σ.obj y) := yLabel.2
  have htauSubtype :
      AR.arTranslationEquiv σ yLabel =
        ⟨X.x, X.x_noninjective⟩ :=
    (AR.arTranslationEquiv σ).apply_symm_apply
      ⟨X.x, X.x_noninjective⟩
  have htau : (AR.arTranslation σ yLabel).1 = X.x :=
    congrArg Subtype.val htauSubtype
  have hc_to_y : HasIrreducibleMorphism (σ.obj C.c) (σ.obj y) := by
    apply (AR.arTranslation_incidence σ yLabel C.c).2
    simpa only [htau] using X.x_to_c
  have hy_to_c : HasIrreducibleMorphism (σ.obj y) (σ.obj C.c) := by
    apply (AR.arTranslation_incidence σ
      ⟨C.c, C.c_nonprojective⟩ y).2
    simpa only [C.tau_c] using hc_to_y
  have hyI : ¬ Injective (σ.obj y) :=
    D.noninjective_of_nonprojective_two_cycle
      (k := k) σ τ ARτ y C.c hyP hy_to_c hc_to_y
  exact ⟨y, hyP, hyI, hc_to_y, hy_to_c⟩

omit [Algebra k R] [FiniteDimensional k R] in
/-- The underlying inverse-translation identity for neighbor successor. -/
theorem successor_val (X : AR.FixedNeighbor σ C) :
    (X.successor (AR := AR) (C := C) (k := k) σ τ D ARτ).x =
      ((AR.arTranslationEquiv σ).symm
        ⟨X.x, X.x_noninjective⟩).1 :=
  rfl

omit [Algebra k R] [FiniteDimensional k R] in
/-- Inverse translation is injective on the fixed-neighbor family. -/
theorem successor_injective : Function.Injective
    (successor (AR := AR) (C := C) (k := k) σ τ D ARτ :
      AR.FixedNeighbor σ C → AR.FixedNeighbor σ C) := by
  intro X Y h
  apply FixedNeighbor.ext
  have hval := congrArg FixedNeighbor.x h
  have hsubtype :
      (AR.arTranslationEquiv σ).symm
          ⟨X.x, X.x_noninjective⟩ =
        (AR.arTranslationEquiv σ).symm
          ⟨Y.x, Y.x_noninjective⟩ := by
    apply Subtype.ext
    simpa only [successor_val] using hval
  have hxy := (AR.arTranslationEquiv σ).symm.injective hsubtype
  exact congrArg Subtype.val hxy

/-- Inverse AR translation is a permutation of all boundary-free neighbors
of one fixed center. -/
def successorEquiv : AR.FixedNeighbor σ C ≃ AR.FixedNeighbor σ C := by
  classical
  let f : AR.FixedNeighbor σ C → AR.FixedNeighbor σ C :=
    successor (AR := AR) (C := C) (k := k) σ τ D ARτ
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨successor_injective (AR := AR) (C := C)
        (k := k) σ τ D ARτ, rfl⟩)

omit [Algebra k R] [FiniteDimensional k R] in
/-- Evaluation of the inverse-translation neighbor permutation. -/
@[simp]
theorem successorEquiv_apply (X : AR.FixedNeighbor σ C) :
    (successorEquiv (AR := AR) (C := C)
      (k := k) σ τ D ARτ X).x =
      ((AR.arTranslationEquiv σ).symm
        ⟨X.x, X.x_noninjective⟩).1 := by
  rfl

/-- The forward cyclic shift used in the manuscript is the inverse of the
inverse-translation neighbor permutation. -/
def forwardEquiv : AR.FixedNeighbor σ C ≃ AR.FixedNeighbor σ C :=
  (successorEquiv (AR := AR) (C := C)
    (k := k) σ τ D ARτ).symm

omit [Algebra k R] [FiniteDimensional k R] in
/-- The AR translate of the preceding neighbor is the original neighbor. -/
theorem arTranslation_forwardEquiv_symm (X : AR.FixedNeighbor σ C) :
    (AR.arTranslation σ
      ⟨((forwardEquiv (AR := AR) (C := C)
        (k := k) σ τ D ARτ).symm X).x,
        ((forwardEquiv (AR := AR) (C := C)
          (k := k) σ τ D ARτ).symm X).x_nonprojective⟩).1 =
      X.x := by
  let E := forwardEquiv (AR := AR) (C := C)
    (k := k) σ τ D ARτ
  let Y := E.symm X
  have hY :
      (AR.arTranslationEquiv σ).symm
          ⟨X.x, X.x_noninjective⟩ =
        (⟨Y.x, Y.x_nonprojective⟩ : σ.NonprojectiveLabel) := by
    apply Subtype.ext
    exact (successorEquiv_apply (AR := AR) (C := C)
      (k := k) σ τ D ARτ X).symm
  have happly := (AR.arTranslationEquiv σ).apply_symm_apply
    ⟨X.x, X.x_noninjective⟩
  rw [hY] at happly
  exact congrArg Subtype.val happly

omit [Algebra k R] [FiniteDimensional k R] in
/-- The forward neighbor permutation is ordinary AR translation on
underlying labels. -/
theorem forwardEquiv_apply (X : AR.FixedNeighbor σ C) :
    (forwardEquiv (AR := AR) (C := C)
      (k := k) σ τ D ARτ X).x =
      (AR.arTranslation σ ⟨X.x, X.x_nonprojective⟩).1 := by
  let E := forwardEquiv (AR := AR) (C := C)
    (k := k) σ τ D ARτ
  have h := arTranslation_forwardEquiv_symm
    (AR := AR) (C := C) (k := k) σ τ D ARτ (E X)
  rw [E.symm_apply_apply] at h
  exact h.symm

end FixedNeighbor

namespace FixedPacket

variable {K : Set ι}
  (F : AR.FixedPacket σ K)
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

/-- The center of every quotient row-`F` packet is a boundary-free fixed
center. -/
def fixedCenter : AR.FixedCenter σ where
  c := F.c.1
  c_nonprojective := F.c_nonprojective
  c_noninjective :=
    D.noninjective_of_nonprojective_two_cycle
      (k := k) σ τ ARτ F.c.1 F.a.1 F.c_nonprojective
        F.c_to_a F.predecessor_c.2.1
  tau_c := F.tau_c

/-- The `a`-vertex of row `F` is a boundary-free neighbor of its fixed
center. -/
def aNeighbor : AR.FixedNeighbor σ (F.fixedCenter (k := k) σ τ D ARτ) := by
  have haI : ¬ Injective (σ.obj F.a.1) := by
    have h := (AR.arTranslation σ
      ⟨F.z.1, F.z_nonprojective⟩).2
    simpa only [F.tau_z] using h
  exact ⟨F.a.1, F.a_nonprojective, haI,
    F.c_to_a, F.predecessor_c.2.1⟩

/-- The `z`-vertex of row `F` is the preceding boundary-free neighbor. -/
def zNeighbor : AR.FixedNeighbor σ (F.fixedCenter (k := k) σ τ D ARτ) :=
  ⟨F.z.1, F.z_nonprojective,
    D.noninjective_of_nonprojective_two_cycle
      (k := k) σ τ ARτ F.z.1 F.c.1 F.z_nonprojective
        F.predecessor_c.2.2.1 F.predecessor_z.1,
    F.predecessor_z.1, F.predecessor_c.2.2.1⟩

omit [Algebra k R] [FiniteDimensional k R] in
/-- In the forward neighbor permutation, `z` is followed by `a`, exactly as
in the manuscript convention `tau z = a`. -/
theorem forwardEquiv_zNeighbor :
    (FixedNeighbor.forwardEquiv
      (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
      (k := k) σ τ D ARτ
      (F.zNeighbor (k := k) σ τ D ARτ)).x = F.a.1 := by
  let Za := F.zNeighbor (k := k) σ τ D ARτ
  let Aa := F.aNeighbor (k := k) σ τ D ARτ
  have hsucc : FixedNeighbor.successorEquiv
      (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
      (k := k) σ τ D ARτ Aa = Za := by
    apply FixedNeighbor.ext
    calc
      (FixedNeighbor.successorEquiv
          (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
          (k := k) σ τ D ARτ Aa).x =
          ((AR.arTranslationEquiv σ).symm
            ⟨Aa.x, Aa.x_noninjective⟩).1 := by
        exact FixedNeighbor.successorEquiv_apply
          (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
          (k := k) σ τ D ARτ Aa
      _ = Za.x := by
        have hlabels :
            (AR.arTranslationEquiv σ).symm
                ⟨Aa.x, Aa.x_noninjective⟩ =
              (⟨Za.x, Za.x_nonprojective⟩ : σ.NonprojectiveLabel) := by
          apply (AR.arTranslationEquiv σ).injective
          apply Subtype.ext
          rw [(AR.arTranslationEquiv σ).apply_symm_apply]
          change F.a.1 =
            (AR.arTranslation σ ⟨F.z.1, F.z_nonprojective⟩).1
          exact F.tau_z.symm
        exact congrArg Subtype.val hlabels
  have hforward := congrArg FixedNeighbor.x
    ((FixedNeighbor.successorEquiv
      (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
      (k := k) σ τ D ARτ).symm_apply_eq.mpr
      hsucc.symm)
  calc
    (FixedNeighbor.forwardEquiv
        (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
        (k := k) σ τ D ARτ Za).x = Aa.x := hforward
    _ = F.a.1 := rfl

omit [Algebra k R] [FiniteDimensional k R] in
/-- Equivalently, the inverse forward shift sends `a` back to `z`. -/
theorem forwardEquiv_symm_aNeighbor :
    (FixedNeighbor.forwardEquiv
      (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
      (k := k) σ τ D ARτ).symm
        (F.aNeighbor (k := k) σ τ D ARτ) =
      F.zNeighbor (k := k) σ τ D ARτ := by
  let E := FixedNeighbor.forwardEquiv
    (AR := AR) (C := F.fixedCenter (k := k) σ τ D ARτ)
    (k := k) σ τ D ARτ
  apply E.symm_apply_eq.mpr
  apply FixedNeighbor.ext
  exact (F.forwardEquiv_zNeighbor (k := k) σ τ D ARτ).symm

end FixedPacket

namespace ReverseFixedPacket

variable {K : Set ι}
  (F : AR.ReverseFixedPacket σ K)
  (D : AlignedBiduality σ τ)
  (ARτ : τ.FiniteARTranslationData)

/-- The center of every source-coordinate reverse row-`F` packet is the
same kind of boundary-free fixed center. -/
def fixedCenter : AR.FixedCenter σ := by
  let cNP : σ.NonprojectiveLabel :=
    (AR.arTranslationEquiv σ).symm
      ⟨F.c.1, F.c_noninjective⟩
  have hcval : cNP.1 = F.c.1 := F.inverseTau_c
  have hcP : ¬ Projective (σ.obj F.c.1) := by
    simpa only [← hcval] using cNP.2
  refine ⟨F.c.1, hcP, F.c_noninjective, ?_⟩
  have hsubtype := (AR.arTranslationEquiv σ).apply_symm_apply
    ⟨F.c.1, F.c_noninjective⟩
  change AR.arTranslation σ cNP =
    ⟨F.c.1, F.c_noninjective⟩ at hsubtype
  have hval := congrArg Subtype.val hsubtype
  have hcNPEq : cNP = (⟨F.c.1, hcP⟩ : σ.NonprojectiveLabel) := by
    apply Subtype.ext
    exact hcval
  rw [← hcNPEq]
  exact hval

/-- The `a`-vertex of a reverse row-`F` packet is a boundary-free fixed
neighbor. -/
def aNeighbor : AR.FixedNeighbor σ
    (F.fixedCenter σ) := by
  let aNP : σ.NonprojectiveLabel :=
    (AR.arTranslationEquiv σ).symm
      ⟨F.z.1, F.z_noninjective⟩
  have haval : aNP.1 = F.a.1 := F.inverseTau_z
  have haP : ¬ Projective (σ.obj F.a.1) := by
    simpa only [← haval] using aNP.2
  exact ⟨F.a.1, haP, F.a_noninjective,
    by simpa [fixedCenter] using F.successor_c.2.1,
    by simpa [fixedCenter] using F.a_to_c⟩

/-- The `z`-vertex of a reverse row-`F` packet is the next boundary-free
fixed neighbor. -/
def zNeighbor : AR.FixedNeighbor σ
    (F.fixedCenter σ) := by
  have hzP : ¬ Projective (σ.obj F.z.1) := by
    intro hzProjective
    apply F.z_noninjective
    exact AR.injective_of_projective_two_cycle
      (K := k) σ F.z.1 F.c.1 hzProjective
        F.successor_z.1 F.successor_c.2.2.1
  exact ⟨F.z.1, hzP, F.z_noninjective,
    by simpa [fixedCenter] using F.successor_c.2.2.1,
    by simpa [fixedCenter] using F.successor_z.1⟩

/-- In the forward neighbor permutation of a reverse row-`F` packet, `a`
is followed by `z`; this is the source-coordinate form of
`inverseTau z = a`. -/
theorem forwardEquiv_aNeighbor :
    (FixedNeighbor.forwardEquiv
      (AR := AR) (C := F.fixedCenter σ)
      (k := k) σ τ D ARτ
      (F.aNeighbor σ)).x = F.z.1 := by
  let Za := F.zNeighbor (k := k) σ
  let Aa := F.aNeighbor σ
  have hsucc : FixedNeighbor.successorEquiv
      (AR := AR) (C := F.fixedCenter σ)
      (k := k) σ τ D ARτ Za = Aa := by
    apply FixedNeighbor.ext
    exact FixedNeighbor.successorEquiv_apply
      (AR := AR) (C := F.fixedCenter σ)
      (k := k) σ τ D ARτ Za |>.trans F.inverseTau_z
  have hforward := congrArg FixedNeighbor.x
    ((FixedNeighbor.successorEquiv
      (AR := AR) (C := F.fixedCenter σ)
      (k := k) σ τ D ARτ).symm_apply_eq.mpr hsucc.symm)
  calc
    (FixedNeighbor.forwardEquiv
        (AR := AR) (C := F.fixedCenter σ)
        (k := k) σ τ D ARτ Aa).x = Za.x := hforward
    _ = F.z.1 := rfl

/-- The forward shift sends the full reverse-packet `a` neighbor to its
`z` neighbor. -/
theorem forwardEquiv_aNeighbor_eq :
    FixedNeighbor.forwardEquiv
      (AR := AR) (C := F.fixedCenter σ)
      (k := k) σ τ D ARτ (F.aNeighbor σ) =
      F.zNeighbor (k := k) σ := by
  apply FixedNeighbor.ext
  exact F.forwardEquiv_aNeighbor (k := k) σ τ D ARτ

end ReverseFixedPacket

end FiniteARTranslationData

end OpConjecture.IndecomposableSkeleton
