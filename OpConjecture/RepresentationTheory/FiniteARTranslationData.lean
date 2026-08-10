import OpConjecture.RepresentationTheory.AlmostSplitKernel
import OpConjecture.RepresentationTheory.AlmostSplitUniqueness
import OpConjecture.RepresentationTheory.ArtinDualityInterface
import OpConjecture.RepresentationTheory.CofiniteTwoMeshRotation

/-!
# Field-free Auslander--Reiten translation on a finite skeleton

This file isolates the exact representation-theoretic data needed to
construct Auslander--Reiten mesh rotation without a field.  Minimal right
almost-split decompositions at nonprojective vertices supply the kernels;
an equivalence between projective and injective boundary labels turns the
resulting injective translation map into a bijection.

The kernel theorem constructs the corresponding minimal left almost-split
maps, so no separate left almost-split existence input is required.  The
result is the `ARMeshRotationData` used by the colevel-two argument and the
literal field-free equality of the two `rad / rad²` boundary counts.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

/-- The exact input for field-free finite Auslander--Reiten translation:
right AR decompositions and a projective--injective boundary equivalence. -/
structure FiniteARTranslationData where
  rightAR_nonempty : ∀ z : σ.NonprojectiveLabel,
    Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1)
  boundary :
    {i : ι // Projective (σ.obj i)} ≃
      {i : ι // Injective (σ.obj i)}

namespace FiniteARTranslationData

variable (D : σ.FiniteARTranslationData)

/-- Choose the right AR decomposition supplied by the abstract input. -/
def chosenRightAR (z : σ.NonprojectiveLabel) :
    σ.MinimalRightAlmostSplitDecomposition z.1 :=
  Classical.choice (D.rightAR_nonempty z)

local instance chosenRightAR_epi (z : σ.NonprojectiveLabel) :
    Epi (chosenRightAR σ D z).map :=
  OpConjecture.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
    σ (chosenRightAR σ D z).map
      (chosenRightAR σ D z).rightAlmostSplit z.2

/-- The chosen right AR map has an indecomposable, noninjective kernel and a
minimal left almost-split kernel inclusion. -/
theorem chosenRightAR_kernel_ar_sequence
    (z : σ.NonprojectiveLabel) :
    IsLeftAlmostSplit (kernel.ι (chosenRightAR σ D z).map) ∧
      IsLeftMinimal (kernel.ι (chosenRightAR σ D z).map) ∧
      OpConjecture.Foundation.IsIndecomposableModule R
        (kernel (chosenRightAR σ D z).map : FGModuleCat.{w} R) ∧
      ¬ Injective (kernel (chosenRightAR σ D z).map) :=
  OpConjecture.IndecomposableSkeleton.MinimalRightAlmostSplitDecomposition.kernel_ar_sequence
    (σ := σ) (chosenRightAR σ D z) z.2

/-- Skeleton label of the kernel of the chosen right AR epimorphism. -/
def arTranslationLabel (z : σ.NonprojectiveLabel) : ι :=
  Classical.choose
    (σ.complete (kernel (chosenRightAR σ D z).map)
      (chosenRightAR_kernel_ar_sequence σ D z).2.2.1)

/-- The chosen kernel-to-skeleton isomorphism. -/
def arTranslationKernelIso (z : σ.NonprojectiveLabel) :
    kernel (chosenRightAR σ D z).map ≅
      σ.obj (arTranslationLabel σ D z) :=
  (Classical.choose_spec
    (σ.complete (kernel (chosenRightAR σ D z).map)
      (chosenRightAR_kernel_ar_sequence σ D z).2.2.1)).some

/-- Field-free AR translation as a map from nonprojective to noninjective
labels. -/
def arTranslation (z : σ.NonprojectiveLabel) :
    σ.NoninjectiveLabel :=
  ⟨arTranslationLabel σ D z, by
    intro h
    apply (chosenRightAR_kernel_ar_sequence σ D z).2.2.2
    exact Injective.of_iso (arTranslationKernelIso σ D z).symm h⟩

/-- The kernel inclusion rewritten with its chosen skeleton representative
as source. -/
def arKernelMap (z : σ.NonprojectiveLabel) :
    σ.obj (arTranslation σ D z).1 ⟶
      (chosenRightAR σ D z).middle :=
  (arTranslationKernelIso σ D z).inv ≫
    kernel.ι (chosenRightAR σ D z).map

/-- The transported kernel inclusion is left almost split. -/
theorem arKernelMap_leftAlmostSplit (z : σ.NonprojectiveLabel) :
    IsLeftAlmostSplit (arKernelMap σ D z) :=
  (chosenRightAR_kernel_ar_sequence σ D z).1.precomp_iso
    (arTranslationKernelIso σ D z).symm

/-- The transported kernel inclusion is left minimal. -/
theorem arKernelMap_leftMinimal (z : σ.NonprojectiveLabel) :
    IsLeftMinimal (arKernelMap σ D z) :=
  (chosenRightAR_kernel_ar_sequence σ D z).2.1.precomp_iso
    (arTranslationKernelIso σ D z).symm

/-- Equality of field-free AR-translation labels identifies the original
nonprojective endpoints. -/
theorem arTranslation_injective :
    Function.Injective (arTranslation σ D) := by
  intro z₁ z₂ hτ
  let hval : (arTranslation σ D z₁).1 =
      (arTranslation σ D z₂).1 :=
    congrArg Subtype.val hτ
  let eobj : σ.obj (arTranslation σ D z₁).1 ≅
      σ.obj (arTranslation σ D z₂).1 :=
    eqToIso (congrArg σ.obj hval)
  let ek : kernel (chosenRightAR σ D z₁).map ≅
      kernel (chosenRightAR σ D z₂).map :=
    (arTranslationKernelIso σ D z₁).trans
      (eobj.trans (arTranslationKernelIso σ D z₂).symm)
  let k₁' : kernel (chosenRightAR σ D z₂).map ⟶
      (chosenRightAR σ D z₁).middle :=
    ek.inv ≫ kernel.ι (chosenRightAR σ D z₁).map
  have hk₁as : IsLeftAlmostSplit k₁' :=
    (chosenRightAR_kernel_ar_sequence σ D z₁).1.precomp_iso ek.symm
  have hk₁min : IsLeftMinimal k₁' :=
    (chosenRightAR_kernel_ar_sequence σ D z₁).2.1.precomp_iso ek.symm
  obtain ⟨emid, hemid⟩ := exists_leftAlmostSplit_middleIso
    hk₁as hk₁min
    (chosenRightAR_kernel_ar_sequence σ D z₂).1
    (chosenRightAR_kernel_ar_sequence σ D z₂).2.1
  let ec : cokernel k₁' ≅
      cokernel (kernel.ι (chosenRightAR σ D z₂).map) :=
    cokernel.mapIso k₁'
      (kernel.ι (chosenRightAR σ D z₂).map)
      (Iso.refl (kernel (chosenRightAR σ D z₂).map)) emid
      (by simpa using hemid)
  let ec₁ : cokernel k₁' ≅
      cokernel (kernel.ι (chosenRightAR σ D z₁).map) :=
    cokernel.mapIso k₁'
      (kernel.ι (chosenRightAR σ D z₁).map)
      ek.symm (Iso.refl (chosenRightAR σ D z₁).middle)
      (by simp [k₁'])
  let e₁ : cokernel k₁' ≅ σ.obj z₁.1 :=
    ec₁.trans (cokernelKernelIsoTarget (chosenRightAR σ D z₁).map)
  let e₂ : cokernel (kernel.ι (chosenRightAR σ D z₂).map) ≅
      σ.obj z₂.1 :=
    cokernelKernelIsoTarget (chosenRightAR σ D z₂).map
  apply Subtype.ext
  apply σ.eq_of_iso
  exact ⟨e₁.symm.trans (ec.trans e₂)⟩

/-- AR translation rotates irreducible incidence.  The two directions are
the summand correspondences for the minimal maps in the same short exact
sequence. -/
theorem arTranslation_incidence
    (z : σ.NonprojectiveLabel) (x : ι) :
    HasIrreducibleMorphism (σ.obj x) (σ.obj z.1) ↔
      HasIrreducibleMorphism (σ.obj (arTranslation σ D z).1)
        (σ.obj x) := by
  let AR := chosenRightAR σ D z
  let A := MinimalRightAlmostSplitDecomposition.ofMap σ
    AR.map AR.finiteLength AR.rightAlmostSplit AR.rightMinimal
  let B := MinimalLeftAlmostSplitDecomposition.ofMap σ
    (arKernelMap σ D z) AR.finiteLength
    (arKernelMap_leftAlmostSplit σ D z)
    (arKernelMap_leftMinimal σ D z)
  exact (A.summandIrreducibleCorrespondence x).symm.trans
    (B.summandIrreducibleCorrespondence x)

section Finite

variable [Fintype ι]

local instance : Finite σ.NonprojectiveLabel :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance : Finite σ.NoninjectiveLabel :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance : Fintype σ.NonprojectiveLabel := Fintype.ofFinite _
local instance : Fintype σ.NoninjectiveLabel := Fintype.ofFinite _

include D in
/-- The abstract boundary equivalence gives equality of the finite
nonprojective and noninjective complements. -/
theorem card_nonprojectiveLabel_eq_card_noninjectiveLabel :
    Fintype.card σ.NonprojectiveLabel =
      Fintype.card σ.NoninjectiveLabel := by
  classical
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  change Nat.card {i : ι // ¬ Projective (σ.obj i)} =
    Nat.card {i : ι // ¬ Injective (σ.obj i)}
  letI : Finite {i : ι // Projective (σ.obj i)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite {i : ι // Injective (σ.obj i)} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype {i : ι // Projective (σ.obj i)} := Fintype.ofFinite _
  letI : Fintype {i : ι // Injective (σ.obj i)} := Fintype.ofFinite _
  have hboundary :
      Fintype.card {i : ι // Projective (σ.obj i)} =
        Fintype.card {i : ι // Injective (σ.obj i)} :=
    Fintype.card_congr D.boundary
  have hcomplement := Fintype.card_compl_eq_card_compl
    (fun i : ι ↦ Projective (σ.obj i))
    (fun i : ι ↦ Injective (σ.obj i)) hboundary
  simpa only [← Nat.card_eq_fintype_card] using hcomplement

/-- Field-free AR translation is an equivalence between nonprojective and
noninjective labels. -/
def arTranslationEquiv :
    σ.NonprojectiveLabel ≃ σ.NoninjectiveLabel := by
  classical
  exact Equiv.ofBijective (arTranslation σ D)
    ((Fintype.bijective_iff_injective_and_card (arTranslation σ D)).2
      ⟨arTranslation_injective σ D,
        card_nonprojectiveLabel_eq_card_noninjectiveLabel σ D⟩)

/-- The kernel construction and surjectivity of AR translation supply a
minimal left almost-split decomposition at every noninjective vertex. -/
def chosenLeftAR (x : σ.NoninjectiveLabel) :
    σ.MinimalLeftAlmostSplitDecomposition x.1 := by
  let z : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  have hτ : arTranslationEquiv σ D z = x :=
    (arTranslationEquiv σ D).apply_symm_apply x
  have hval : (arTranslation σ D z).1 = x.1 :=
    congrArg Subtype.val hτ
  let e : σ.obj x.1 ≅ σ.obj (arTranslation σ D z).1 :=
    eqToIso (congrArg σ.obj hval.symm)
  let f : σ.obj x.1 ⟶ (chosenRightAR σ D z).middle :=
    e.hom ≫ arKernelMap σ D z
  exact MinimalLeftAlmostSplitDecomposition.ofMap σ f
    (chosenRightAR σ D z).finiteLength
    ((arKernelMap_leftAlmostSplit σ D z).precomp_iso e)
    ((arKernelMap_leftMinimal σ D z).precomp_iso e)

/-- The cokernel of the chosen left AR map is the representative at the
inverse AR-translation label. -/
def chosenLeftARCokernelIso (x : σ.NoninjectiveLabel) :
    cokernel (chosenLeftAR σ D x).map ≅
      σ.obj ((arTranslationEquiv σ D).symm x).1 := by
  let z : σ.NonprojectiveLabel := (arTranslationEquiv σ D).symm x
  let A := chosenRightAR σ D z
  letI : Epi A.map :=
    OpConjecture.IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      σ A.map A.rightAlmostSplit z.2
  let hTau : arTranslationEquiv σ D z = x :=
    (arTranslationEquiv σ D).apply_symm_apply x
  let hval : (arTranslation σ D z).1 = x.1 :=
    congrArg Subtype.val hTau
  let e : σ.obj x.1 ≅ σ.obj (arTranslation σ D z).1 :=
    eqToIso (congrArg σ.obj hval.symm)
  let j : σ.obj x.1 ≅ kernel A.map :=
    e.trans (arTranslationKernelIso σ D z).symm
  exact
    (cokernel.mapIso
      (chosenLeftAR σ D x).map (kernel.ι A.map)
      j (Iso.refl _) (by
        simp [chosenLeftAR, arKernelMap, z, A, e, j,
          MinimalLeftAlmostSplitDecomposition.ofMap])).trans
      (OpConjecture.cokernelKernelIsoTarget A.map)

/-- The field-free mesh-rotation datum constructed from the exact abstract
input. -/
def arMeshRotationData : σ.ARMeshRotationData where
  tau := arTranslationEquiv σ D
  incidence := by
    intro z x
    exact arTranslation_incidence σ D z x

include D in
/-- The categorical irreducible boundary-pair counts agree. -/
theorem natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair :
    Nat.card σ.QIrreducibleBoundaryPair =
      Nat.card σ.SIrreducibleBoundaryPair := by
  letI : DecidableEq ι := Classical.decEq ι
  exact
    ARMeshRotationData.natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair
      (σ := σ) (arMeshRotationData σ D)

include D in
/-- The manuscript's literal field-free radical-quotient boundary terms
satisfy `beta_q = beta_s`. -/
theorem
    natCard_QRadicalQuotientBoundaryPair_eq_natCard_SRadicalQuotientBoundaryPair :
    Nat.card σ.QRadicalQuotientBoundaryPair =
      Nat.card σ.SRadicalQuotientBoundaryPair := by
  calc
    Nat.card σ.QRadicalQuotientBoundaryPair =
        Nat.card σ.QIrreducibleBoundaryPair :=
      σ.natCard_QRadicalQuotientBoundaryPair_eq_natCard_QIrreducibleBoundaryPair
    _ = Nat.card σ.SIrreducibleBoundaryPair :=
      natCard_QIrreducibleBoundaryPair_eq_natCard_SIrreducibleBoundaryPair
        σ D
    _ = Nat.card σ.SRadicalQuotientBoundaryPair :=
      σ.natCard_SRadicalQuotientBoundaryPair_eq_natCard_SIrreducibleBoundaryPair.symm

end Finite

end FiniteARTranslationData

section ArtinDualityAdapter

universe u v

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  [IsNoetherianRing Rᵐᵒᵖ]
  {ι : Type v}
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

/-- The abstract Artin-duality interface supplies exactly the
projective--injective boundary field. -/
def FiniteARTranslationData.ofArtinDuality
    (A : OpConjecture.ArtinDuality.Data R)
    (rightAR : ∀ z : σ.NonprojectiveLabel,
      Nonempty (σ.MinimalRightAlmostSplitDecomposition z.1)) :
    σ.FiniteARTranslationData where
  rightAR_nonempty := rightAR
  boundary := by
    simpa [OpConjecture.RingelStable.projectiveSet,
      OpConjecture.RingelStable.injectiveSet] using
      OpConjecture.ArtinDuality.projectiveInjectiveLabelEquiv A σ

end ArtinDualityAdapter

end OpConjecture.IndecomposableSkeleton
