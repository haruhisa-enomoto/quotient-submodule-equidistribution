import OpConjecture.RepresentationTheory.NakayamaFixedTopChains
import OpConjecture.RepresentationTheory.LengthTwoContragredient
import OpConjecture.RepresentationTheory.OppositeDuality

/-!
# Fixed-socle chains by duality

An aligned anti-equivalence transports fixed-top quotient chains to
fixed-socle submodule chains.  Combining this transport with the general
fixed-top construction proves quotient/submodule level-polynomial equality
for any finite complete uniserial skeleton admitting an aligned biduality.
The final theorem instantiates that argument with finite-dimensional
contragredient duality for the canonical right-module skeleton.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.DualFixedSocleTransport

universe uR uS vR vS wR wS

variable
    {R : Type uR} [Ring R] [IsNoetherianRing R]
    {S : Type uS} [Ring S] [IsNoetherianRing S]
    {ι : Type vR} {κ : Type vS}
    (σ : IndecomposableSkeleton.{uR, vR, wR} R ι)
    (τ : IndecomposableSkeleton.{uS, vS, wS} S κ)
    (D : IndecomposableSkeleton.AlignedAntiEquivalence σ τ)

/-- An aligned anti-equivalence turns a source monomorphism into a target
epimorphism, with the direction reversed. -/
def dualMap {i j : ι} (f : σ.obj i ⟶ σ.obj j) :
    τ.obj (D.labelEquiv j) ⟶ τ.obj (D.labelEquiv i) :=
  (D.objIso j).inv ≫ D.categoryEquiv.functor.map f.op ≫ (D.objIso i).hom

instance dualMap_epi {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Mono f] :
    Epi (dualMap σ τ D f) := by
  dsimp [dualMap]
  infer_instance

/-- A target morphism in the reversed direction has a chosen source
preimage under the fully faithful functor underlying the equivalence. -/
def undualMap {i j : ι}
    (g : τ.obj (D.labelEquiv j) ⟶ τ.obj (D.labelEquiv i)) :
    σ.obj i ⟶ σ.obj j :=
  (D.categoryEquiv.functor.preimage
    ((D.objIso j).hom ≫ g ≫ (D.objIso i).inv)).unop

instance undualMap_mono {i j : ι}
    (g : τ.obj (D.labelEquiv j) ⟶ τ.obj (D.labelEquiv i)) [Epi g] :
    Mono (undualMap σ τ D g) := by
  let h := (D.objIso j).hom ≫ g ≫ (D.objIso i).inv
  haveI : Epi h := by
    dsimp [h]
    infer_instance
  haveI : Epi
      (D.categoryEquiv.functor.map
        (D.categoryEquiv.functor.preimage h)) := by
    rw [D.categoryEquiv.functor.map_preimage]
    infer_instance
  haveI : Epi (D.categoryEquiv.functor.preimage h) :=
    (D.categoryEquiv.functor.epi_map_iff_epi
      (D.categoryEquiv.functor.preimage h)).mp inferInstance
  change Mono
    (D.categoryEquiv.functor.preimage
      ((D.objIso j).hom ≫ g ≫ (D.objIso i).inv)).unop
  dsimp [h] at *
  infer_instance

/-- Existence of monomorphisms is exactly existence of epimorphisms after
applying an aligned anti-equivalence. -/
theorem exists_mono_iff_exists_epi {i j : ι} :
    (∃ f : σ.obj i ⟶ σ.obj j, Mono f) ↔
      ∃ g : τ.obj (D.labelEquiv j) ⟶ τ.obj (D.labelEquiv i), Epi g := by
  constructor
  · rintro ⟨f, hf⟩
    letI : Mono f := hf
    exact ⟨dualMap σ τ D f, inferInstance⟩
  · rintro ⟨g, hg⟩
    letI : Epi g := hg
    exact ⟨undualMap σ τ D g, inferInstance⟩

/-- Uniseriality is preserved by an aligned anti-equivalence. -/
theorem isUniserialModule_of_image
    (i : ι)
    (hi : IsUniserialModule S (τ.obj (D.labelEquiv i))) :
    IsUniserialModule R (σ.obj i) := by
  unfold IsUniserialModule at hi ⊢
  constructor
  intro U V
  let e :=
    OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.moduleSubobjectOrderIso
      σ τ D i
  rcases hi.total (e U) (e V) with hUV | hVU
  · right
    exact (e.le_iff_le).mp hUV
  · left
    exact (e.le_iff_le).mp hVU

universe x

/-- Fixed-top quotient chains on the target of an aligned
anti-equivalence become fixed-socle submodule chains on the source, with
the same capacities. -/
def fixedSocleChainDataOfFixedTop
    {χ : Type x} [Fintype χ] {c : χ → ℕ}
    (Q : OpConjecture.NakayamaModuleChains.FixedTopChainData τ c) :
    OpConjecture.NakayamaModuleChains.FixedSocleChainData σ c where
  labelEquiv := Q.labelEquiv.trans D.labelEquiv.symm
  uniserial i :=
    isUniserialModule_of_image σ τ D i
      (Q.uniserial (D.labelEquiv i))
  mono_iff i j := by
    rw [exists_mono_iff_exists_epi σ τ D]
    simpa using Q.epi_iff (D.labelEquiv j) (D.labelEquiv i)

/-- An aligned anti-equivalence restricts its label equivalence to the
simple representatives. -/
def simpleIndexEquiv : σ.SimpleIndex ≃ τ.SimpleIndex where
  toFun i := ⟨D.labelEquiv i.1, by
    rw [← τ.compositionLength_eq_one_iff_simple]
    rw [OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    exact (σ.compositionLength_eq_one_iff_simple i.1).2 i.2⟩
  invFun j := ⟨D.labelEquiv.symm j.1, by
    rw [← σ.compositionLength_eq_one_iff_simple]
    rw [← OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ D]
    simp only [Equiv.apply_symm_apply]
    exact (τ.compositionLength_eq_one_iff_simple j.1).2 j.2⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv j := by
    apply Subtype.ext
    simp

/-- A complete finite uniserial skeleton has equal quotient and submodule
level polynomials whenever it participates in an aligned biduality with a
complete opposite skeleton.  Fixed-top chains are constructed on both
sides; the target chains are then transported back as fixed-socle chains. -/
theorem levelPolynomial_eq_of_alignedBiduality
    {ι₀ : Type vR} {κ₀ : Type vS}
    [Finite ι₀] [Finite κ₀]
    (σ₀ : IndecomposableSkeleton.{uR, vR, uR} R ι₀)
    (τ₀ : IndecomposableSkeleton.{uS, vS, uS} S κ₀)
    (B : IndecomposableSkeleton.AlignedBiduality σ₀ τ₀)
    (hσ : ∀ i : ι₀, IsUniserialModule R (σ₀.obj i)) :
    σ₀.qClosure.levelPolynomial = σ₀.sClosure.levelPolynomial := by
  let hτ : ∀ j : κ₀, IsUniserialModule S (τ₀.obj j) := fun j ↦
    isUniserialModule_of_image τ₀ σ₀ B.backward j
      (hσ (B.backward.labelEquiv j))
  letI : Finite σ₀.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τ₀.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ₀.SimpleIndex := Fintype.ofFinite σ₀.SimpleIndex
  letI : Fintype τ₀.SimpleIndex := Fintype.ofFinite τ₀.SimpleIndex
  let Qσ :=
    OpConjecture.NakayamaFixedTopChains.fixedTopChainData σ₀ hσ
  let Qτ :=
    OpConjecture.NakayamaFixedTopChains.fixedTopChainData τ₀ hτ
  let Sσ := fixedSocleChainDataOfFixedTop σ₀ τ₀ B.forward Qτ
  apply
    OpConjecture.NakayamaModuleChains.quotient_levelPolynomial_eq_submodule_of_fixedChains
      σ₀ Qσ Sσ (simpleIndexEquiv σ₀ τ₀ B.forward)
  · intro p
    exact
      OpConjecture.NakayamaFixedTopChains.fixedTopLabel_compositionLength
        σ₀ hσ p
  · intro p
    change
      σ₀.compositionLength
          (B.forward.labelEquiv.symm (Qτ.labelEquiv p)) =
        (p.2 : ℕ) + 1
    rw [← OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ₀ τ₀ B.forward]
    simp only [Equiv.apply_symm_apply]
    exact
      OpConjecture.NakayamaFixedTopChains.fixedTopLabel_compositionLength
        τ₀ hτ p

universe z

/-- Paper-facing canonical-skeleton endpoint: representation-finiteness
and uniseriality of every indecomposable right module imply the strong
quotient/submodule level-polynomial equality. -/
theorem rightEquidistribution_of_all_indec_uniserial
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hA : IsRightRepresentationFinite.{z, z, z} K A)
    (hNakayama :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
      let σA := rightIndecomposableSkeleton.{z, z, z} K A
      ∀ i, IsUniserialModule Aᵐᵒᵖ (σA.obj i)) :
    RightQuotientSubmoduleEquidistribution K A hA := by
  have hAop : IsRightRepresentationFinite.{z, z, z} K Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff K A).mp hA
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA := rightIndecomposableSkeleton.{z, z, z} K A
  let τA := rightIndecomposableSkeleton.{z, z, z} K Aᵐᵒᵖ
  change σA.qClosure.levelPolynomial = σA.sClosure.levelPolynomial
  exact
    levelPolynomial_eq_of_alignedBiduality σA τA
      (rightOppositeAlignedBiduality K A) hNakayama

end OpConjecture.DualFixedSocleTransport
