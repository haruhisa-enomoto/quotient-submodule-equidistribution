import OpConjecture.RepresentationTheory.NakayamaRepresentationFiniteBridge

/-!
# Exact Nakayama product formula

The general fixed-top construction identifies the actual quotient level
polynomial with the product of the geometric chain factors determined by the
lengths of the chosen indecomposable projective covers.  Aligned biduality
makes the submodule polynomial equal to the same product, and the final
endpoint specializes this statement to the canonical right-module skeleton.
-/

noncomputable section

open scoped BigOperators

namespace OpConjecture.NakayamaProductFormula

universe u v

open OpConjecture.NakayamaModuleChains

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]

/-- The product of the geometric chain factors indexed by the simple tops
of a finite complete skeleton. -/
noncomputable def fixedTopChainPolynomial
    (σ : IndecomposableSkeleton.{u, v, u} R ι) : Polynomial ℕ := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  exact
    ∏ j : σ.SimpleIndex,
      NakayamaCombinatorics.chainPolynomial
        (NakayamaFixedTopChains.fixedTopCapacity σ j)

/-- Under the all-indecomposables-uniserial hypothesis, the actual quotient
level polynomial is the product indexed by the lengths of the selected
indecomposable projective covers. -/
theorem quotient_levelPolynomial_eq_fixedTopChainPolynomial
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    σ.qClosure.levelPolynomial = fixedTopChainPolynomial σ := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  let Q := NakayamaFixedTopChains.fixedTopChainData σ hσ
  calc
    σ.qClosure.levelPolynomial =
        NakayamaCombinatorics.capacityPolynomial
          (NakayamaFixedTopChains.fixedTopCapacity σ) :=
      Q.quotient_levelPolynomial_eq_capacityPolynomial
    _ = ∏ j : σ.SimpleIndex,
          NakayamaCombinatorics.chainPolynomial
            (NakayamaFixedTopChains.fixedTopCapacity σ j) :=
      NakayamaCombinatorics.capacityPolynomial_eq_prod_chainPolynomial _
    _ = fixedTopChainPolynomial σ := by
      rfl

/-- The actual quotient-closed-set lattice is the product of the fixed-top
capacity chains. -/
noncomputable def quotientClosedsOrderIso
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    NakayamaCombinatorics.CapacityVector
        (NakayamaFixedTopChains.fixedTopCapacity σ) ≃o
      σ.qClosure.Closeds := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  exact
    NakayamaCombinatorics.chainClosedOrderIso.trans
      (NakayamaFixedTopChains.fixedTopChainData σ hσ).relabeling.closedsOrderIso

variable {S : Type u} [Ring S] [IsNoetherianRing S]
  {κ : Type v} [Finite κ]

/-- With an aligned biduality, both actual level polynomials equal the same
fixed-top projective-length product. -/
theorem levelPolynomials_eq_fixedTopChainPolynomial_of_alignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    σ.qClosure.levelPolynomial = fixedTopChainPolynomial σ ∧
      σ.sClosure.levelPolynomial = fixedTopChainPolynomial σ := by
  have hq := quotient_levelPolynomial_eq_fixedTopChainPolynomial σ hσ
  have hqs :=
    DualFixedSocleTransport.levelPolynomial_eq_of_alignedBiduality
      σ τ B hσ
  exact ⟨hq, hqs.symm.trans hq⟩

/-- The actual submodule-closed-set lattice is the product of the fixed-top
capacity chains on the opposite side of an aligned biduality. -/
noncomputable def submoduleClosedsOrderIsoOfAlignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    NakayamaCombinatorics.CapacityVector
        (NakayamaFixedTopChains.fixedTopCapacity τ) ≃o
      σ.sClosure.Closeds := by
  let hτ : ∀ j : κ, IsUniserialModule S (τ.obj j) := fun j ↦
    DualFixedSocleTransport.isUniserialModule_of_image
      τ σ B.backward j (hσ (B.backward.labelEquiv j))
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  let Qτ := NakayamaFixedTopChains.fixedTopChainData τ hτ
  let Sσ :=
    DualFixedSocleTransport.fixedSocleChainDataOfFixedTop
      σ τ B.forward Qτ
  exact
    NakayamaCombinatorics.chainClosedOrderIso.trans
      Sσ.relabeling.closedsOrderIso

/-- The fixed-top projective capacities on the two sides of an aligned
biduality have the same multiset.  On the source these are the fixed-top
chain lengths; after transport from the target they are the fixed-socle
chain lengths. -/
theorem fixedTopCapacityMultiset_eq_of_alignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    letI : Finite σ.SimpleIndex :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Finite τ.SimpleIndex :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
    letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
    NakayamaCombinatorics.capacityMultiset
        (NakayamaFixedTopChains.fixedTopCapacity σ) =
      NakayamaCombinatorics.capacityMultiset
        (NakayamaFixedTopChains.fixedTopCapacity τ) := by
  let hτ : ∀ j : κ, IsUniserialModule S (τ.obj j) := fun j ↦
    DualFixedSocleTransport.isUniserialModule_of_image
      τ σ B.backward j (hσ (B.backward.labelEquiv j))
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  let Qσ := NakayamaFixedTopChains.fixedTopChainData σ hσ
  let Qτ := NakayamaFixedTopChains.fixedTopChainData τ hτ
  let Sσ :=
    DualFixedSocleTransport.fixedSocleChainDataOfFixedTop
      σ τ B.forward Qτ
  apply NakayamaCombinatorics.capacityMultiset_eq_of_atLeastCount_eq
  apply capacityAtLeastCount_eq_of_labelLength
    Qσ.labelEquiv Sσ.labelEquiv
    (DualFixedSocleTransport.simpleIndexEquiv σ τ B.forward)
    σ.compositionLength
  · intro p
    exact
      NakayamaFixedTopChains.fixedTopLabel_compositionLength
        σ hσ p
  · intro p
    change
      σ.compositionLength
          (B.forward.labelEquiv.symm (Qτ.labelEquiv p)) =
        (p.2 : ℕ) + 1
    rw [← OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
      σ τ B.forward]
    simp only [Equiv.apply_symm_apply]
    exact
      NakayamaFixedTopChains.fixedTopLabel_compositionLength
        τ hτ p

/-- Matching the equal capacity multisets gives an explicit order
isomorphism between the actual quotient- and submodule-closed-set lattices. -/
noncomputable def quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i)) :
    σ.qClosure.Closeds ≃o σ.sClosure.Closeds := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  exact
    (quotientClosedsOrderIso σ hσ).symm.trans
      ((NakayamaCombinatorics.capacityVectorOrderIsoOfMultisetEq
          (NakayamaFixedTopChains.fixedTopCapacity σ)
          (NakayamaFixedTopChains.fixedTopCapacity τ)
          (fixedTopCapacityMultiset_eq_of_alignedBiduality
            σ τ B hσ)).trans
        (submoduleClosedsOrderIsoOfAlignedBiduality σ τ B hσ))

/-- The quotient-chain parametrization records closed-set cardinality as
the capacity-vector grading. -/
theorem ncard_quotientClosedsOrderIso
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (x : NakayamaCombinatorics.CapacityVector
      (NakayamaFixedTopChains.fixedTopCapacity σ)) :
    letI : Finite σ.SimpleIndex :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
    (((quotientClosedsOrderIso σ hσ x :
      σ.qClosure.Closeds) : Set ι)).ncard =
      NakayamaCombinatorics.capacityWeight x := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  change
    (((NakayamaFixedTopChains.fixedTopChainData σ hσ).relabeling.closedsOrderIso
      (NakayamaCombinatorics.chainClosedOrderIso x) :
        σ.qClosure.Closeds) : Set ι).ncard = _
  rw [SetClosure.RelabelingEquiv.ncard_closedsOrderIso_apply]
  change (NakayamaCombinatorics.initialSegment x).ncard = _
  exact NakayamaCombinatorics.ncard_initialSegment x

omit [Finite ι] in
/-- The transported fixed-socle parametrization records cardinality by the
opposite-side capacity-vector grading. -/
theorem ncard_submoduleClosedsOrderIsoOfAlignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (x : NakayamaCombinatorics.CapacityVector
      (NakayamaFixedTopChains.fixedTopCapacity τ)) :
    letI : Finite τ.SimpleIndex :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
    (((submoduleClosedsOrderIsoOfAlignedBiduality σ τ B hσ x :
      σ.sClosure.Closeds) : Set ι)).ncard =
      NakayamaCombinatorics.capacityWeight x := by
  let hτ : ∀ j : κ, IsUniserialModule S (τ.obj j) := fun j ↦
    DualFixedSocleTransport.isUniserialModule_of_image
      τ σ B.backward j (hσ (B.backward.labelEquiv j))
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  let Qτ := NakayamaFixedTopChains.fixedTopChainData τ hτ
  let Sσ :=
    DualFixedSocleTransport.fixedSocleChainDataOfFixedTop
      σ τ B.forward Qτ
  change
    ((Sσ.relabeling.closedsOrderIso
      (NakayamaCombinatorics.chainClosedOrderIso x) :
        σ.sClosure.Closeds) : Set ι).ncard = _
  rw [SetClosure.RelabelingEquiv.ncard_closedsOrderIso_apply]
  change (NakayamaCombinatorics.initialSegment x).ncard = _
  exact NakayamaCombinatorics.ncard_initialSegment x

/-- The quotient--submodule lattice isomorphism furnished by aligned
biduality is graded: it preserves the number of indecomposable labels in
every closed set. -/
theorem ncard_quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
    (σ : IndecomposableSkeleton.{u, v, u} R ι)
    (τ : IndecomposableSkeleton.{u, v, u} S κ)
    (B : IndecomposableSkeleton.AlignedBiduality σ τ)
    (hσ : ∀ i : ι, IsUniserialModule R (σ.obj i))
    (C : σ.qClosure.Closeds) :
    (((quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σ τ B hσ C : σ.sClosure.Closeds) : Set ι)).ncard =
      (C : Set ι).ncard := by
  letI : Finite σ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite τ.SimpleIndex :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype σ.SimpleIndex := Fintype.ofFinite σ.SimpleIndex
  letI : Fintype τ.SimpleIndex := Fintype.ofFinite τ.SimpleIndex
  let cσ := NakayamaFixedTopChains.fixedTopCapacity σ
  let cτ := NakayamaFixedTopChains.fixedTopCapacity τ
  let Q := quotientClosedsOrderIso σ hσ
  let P := NakayamaCombinatorics.capacityVectorOrderIsoOfMultisetEq
    cσ cτ (fixedTopCapacityMultiset_eq_of_alignedBiduality σ τ B hσ)
  let T := submoduleClosedsOrderIsoOfAlignedBiduality σ τ B hσ
  change (((T (P (Q.symm C)) : σ.sClosure.Closeds) : Set ι)).ncard = _
  calc
    (((T (P (Q.symm C)) : σ.sClosure.Closeds) : Set ι)).ncard =
        NakayamaCombinatorics.capacityWeight (P (Q.symm C)) :=
      ncard_submoduleClosedsOrderIsoOfAlignedBiduality
        σ τ B hσ (P (Q.symm C))
    _ = NakayamaCombinatorics.capacityWeight (Q.symm C) :=
      NakayamaCombinatorics.capacityWeight_capacityVectorOrderIsoOfMultisetEq
        cσ cτ
        (fixedTopCapacityMultiset_eq_of_alignedBiduality σ τ B hσ)
        (Q.symm C)
    _ = (((Q (Q.symm C) : σ.qClosure.Closeds) : Set ι)).ncard :=
      (ncard_quotientClosedsOrderIso σ hσ (Q.symm C)).symm
    _ = (C : Set ι).ncard := by
      rw [Q.apply_symm_apply]

universe z

/-- Canonical right-module form of the exact Nakayama product formula. -/
theorem rightLevelPolynomials_eq_fixedTopChainPolynomial
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
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
    let σA := rightIndecomposableSkeleton.{z, z, z} K A
    σA.qClosure.levelPolynomial = fixedTopChainPolynomial σA ∧
      σA.sClosure.levelPolynomial = fixedTopChainPolynomial σA := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
  have hAop : IsRightRepresentationFinite.{z, z, z} K Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA := rightIndecomposableSkeleton.{z, z, z} K A
  let τA := rightIndecomposableSkeleton.{z, z, z} K Aᵐᵒᵖ
  exact
    levelPolynomials_eq_fixedTopChainPolynomial_of_alignedBiduality
      σA τA (rightOppositeAlignedBiduality K A) hNakayama

/-- Canonical right-module form of the product-of-chains order
isomorphism. -/
noncomputable def rightQuotientSubmoduleClosedsOrderIso
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
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
    let σA := rightIndecomposableSkeleton.{z, z, z} K A
    σA.qClosure.Closeds ≃o σA.sClosure.Closeds := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
  have hAop : IsRightRepresentationFinite.{z, z, z} K Aᵐᵒᵖ :=
    (rightRepresentationFinite_op_iff K A).mp hA
  letI : Finite
      (CanonicalIndecomposableIndex.{z, z} (Aᵐᵒᵖ)ᵐᵒᵖ) := hAop
  let σA := rightIndecomposableSkeleton.{z, z, z} K A
  let τA := rightIndecomposableSkeleton.{z, z, z} K Aᵐᵒᵖ
  exact
    quotientSubmoduleClosedsOrderIsoOfAlignedBiduality
      σA τA (rightOppositeAlignedBiduality K A) hNakayama

/-- The all-indecomposable-right-modules-uniserial formulation supplies both
the required representation-finiteness witness and the exact common product
formula. -/
theorem exists_rightLevelPolynomials_eq_fixedTopChainPolynomial
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      let σA := rightIndecomposableSkeleton.{z, z, z} K A
      LocalNakayamaBranch.IsNakayamaSkeleton σA) :
    ∃ hA : IsRightRepresentationFinite.{z, z, z} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
      let σA := rightIndecomposableSkeleton.{z, z, z} K A
      σA.qClosure.levelPolynomial = fixedTopChainPolynomial σA ∧
        σA.sClosure.levelPolynomial = fixedTopChainPolynomial σA := by
  let hA : IsRightRepresentationFinite.{z, z, z} K A :=
    NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hNakayama
  refine ⟨hA, ?_⟩
  apply rightLevelPolynomials_eq_fixedTopChainPolynomial K A hA
  exact hNakayama

/-- The all-indecomposable-right-modules-uniserial formulation also supplies
an actual order isomorphism between the two closed-set lattices. -/
theorem exists_rightQuotientSubmoduleClosedsOrderIso
    (K A : Type z)
    [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hNakayama :
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      let σA := rightIndecomposableSkeleton.{z, z, z} K A
      LocalNakayamaBranch.IsNakayamaSkeleton σA) :
    ∃ hA : IsRightRepresentationFinite.{z, z, z} K A,
      letI : IsNoetherianRing Aᵐᵒᵖ :=
        isNoetherianRing_op_of_finiteDimensional K A
      letI : Finite
          (CanonicalIndecomposableIndex.{z, z} Aᵐᵒᵖ) := hA
      let σA := rightIndecomposableSkeleton.{z, z, z} K A
      Nonempty (σA.qClosure.Closeds ≃o σA.sClosure.Closeds) := by
  let hA : IsRightRepresentationFinite.{z, z, z} K A :=
    NakayamaRepresentationFiniteBridge.rightRepresentationFinite_of_all_indec_uniserial
      K A hNakayama
  refine ⟨hA, ⟨?_⟩⟩
  exact rightQuotientSubmoduleClosedsOrderIso K A hA hNakayama

end OpConjecture.NakayamaProductFormula
