import OpConjecture.RepresentationTheory.FourVertexReversePacketTransport
import OpConjecture.RepresentationTheory.ReverseARPacketStructures

/-!
# Source coordinates for the reverse four-packet families

The reverse packet types used by the final cardinality identity are quotient
packet types on the aligned dual skeleton.  Here they are replaced by
equivalent types whose packet data live on the original skeleton.  The base
support is retained as a dual rooted four-support, while its deleted labels
are pulled back through the aligned label equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {k R S : Type u} [Field k] [IsAlgClosed k]
  [Ring R] [Algebra k R] [FiniteDimensional k R]
  [Ring S] [Algebra k S] [FiniteDimensional k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
  [DecidableEq ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)
  (τ : IndecomposableSkeleton.{u, w, u} S κ)
  (D : AlignedBiduality σ τ)

/-- The source deleted support underlying a rooted support on the aligned
dual skeleton. -/
def sourceDeletedOfDualRooted
    (Q : QuotientRootedFour τ) : Finset ι :=
  D.forward.labelEquiv.finsetCongr.symm Q.1

namespace AlignedBiduality

omit [Fintype ι] [DecidableEq ι] in
/-- The image of the source kept set attached to a dual rooted support is
the dual kept set itself. -/
theorem image_sourceDeleted_compl_eq
    (Q : QuotientRootedFour τ) :
    D.forward.labelEquiv ''
        (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ) =
      (((Q.1 : Finset κ) : Set κ)ᶜ) := by
  have h := D.image_compl_eq_dualDeleted_compl σ τ
    (sourceDeletedOfDualRooted σ τ D Q)
  have hDeleted :
      D.dualDeleted σ τ (sourceDeletedOfDualRooted σ τ D Q) = Q.1 := by
    change D.forward.labelEquiv.finsetCongr
      (D.forward.labelEquiv.finsetCongr.symm Q.1) = Q.1
    exact D.forward.labelEquiv.finsetCongr.apply_symm_apply Q.1
  simpa only [hDeleted] using h

/-- Fiberwise conversion of an admissible hook on a dual rooted support to
the source-coordinate reverse hook. -/
def admissibleHookOnDualRootedEquivReverse
    (Q : QuotientRootedFour τ) :
    (τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ
        (((Q.1 : Finset κ) : Set κ)ᶜ) ≃
      (σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
        (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ) := by
  let K : Set ι :=
    (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)
  let hK : D.forward.labelEquiv '' K =
      (((Q.1 : Finset κ) : Set κ)ᶜ) :=
    D.image_sourceDeleted_compl_eq σ τ Q
  exact (Equiv.cast (congrArg
      ((τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ)
      hK).symm).trans
    (D.admissibleHookEquivReverse σ τ
      (σ.finiteDimensionalARTranslationData k R)
      (τ.finiteDimensionalARTranslationData k S) K)

/-- Fiberwise conversion of row `F` on a dual rooted support. -/
def fixedPacketOnDualRootedEquivReverse
    (Q : QuotientRootedFour τ) :
    (τ.finiteDimensionalARTranslationData k S).FixedPacket τ
        (((Q.1 : Finset κ) : Set κ)ᶜ) ≃
      (σ.finiteDimensionalARTranslationData k R).ReverseFixedPacket σ
        (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ) := by
  let K : Set ι :=
    (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)
  let hK : D.forward.labelEquiv '' K =
      (((Q.1 : Finset κ) : Set κ)ᶜ) :=
    D.image_sourceDeleted_compl_eq σ τ Q
  exact (Equiv.cast (congrArg
      ((τ.finiteDimensionalARTranslationData k S).FixedPacket τ)
      hK).symm).trans
    (D.fixedPacketEquivReverse σ τ
      (σ.finiteDimensionalARTranslationData k R)
      (τ.finiteDimensionalARTranslationData k S) K)

/-- Fiberwise conversion of row `T` on a dual rooted support. -/
def trianglePacketOnDualRootedEquivReverse
    (Q : QuotientRootedFour τ) :
    (τ.finiteDimensionalARTranslationData k S).TrianglePacket τ
        (((Q.1 : Finset κ) : Set κ)ᶜ) ≃
      (σ.finiteDimensionalARTranslationData k R).ReverseTrianglePacket σ
        (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ) := by
  let K : Set ι :=
    (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)
  let hK : D.forward.labelEquiv '' K =
      (((Q.1 : Finset κ) : Set κ)ᶜ) :=
    D.image_sourceDeleted_compl_eq σ τ Q
  exact (Equiv.cast (congrArg
      ((τ.finiteDimensionalARTranslationData k S).TrianglePacket τ)
      hK).symm).trans
    (D.trianglePacketEquivReverse σ τ
      (σ.finiteDimensionalARTranslationData k R)
      (τ.finiteDimensionalARTranslationData k S) K)

end AlignedBiduality

/-- Hook occurrences on the reverse side, with packet labels pulled back to
the source skeleton. -/
abbrev SourceReverseHookOccurrenceFour : Type (max v w) :=
  Σ Q : QuotientRootedFour τ,
    (σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
      (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)

/-- Reverse double-hook supports in source packet coordinates. -/
abbrev SourceReverseDoubleHookFour : Type w :=
  {Q : QuotientRootedFour τ //
    Nontrivial
      ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
        (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ))}

/-- Reverse row-`F` supports in source packet coordinates. -/
abbrev SourceReverseFixedPacketFour : Type w :=
  {Q : QuotientRootedFour τ //
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).ReverseFixedPacket σ
          (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)) ∧
      IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ))}

/-- Reverse row-`T` supports in source packet coordinates. -/
abbrev SourceReverseTrianglePacketFour : Type w :=
  {Q : QuotientRootedFour τ //
    Nonempty
        ((σ.finiteDimensionalARTranslationData k R).ReverseTrianglePacket σ
          (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ)) ∧
      IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q : Finset ι) : Set ι)ᶜ))}

noncomputable instance sourceReverseHookOccurrenceFourFintype :
    Fintype (SourceReverseHookOccurrenceFour
      (k := k) (R := R) σ τ D) := Fintype.ofFinite _

noncomputable instance sourceReverseDoubleHookFourFintype :
    Fintype (SourceReverseDoubleHookFour
      (k := k) (R := R) σ τ D) := Fintype.ofFinite _

noncomputable instance sourceReverseFixedPacketFourFintype :
    Fintype (SourceReverseFixedPacketFour
      (k := k) (R := R) σ τ D) := Fintype.ofFinite _

noncomputable instance sourceReverseTrianglePacketFourFintype :
    Fintype (SourceReverseTrianglePacketFour
      (k := k) (R := R) σ τ D) := Fintype.ofFinite _

/-- The actual reverse hook-occurrence type is equivalent to the same
family written on source labels. -/
def submoduleHookOccurrenceFourEquivSourceReverse :
    SubmoduleHookOccurrenceFour (k := k) (S := S) τ ≃
      SourceReverseHookOccurrenceFour
        (k := k) (R := R) σ τ D :=
  Equiv.sigmaCongr (Equiv.refl _) fun Q ↦
    D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q

/-- The actual reverse double-hook support type in source coordinates. -/
def submoduleDoubleHookFourEquivSourceReverse :
    SubmoduleDoubleHookFour (k := k) (S := S) τ ≃
      SourceReverseDoubleHookFour
        (k := k) (R := R) σ τ D where
  toFun Q := by
    let E := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    letI : Nontrivial
        ((τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ
          (((Q.1.1 : Finset κ) : Set κ)ᶜ)) := Q.2
    letI : Nontrivial
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ)) :=
      E.injective.nontrivial
    exact ⟨Q.1, inferInstance⟩
  invFun Q := by
    let E := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    letI : Nontrivial
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ)) :=
      Q.2
    letI : Nontrivial
        ((τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ
          (((Q.1.1 : Finset κ) : Set κ)ᶜ)) :=
      E.symm.injective.nontrivial
    exact ⟨Q.1, inferInstance⟩
  left_inv Q := by rfl
  right_inv Q := by rfl

/-- The actual reverse fixed-packet support type in source coordinates. -/
def submoduleFixedPacketFourEquivSourceReverse :
    SubmoduleFixedPacketFour (k := k) (S := S) τ ≃
      SourceReverseFixedPacketFour
        (k := k) (R := R) σ τ D where
  toFun Q := by
    let EF := D.fixedPacketOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let EH := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let hEmpty : IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ)) :=
      ⟨fun H ↦ @IsEmpty.false _ Q.2.2 (EH.symm H)⟩
    exact ⟨Q.1, Nonempty.map EF Q.2.1, hEmpty⟩
  invFun Q := by
    let EF := D.fixedPacketOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let EH := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let hEmpty : IsEmpty
        ((τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ
          (((Q.1.1 : Finset κ) : Set κ)ᶜ)) :=
      ⟨fun H ↦ @IsEmpty.false _ Q.2.2 (EH H)⟩
    exact ⟨Q.1, Nonempty.map EF.symm Q.2.1, hEmpty⟩
  left_inv Q := by rfl
  right_inv Q := by rfl

/-- The actual reverse triangle-packet support type in source coordinates. -/
def submoduleTrianglePacketFourEquivSourceReverse :
    SubmoduleTrianglePacketFour (k := k) (S := S) τ ≃
      SourceReverseTrianglePacketFour
        (k := k) (R := R) σ τ D where
  toFun Q := by
    let ET := D.trianglePacketOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let EH := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let hEmpty : IsEmpty
        ((σ.finiteDimensionalARTranslationData k R).ReverseAdmissibleHook σ
          (((sourceDeletedOfDualRooted σ τ D Q.1 : Finset ι) : Set ι)ᶜ)) :=
      ⟨fun H ↦ @IsEmpty.false _ Q.2.2 (EH.symm H)⟩
    exact ⟨Q.1, Nonempty.map ET Q.2.1, hEmpty⟩
  invFun Q := by
    let ET := D.trianglePacketOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let EH := D.admissibleHookOnDualRootedEquivReverse
      (k := k) (R := R) (S := S) σ τ Q.1
    let hEmpty : IsEmpty
        ((τ.finiteDimensionalARTranslationData k S).AdmissibleHook τ
          (((Q.1.1 : Finset κ) : Set κ)ᶜ)) :=
      ⟨fun H ↦ @IsEmpty.false _ Q.2.2 (EH H)⟩
    exact ⟨Q.1, Nonempty.map ET.symm Q.2.1, hEmpty⟩
  left_inv Q := by rfl
  right_inv Q := by rfl

end OpConjecture.IndecomposableSkeleton
