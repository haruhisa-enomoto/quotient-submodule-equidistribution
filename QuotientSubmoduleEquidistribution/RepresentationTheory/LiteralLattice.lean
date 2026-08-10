import Mathlib.Tactic
import Mathlib.Order.Hom.CompleteLattice
import QuotientSubmoduleEquidistribution.RepresentationTheory.AdditiveSubcategory
import QuotientSubmoduleEquidistribution.RepresentationTheory.ConvexStructure

/-!
# Literal additive-subcategory lattice transport

This file transports the complete lattices of `qClosure.Closeds` and
`sClosure.Closeds` across the exact support order isomorphisms.
-/

noncomputable section

open Set
open CategoryTheory

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

/-- Pull a complete-lattice structure backwards across an order isomorphism. -/
noncomputable abbrev completeLatticeOfOrderIso
    {A B : Type*} [PartialOrder A] [CompleteLattice B]
    (e : A ≃o B) : CompleteLattice A :=
  e.symm.toGaloisInsertion.liftCompleteLattice

/-- The quotient-closed literal additive subcategories carry a complete
lattice transported from quotient-closed indecomposable supports.

This is deliberately a named structure rather than a global instance:
the literal subtype mentions `R` but not the chosen skeleton `σ`, so typeclass
search cannot recover which support equivalence should provide the structure. -/
noncomputable abbrev quotientClosedCompleteLattice :
    CompleteLattice (QuotientClosedAdditiveSubcategory (R := R)) :=
  completeLatticeOfOrderIso σ.quotientClosedSupportOrderIso

/-- The analogous named complete lattice on subobject-closed literal
additive subcategories. -/
noncomputable abbrev subobjectClosedCompleteLattice :
    CompleteLattice (SubobjectClosedAdditiveSubcategory (R := R)) :=
  completeLatticeOfOrderIso σ.subobjectClosedSupportOrderIso

namespace Transport

section Compact

variable {A B : Type*} [PartialOrder A] [PartialOrder B]

/-- Compactness is invariant under an order isomorphism.  This formulation
uses the order-theoretic definition of `IsCompactElement`, so no lattice
operations need to be compared. -/
theorem isCompactElement_map (e : A ≃o B) {a : A}
    (ha : IsCompactElement a) :
    IsCompactElement (e a) := by
  intro S u hS hdir hLUB hau
  have hpre_nonempty : (e.symm '' S).Nonempty :=
    hS.image e.symm
  have hpre_directed : DirectedOn (· ≤ ·) (e.symm '' S) := by
    rintro _ ⟨x, hxS, rfl⟩ _ ⟨y, hyS, rfl⟩
    obtain ⟨z, hzS, hxz, hyz⟩ := hdir x hxS y hyS
    exact ⟨e.symm z, ⟨z, hzS, rfl⟩,
      e.symm.monotone hxz, e.symm.monotone hyz⟩
  have hpre_lub :
      IsLUB (e.symm '' S) (e.symm u) :=
    e.symm.isLUB_image'.2 hLUB
  have hau' : a ≤ e.symm u := by
    exact e.le_symm_apply.mpr hau
  obtain ⟨x, hxpre, hax⟩ :=
    ha (e.symm '' S) (e.symm u)
      hpre_nonempty hpre_directed hpre_lub hau'
  obtain ⟨y, hyS, rfl⟩ := hxpre
  exact ⟨y, hyS, e.le_symm_apply.mp hax⟩

theorem isCompactElement_iff (e : A ≃o B) (a : A) :
    IsCompactElement a ↔ IsCompactElement (e a) :=
  ⟨isCompactElement_map e,
    fun h ↦ by
      simpa using isCompactElement_map e.symm h⟩

end Compact

section CompletelyJoinIrreducible

variable {A B : Type*} [CompleteLattice A] [CompleteLattice B]

/-- Complete join-irreducibility is invariant under a complete-lattice
order isomorphism. -/
theorem isCompletelyJoinIrreducible_map (e : A ≃o B) {a : A}
    (ha : QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible a) :
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible (e a) := by
  intro S hS
  let T : Set A := e.symm '' S
  have hT_lub :
      IsLUB T (e.symm (sSup S)) :=
    e.symm.isLUB_image'.2 (isLUB_sSup S)
  have hT :
      sSup T = a := by
    calc
      sSup T = e.symm (sSup S) :=
        (isLUB_sSup T).unique hT_lub
      _ = a := by rw [hS]; simp
  have haT : a ∈ T := ha T hT
  obtain ⟨b, hbS, hba⟩ := haT
  have : b = e a := by
    apply e.symm.injective
    simpa using hba
  simpa [this] using hbS

theorem isCompletelyJoinIrreducible_iff (e : A ≃o B) (a : A) :
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible a ↔
      QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible (e a) :=
  ⟨isCompletelyJoinIrreducible_map e,
    fun h ↦ by
      simpa using isCompletelyJoinIrreducible_map e.symm h⟩

end CompletelyJoinIrreducible

end Transport

namespace QuotientLattice

/-- The literal objectwise intersection of quotient-closed additive
subcategories. -/
def intersection {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R)) :
    QuotientClosedAdditiveSubcategory (R := R) where
  val :=
    { carrier := fun X ↦ ∀ k, (C k).1.carrier X
      biproduct_mem := by
        intro J F hF k
        exact (C k).1.biproduct_mem J F (fun j ↦ hF j k)
      retract_mem := by
        intro X Y r hY k
        exact (C k).1.retract_mem r (hY k) }
  property := by
    constructor
    intro X Y f _ hX k
    letI : (C k).1.carrier.IsClosedUnderQuotients := (C k).2
    exact (C k).1.carrier.prop_of_epi f (hX k)

/-- The literal quotient-closed subcategory corresponding to the closure
of one indecomposable representative. -/
def pointGenerated (i : ι) :
    QuotientClosedAdditiveSubcategory (R := R) :=
  σ.quotientClosedSupportOrderIso.symm
    (σ.qClosure.pointClosure i)

@[simp]
theorem support_pointGenerated (i : ι) :
    σ.support (pointGenerated σ i).1 =
      σ.qClosure ({i} : Set ι) := by
  change
    ((σ.quotientClosedSupportOrderIso
      (σ.quotientClosedSupportOrderIso.symm
        (σ.qClosure.pointClosure i)) :
      σ.qClosure.Closeds) : Set ι) =
      σ.qClosure ({i} : Set ι)
  rw [σ.quotientClosedSupportOrderIso.apply_symm_apply]
  rfl

/-- The support equivalence, viewed as a complete-lattice homomorphism. -/
noncomputable def supportCompleteLatticeHom :
    let _ := quotientClosedCompleteLattice σ
    CompleteLatticeHom
        (QuotientClosedAdditiveSubcategory (R := R))
        σ.qClosure.Closeds :=
  by
    letI := quotientClosedCompleteLattice σ
    exact CompleteLatticeHom.OrderIso.toCompleteLatticeHom
      σ.quotientClosedSupportOrderIso

/-- Its inverse complete-lattice homomorphism. -/
noncomputable def generatedCompleteLatticeHom :
    let _ := quotientClosedCompleteLattice σ
    CompleteLatticeHom
        σ.qClosure.Closeds
        (QuotientClosedAdditiveSubcategory (R := R)) :=
  by
    letI := quotientClosedCompleteLattice σ
    exact CompleteLatticeHom.OrderIso.toCompleteLatticeHom
      σ.quotientClosedSupportOrderIso.symm

theorem support_inf
    (C D : QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    σ.support ((C ⊓ D).1) =
        σ.support C.1 ∩ σ.support D.1 := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso (C ⊓ D) :
        σ.qClosure.Closeds) : Set ι) =
      σ.support C.1 ∩ σ.support D.1
  rw [σ.quotientClosedSupportOrderIso.map_inf]
  rfl

theorem support_sup
    (C D : QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    σ.support ((C ⊔ D).1) =
        σ.qClosure (σ.support C.1 ∪ σ.support D.1) := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso (C ⊔ D) :
        σ.qClosure.Closeds) : Set ι) =
      σ.qClosure (σ.support C.1 ∪ σ.support D.1)
  rw [σ.quotientClosedSupportOrderIso.map_sup]
  rfl

theorem support_bot :
    let _ := quotientClosedCompleteLattice σ
    σ.support
        ((⊥ : QuotientClosedAdditiveSubcategory (R := R)).1) =
      σ.qClosure ∅ := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso ⊥ :
        σ.qClosure.Closeds) : Set ι) =
      σ.qClosure ∅
  rw [σ.quotientClosedSupportOrderIso.map_bot]
  rfl

theorem support_top :
    let _ := quotientClosedCompleteLattice σ
    σ.support
        ((⊤ : QuotientClosedAdditiveSubcategory (R := R)).1) =
      Set.univ := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso ⊤ :
        σ.qClosure.Closeds) : Set ι) =
      Set.univ
  rw [σ.quotientClosedSupportOrderIso.map_top]
  rfl

theorem support_iInf {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    σ.support ((⨅ k, C k).1) =
        ⋂ k, σ.support (C k).1 := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso (⨅ k, C k) :
        σ.qClosure.Closeds) : Set ι) =
      ⋂ k, σ.support (C k).1
  rw [σ.quotientClosedSupportOrderIso.map_iInf]
  exact QuotientSubmoduleEquidistribution.SetClosure.coe_iInf _

theorem support_iSup {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    σ.support ((⨆ k, C k).1) =
        σ.qClosure (⋃ k, σ.support (C k).1) := by
  letI := quotientClosedCompleteLattice σ
  change
    ((σ.quotientClosedSupportOrderIso (⨆ k, C k) :
        σ.qClosure.Closeds) : Set ι) =
      σ.qClosure (⋃ k, σ.support (C k).1)
  rw [σ.quotientClosedSupportOrderIso.map_iSup]
  exact QuotientSubmoduleEquidistribution.SetClosure.coe_iSup _

/-- The transported infimum is definitionally represented by the literal
objectwise intersection above. -/
theorem iInf_eq_intersection {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    (⨅ k, C k) = intersection C := by
  letI := quotientClosedCompleteLattice σ
  apply le_antisymm
  · intro X hX k
    exact (iInf_le C k) X hX
  · apply le_iInf
    intro k X hX
    exact hX k

/-- Consequently arbitrary meets are literal intersections on objects. -/
theorem carrier_iInf_iff {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R))
    (X : FGModuleCat.{w} R) :
    let _ := quotientClosedCompleteLattice σ
    ((⨅ k, C k).1).carrier X ↔
      ∀ k, (C k).1.carrier X := by
  letI := quotientClosedCompleteLattice σ
  change ((⨅ k, C k).1).carrier X ↔
    ∀ k, (C k).1.carrier X
  rw [iInf_eq_intersection σ C]
  rfl

/-- Arbitrary joins are the additive subcategory generated by the
quotient closure of the union of indecomposable supports. -/
theorem val_iSup_eq_generated {κ : Sort*}
    (C : κ → QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    ((⨆ k, C k).1) =
      σ.generated
        (σ.qClosure (⋃ k, σ.support (C k).1)) := by
  letI := quotientClosedCompleteLattice σ
  calc
    ((⨆ k, C k).1) =
        σ.generated (σ.support ((⨆ k, C k).1)) :=
      (generated_support σ _).symm
    _ = σ.generated
          (σ.qClosure (⋃ k, σ.support (C k).1)) :=
      congrArg σ.generated (support_iSup σ C)

theorem isCompactElement_iff
    (C : QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    IsCompactElement C ↔
        IsCompactElement (σ.quotientClosedSupportOrderIso C) := by
  letI := quotientClosedCompleteLattice σ
  exact Transport.isCompactElement_iff
    σ.quotientClosedSupportOrderIso C

theorem isCompletelyJoinIrreducible_iff
    (C : QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
        QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible
          (σ.quotientClosedSupportOrderIso C) := by
  letI := quotientClosedCompleteLattice σ
  exact Transport.isCompletelyJoinIrreducible_iff
    σ.quotientClosedSupportOrderIso C

/-- Under the finite-dimensional hypotheses, the completely
join-irreducible literal quotient-closed subcategories are exactly the
one-point-generated subcategories. -/
theorem isCompletelyJoinIrreducible_iff_eq_pointGenerated
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (C : QuotientClosedAdditiveSubcategory (R := R)) :
    let _ := quotientClosedCompleteLattice σ
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
      ∃ i : ι, C = pointGenerated σ i := by
  letI := quotientClosedCompleteLattice σ
  calc
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
        QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible
          (σ.quotientClosedSupportOrderIso C) :=
      isCompletelyJoinIrreducible_iff σ C
    _ ↔ ∃ i : ι,
        σ.quotientClosedSupportOrderIso C =
          σ.qClosure.pointClosure i :=
      (qClosure_infiniteConvexStructure_of_finiteDimensional
        (K := K) σ).completelyJoinIrreducible_iff_pointClosure _
    _ ↔ ∃ i : ι, C = pointGenerated σ i := by
      apply exists_congr
      intro i
      exact
        σ.quotientClosedSupportOrderIso.apply_eq_iff_eq_symm_apply
          C (σ.qClosure.pointClosure i)

/-- One-point-generated literal quotient-closed subcategories are compact. -/
theorem pointGenerated_isCompactElement
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (i : ι) :
    let _ := quotientClosedCompleteLattice σ
    IsCompactElement (pointGenerated σ i) := by
  letI := quotientClosedCompleteLattice σ
  apply (isCompactElement_iff σ (pointGenerated σ i)).2
  simpa [pointGenerated] using
    (qClosure_infiniteConvexStructure_of_finiteDimensional
      (K := K) σ).pointClosure_compact i

/-- The compact-basis theorem transported all the way to a literal
quotient-closed additive subcategory. -/
theorem compact_relativeSplitProjectives_basis
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (C : QuotientClosedAdditiveSubcategory (R := R))
    (hcompact :
      let _ := quotientClosedCompleteLattice σ
      IsCompactElement C) :
    (σ.relativeSplitProjectives (σ.support C.1)).Finite ∧
      σ.qClosure.IsMinimalGenerator
        (σ.relativeSplitProjectives (σ.support C.1))
        (σ.support C.1) := by
  letI := quotientClosedCompleteLattice σ
  have hcompact' :
      IsCompactElement (σ.quotientClosedSupportOrderIso C) :=
    (isCompactElement_iff σ C).1 hcompact
  exact qCompact_relativeSplitProjectives_basis_of_finiteDimensional
    (K := K) σ hcompact'

end QuotientLattice

namespace SubobjectLattice

/-- The literal objectwise intersection of subobject-closed additive
subcategories. -/
def intersection {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R)) :
    SubobjectClosedAdditiveSubcategory (R := R) where
  val :=
    { carrier := fun X ↦ ∀ k, (C k).1.carrier X
      biproduct_mem := by
        intro J F hF k
        exact (C k).1.biproduct_mem J F (fun j ↦ hF j k)
      retract_mem := by
        intro X Y r hY k
        exact (C k).1.retract_mem r (hY k) }
  property := by
    constructor
    intro X Y f _ hY k
    letI : (C k).1.carrier.IsClosedUnderSubobjects := (C k).2
    exact (C k).1.carrier.prop_of_mono f (hY k)

/-- The literal subobject-closed subcategory corresponding to the closure
of one indecomposable representative. -/
def pointGenerated (i : ι) :
    SubobjectClosedAdditiveSubcategory (R := R) :=
  σ.subobjectClosedSupportOrderIso.symm
    (σ.sClosure.pointClosure i)

@[simp]
theorem support_pointGenerated (i : ι) :
    σ.support (pointGenerated σ i).1 =
      σ.sClosure ({i} : Set ι) := by
  change
    ((σ.subobjectClosedSupportOrderIso
      (σ.subobjectClosedSupportOrderIso.symm
        (σ.sClosure.pointClosure i)) :
      σ.sClosure.Closeds) : Set ι) =
      σ.sClosure ({i} : Set ι)
  rw [σ.subobjectClosedSupportOrderIso.apply_symm_apply]
  rfl

/-- The support equivalence, viewed as a complete-lattice homomorphism. -/
noncomputable def supportCompleteLatticeHom :
    let _ := subobjectClosedCompleteLattice σ
    CompleteLatticeHom
        (SubobjectClosedAdditiveSubcategory (R := R))
        σ.sClosure.Closeds :=
  by
    letI := subobjectClosedCompleteLattice σ
    exact CompleteLatticeHom.OrderIso.toCompleteLatticeHom
      σ.subobjectClosedSupportOrderIso

/-- Its inverse complete-lattice homomorphism. -/
noncomputable def generatedCompleteLatticeHom :
    let _ := subobjectClosedCompleteLattice σ
    CompleteLatticeHom
        σ.sClosure.Closeds
        (SubobjectClosedAdditiveSubcategory (R := R)) :=
  by
    letI := subobjectClosedCompleteLattice σ
    exact CompleteLatticeHom.OrderIso.toCompleteLatticeHom
      σ.subobjectClosedSupportOrderIso.symm

theorem support_inf
    (C D : SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    σ.support ((C ⊓ D).1) =
        σ.support C.1 ∩ σ.support D.1 := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso (C ⊓ D) :
        σ.sClosure.Closeds) : Set ι) =
      σ.support C.1 ∩ σ.support D.1
  rw [σ.subobjectClosedSupportOrderIso.map_inf]
  rfl

theorem support_sup
    (C D : SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    σ.support ((C ⊔ D).1) =
        σ.sClosure (σ.support C.1 ∪ σ.support D.1) := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso (C ⊔ D) :
        σ.sClosure.Closeds) : Set ι) =
      σ.sClosure (σ.support C.1 ∪ σ.support D.1)
  rw [σ.subobjectClosedSupportOrderIso.map_sup]
  rfl

theorem support_bot :
    let _ := subobjectClosedCompleteLattice σ
    σ.support
        ((⊥ : SubobjectClosedAdditiveSubcategory (R := R)).1) =
      σ.sClosure ∅ := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso ⊥ :
        σ.sClosure.Closeds) : Set ι) =
      σ.sClosure ∅
  rw [σ.subobjectClosedSupportOrderIso.map_bot]
  rfl

theorem support_top :
    let _ := subobjectClosedCompleteLattice σ
    σ.support
        ((⊤ : SubobjectClosedAdditiveSubcategory (R := R)).1) =
      Set.univ := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso ⊤ :
        σ.sClosure.Closeds) : Set ι) =
      Set.univ
  rw [σ.subobjectClosedSupportOrderIso.map_top]
  rfl

theorem support_iInf {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    σ.support ((⨅ k, C k).1) =
        ⋂ k, σ.support (C k).1 := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso (⨅ k, C k) :
        σ.sClosure.Closeds) : Set ι) =
      ⋂ k, σ.support (C k).1
  rw [σ.subobjectClosedSupportOrderIso.map_iInf]
  exact QuotientSubmoduleEquidistribution.SetClosure.coe_iInf _

theorem support_iSup {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    σ.support ((⨆ k, C k).1) =
        σ.sClosure (⋃ k, σ.support (C k).1) := by
  letI := subobjectClosedCompleteLattice σ
  change
    ((σ.subobjectClosedSupportOrderIso (⨆ k, C k) :
        σ.sClosure.Closeds) : Set ι) =
      σ.sClosure (⋃ k, σ.support (C k).1)
  rw [σ.subobjectClosedSupportOrderIso.map_iSup]
  exact QuotientSubmoduleEquidistribution.SetClosure.coe_iSup _

theorem iInf_eq_intersection {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    (⨅ k, C k) = intersection C := by
  letI := subobjectClosedCompleteLattice σ
  apply le_antisymm
  · intro X hX k
    exact (iInf_le C k) X hX
  · apply le_iInf
    intro k X hX
    exact hX k

theorem carrier_iInf_iff {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R))
    (X : FGModuleCat.{w} R) :
    let _ := subobjectClosedCompleteLattice σ
    ((⨅ k, C k).1).carrier X ↔
      ∀ k, (C k).1.carrier X := by
  letI := subobjectClosedCompleteLattice σ
  change ((⨅ k, C k).1).carrier X ↔
    ∀ k, (C k).1.carrier X
  rw [iInf_eq_intersection σ C]
  rfl

/-- Arbitrary joins are the additive subcategory generated by the
subobject closure of the union of indecomposable supports. -/
theorem val_iSup_eq_generated {κ : Sort*}
    (C : κ → SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    ((⨆ k, C k).1) =
      σ.generated
        (σ.sClosure (⋃ k, σ.support (C k).1)) := by
  letI := subobjectClosedCompleteLattice σ
  calc
    ((⨆ k, C k).1) =
        σ.generated (σ.support ((⨆ k, C k).1)) :=
      (generated_support σ _).symm
    _ = σ.generated
          (σ.sClosure (⋃ k, σ.support (C k).1)) :=
      congrArg σ.generated (support_iSup σ C)

theorem isCompactElement_iff
    (C : SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    IsCompactElement C ↔
        IsCompactElement (σ.subobjectClosedSupportOrderIso C) := by
  letI := subobjectClosedCompleteLattice σ
  exact Transport.isCompactElement_iff
    σ.subobjectClosedSupportOrderIso C

theorem isCompletelyJoinIrreducible_iff
    (C : SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
        QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible
          (σ.subobjectClosedSupportOrderIso C) := by
  letI := subobjectClosedCompleteLattice σ
  exact Transport.isCompletelyJoinIrreducible_iff
    σ.subobjectClosedSupportOrderIso C

/-- Under the finite-dimensional hypotheses, the completely
join-irreducible literal subobject-closed subcategories are exactly the
one-point-generated subcategories. -/
theorem isCompletelyJoinIrreducible_iff_eq_pointGenerated
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (C : SubobjectClosedAdditiveSubcategory (R := R)) :
    let _ := subobjectClosedCompleteLattice σ
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
      ∃ i : ι, C = pointGenerated σ i := by
  letI := subobjectClosedCompleteLattice σ
  calc
    QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible C ↔
        QuotientSubmoduleEquidistribution.IsCompletelyJoinIrreducible
          (σ.subobjectClosedSupportOrderIso C) :=
      isCompletelyJoinIrreducible_iff σ C
    _ ↔ ∃ i : ι,
        σ.subobjectClosedSupportOrderIso C =
          σ.sClosure.pointClosure i :=
      (sClosure_infiniteConvexStructure_of_finiteDimensional
        (K := K) σ).completelyJoinIrreducible_iff_pointClosure _
    _ ↔ ∃ i : ι, C = pointGenerated σ i := by
      apply exists_congr
      intro i
      exact
        σ.subobjectClosedSupportOrderIso.apply_eq_iff_eq_symm_apply
          C (σ.sClosure.pointClosure i)

/-- One-point-generated literal subobject-closed subcategories are compact. -/
theorem pointGenerated_isCompactElement
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (i : ι) :
    let _ := subobjectClosedCompleteLattice σ
    IsCompactElement (pointGenerated σ i) := by
  letI := subobjectClosedCompleteLattice σ
  apply (isCompactElement_iff σ (pointGenerated σ i)).2
  simpa [pointGenerated] using
    (sClosure_infiniteConvexStructure_of_finiteDimensional
      (K := K) σ).pointClosure_compact i

/-- The compact-basis theorem transported all the way to a literal
subobject-closed additive subcategory. -/
theorem compact_relativeSplitInjectives_basis
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (C : SubobjectClosedAdditiveSubcategory (R := R))
    (hcompact :
      let _ := subobjectClosedCompleteLattice σ
      IsCompactElement C) :
    (σ.relativeSplitInjectives (σ.support C.1)).Finite ∧
      σ.sClosure.IsMinimalGenerator
        (σ.relativeSplitInjectives (σ.support C.1))
        (σ.support C.1) := by
  letI := subobjectClosedCompleteLattice σ
  have hcompact' :
      IsCompactElement (σ.subobjectClosedSupportOrderIso C) :=
    (isCompactElement_iff σ C).1 hcompact
  exact sCompact_relativeSplitInjectives_basis_of_finiteDimensional
    (K := K) σ hcompact'

end SubobjectLattice

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
