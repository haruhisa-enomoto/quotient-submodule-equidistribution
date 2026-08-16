import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaWordTauCategoryRealization
import QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMeshStrictness
import QuotientSubmoduleEquidistribution.RepresentationDirected.ARCoordinateRecurrence
import QuotientSubmoduleEquidistribution.RepresentationDirected.ARWordPrincipalPositivity
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryFactorLadderRecurrence
import QuotientSubmoduleEquidistribution.CategoryTheory.LinearGeneratedHomIdeal

/-!
# The factor Auslander--Reiten word in the literal ideal quotient

This file identifies a selected segment of the directed AR word with the
indecomposable labels and right meshes of the corresponding literal factor
category.  It is the categorical realization used by the paper's
right-additive mesh argument.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.RepresentationDirected.FactorARWord

open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord
open QuotientSubmoduleEquidistribution.RepresentationDirected.ARWord.SelectedSegments
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit
open QuotientSubmoduleEquidistribution.RepresentationDirected.DirectedAROrbit.OrderedARWord
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v uC vC

variable {K R : Type u} [Field K] [IsAlgClosed K]
  [Ring R] [Algebra K R] [FiniteDimensional K R] [IsNoetherianRing R]
variable {Iota : Type v} [Fintype Iota]
variable (sigma : IndecomposableSkeleton.{u, v, u} R Iota)

/-- The positions of a selected segment word are exactly the surviving
indecomposable labels in the complementary ideal quotient. -/
def selectedPositionDeletedLabelEquiv
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length)) :
    Fin (segmentWord (wordFor sigma H T E) C).length ≃
      DeletedLabel {i | i ∉ omittedLabelFinsetFor sigma H T E C} := by
  let f : Fin (segmentWord (wordFor sigma H T E) C).length →
      DeletedLabel {i | i ∉ omittedLabelFinsetFor sigma H T E C} := fun x ↦
    ⟨positionEquivFor sigma H T E
        (positionInOriginal (wordFor sigma H T E) C x), by
      simp only [Set.mem_setOf_eq, not_not]
      exact (mem_omittedLabelFinsetFor_iff sigma H T E C _).2
        (positionInOriginal_mem (wordFor sigma H T E) C x)⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    change (⟨positionEquivFor sigma H T E
        (positionInOriginal (wordFor sigma H T E) C x), _⟩ :
          DeletedLabel {i | i ∉ omittedLabelFinsetFor sigma H T E C}) =
      ⟨positionEquivFor sigma H T E
        (positionInOriginal (wordFor sigma H T E) C y), _⟩ at hxy
    have hpos : positionInOriginal (wordFor sigma H T E) C x =
        positionInOriginal (wordFor sigma H T E) C y :=
      (positionEquivFor sigma H T E).injective
        (congrArg (fun z : DeletedLabel
          {i | i ∉ omittedLabelFinsetFor sigma H T E C} ↦ z.1) hxy)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy' | hyx'
    · exact (ne_of_lt ((positionInOriginal_lt_iff
        (wordFor sigma H T E) C x y).2 hxy')) hpos
    · exact (ne_of_lt ((positionInOriginal_lt_iff
        (wordFor sigma H T E) C y x).2 hyx')) hpos.symm
  · intro i
    have hi : i.1 ∈ omittedLabelFinsetFor sigma H T E C := by
      simpa only [Set.mem_setOf_eq, not_not] using i.2
    have hiC : (positionEquivFor sigma H T E).symm i.1 ∈ C :=
      (mem_omittedLabelFinsetFor_iff sigma H T E C _).1 (by
        rw [positionEquivFor_symm_apply_apply]
        exact hi)
    let x := positionOfSelected (wordFor sigma H T E) C
      ((positionEquivFor sigma H T E).symm i.1) hiC
    refine ⟨x, Subtype.ext ?_⟩
    dsimp only [x]
    change positionEquivFor sigma H T E
      (positionInOriginal (wordFor sigma H T E) C
        (positionOfSelected (wordFor sigma H T E) C
          ((positionEquivFor sigma H T E).symm i.1) hiC)) = i.1
    rw [positionInOriginal_positionOfSelected,
      positionEquivFor_symm_apply_apply]

@[simp]
theorem selectedPositionDeletedLabelEquiv_apply_val
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (x : Fin (segmentWord (wordFor sigma H T E) C).length) :
    (selectedPositionDeletedLabelEquiv sigma H T E C x).1 =
      positionEquivFor sigma H T E
        (positionInOriginal (wordFor sigma H T E) C x) :=
  rfl

/-- Hom spaces between surviving indecomposables in the literal factor
category are finite-dimensional over the ground field. -/
theorem factorObject_hom_moduleFinite
    (S : Set Iota) (a x : DeletedLabel S) :
    let I := sigma.factorThroughAddIdeal Set.univ S
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
    letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
      I.quotientFunctorLinear
    Module.Finite K
      (sigma.factorObject S a ⟶ sigma.factorObject S x) := by
  dsimp only
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
  letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
    I.quotientFunctorLinear
  let F := sigma.factorFunctor S
  letI : Module.Finite K
      ((sigma.deletedAddPoint a).obj ⟶
        (sigma.deletedAddPoint x).obj) := by
    change Module.Finite K (sigma.obj a.1 ⟶ sigma.obj x.1)
    exact finiteDimensional_hom_obj K R sigma a.1 x.1
  letI : Module.Finite K
      (sigma.deletedAddPoint a ⟶ sigma.deletedAddPoint x) :=
    Module.Finite.equiv
      (CategoryTheory.InducedCategory.homLinearEquiv (R := K)).symm
  exact Module.Finite.of_surjective (F.mapLinearMap K) F.map_surjective

/-- Directed Schur endomorphisms remain scalar after passage to the literal
factor category. -/
theorem factorObject_endomorphism_eq_smul_id
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (S : Set Iota) (x : DeletedLabel S)
    (f :
      let I := sigma.factorThroughAddIdeal Set.univ S
      letI : Preadditive (CategoryTheory.Quotient I.rel) :=
        I.quotientPreadditive
      letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
        CategoryTheory.Quotient.functor_additive I.rel
          (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
            I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
      letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
      letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
        I.quotientFunctorLinear
      sigma.factorObject S x ⟶ sigma.factorObject S x) :
    let I := sigma.factorThroughAddIdeal Set.univ S
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
    letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
      I.quotientFunctorLinear
    ∃ c : K, c • 𝟙 (sigma.factorObject S x) = f := by
  dsimp only at f ⊢
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
  letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
    I.quotientFunctorLinear
  let F := sigma.factorFunctor S
  obtain ⟨g, rfl⟩ := F.map_surjective f
  obtain ⟨c, hc⟩ :=
    H.endomorphism_eq_smul_id K R sigma x.1 g.hom
  refine ⟨c, ?_⟩
  rw [← F.map_id, ← F.map_smul]
  apply congrArg F.map
  apply ObjectProperty.hom_ext
  exact hc

/-- Scalar endomorphisms transport across an equality of objects. -/
private theorem scalarEndomorphism_of_object_eq
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear K C]
    {X Y : C} (hXY : X = Y)
    (hY : ∀ g : Y ⟶ Y, ∃ c : K, c • 𝟙 Y = g)
    (f : X ⟶ X) :
    ∃ c : K, c • 𝟙 X = f := by
  subst Y
  exact hY f

/-- The literal Hom dimension between two word positions in the selected
factor category.  This is the paper's
`dim_k ((mod A)/[C_D])(X_a,X_x)`, with the word-position/indecomposable
identification made explicit. -/
def selectedFactorHomDimension
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (a x : Fin (segmentWord (wordFor sigma H T E) C).length) : ℕ := by
  classical
  let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
  letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
    I.quotientFunctorLinear
  letI : Module.Finite K
      (sigma.factorObject S (selectedPositionDeletedLabelEquiv sigma H T E C a) ⟶
        sigma.factorObject S
          (selectedPositionDeletedLabelEquiv sigma H T E C x)) :=
    factorObject_hom_moduleFinite (K := K) (R := R) sigma S _ _
  exact Module.finrank K
    (sigma.factorObject S (selectedPositionDeletedLabelEquiv sigma H T E C a) ⟶
      sigma.factorObject S
        (selectedPositionDeletedLabelEquiv sigma H T E C x))

/-- Middle positions of the factor word are exactly the surviving summands
of the ambient minimal right almost-split middle term.  Because the ambient
AR word records occurrences, this equivalence retains multiplicities. -/
def selectedMiddleFactorIndexEquiv
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H T) (wordFor sigma H T E))
    (x : Fin (segmentWord (wordFor sigma H T E) C).length) :
    IndecomposableSkeleton.FiniteARTranslationData.factorCategoryMiddleIndex
        sigma T {i | i ∉ omittedLabelFinsetFor sigma H T E C}
        (selectedPositionDeletedLabelEquiv sigma H T E C x) ≃
      {y : Fin (segmentWord (wordFor sigma H T E) C).length //
        IsMiddle
          (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
          (segmentWord (wordFor sigma H T E) C) y x} := by
  let ox := positionInOriginal (wordFor sigma H T E) C x
  let e := middleIndexEquivFor sigma K H T E ox
  let eSelected :
      IndecomposableSkeleton.FiniteARTranslationData.factorCategoryMiddleIndex
          sigma T {i | i ∉ omittedLabelFinsetFor sigma H T E C}
          (selectedPositionDeletedLabelEquiv sigma H T E C x) ≃
        {y : {y : Fin (wordFor sigma H T E).length //
          IsMiddle (orbitGraph sigma H T) (wordFor sigma H T E) y ox} //
            y.1 ∈ C} :=
    e.subtypeEquiv (fun t ↦ by
      change
        (¬(T.factorLadderRightARAt sigma
            (positionEquivFor sigma H T E ox)).label t ∉
            omittedLabelFinsetFor sigma H T E C) ↔
          (e t).1 ∈ C
      rw [not_not]
      have hmem := mem_omittedLabelFinsetFor_iff sigma H T E C
        ((positionEquivFor sigma H T E).symm
          ((T.factorLadderRightARAt sigma
            (positionEquivFor sigma H T E ox)).label t))
      change
        (T.factorLadderRightARAt sigma
            (positionEquivFor sigma H T E ox)).label t ∈
            omittedLabelFinsetFor sigma H T E C ↔
          (positionEquivFor sigma H T E).symm
            ((T.factorLadderRightARAt sigma
              (positionEquivFor sigma H T E ox)).label t) ∈ C
      simpa only [positionEquivFor_symm_apply_apply] using hmem)
  let eFlatten := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun y : Fin (wordFor sigma H T E).length ↦
      IsMiddle (orbitGraph sigma H T) (wordFor sigma H T E) y ox)
    (fun y ↦ y ∈ C)
  exact eSelected.trans <|
    eFlatten.trans (middlePositionEquiv hRuns C x).symm

@[simp]
theorem selectedMiddleFactorIndexEquiv_label
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H T) (wordFor sigma H T E))
    (x : Fin (segmentWord (wordFor sigma H T E) C).length)
    (t : IndecomposableSkeleton.FiniteARTranslationData.factorCategoryMiddleIndex
      sigma T {i | i ∉ omittedLabelFinsetFor sigma H T E C}
    (selectedPositionDeletedLabelEquiv sigma H T E C x)) :
    selectedPositionDeletedLabelEquiv sigma H T E C
        ((selectedMiddleFactorIndexEquiv (K := K)
          sigma H T E C hRuns x t).1) =
      IndecomposableSkeleton.FiniteARTranslationData.factorCategoryMiddleLabel
        sigma T {i | i ∉ omittedLabelFinsetFor sigma H T E C}
        (selectedPositionDeletedLabelEquiv sigma H T E C x) t := by
  apply Subtype.ext
  have hpos : positionInOriginal (wordFor sigma H T E) C
      ((selectedMiddleFactorIndexEquiv (K := K)
        sigma H T E C hRuns x t).1) =
      (middleIndexEquivFor sigma K H T E
        (positionInOriginal (wordFor sigma H T E) C x) t.1).1 := by
    simp [selectedMiddleFactorIndexEquiv, middlePositionEquiv]
    rfl
  rw [selectedPositionDeletedLabelEquiv_apply_val, hpos]
  have he :
      (middleIndexEquivFor sigma K H T E
        (positionInOriginal (wordFor sigma H T E) C x) t.1).1 =
        (positionEquivFor sigma H T E).symm
          ((T.factorLadderRightARAt sigma
            (positionEquivFor sigma H T E
              (positionInOriginal (wordFor sigma H T E) C x))).label t.1) := by
    unfold middleIndexEquivFor
    rw [Equiv.ofBijective_apply]
    rfl
  rw [he, positionEquivFor_symm_apply_apply]
  rfl

include K

/-- A predecessor in the factor word gives the literal surviving target of
the restricted AR translation.  Positive right-additivity rules out the
otherwise possible zero-middle truncation. -/
theorem factorLadderTauTarget_eq_some_of_isPrevious
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H T) (wordFor sigma H T E))
    (weight : Fin (segmentWord (wordFor sigma H T E) C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
      (segmentWord (wordFor sigma H T E) C) weight)
    (p x : Fin (segmentWord (wordFor sigma H T E) C).length)
    (hpx : IsPrevious (segmentWord (wordFor sigma H T E) C) p x) :
    T.factorLadderTauTarget sigma
        {i | i ∉ omittedLabelFinsetFor sigma H T E C}
        (selectedPositionDeletedLabelEquiv sigma H T E C x) =
      some (selectedPositionDeletedLabelEquiv sigma H T E C p) := by
  let Q := wordFor sigma H T E
  let ox := positionInOriginal Q C x
  let op := positionInOriginal Q C p
  have hpOriginal : IsPrevious Q op ox :=
    (isPrevious_segmentWord_iff C p x).1 hpx
  have hxNonprojective : ¬ Projective
      (sigma.obj (positionEquivFor sigma H T E ox)) := by
    apply (exists_previous_positionFor_iff_not_projective sigma H T E
      (positionEquivFor sigma H T E ox)).1
    refine ⟨op, ?_⟩
    simpa only [positionEquivFor_apply_symm_apply] using hpOriginal
  have htranslate : positionEquivFor sigma H T E op =
      (T.arTranslation sigma
        ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩).1 :=
    (isPrevious_positionFor_iff_eq_arTranslation sigma H T E
      ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩ op).1 (by
        simpa only [positionEquivFor_apply_symm_apply] using hpOriginal)
  have htranslateSurvives :
      (T.arTranslation sigma
        ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩).1 ∉
          {i | i ∉ omittedLabelFinsetFor sigma H T E C} := by
    simp only [Set.mem_setOf_eq, not_not]
    rw [← htranslate]
    exact (mem_omittedLabelFinsetFor_iff sigma H T E C op).2
      (positionInOriginal_mem Q C p)
  obtain ⟨y, hy⟩ :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.IyamaMesh.Word.nonprojective_hasIncoming_of_positiveRightAdditive
      (segmentGraph (orbitGraph sigma H T) Q C) (segmentWord Q C)
      weight hweight ⟨x, ⟨p, hpx⟩⟩
  let t := (selectedMiddleFactorIndexEquiv (K := K)
    sigma H T E C hRuns x).symm ⟨y, hy⟩
  have hmiddle : T.factorLadderTheta sigma
      {i | i ∉ omittedLabelFinsetFor sigma H T E C}
      (FactorLadder.basis
        (selectedPositionDeletedLabelEquiv sigma H T E C x)) ≠ 0 :=
    (T.factorLadderTheta_basis_ne_zero_iff sigma
      {i | i ∉ omittedLabelFinsetFor sigma H T E C}
      (selectedPositionDeletedLabelEquiv sigma H T E C x)).2
        ⟨t.1, t.2⟩
  have htarget := T.factorLadderTauTarget_eq_some sigma
    {i | i ∉ omittedLabelFinsetFor sigma H T E C}
    (selectedPositionDeletedLabelEquiv sigma H T E C x)
    hxNonprojective htranslateSurvives hmiddle
  have hlabel :
      (⟨(T.arTranslation sigma
          ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩).1,
        htranslateSurvives⟩ :
          DeletedLabel {i | i ∉ omittedLabelFinsetFor sigma H T E C}) =
        selectedPositionDeletedLabelEquiv sigma H T E C p := by
    apply Subtype.ext
    exact htranslate.symm
  exact htarget.trans (congrArg some hlabel)

omit K

/-- Conversely, every defined restricted AR target comes from the unique
predecessor in the selected factor word. -/
theorem exists_isPrevious_of_factorLadderTauTarget_eq_some
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (x : Fin (segmentWord (wordFor sigma H T E) C).length)
    {y : DeletedLabel {i | i ∉ omittedLabelFinsetFor sigma H T E C}}
    (htarget : T.factorLadderTauTarget sigma
        {i | i ∉ omittedLabelFinsetFor sigma H T E C}
        (selectedPositionDeletedLabelEquiv sigma H T E C x) = some y) :
    ∃ p, IsPrevious (segmentWord (wordFor sigma H T E) C) p x := by
  let Q := wordFor sigma H T E
  let ox := positionInOriginal Q C x
  have hxNonprojective : ¬ Projective
      (sigma.obj (positionEquivFor sigma H T E ox)) := by
    intro hx
    have hnone := T.factorLadderTauTarget_eq_none_of_projective sigma
      {i | i ∉ omittedLabelFinsetFor sigma H T E C}
      (selectedPositionDeletedLabelEquiv sigma H T E C x) hx
    rw [htarget] at hnone
    simp at hnone
  obtain ⟨op, hpOriginal⟩ :=
    (exists_previous_positionFor_iff_not_projective sigma H T E
      (positionEquivFor sigma H T E ox)).2 hxNonprojective
  have hpOriginal' : IsPrevious Q op ox := by
    simpa only [Q, positionEquivFor_apply_symm_apply] using hpOriginal
  have htranslate : positionEquivFor sigma H T E op =
      (T.arTranslation sigma
        ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩).1 :=
    (isPrevious_positionFor_iff_eq_arTranslation sigma H T E
      ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩ op).1 hpOriginal
  have htranslateSurvives :
      (T.arTranslation sigma
        ⟨positionEquivFor sigma H T E ox, hxNonprojective⟩).1 ∉
          {i | i ∉ omittedLabelFinsetFor sigma H T E C} := by
    intro hkill
    have hnone := T.factorLadderTauTarget_eq_none_of_translation_mem sigma
      {i | i ∉ omittedLabelFinsetFor sigma H T E C}
      (selectedPositionDeletedLabelEquiv sigma H T E C x)
      hxNonprojective hkill
    rw [htarget] at hnone
    simp at hnone
  have hopC : op ∈ C :=
    (mem_omittedLabelFinsetFor_iff sigma H T E C op).1 (by
      rw [htranslate]
      simpa only [Set.mem_setOf_eq, not_not] using htranslateSurvives)
  exact (exists_isPrevious_segmentWord_iff C x).2
    ⟨op, hpOriginal', hopC⟩

include K

/-- The left term of the literal quotient mesh vanishes exactly at a first
position of the factor AR word. -/
theorem factorCategoryRightMesh_X₁_isZero_iff_no_previous
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (T : sigma.FiniteARTranslationData)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H T E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H T) (wordFor sigma H T E))
    (weight : Fin (segmentWord (wordFor sigma H T E) C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
      (segmentWord (wordFor sigma H T E) C) weight)
    (x : Fin (segmentWord (wordFor sigma H T E) C).length) :
    let I := sigma.factorThroughAddIdeal Set.univ
      {i | i ∉ omittedLabelFinsetFor sigma H T E C}
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    IsZero (IndecomposableSkeleton.FiniteARTranslationData.factorCategoryRightMesh
        sigma T {i | i ∉ omittedLabelFinsetFor sigma H T E C}
        (selectedPositionDeletedLabelEquiv sigma H T E C x)).X₁ ↔
      ¬ ∃ p, IsPrevious (segmentWord (wordFor sigma H T E) C) p x := by
  classical
  dsimp only
  let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  have hmesh :=
    T.factorCategoryRightMesh_X₁_isZero_iff_tauTarget_eq_none sigma S
      (selectedPositionDeletedLabelEquiv sigma H T E C x)
  have hmesh' :
      IsZero (T.factorCategoryRightMesh sigma S
        (selectedPositionDeletedLabelEquiv sigma H T E C x)).X₁ ↔
      T.factorLadderTauTarget sigma S
        (selectedPositionDeletedLabelEquiv sigma H T E C x) = none := by
    simpa only using hmesh
  rw [hmesh']
  constructor
  · intro hnone hp
    obtain ⟨p, hp⟩ := hp
    have hsome := factorLadderTauTarget_eq_some_of_isPrevious
      (K := K) sigma H T E C hRuns weight hweight p x hp
    rw [hsome] at hnone
    simp at hnone
  · intro hfirst
    cases htarget : T.factorLadderTauTarget sigma S
        (selectedPositionDeletedLabelEquiv sigma H T E C x) with
    | none => rfl
    | some y =>
        exact False.elim (hfirst
          (exists_isPrevious_of_factorLadderTauTarget_eq_some
            sigma H T E C x htarget))

omit K

/-- The literal factor category, with its quotient right meshes, realizes
the selected segment word.  This is the precise Lean counterpart of the
paper's "factor AR word" and "factor mesh positions" terminology. -/
def factorWordTauCategoryRealization
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H
      (sigma.finiteDimensionalARTranslationData K R) E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E))
    (weight : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph
        (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      (segmentWord
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      weight) :
    let T := sigma.finiteDimensionalARTranslationData K R
    let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
    let I := sigma.factorThroughAddIdeal Set.univ S
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
    letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
      I.quotientFunctorLinear
    letI : HasFiniteBiproducts (sigma.FactorCategory S) :=
      sigma.factorQuotientHasFiniteBiproducts Set.univ S
    letI : HasBinaryBiproducts (sigma.FactorCategory S) :=
      HasBinaryBiproducts.of_hasBinaryCoproducts
    let hidem := sigma.factorCategory_isIdempotentComplete
      (k := K) (R := R) S
    letI : IsIdempotentComplete (sigma.FactorCategory S) := hidem
    letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
    letI : DecidableEq (DeletedLabel S) := Classical.decEq _
    let TauExt := sigma.finiteDimensionalFactorCategoryTauExtension
      (k := K) (R := R) S
    let Tau := TauExt.data
    IyamaMesh.WordTauCategoryRealization Tau
      (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
      (segmentWord (wordFor sigma H T E) C)
      (selectedPositionDeletedLabelEquiv sigma H T E C) := by
  classical
  dsimp only
  let T := sigma.finiteDimensionalARTranslationData K R
  let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
  letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
    I.quotientFunctorLinear
  letI : HasFiniteBiproducts (sigma.FactorCategory S) :=
    sigma.factorQuotientHasFiniteBiproducts Set.univ S
  letI : HasBinaryBiproducts (sigma.FactorCategory S) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  let hidem := sigma.factorCategory_isIdempotentComplete
    (k := K) (R := R) S
  letI : IsIdempotentComplete (sigma.FactorCategory S) := hidem
  letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
  letI : DecidableEq (DeletedLabel S) := Classical.decEq _
  let TauExt := sigma.finiteDimensionalFactorCategoryTauExtension
    (k := K) (R := R) S
  let Tau := TauExt.data
  let label := selectedPositionDeletedLabelEquiv sigma H T E C
  refine
    { projective_iff := ?_
      left_iso := ?_
      middle_iso := ?_ }
  · intro x
    let ePack := Classical.choice
      (sigma.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
        (k := K) (R := R) S hidem (label x)
      )
    let e₀ : (Tau.rightMesh (Tau.obj (label x))).X₁ ≅
        (T.factorCategoryRightMesh sigma S (label x)).X₁ := by
      rw [TauExt.right_eq]
      exact ShortComplex.π₁.mapIso ePack
    have hExplicit := factorCategoryRightMesh_X₁_isZero_iff_no_previous
      (K := K) sigma H T E C hRuns weight hweight x
    constructor
    · intro hzero
      apply hExplicit.1
      exact IsZero.of_iso hzero e₀.symm
    · intro hfirst
      exact IsZero.of_iso (hExplicit.2 hfirst)
        e₀
  · intro x
    let ePack := Classical.choice
      (sigma.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
        (k := K) (R := R) S hidem (label x)
      )
    let e₀ : (Tau.rightMesh (Tau.obj (label x))).X₁ ≅
        (T.factorCategoryRightMesh sigma S (label x)).X₁ := by
      rw [TauExt.right_eq]
      exact ShortComplex.π₁.mapIso ePack
    by_cases hprev : ∃ p,
        IsPrevious (segmentWord (wordFor sigma H T E) C) p x
    · let p := Classical.choose hprev
      have hp := Classical.choose_spec hprev
      have htarget := factorLadderTauTarget_eq_some_of_isPrevious
        (K := K) sigma H T E C hRuns weight hweight p x hp
      let e₁ := T.factorCategoryRightMeshLeftIso_of_tauTarget_eq_some
        sigma S (label x) (label p) htarget
      let p₀ : {q : Fin (segmentWord (wordFor sigma H T E) C).length //
          IsPrevious (segmentWord (wordFor sigma H T E) C) q x} := ⟨p, hp⟩
      letI : Unique {q : Fin (segmentWord (wordFor sigma H T E) C).length //
          IsPrevious (segmentWord (wordFor sigma H T E) C) q x} :=
        ⟨⟨p₀⟩, fun q ↦ Subtype.ext (isPrevious_unique q.2 hp)⟩
      let eObj : sigma.factorObject S (label p) ≅
          Tau.obj (label (default :
            {q : Fin (segmentWord (wordFor sigma H T E) C).length //
              IsPrevious (segmentWord (wordFor sigma H T E) C) q x}).1) :=
        eqToIso (by rfl)
      exact e₀.trans <| e₁.trans <| eObj.trans <|
        (biproductUniqueIso
          (fun q : {q : Fin (segmentWord (wordFor sigma H T E) C).length //
            IsPrevious (segmentWord (wordFor sigma H T E) C) q x} ↦
              Tau.obj (label q.1))).symm
    · have hExplicit : IsZero
          (T.factorCategoryRightMesh sigma S (label x)).X₁ :=
        (factorCategoryRightMesh_X₁_isZero_iff_no_previous
          (K := K) sigma H T E C hRuns weight hweight x).2 hprev
      have hBiproduct : IsZero
          (⨁ fun q : {q : Fin (segmentWord (wordFor sigma H T E) C).length //
            IsPrevious (segmentWord (wordFor sigma H T E) C) q x} ↦
              Tau.obj (label q.1)) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply biproduct.hom_ext
        intro q
        exact False.elim (hprev ⟨q.1, q.2⟩)
      exact e₀.trans (IsZero.iso hExplicit hBiproduct)
  · intro x
    let ePack := Classical.choice
      (sigma.finiteDimensionalFactorCategoryRightMesh_factorObject_iso
        (k := K) (R := R) S hidem (label x)
      )
    let e₀ : Tau.thetaPlus (label x) ≅
        (T.factorCategoryRightMesh sigma S (label x)).X₂ := by
      change
        ((Tau.toFiniteRightTauCategoryData).rightMesh
          ((Tau.toFiniteRightTauCategoryData).obj (label x))).X₂ ≅ _
      rw [TauExt.right_eq]
      exact ShortComplex.π₂.mapIso ePack
    let e₁ : (T.factorCategoryRightMesh sigma S (label x)).X₂ ≅
        ⨁ fun t : T.factorCategoryMiddleIndex sigma S (label x) ↦
          sigma.factorObject S (T.factorCategoryMiddleLabel sigma S (label x) t) := by
      simpa only using T.factorCategoryRightMeshMiddleIso sigma S (label x)
    let eIndex := selectedMiddleFactorIndexEquiv (K := K)
      sigma H T E C hRuns x
    let e₂ :
        (⨁ fun t : T.factorCategoryMiddleIndex sigma S (label x) ↦
          sigma.factorObject S (T.factorCategoryMiddleLabel sigma S (label x) t)) ≅
        (⨁ fun y : {y : Fin (segmentWord (wordFor sigma H T E) C).length //
          IsMiddle
            (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
            (segmentWord (wordFor sigma H T E) C) y x} ↦
              Tau.obj (label y.1)) :=
      biproduct.whiskerEquiv eIndex (fun t ↦
        eqToIso (by
          change sigma.factorObject S (label (eIndex t).1) =
            sigma.factorObject S
              (T.factorCategoryMiddleLabel sigma S (label x) t)
          rw [selectedMiddleFactorIndexEquiv_label
            (K := K) sigma H T E C hRuns x t]))
    exact e₀.trans (e₁.trans e₂)

/-- The literal quotient tau-category supplies the representable mesh
exactness data for the selected factor AR word.  Its entries are the actual
dimensions of quotient-category Hom spaces. -/
def factorWordRepresentableMeshExactnessData
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H
      (sigma.finiteDimensionalARTranslationData K R) E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E))
    (weight : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph
        (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      (segmentWord
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      weight) :
    let T := sigma.finiteDimensionalARTranslationData K R
    let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
    let I := sigma.factorThroughAddIdeal Set.univ S
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
          I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
    letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
    letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
      I.quotientFunctorLinear
    letI : HasFiniteBiproducts (sigma.FactorCategory S) :=
      sigma.factorQuotientHasFiniteBiproducts Set.univ S
    letI : HasBinaryBiproducts (sigma.FactorCategory S) :=
      HasBinaryBiproducts.of_hasBinaryCoproducts
    let hidem := sigma.factorCategory_isIdempotentComplete
      (k := K) (R := R) S
    letI : IsIdempotentComplete (sigma.FactorCategory S) := hidem
    letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
    letI : DecidableEq (DeletedLabel S) := Classical.decEq _
    MeshExactness.RepresentableMeshExactnessData
      (segmentGraph (orbitGraph sigma H T) (wordFor sigma H T E) C)
      (segmentWord (wordFor sigma H T E) C) := by
  classical
  dsimp only
  let T := sigma.finiteDimensionalARTranslationData K R
  let S := {i | i ∉ omittedLabelFinsetFor sigma H T E C}
  let I := sigma.factorThroughAddIdeal Set.univ S
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ h₁ h₂ ↦
        I.add_compatible f₁ f₂ g₁ g₂ h₁ h₂)
  letI : Linear K (sigma.FactorCategory S) := I.quotientLinear
  letI : (CategoryTheory.Quotient.functor I.rel).Linear K :=
    I.quotientFunctorLinear
  letI : HasFiniteBiproducts (sigma.FactorCategory S) :=
    sigma.factorQuotientHasFiniteBiproducts Set.univ S
  letI : HasBinaryBiproducts (sigma.FactorCategory S) :=
    HasBinaryBiproducts.of_hasBinaryCoproducts
  let hidem := sigma.factorCategory_isIdempotentComplete
    (k := K) (R := R) S
  letI : IsIdempotentComplete (sigma.FactorCategory S) := hidem
  letI : Fintype (DeletedLabel S) := Fintype.ofFinite _
  letI : DecidableEq (DeletedLabel S) := Classical.decEq _
  let TauExt := sigma.finiteDimensionalFactorCategoryTauExtension
    (k := K) (R := R) S
  let Tau := TauExt.data
  let label := selectedPositionDeletedLabelEquiv sigma H T E C
  let Real := factorWordTauCategoryRealization
    (K := K) (R := R) sigma H E C hRuns weight hweight
  letI homFinite : ∀ a x : DeletedLabel S,
      Module.Finite K (Tau.obj a ⟶ Tau.obj x) := fun a x ↦ by
    change Module.Finite K
      (sigma.factorObject S a ⟶ sigma.factorObject S x)
    exact factorObject_hom_moduleFinite
      (K := K) (R := R) sigma S a x
  have scalar_mod_radical :
      ∀ (x : DeletedLabel S) (f : Tau.obj x ⟶ Tau.obj x),
        ∃ c : K,
          f - c • 𝟙 (Tau.obj x) ∈
            Tau.radicalHomSubmodule (K := K) x x := by
    intro x f
    have hobj : Tau.obj x = sigma.factorObject S x :=
      congrFun (congrArg
        (fun D : QuotientSubmoduleEquidistribution.Iyama.FiniteRightTauCategoryData
          (sigma.FactorCategory S) (DeletedLabel S) ↦ D.obj)
        TauExt.right_eq) x
    obtain ⟨c, hc⟩ := scalarEndomorphism_of_object_eq
      (K := K) hobj
      (factorObject_endomorphism_eq_smul_id
        (K := K) (R := R) sigma H S x) f
    refine ⟨c, ?_⟩
    rw [← hc, sub_self]
    exact (Tau.radicalHomSubmodule (K := K) x x).zero_mem
  exact Real.toRepresentableMeshExactnessData
    (K := K) scalar_mod_radical weight hweight

include K

@[simp]
theorem factorWordRepresentableMeshExactnessData_homDimension
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H
      (sigma.finiteDimensionalARTranslationData K R) E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E))
    (weight : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph
        (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      (segmentWord
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      weight)
    (a x : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length) :
    (factorWordRepresentableMeshExactnessData
      (K := K) (R := R) sigma H E C hRuns weight hweight).homDimension a x =
      selectedFactorHomDimension (K := K) (R := R) sigma H
        (sigma.finiteDimensionalARTranslationData K R) E C a x := by
  rfl

/-- The manuscript's selected mixed coordinate is exactly the Hom dimension
in the literal factor category whenever a positive right-additive word
weight supplies the quotient mesh exactness. -/
theorem selectedWordMixedMultiplicityFor_eq_factorHomDimension
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H
      (sigma.finiteDimensionalARTranslationData K R) E).length))
    (hRuns : HasOnlyBoundaryRepeatedRuns
      (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E))
    (weight : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length → ℤ)
    (hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph
        (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      (segmentWord
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E) C)
      weight)
    (a x : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length) :
    wordMixedMultiplicityFor (K := K) (R := R) sigma H
        (sigma.finiteDimensionalARTranslationData K R) E C
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C a)
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C x) =
      (selectedFactorHomDimension (K := K) (R := R) sigma H
        (sigma.finiteDimensionalARTranslationData K R) E C a x : ℤ) := by
  let T := sigma.finiteDimensionalARTranslationData K R
  let Q := wordFor sigma H T E
  let G := orbitGraph sigma H T
  let Exact := factorWordRepresentableMeshExactnessData
    (K := K) (R := R) sigma H E C hRuns weight hweight
  have hRec :=
    PrincipalPositivity.selectedWordMixedMultiplicityFor_satisfiesWordMeshInverseRecurrence
      (K := K) (R := R) sigma H T E C
  have hEq :=
    QuotientSubmoduleEquidistribution.RepresentationDirected.MeshExactness.recurrenceSolution_eq_homDimension
    (segmentGraph G Q C) (segmentWord Q C) Exact _ hRec
  have hEntry := congrFun (congrFun hEq a) x
  have hDimension : Exact.homDimension a x =
      selectedFactorHomDimension (K := K) (R := R) sigma H T E C a x := by
    dsimp only [Exact]
    exact factorWordRepresentableMeshExactnessData_homDimension
      (K := K) (R := R) sigma H E C hRuns weight hweight a x
  rw [hDimension] at hEntry
  simpa only [T, Q, G] using hEntry

/-- Literal form of the revised manuscript lemma: if the selected subword is
reduced, then every selected mixed coordinate is the dimension of the
corresponding Hom space in `(mod A)/[C_D]`, hence is nonnegative. -/
theorem selectedWordMixedMultiplicityFor_eq_factorHomDimension_of_reduced
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (E : DirectedOrderChoice sigma)
    (C : Finset (Fin (wordFor sigma H
      (sigma.finiteDimensionalARTranslationData K R) E).length))
    (hProjectedReduced : SimpleGraphCoxeter.IsReduced
      (orbitGraph sigma H (sigma.finiteDimensionalARTranslationData K R))
      (selectedWord
        (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
        C))
    (a x : Fin (segmentWord
      (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
      C).length) :
    wordMixedMultiplicityFor (K := K) (R := R) sigma H
        (sigma.finiteDimensionalARTranslationData K R) E C
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C a)
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C x) =
        (selectedFactorHomDimension (K := K) (R := R) sigma H
          (sigma.finiteDimensionalARTranslationData K R) E C a x : ℤ) ∧
      0 ≤ wordMixedMultiplicityFor (K := K) (R := R) sigma H
        (sigma.finiteDimensionalARTranslationData K R) E C
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C a)
        (positionInOriginal
          (wordFor sigma H (sigma.finiteDimensionalARTranslationData K R) E)
          C x) := by
  let T := sigma.finiteDimensionalARTranslationData K R
  let Q := wordFor sigma H T E
  let G := orbitGraph sigma H T
  have hRuns : HasOnlyBoundaryRepeatedRuns G Q :=
    wordFor_hasOnlyBoundaryRepeatedRuns sigma H T E
  have hSegmentRuns : HasOnlyBoundaryRepeatedRuns
      (segmentGraph G Q C) (segmentWord Q C) :=
    hasOnlyBoundaryRepeatedRuns_segmentWord hRuns C
  have hSegmentReduced : SimpleGraphCoxeter.IsReduced
      (segmentGraph G Q C) (segmentWord Q C) :=
    SegmentReducedness.segmentWord_isReduced
      G Q C hRuns hProjectedReduced
  let weight : Fin (segmentWord Q C).length → ℤ := fun z ↦
    WordRootProcess.height
      (WordRootProcess.inversionRoot
        (segmentGraph G Q C) (segmentWord Q C) z)
  have hweight : PrincipalPositivity.IsPositiveRightAdditive
      (segmentGraph G Q C) (segmentWord Q C) weight :=
    PrincipalPositivity.inversionRootHeight_isPositiveRightAdditive
      (segmentGraph G Q C) (segmentWord Q C)
      hSegmentRuns hSegmentReduced
  have hEq := selectedWordMixedMultiplicityFor_eq_factorHomDimension
    (K := K) (R := R) sigma H E C hRuns weight hweight a x
  refine ⟨?_, ?_⟩
  · simpa only [T, Q, G] using hEq
  · rw [hEq]
    exact Int.natCast_nonneg _

end QuotientSubmoduleEquidistribution.RepresentationDirected.FactorARWord
