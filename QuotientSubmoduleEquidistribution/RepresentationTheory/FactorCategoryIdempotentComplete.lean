import QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting
import QuotientSubmoduleEquidistribution.CategoryTheory.IyamaTauBiproduct
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryKrullSchmidt
import QuotientSubmoduleEquidistribution.RepresentationTheory.FactorCategoryRadicalNilpotence

/-!
# Idempotent completeness of the literal factor category

The ideal quotient `add(ind R) / [add K]` is idempotent complete.  A quotient
object is first replaced by a biproduct of representatives outside `K`.  On
such a reduced representative, every endomorphism killed by the quotient
factors through `add K`, hence is ambient-categorical-radical and therefore
nilpotent.  Ring-theoretic idempotent lifting then supplies the splitting.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

open CategoricalRadical

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

universe u v

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι]
  (σ : IndecomposableSkeleton.{u, v, u} R ι)

omit [Fintype ι] in
/-- Every literal additive subcategory `add S` is idempotent complete,
because it is closed under retracts inside the abelian module category. -/
theorem addCategory_isIdempotentComplete (S : Set ι) :
    IsIdempotentComplete (σ.AddCategory S) := by
  refine ⟨?_⟩
  intro X p hp
  have hp' : p.hom ≫ p.hom = p.hom :=
    congrArg (fun q ↦ q.hom) hp
  obtain ⟨Z, i, e, hi, he⟩ :=
    IsIdempotentComplete.idempotents_split X.obj p.hom hp'
  let r : Retract Z X.obj :=
    { i := i
      r := e
      retract := hi }
  let Z' : σ.AddCategory S :=
    ⟨Z, inAdd_of_retract σ r X.property⟩
  refine ⟨Z', ObjectProperty.homMk i, ObjectProperty.homMk e, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    exact hi
  · apply ObjectProperty.hom_ext
    exact he

include k in
/-- On a finite biproduct of representatives outside `K`, every
endomorphism killed by the factor functor is nilpotent. -/
theorem factorFunctor_kernel_isNilpotent_on_surviving_biproduct
    (K : Set ι) {n : ℕ} (label : Fin n → DeletedLabel K) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
      σ.addCategoryHasFiniteBiproducts Set.univ
    ∀ f : End (⨁ fun i ↦ σ.deletedAddPoint (label i)),
      (σ.factorFunctor K).map f = 0 → IsNilpotent f := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  let Q := σ.ambientAddCategoryNilpotentRadicalData
    (k := k) (R := R)
  intro f hf
  have hfactor : FactorsThroughAdd σ K f.hom :=
    (I.map_eq_zero_iff f).1 hf
  obtain ⟨M, hM, left, right, hcomp⟩ := hfactor
  let M' : σ.AddCategory Set.univ := ⟨M, σ.inAdd_univ M⟩
  let left' :
      (⨁ fun i ↦ σ.deletedAddPoint (label i)) ⟶ M' :=
    ObjectProperty.homMk left
  let right' :
      M' ⟶ (⨁ fun i ↦ σ.deletedAddPoint (label i)) :=
    ObjectProperty.homMk right
  have hcomponent (i : Fin n) :
      IsRadicalMorphism
        (biproduct.ι (fun i ↦ σ.deletedAddPoint (label i)) i ≫ left') := by
    let a : σ.obj (label i).1 ⟶ M :=
      (biproduct.ι (fun i ↦ σ.deletedAddPoint (label i)) i ≫ left').hom
    have haNot : ¬ IsSplitMono a := by
      intro ha
      letI : IsSplitMono a := ha
      let r : Retract (σ.obj (label i).1) M :=
        { i := a
          r := retraction a
          retract := IsSplitMono.id a }
      exact (label i).2 (index_mem_of_retract_inAdd σ r hM)
    have haRad : IsRadicalMorphism a :=
      (σ.isRadicalMorphism_iff_not_isSplitMono_from_obj a).2 haNot
    intro g
    let U := ObjectProperty.ι (σ.generated Set.univ).carrier
    let q := 𝟙 _ -
      (biproduct.ι (fun i ↦ σ.deletedAddPoint (label i)) i ≫ left') ≫ g
    have hq : IsIso (U.map q) := by
      dsimp only [U, q]
      exact haRad g.hom
    letI : IsIso (U.map q) := hq
    exact Functor.ReflectsIsomorphisms.reflects U q
  have hleft : left' ∈ Q.ideal.hom _ M' := by
    apply QuotientSubmoduleEquidistribution.Iyama.mem_radicalIdeal_of_biproduct_source_components
      Q left'
    intro i
    exact (Q.mem_ideal_iff _).2 (hcomponent i)
  have hfacAdd : left' ≫ right' = f := by
    apply ObjectProperty.hom_ext
    exact hcomp
  have hfRad : f ∈ Q.ideal.hom _ _ := by
    rw [← hfacAdd]
    exact Q.ideal.postcomp right' hleft
  exact Q.isNilpotent_end_of_mem_ideal hfRad

include k in
/-- The literal factor category is idempotent complete under the paper's
finite-dimensional representation-finite hypotheses. -/
theorem factorCategory_isIdempotentComplete (K : Set ι) :
    let I := σ.factorThroughAddIdeal Set.univ K
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    IsIdempotentComplete (σ.FactorCategory K) := by
  dsimp only
  let I := σ.factorThroughAddIdeal Set.univ K
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts (σ.AddCategory Set.univ) :=
    σ.addCategoryHasFiniteBiproducts Set.univ
  letI : HasFiniteBiproducts (σ.FactorCategory K) :=
    σ.factorQuotientHasFiniteBiproducts Set.univ K
  letI : IsIdempotentComplete (σ.AddCategory Set.univ) :=
    σ.addCategory_isIdempotentComplete Set.univ
  let F := σ.factorFunctor K
  apply
    QuotientSubmoduleEquidistribution.CategoryTheory.IdempotentLifting.isIdempotentComplete_of_objectwise_nilpotent_kernel
      F
  intro X
  obtain ⟨n, label, ⟨e⟩⟩ := σ.factorCategory_obj_decomposition K X
  let Y : σ.AddCategory Set.univ :=
    ⨁ fun i : Fin n ↦ σ.deletedAddPoint (label i)
  let ε : F.obj Y ≅ X :=
    (F.mapBiproduct (fun i : Fin n ↦ σ.deletedAddPoint (label i))).trans
      e.symm
  refine ⟨Y, ε, ?_⟩
  exact σ.factorFunctor_kernel_isNilpotent_on_surviving_biproduct
    (k := k) (R := R) K label

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
