import OpConjecture.CategoryTheory.IdealQuotient
import OpConjecture.CategoryTheory.CategoricalRadical
import OpConjecture.RepresentationTheory.GenericAdditiveRejective
import OpConjecture.RepresentationTheory.RejectiveChains

/-!
# Ideal quotients under additive equivalence

An additive equivalence which identifies two Hom ideals induces an
equivalence of their quotient categories.  Specializing to ideals of maps
factoring through additive subcategories proves that the literal one-point
factors in a source maximal rejective chain and in its Auslander target are
equivalent.  Consequently finite biproducts and zero categorical radical
transport step by step.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture

namespace CategoricalRadical

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

/-- Zero categorical radical transports from the source to the target
of an equivalence of preadditive categories with finite biproducts. -/
theorem hasZeroRadical_of_equivalence
    (E : C ≌ D) (hC : HasZeroRadical C) :
    HasZeroRadical D := by
  letI : E.inverse.Additive :=
    Functor.additive_of_preserves_binary_products E.inverse
  intro X Y f hf
  have hrad : IsRadicalMorphism (E.inverse.map f) := by
    intro g
    obtain ⟨g', rfl⟩ := E.inverse.map_surjective g
    haveI : IsIso (𝟙 X - f ≫ g') := hf g'
    rw [← E.inverse.map_id, ← E.inverse.map_comp,
      ← E.inverse.map_sub]
    infer_instance
  have hzero : E.inverse.map f = 0 :=
    hC (E.inverse.map f) hrad
  apply E.inverse.map_injective
  simpa using hzero

/-- Having zero categorical radical is invariant under an equivalence
of preadditive categories with finite biproducts. -/
theorem hasZeroRadical_iff_of_equivalence
    (E : C ≌ D) :
    HasZeroRadical C ↔ HasZeroRadical D :=
  ⟨hasZeroRadical_of_equivalence E,
    hasZeroRadical_of_equivalence E.symm⟩

end CategoricalRadical

namespace CategoricalIdeal

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]

namespace HomIdeal

variable (E : C ≌ D) [E.functor.Additive]
  (I : HomIdeal C) (J : HomIdeal D)
  (map_mem_iff :
    ∀ {X Y : C} (f : X ⟶ Y),
      E.functor.map f ∈ J.hom _ _ ↔ f ∈ I.hom X Y)

/-- The functor on ideal quotients induced by an additive equivalence
which identifies the two Hom ideals. -/
def quotientMap :
    CategoryTheory.Quotient I.rel ⥤
      CategoryTheory.Quotient J.rel :=
  CategoryTheory.Quotient.lift I.rel
    (E.functor ⋙ CategoryTheory.Quotient.functor J.rel)
    (by
      intro X Y f g hfg
      apply CategoryTheory.Quotient.sound J.rel
      change E.functor.map f - E.functor.map g ∈ J.hom _ _
      rw [← E.functor.map_sub]
      exact (map_mem_iff (f - g)).2 hfg)

@[simp]
theorem quotientMap_obj (X : C) :
    (quotientMap E I J map_mem_iff).obj
        ((CategoryTheory.Quotient.functor I.rel).obj X) =
      (CategoryTheory.Quotient.functor J.rel).obj
        (E.functor.obj X) :=
  rfl

@[simp]
theorem quotientMap_map
    {X Y : C} (f : X ⟶ Y) :
    (quotientMap E I J map_mem_iff).map
        ((CategoryTheory.Quotient.functor I.rel).map f) =
      (CategoryTheory.Quotient.functor J.rel).map
        (E.functor.map f) :=
  rfl

instance quotientMap_full :
    (quotientMap E I J map_mem_iff).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨g, rfl⟩ :=
      (CategoryTheory.Quotient.functor J.rel).map_surjective f
    obtain ⟨h, rfl⟩ := E.functor.map_surjective g
    exact
      ⟨(CategoryTheory.Quotient.functor I.rel).map h, rfl⟩

instance quotientMap_faithful :
    (quotientMap E I J map_mem_iff).Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ h
    change
      (CategoryTheory.Quotient.functor J.rel).map
          (E.functor.map f) =
        (CategoryTheory.Quotient.functor J.rel).map
          (E.functor.map g) at h
    rw [CategoryTheory.Quotient.functor_map_eq_iff] at h
    apply CategoryTheory.Quotient.sound I.rel
    change E.functor.map f - E.functor.map g ∈ J.hom _ _ at h
    rw [← E.functor.map_sub] at h
    exact (map_mem_iff (f - g)).1 h

instance quotientMap_essSurj :
    (quotientMap E I J map_mem_iff).EssSurj where
  mem_essImage := by
    rintro ⟨Y⟩
    let X := E.functor.objPreimage Y
    refine
      ⟨(CategoryTheory.Quotient.functor I.rel).obj X, ?_⟩
    exact
      ⟨(CategoryTheory.Quotient.functor J.rel).mapIso
        (E.functor.objObjPreimageIso Y)⟩

instance quotientMap_isEquivalence :
    (quotientMap E I J map_mem_iff).IsEquivalence where

/-- An additive equivalence identifying two Hom ideals induces an
equivalence of the corresponding quotient categories. -/
def quotientEquivalence :
    CategoryTheory.Quotient I.rel ≌
      CategoryTheory.Quotient J.rel :=
  (quotientMap E I J map_mem_iff).asEquivalence

end HomIdeal

end CategoricalIdeal

namespace CategoricalAdditiveSubcategory

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasFiniteBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

namespace Subcategory

/-- A morphism in the full category on `P` factors through the
additive subcategory `Q` if it factors through one ambient object
belonging to `Q`. -/
def FactorsThrough
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) : Prop :=
  ∃ (M : C), Q.carrier M ∧
    ∃ (left : X.obj ⟶ M) (right : M ⟶ Y.obj),
      left ≫ right = f.hom

private theorem biprod_mem
    (Q : Subcategory C)
    {M N : C}
    (hM : Q.carrier M) (hN : Q.carrier N) :
    Q.carrier (M ⊞ N) := by
  let F : WalkingPair → C := pairFunction M N
  have hF : ∀ j, Q.carrier (F j) := by
    intro j
    cases j with
    | left => exact hM
    | right => exact hN
  have hsum : Q.carrier (biproduct F) :=
    Q.biproduct_mem (FintypeCat.of WalkingPair) F hF
  let b : BinaryBicone M N :=
    (biproduct.bicone F).toBinaryBicone
  have hb : b.IsBilimit :=
    (Bicone.toBinaryBiconeIsBilimit
      (biproduct.bicone F)).symm
      (biproduct.isBilimit F)
  exact Q.iso_mem (biprod.uniqueUpToIso M N hb) hsum

private theorem factorsThrough_zero
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} :
    FactorsThrough P Q (0 : X ⟶ Y) := by
  let F : Empty → C := Empty.elim
  let M : C := biproduct F
  have hM : Q.carrier M :=
    Q.biproduct_mem (FintypeCat.of Empty) F
      (fun j ↦ j.elim)
  exact ⟨M, hM, 0, 0, by simp⟩

private theorem FactorsThrough.add
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} {f g : X ⟶ Y}
    (hf : FactorsThrough P Q f)
    (hg : FactorsThrough P Q g) :
    FactorsThrough P Q (f + g) := by
  rcases hf with ⟨M, hM, leftM, rightM, hfacM⟩
  rcases hg with ⟨N, hN, leftN, rightN, hfacN⟩
  refine ⟨M ⊞ N, biprod_mem Q hM hN,
    biprod.lift leftM leftN,
    biprod.desc rightM rightN, ?_⟩
  rw [biprod.lift_desc, hfacM, hfacN]
  rfl

private theorem FactorsThrough.neg
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} {f : X ⟶ Y}
    (hf : FactorsThrough P Q f) :
    FactorsThrough P Q (-f) := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  refine ⟨M, hM, -left, right, ?_⟩
  rw [Preadditive.neg_comp, hfac]
  change
    -(P.carrier.ι.map f) =
      P.carrier.ι.map (-f)
  exact (P.carrier.ι.map_neg (f := f)).symm

/-- The additive two-sided Hom ideal in `P` consisting of maps which
factor through `Q`. -/
def factorThroughIdeal (P Q : Subcategory C) :
    CategoricalIdeal.HomIdeal P.FullSubcategory where
  hom X Y :=
    { carrier := FactorsThrough P Q
      zero_mem' := factorsThrough_zero P Q
      add_mem' := fun hf hg ↦ hf.add P Q hg
      neg_mem' := fun hf ↦ hf.neg P Q }
  precomp := by
    intro X Y Z f g hg
    rcases hg with ⟨M, hM, left, right, hfac⟩
    exact
      ⟨M, hM, f.hom ≫ left, right,
        by rw [Category.assoc, hfac]; rfl⟩
  postcomp := by
    intro X Y Z f g hf
    rcases hf with ⟨M, hM, left, right, hfac⟩
    exact
      ⟨M, hM, left, right ≫ g.hom,
        by rw [← Category.assoc, hfac]; rfl⟩

@[simp]
theorem mem_factorThroughIdeal_iff
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    f ∈ (factorThroughIdeal P Q).hom X Y ↔
      FactorsThrough P Q f :=
  Iff.rfl

/-- A generic full additive subcategory has finite biproducts. -/
theorem fullSubcategoryHasFiniteBiproducts
    (P : Subcategory C) :
    HasFiniteBiproducts P.FullSubcategory where
  out n :=
    { has_biproduct := fun A ↦ by
        classical
        let B : P.FullSubcategory :=
          ⟨biproduct (fun j : Fin n ↦ (A j).obj),
            P.biproduct_mem (FintypeCat.of (Fin n))
              (fun j : Fin n ↦ (A j).obj)
              (fun j ↦ (A j).property)⟩
        let b : Bicone A :=
          { pt := B
            π := fun j ↦ ObjectProperty.homMk
              (biproduct.π (fun k : Fin n ↦ (A k).obj) j)
            ι := fun j ↦ ObjectProperty.homMk
              (biproduct.ι (fun k : Fin n ↦ (A k).obj) j)
            ι_π := by
              intro j k
              apply ObjectProperty.hom_ext
              by_cases h : j = k
              · subst k
                simp only [eqToHom_refl]
                exact biproduct.ι_π_self _ _
              · simp only [dif_neg h]
                exact biproduct.ι_π_ne _ h }
        apply HasBiproduct.mk
        refine
          { bicone := b
            isBilimit := isBilimitOfTotal b ?_ }
        let G := ObjectProperty.ι P.carrier
        apply G.map_injective
        rw [G.map_sum, G.map_id]
        exact biproduct.total }

/-- The quotient by a factor-through ideal inherits finite biproducts from
the upper additive subcategory. -/
theorem factorQuotientHasFiniteBiproducts
    (P Q : Subcategory C) :
    let I := factorThroughIdeal P Q
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) := by
  dsimp only
  let I := factorThroughIdeal P Q
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts P.FullSubcategory :=
    fullSubcategoryHasFiniteBiproducts P
  let F := CategoryTheory.Quotient.functor I.rel
  letI : HasFiniteProducts
      (CategoryTheory.Quotient I.rel) :=
    Functor.hasFiniteProducts_of_additive_of_essSurj F
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Cosemisimplicity of `Q` inside `P`, expressed as zero categorical
radical of the literal factor-through ideal quotient `P / [Q]`. -/
def FactorIsCosemisimple
    (P Q : Subcategory C) : Prop :=
  let I := factorThroughIdeal P Q
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    factorQuotientHasFiniteBiproducts P Q
  CategoricalRadical.HasZeroRadical
    (CategoryTheory.Quotient I.rel)

variable (E : C ≌ D)

/-- The restricted equivalence on a replete additive subcategory. -/
abbrev restrictedEquivalence (P : Subcategory C) :
    P.FullSubcategory ≌
      (P.transport E).FullSubcategory :=
  CategoricalRejective.Equivalence.restricted E P.carrier

/-- An ambient additive equivalence preserves and reflects the
factor-through ideal on corresponding full additive subcategories. -/
theorem restrictedEquivalence_map_mem_factorThroughIdeal_iff
    (P Q : Subcategory C)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    letI : E.functor.Additive :=
      Functor.additive_of_preserves_binary_products E.functor
    (restrictedEquivalence E P).functor.map f ∈
        (factorThroughIdeal (P.transport E) (Q.transport E)).hom _ _ ↔
      f ∈ (factorThroughIdeal P Q).hom X Y := by
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  constructor
  · rintro ⟨N, hN, left, right, hfac⟩
    let left' : E.functor.obj X.obj ⟶ N := left
    let right' : N ⟶ E.functor.obj Y.obj := right
    have hfac' :
        left' ≫ right' = E.functor.map f.hom := by
      exact hfac
    let a' :
        E.functor.obj X.obj ⟶
          E.functor.obj (E.inverse.obj N) :=
      left' ≫ E.counitIso.inv.app N
    let b' :
        E.functor.obj (E.inverse.obj N) ⟶
          E.functor.obj Y.obj :=
      E.counitIso.hom.app N ≫ right'
    obtain ⟨a, ha⟩ := E.functor.map_surjective a'
    obtain ⟨b, hb⟩ := E.functor.map_surjective b'
    refine
      ⟨E.inverse.obj N, hN, a, b, ?_⟩
    apply E.functor.map_injective
    rw [E.functor.map_comp, ha, hb]
    simp [a', b', Category.assoc, hfac']
  · rintro ⟨M, hM, left, right, hfac⟩
    refine
      ⟨E.functor.obj M,
        Q.iso_mem (E.unitIso.app M) hM,
        E.functor.map left, E.functor.map right, ?_⟩
    change
      E.functor.map left ≫ E.functor.map right =
        E.functor.map f.hom
    rw [← E.functor.map_comp, hfac]

/-- The quotient by maps factoring through an additive subcategory is
invariant under ambient equivalence. -/
def factorQuotientEquivalence
    (E : C ≌ D) (P Q : Subcategory C) :
    CategoryTheory.Quotient (factorThroughIdeal P Q).rel ≌
      CategoryTheory.Quotient
        (factorThroughIdeal
          (P.transport E) (Q.transport E)).rel := by
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  letI : (P.carrier.ι ⋙ E.functor).Additive :=
    inferInstance
  letI : (restrictedEquivalence E P).functor.Additive := by
    constructor
    intro X Y f g
    apply ObjectProperty.hom_ext
    change
      E.functor.map (P.carrier.ι.map (f + g)) =
        E.functor.map (P.carrier.ι.map f) +
          E.functor.map (P.carrier.ι.map g)
    rw [P.carrier.ι.map_add, E.functor.map_add]
  exact
    CategoricalIdeal.HomIdeal.quotientEquivalence
      (restrictedEquivalence E P)
      (factorThroughIdeal P Q)
      (factorThroughIdeal
        (P.transport E) (Q.transport E))
      (restrictedEquivalence_map_mem_factorThroughIdeal_iff
        E P Q)

end Subcategory

end CategoricalAdditiveSubcategory

namespace IndecomposableSkeleton

universe uR uι w vD uD

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, w} R ι)
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasFiniteBiproducts D]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

open CategoricalAdditiveSubcategory
open CategoricalAdditiveSubcategory.ModuleBridge

/-- The generic additive-subcategory wrapper on the existing literal
module category `add S`. -/
abbrev genericGeneratedSubcategory (S : Set ι) :
    Subcategory (FGModuleCat.{w} R) :=
  ofFGModuleSubcategory (σ.generated S)

/-- The transported copy of `add S` in an equivalent preadditive
target category. -/
abbrev transportedGeneratedSubcategory
    (E : FGModuleCat.{w} R ≌ D) (S : Set ι) :
    Subcategory D :=
  (σ.genericGeneratedSubcategory S).transport E

/-- The factor-through ideal between two transported generated
subcategories. -/
abbrev transportedFactorIdeal
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι) :
    CategoricalIdeal.HomIdeal
      (σ.transportedGeneratedSubcategory E S).FullSubcategory :=
  Subcategory.factorThroughIdeal
    (σ.transportedGeneratedSubcategory E S)
    (σ.transportedGeneratedSubcategory E T)

/-- The corresponding target factor category. -/
abbrev TransportedFactorQuotient
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι) :=
  CategoryTheory.Quotient
    (σ.transportedFactorIdeal E S T).rel

/-- The existing module-specific factor-through ideal and the generic
factor-through ideal have literally the same membership predicate. -/
theorem mem_genericFactorThroughIdeal_iff_mem_factorThroughAddIdeal
    (S T : Set ι)
    {X Y : σ.AddCategory S} (f : X ⟶ Y) :
    f ∈
        (Subcategory.factorThroughIdeal
          (σ.genericGeneratedSubcategory S)
          (σ.genericGeneratedSubcategory T)).hom X Y ↔
      f ∈ (σ.factorThroughAddIdeal S T).hom X Y :=
  Iff.rfl

/-- The restricted ambient equivalence preserves and reflects the
existing module-side factor-through ideal against the generic ideal
in the transported target. -/
theorem restrictedEquivalence_map_mem_transportedFactorIdeal_iff
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι)
    {X Y : σ.AddCategory S} (f : X ⟶ Y) :
    letI : E.functor.Additive :=
      Functor.additive_of_preserves_binary_products E.functor
    (Subcategory.restrictedEquivalence E
        (σ.genericGeneratedSubcategory S)).functor.map f ∈
        (Subcategory.factorThroughIdeal
          (σ.transportedGeneratedSubcategory E S)
          (σ.transportedGeneratedSubcategory E T)).hom _ _ ↔
      f ∈ (σ.factorThroughAddIdeal S T).hom X Y := by
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  exact
    (Subcategory.restrictedEquivalence_map_mem_factorThroughIdeal_iff
      E
      (σ.genericGeneratedSubcategory S)
      (σ.genericGeneratedSubcategory T)
      f).trans
        (σ.mem_genericFactorThroughIdeal_iff_mem_factorThroughAddIdeal
          S T f)

/-- The literal module-side factor quotient `add S / [add T]` is
equivalent to the corresponding factor quotient in any equivalent
preadditive target. -/
def transportedFactorQuotientEquivalence
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι) :
    CategoryTheory.Quotient
        (σ.factorThroughAddIdeal S T).rel ≌
      CategoryTheory.Quotient
        (Subcategory.factorThroughIdeal
          (σ.transportedGeneratedSubcategory E S)
          (σ.transportedGeneratedSubcategory E T)).rel := by
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  let P := σ.genericGeneratedSubcategory S
  let EP := Subcategory.restrictedEquivalence E P
  letI : (P.carrier.ι ⋙ E.functor).Additive :=
    inferInstance
  let hEP : EP.functor.Additive := by
    constructor
    intro X Y f g
    apply ObjectProperty.hom_ext
    change
      E.functor.map (P.carrier.ι.map (f + g)) =
        E.functor.map (P.carrier.ι.map f) +
          E.functor.map (P.carrier.ι.map g)
    rw [P.carrier.ι.map_add, E.functor.map_add]
  exact
    @CategoricalIdeal.HomIdeal.quotientEquivalence
      _ _ _ _ _ _ EP hEP
      (σ.factorThroughAddIdeal S T)
      (Subcategory.factorThroughIdeal
        (σ.transportedGeneratedSubcategory E S)
        (σ.transportedGeneratedSubcategory E T))
      (σ.restrictedEquivalence_map_mem_transportedFactorIdeal_iff
        E S T)

/-- The target factor quotient has finite biproducts, transported from
the literal module-side quotient equivalence. -/
theorem transportedFactorQuotientHasFiniteBiproducts
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι) :
    let J := σ.transportedFactorIdeal E S T
    letI : Preadditive (CategoryTheory.Quotient J.rel) :=
      J.quotientPreadditive
    HasFiniteBiproducts
      (CategoryTheory.Quotient J.rel) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S T
  let J := σ.transportedFactorIdeal E S T
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : Preadditive (CategoryTheory.Quotient J.rel) :=
    J.quotientPreadditive
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S T
  exact
    CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
      (σ.transportedFactorQuotientEquivalence E S T)

/-- Cosemisimplicity of a target factor means that its categorical
radical is zero. -/
def TransportedFactorIsCosemisimple
    (E : FGModuleCat.{w} R ≌ D)
    (S T : Set ι) : Prop :=
  let J := σ.transportedFactorIdeal E S T
  letI : Preadditive (CategoryTheory.Quotient J.rel) :=
    J.quotientPreadditive
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient J.rel) :=
    σ.transportedFactorQuotientHasFiniteBiproducts E S T
  CategoricalRadical.HasZeroRadical
    (CategoryTheory.Quotient J.rel)

/-- The literal one-point module factor is cosemisimple exactly when
the corresponding target factor is. -/
theorem onePointFactorIsCosemisimple_iff_transported
    (E : FGModuleCat.{w} R ≌ D)
    (S : Set ι) (x : ι) :
    σ.OnePointFactorIsCosemisimple S x ↔
      σ.TransportedFactorIsCosemisimple
        E S (S \ {x}) := by
  let I := σ.factorThroughAddIdeal S (S \ {x})
  let J := σ.transportedFactorIdeal E S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : Preadditive (CategoryTheory.Quotient J.rel) :=
    J.quotientPreadditive
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S (S \ {x})
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient J.rel) :=
    σ.transportedFactorQuotientHasFiniteBiproducts
      E S (S \ {x})
  change
    CategoricalRadical.HasZeroRadical
        (CategoryTheory.Quotient I.rel) ↔
      CategoricalRadical.HasZeroRadical
        (CategoryTheory.Quotient J.rel)
  exact
    CategoricalRadical.hasZeroRadical_iff_of_equivalence
      (σ.transportedFactorQuotientEquivalence
        E S (S \ {x}))

namespace LegalQuotientDeletionChain

variable [Fintype ι]

/-- An arbitrary saturated endpoint chain in the full target poset of
ambient right-rejective additive subcategories.  No preselected source
support chain is part of this data. -/
abbrev SaturatedTargetRightRejectiveChain
    (E : FGModuleCat.{w} R ≌ D) :=
  OpConjecture.SetClosure.SaturatedOrderDeletionChain
    (qClosedSupportTargetRightRejectiveOrderIso σ E)

/-- An arbitrary saturated total right-rejective target chain: its terms
are ambient right rejective by their type, and every successive literal
factor is cosemisimple. -/
structure SaturatedTotalTargetRightRejectiveChain
    (E : FGModuleCat.{w} R ≌ D)
    extends SaturatedTargetRightRejectiveChain σ E where
  step_cosemisimple :
    ∀ i : Fin (Fintype.card ι),
      Subcategory.FactorIsCosemisimple
        (term i.castSucc).1
        (term i.succ).1

/-- Every arbitrary saturated target right-rejective endpoint chain pulls
back to a genuine maximal quotient-closed flag.  In particular, this
applies after forgetting cosemisimplicity from any saturated total target
chain. -/
def closedFlagOfSaturatedTargetRightRejective
    (E : FGModuleCat.{w} R ≌ D)
    (d : SaturatedTargetRightRejectiveChain σ E) :
    OpConjecture.SetClosure.ClosedFlag σ.qClosure :=
  d.toClosedFlag

/-- Consequently every arbitrary saturated total right-rejective chain in
the target arises from a maximal quotient-closed flag after pullback along
the rejective order isomorphism. -/
def closedFlagOfSaturatedTotalTargetRightRejective
    (E : FGModuleCat.{w} R ≌ D)
    (d : SaturatedTotalTargetRightRejectiveChain σ E) :
    OpConjecture.SetClosure.ClosedFlag σ.qClosure :=
  closedFlagOfSaturatedTargetRightRejective
    σ E d.toSaturatedOrderDeletionChain

/-- The target right-rejective term has exactly the transported
generated subcategory as its underlying additive subcategory. -/
theorem targetRightRejectiveTerm_subcategory
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (i : Fin (Fintype.card ι + 1)) :
    (targetRightRejectiveTerm σ E d i).1 =
      σ.transportedGeneratedSubcategory E (d.support i) :=
  rfl

/-- Every cosemisimple legal source step transports to a
cosemisimple factor of the corresponding target right-rejective
terms. -/
theorem targetRightRejectiveTerm_step_cosemisimple
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalRightRejectiveChain σ d)
    (i : Fin (Fintype.card ι)) :
    σ.TransportedFactorIsCosemisimple E
      (d.support i.castSucc)
      (d.support i.castSucc \ {d.removed i}) :=
  (σ.onePointFactorIsCosemisimple_iff_transported
    E (d.support i.castSucc) (d.removed i)).1
      (hd.step_cosemisimple i)

/-- Package the transported terms of a source total chain as an arbitrary
target total chain, with no source supports retained in the resulting
structure. -/
def saturatedTotalTargetRightRejectiveChain
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalRightRejectiveChain σ d) :
    SaturatedTotalTargetRightRejectiveChain σ E where
  term i := targetRightRejectiveTerm σ E d i
  top := by
    apply congrArg
      (qClosedSupportTargetRightRejectiveOrderIso σ E)
    apply Subtype.ext
    exact d.top
  bottom := by
    apply congrArg
      (qClosedSupportTargetRightRejectiveOrderIso σ E)
    apply Subtype.ext
    simpa only [closedSupportAt,
      OpConjecture.SetClosure.coe_bot,
      (qClosure_isClosed_empty σ).closure_eq] using
        d.bottom
  step_covBy i :=
    targetRightRejectiveTerm_succ_covBy σ E d i
  step_cosemisimple i := by
    rw [targetRightRejectiveTerm_subcategory σ E d i.castSucc,
      targetRightRejectiveTerm_subcategory σ E d i.succ]
    change
      σ.TransportedFactorIsCosemisimple E
        (d.support i.castSucc) (d.support i.succ)
    rw [d.step i]
    exact
      targetRightRejectiveTerm_step_cosemisimple
        σ E d hd i

/-- The arbitrary target-total-chain presentation attached directly to a
maximal quotient-closed flag. -/
def saturatedTotalTargetRightRejectiveChainOfClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.qClosure) :
    SaturatedTotalTargetRightRejectiveChain σ E :=
  saturatedTotalTargetRightRejectiveChain
    σ E (ofClosedFlag (K := K) σ s)
      (ofClosedFlag_isTotalRightRejectiveChain
        (K := K) σ s)

/-- Pulling back the target chain constructed from a source legal chain
recovers its increasing closed-support enumeration term by term. -/
theorem saturatedTotalTargetRightRejectiveChain_ascending
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalRightRejectiveChain σ d)
    (i : Fin (Fintype.card ι + 1)) :
    (saturatedTotalTargetRightRejectiveChain
        σ E d hd).toSaturatedOrderDeletionChain.ascending i =
      d.ascending i := by
  apply Subtype.ext
  simp [OpConjecture.SetClosure.SaturatedOrderDeletionChain.ascending,
    saturatedTotalTargetRightRejectiveChain,
    targetRightRejectiveTerm, closedSupportAt,
    OpConjecture.SetClosure.LegalDeletionChain.ascending]

/-- Pulling the target chain attached to a maximal flag back along the
rejective order isomorphism recovers that flag. -/
theorem closedFlagOfSaturatedTotalTargetRightRejective_ofClosedFlag
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.qClosure) :
    closedFlagOfSaturatedTotalTargetRightRejective σ E
        (saturatedTotalTargetRightRejectiveChainOfClosedFlag
          (K := K) σ E s) =
      s := by
  let d := ofClosedFlag (K := K) σ s
  let hd : IsTotalRightRejectiveChain σ d :=
    ofClosedFlag_isTotalRightRejectiveChain
      (K := K) σ s
  change
    (saturatedTotalTargetRightRejectiveChain
        σ E d hd).toSaturatedOrderDeletionChain.toClosedFlag =
      s
  calc
    _ = d.toClosedFlag (qClosure_isClosed_empty σ) := by
      apply
        OpConjecture.SetClosure.SaturatedOrderDeletionChain.toClosedFlag_eq_legalToClosedFlag
      exact fun i ↦
        saturatedTotalTargetRightRejectiveChain_ascending
          σ E d hd i
    _ = s :=
      ofClosedFlag_reconstructs (K := K) σ s

/-- A compact target-side package: the transported terms are ambient
right rejective, successive terms are covers, and every successive
factor has zero categorical radical. -/
structure IsTransportedTotalRightRejectiveChain
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ) : Prop where
  term_rightRejective :
    ∀ i : Fin (Fintype.card ι + 1),
      CategoricalRejective.IsRightRejective
        (targetRightRejectiveTerm σ E d i).1.carrier
  step_covBy :
    ∀ i : Fin (Fintype.card ι),
      targetRightRejectiveTerm σ E d i.succ ⋖
        targetRightRejectiveTerm σ E d i.castSucc
  step_cosemisimple :
    ∀ i : Fin (Fintype.card ι),
      σ.TransportedFactorIsCosemisimple E
        (d.support i.castSucc)
        (d.support i.castSucc \ {d.removed i})

/-- Transporting a legal total right-rejective source chain gives the
full target-side package, step by step. -/
theorem isTransportedTotalRightRejectiveChain
    (E : FGModuleCat.{w} R ≌ D)
    (d : Chain σ)
    (hd : IsTotalRightRejectiveChain σ d) :
    IsTransportedTotalRightRejectiveChain σ E d where
  term_rightRejective i :=
    (targetRightRejectiveTerm σ E d i).2
  step_covBy i :=
    targetRightRejectiveTerm_succ_covBy σ E d i
  step_cosemisimple i :=
    targetRightRejectiveTerm_step_cosemisimple
      σ E d hd i

/-- A maximal quotient-closed flag gives the full saturated total
right-rejective chain in the equivalent target category. -/
theorem ofClosedFlag_isTransportedTotalRightRejectiveChain
    {K : Type*} [Field K] [Algebra K R]
    [∀ i : ι, Module K (σ.obj i)]
    [∀ i : ι, IsScalarTower K R (σ.obj i)]
    [∀ i : ι, FiniteDimensional K (σ.obj i)]
    (E : FGModuleCat.{w} R ≌ D)
    (s :
      OpConjecture.SetClosure.ClosedFlag
        σ.qClosure) :
    IsTransportedTotalRightRejectiveChain σ E
      (ofClosedFlag (K := K) σ s) :=
  isTransportedTotalRightRejectiveChain
    σ E (ofClosedFlag (K := K) σ s)
      (ofClosedFlag_isTotalRightRejectiveChain
        (K := K) σ s)

end LegalQuotientDeletionChain

end IndecomposableSkeleton

end OpConjecture
