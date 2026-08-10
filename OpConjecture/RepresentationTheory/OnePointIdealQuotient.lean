import OpConjecture.CategoryTheory.IdealQuotient
import OpConjecture.CategoryTheory.CategoricalRadical
import OpConjecture.RepresentationTheory.OnePointCosemisimple
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The one-point ideal quotient

This file constructs the literal ideal quotient
`add S / [add T]`. For a quotient-closed support `S`, it proves that every
Jacobson-radical endomorphism of a removed indecomposable maps to zero in
`add S / [add (S \ {x})]`.
-/

noncomputable section

namespace OpConjecture.IndecomposableSkeleton

open Set
open CategoryTheory CategoryTheory.Limits

universe uR uι w

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι} (σ : IndecomposableSkeleton.{uR, uι, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The full category `add S`. -/
abbrev AddCategory (S : Set ι) :=
  (σ.generated S).FullSubcategory

/-- The maps in `add S` which factor through an object of `add T`. -/
def factorThroughAddMaps (S T : Set ι)
    (X Y : σ.AddCategory S) : Set (X ⟶ Y) :=
  {f | FactorsThroughAdd σ T f.hom}

private theorem inAdd_biprod
    {T : Set ι} {M N : FGModuleCat.{w} R}
    (hM : σ.InAdd T M) (hN : σ.InAdd T N) :
    σ.InAdd T (M ⊞ N) := by
  let F : WalkingPair → FGModuleCat.{w} R :=
    pairFunction M N
  have hF : ∀ j, σ.InAdd T (F j) := by
    intro j
    cases j with
    | left => exact hM
    | right => exact hN
  have hsum : σ.InAdd T (biproduct F) :=
    inAdd_biproduct σ (FintypeCat.of WalkingPair) F hF
  let b : BinaryBicone M N :=
    (biproduct.bicone F).toBinaryBicone
  have hb : b.IsBilimit :=
    (Bicone.toBinaryBiconeIsBilimit
      (biproduct.bicone F)).symm
      (biproduct.isBilimit F)
  exact
    (inAdd_iff_of_iso σ
      (biprod.uniqueUpToIso M N hb)).1 hsum

private theorem factorsThroughAdd_zero
    (T : Set ι) {X Y : FGModuleCat.{w} R} :
    FactorsThroughAdd σ T (0 : X ⟶ Y) := by
  let F : Empty → FGModuleCat.{w} R := Empty.elim
  let M : FGModuleCat.{w} R := biproduct F
  have hM : σ.InAdd T M :=
    inAdd_biproduct σ (FintypeCat.of Empty) F
      (fun j ↦ j.elim)
  exact ⟨M, hM, 0, 0, by simp⟩

private theorem FactorsThroughAdd.add
    {T : Set ι} {X Y : FGModuleCat.{w} R}
    {f g : X ⟶ Y}
    (hf : FactorsThroughAdd σ T f)
    (hg : FactorsThroughAdd σ T g) :
    FactorsThroughAdd σ T (f + g) := by
  rcases hf with ⟨M, hM, leftM, rightM, hfacM⟩
  rcases hg with ⟨N, hN, leftN, rightN, hfacN⟩
  refine ⟨M ⊞ N, inAdd_biprod σ hM hN,
    biprod.lift leftM leftN,
    biprod.desc rightM rightN, ?_⟩
  rw [biprod.lift_desc, hfacM, hfacN]

private theorem FactorsThroughAdd.neg
    {T : Set ι} {X Y : FGModuleCat.{w} R}
    {f : X ⟶ Y}
    (hf : FactorsThroughAdd σ T f) :
    FactorsThroughAdd σ T (-f) := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  exact ⟨M, hM, -left, right, by simp [hfac]⟩

private theorem factorThroughAddMaps_precomp
    {S T : Set ι} {X Y Z : σ.AddCategory S}
    (f : X ⟶ Y) {g : Y ⟶ Z}
    (hg : g ∈ σ.factorThroughAddMaps S T Y Z) :
    f ≫ g ∈ σ.factorThroughAddMaps S T X Z := by
  rcases hg with ⟨M, hM, left, right, hfac⟩
  refine ⟨M, hM, f.hom ≫ left, right, ?_⟩
  rw [Category.assoc, hfac]
  rfl

private theorem factorThroughAddMaps_postcomp
    {S T : Set ι} {X Y Z : σ.AddCategory S}
    {f : X ⟶ Y} (g : Y ⟶ Z)
    (hf : f ∈ σ.factorThroughAddMaps S T X Y) :
    f ≫ g ∈ σ.factorThroughAddMaps S T X Z := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  refine ⟨M, hM, left, right ≫ g.hom, ?_⟩
  rw [← Category.assoc, hfac]
  rfl

/-- The additive two-sided Hom ideal of maps factoring through `add T`
inside the full additive category `add S`. -/
def factorThroughAddIdeal (S T : Set ι) :
    OpConjecture.CategoricalIdeal.HomIdeal (σ.AddCategory S) where
  hom X Y :=
    { carrier := σ.factorThroughAddMaps S T X Y
      zero_mem' := factorsThroughAdd_zero σ T
      add_mem' := fun hf hg ↦ hf.add σ hg
      neg_mem' := fun hf ↦ hf.neg σ }
  precomp := factorThroughAddMaps_precomp σ
  postcomp := factorThroughAddMaps_postcomp σ

/-- The precise module-theoretic input needed for the one-point factor
category: every radical endomorphism of the surviving indecomposable factors
through the deleted additive subcategory. -/
def DeletedPointRadicalFactorization
    (S : Set ι) (x : ι) : Prop :=
  ∀ (f : σ.obj x ⟶ σ.obj x),
    f.hom.hom ∈
        Ring.jacobson (Module.End R (σ.obj x)) →
      FactorsThroughAdd σ (S \ {x}) f

@[simp]
theorem mem_factorThroughAddIdeal_iff
    {S T : Set ι} {X Y : σ.AddCategory S}
    (f : X ⟶ Y) :
    f ∈ (σ.factorThroughAddIdeal S T).hom X Y ↔
      FactorsThroughAdd σ T f.hom :=
  Iff.rfl

/-- The quotient category `add S / [add T]`. -/
abbrev FactorQuotient (S T : Set ι) :=
  CategoryTheory.Quotient (σ.factorThroughAddIdeal S T).rel

/-- The chosen indecomposable `x`, regarded as an object of `add S`. -/
def addPoint {S : Set ι} {x : ι} (hx : x ∈ S) :
    σ.AddCategory S :=
  ⟨σ.obj x, inAdd_obj σ hx⟩

/-- Every point other than `x` is a zero object in
`add S / [add (S \ {x})]`. -/
theorem quotientDeletedPoint_isZero
    {S : Set ι} {x y : ι}
    (hy : y ∈ S) (hyx : y ≠ x) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    IsZero
      ((CategoryTheory.Quotient.functor I.rel).obj
        (σ.addPoint hy)) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  rw [IsZero.iff_id_eq_zero, ← F.map_id]
  apply (I.map_eq_zero_iff (𝟙 (σ.addPoint hy))).2
  rw [mem_factorThroughAddIdeal_iff]
  exact
    ⟨σ.obj y, inAdd_obj σ ⟨hy, hyx⟩,
      𝟙 (σ.obj y), 𝟙 (σ.obj y), by
        change 𝟙 (σ.obj y) ≫ 𝟙 (σ.obj y) =
          𝟙 (σ.obj y)
        simp⟩

/-- The explicit additive closure `add S` has finite biproducts.

This is kept as a named structure rather than a global instance so callers
can install it only where needed. -/
theorem addCategoryHasFiniteBiproducts
    (S : Set ι) :
    HasFiniteBiproducts (σ.AddCategory S) where
  out n :=
    { has_biproduct := fun A ↦ by
        classical
        let B : σ.AddCategory S :=
          ⟨biproduct (fun j : Fin n ↦ (A j).obj),
            inAdd_biproduct σ (FintypeCat.of (Fin n))
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
        let G :=
          ObjectProperty.ι (σ.generated S).carrier
        apply G.map_injective
        rw [G.map_sum, G.map_id]
        exact biproduct.total }

/-- The factor category inherits finite biproducts from `add S` through
the full, essentially-surjective additive quotient functor. -/
theorem factorQuotientHasFiniteBiproducts
    (S T : Set ι) :
    let I := σ.factorThroughAddIdeal S T
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S T
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts (σ.AddCategory S) :=
    σ.addCategoryHasFiniteBiproducts S
  let F := CategoryTheory.Quotient.functor I.rel
  letI : HasFiniteProducts (CategoryTheory.Quotient I.rel) :=
    Functor.hasFiniteProducts_of_additive_of_essSurj F
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Every object of `add S / [add (S \ {x})]` has a finite-biproduct
presentation whose factors are all isomorphic to the surviving point.

The statement uses an explicit bilimit bicone rather than installing global
chosen finite biproducts on the quotient category. -/
theorem quotientObject_exists_pointBiproduct
    {S : Set ι} {x : ι} (hx : x ∈ S)
    (X : σ.AddCategory S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    let F := CategoryTheory.Quotient.functor I.rel
    ∃ (J : FintypeCat.{0})
      (A : J → CategoryTheory.Quotient I.rel)
      (b : Bicone A),
      b.pt = F.obj X ∧ Nonempty b.IsBilimit ∧
        ∀ j, Nonempty (A j ≅ F.obj (σ.addPoint hx)) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  classical
  obtain ⟨P⟩ := X.property
  letI : Fintype P.index := Fintype.ofFinite P.index
  let Y : P.index → σ.AddCategory S :=
    fun t ↦ σ.addPoint (P.mem t)
  let proj : ∀ t, X ⟶ Y t :=
    fun t ↦ ObjectProperty.homMk
      (P.iso.hom ≫
        biproduct.π
          (fun s : P.index ↦ σ.obj (P.label s)) t)
  let incl : ∀ t, Y t ⟶ X :=
    fun t ↦ ObjectProperty.homMk
      (biproduct.ι
          (fun s : P.index ↦ σ.obj (P.label s)) t ≫
        P.iso.inv)
  let J : FintypeCat.{0} :=
    FintypeCat.of {t : P.index // P.label t = x}
  letI : Fintype J :=
    Subtype.fintype (fun t : P.index ↦ P.label t = x)
  let A : J → CategoryTheory.Quotient I.rel :=
    fun j ↦ F.obj (Y j.1)
  let b : Bicone A :=
    { pt := F.obj X
      π := fun j ↦ F.map (proj j.1)
      ι := fun j ↦ F.map (incl j.1)
      ι_π := by
        intro j k
        by_cases h : j = k
        · subst k
          simp only [eqToHom_refl]
          rw [← F.map_comp, ← F.map_id]
          apply congrArg F.map
          apply ObjectProperty.hom_ext
          simp [incl, proj]
          change
            biproduct.ι
                (fun s : P.index ↦ σ.obj (P.label s)) j.1 ≫
              biproduct.π
                (fun s : P.index ↦ σ.obj (P.label s)) j.1 =
              𝟙 (σ.obj (P.label j.1))
          simp
        · have hv : (j.1 : P.index) ≠ k.1 := by
            intro hv
            apply h
            exact Subtype.ext hv
          simp only [dif_neg h]
          rw [← F.map_comp, ← F.map_zero]
          apply congrArg F.map
          apply ObjectProperty.hom_ext
          simp [incl, proj]
          change
            biproduct.ι
                (fun s : P.index ↦ σ.obj (P.label s)) j.1 ≫
              biproduct.π
                (fun s : P.index ↦ σ.obj (P.label s)) k.1 =
              0
          exact biproduct.ι_π_ne _ hv }
  have htotal_source :
      ∑ t : P.index, proj t ≫ incl t = 𝟙 X := by
    let G :=
      ObjectProperty.ι (σ.generated S).carrier
    apply G.map_injective
    rw [G.map_sum, G.map_id]
    change
      (∑ t : P.index,
        (P.iso.hom ≫
          biproduct.π
            (fun s : P.index ↦ σ.obj (P.label s)) t) ≫
          (biproduct.ι
              (fun s : P.index ↦ σ.obj (P.label s)) t ≫
            P.iso.inv)) =
        𝟙 X.obj
    have htotal :
        (∑ t : P.index,
            biproduct.π
                (fun s : P.index ↦ σ.obj (P.label s)) t ≫
              biproduct.ι
                (fun s : P.index ↦ σ.obj (P.label s)) t) =
          𝟙 (biproduct
            (fun s : P.index ↦ σ.obj (P.label s))) :=
      biproduct.total
    have hconjugated :=
      congrArg
        (fun q ↦ P.iso.hom ≫ q ≫ P.iso.inv)
        htotal
    simpa only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc, Category.comp_id, Category.id_comp,
      P.iso.hom_inv_id] using hconjugated
  have htotal_full :
      ∑ t : P.index,
          F.map (proj t) ≫ F.map (incl t) =
        𝟙 (F.obj X) := by
    simp_rw [← F.map_comp]
    rw [← F.map_sum, htotal_source, F.map_id]
  have hdeleted :
      ∀ (t : P.index), P.label t ≠ x →
        F.map (proj t) ≫ F.map (incl t) = 0 := by
    intro t ht
    have hzero :
        IsZero (F.obj (Y t)) := by
      exact quotientDeletedPoint_isZero
        σ (P.mem t) ht
    rw [hzero.eq_of_tgt (F.map (proj t)) 0, zero_comp]
  have htotal_retained :
      ∑ j : J,
          F.map (proj j.1) ≫ F.map (incl j.1) =
        𝟙 (F.obj X) := by
    have hsplit :=
      Fintype.sum_subtype_add_sum_subtype
        (fun t : P.index ↦ P.label t = x)
        (fun t ↦ F.map (proj t) ≫ F.map (incl t))
    have hcomplement :
        (∑ j : {t : P.index // P.label t ≠ x},
          F.map (proj j.1) ≫ F.map (incl j.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact hdeleted j.1 j.2
    rw [hcomplement, add_zero, htotal_full] at hsplit
    simpa [J] using hsplit
  refine ⟨J, A, b, rfl, ?_, ?_⟩
  · exact ⟨isBilimitOfTotal b (by
      simpa only [b] using htotal_retained)⟩
  · intro j
    let e :
        Y j.1 ≅ σ.addPoint hx :=
      ObjectProperty.isoMk _
        (eqToIso (congrArg σ.obj j.2))
    exact ⟨F.mapIso e⟩

/-- Every Jacobson-radical endomorphism of the removed point maps to zero
in the literal ideal quotient `add S / [add (S \ {x})]`. -/
theorem quotientMap_radicalEndomorphism_eq_zero
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (f : σ.obj x ⟶ σ.obj x)
    (hf :
      f.hom.hom ∈
        Ring.jacobson (Module.End R (σ.obj x))) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    (CategoryTheory.Quotient.functor I.rel).map
        (ObjectProperty.homMk f :
          σ.addPoint hx ⟶ σ.addPoint hx) =
      0 := by
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  apply (I.map_eq_zero_iff
    (ObjectProperty.homMk f :
      σ.addPoint hx ⟶ σ.addPoint hx)).2
  exact radicalEndomorphism_factorsThroughAdd_sdiff
    σ hS hx f hf

/-- Radical factorization, independently of how it was obtained, kills the
corresponding endomorphism in the literal one-point ideal quotient. -/
theorem quotientMap_radicalEndomorphism_eq_zero_of_factorization
    {S : Set ι} {x : ι} (hx : x ∈ S)
    (hfactor : σ.DeletedPointRadicalFactorization S x)
    (f : σ.obj x ⟶ σ.obj x)
    (hf :
      f.hom.hom ∈
        Ring.jacobson (Module.End R (σ.obj x))) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    (CategoryTheory.Quotient.functor I.rel).map
        (ObjectProperty.homMk f :
          σ.addPoint hx ⟶ σ.addPoint hx) =
      0 := by
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  apply (I.map_eq_zero_iff
    (ObjectProperty.homMk f :
      σ.addPoint hx ⟶ σ.addPoint hx)).2
  exact hfactor f hf

/-- Every nonzero endomorphism of the surviving point in the one-point
factor quotient is an isomorphism.

A nonunit ambient lift lies in the local endomorphism-ring radical and is
therefore killed by the quotient; hence a nonzero quotient class has a unit
lift. -/
theorem quotientPoint_isIso_of_ne_zero
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    ∀ q :
        End
        ((CategoryTheory.Quotient.functor I.rel).obj
          (σ.addPoint hx)),
      q ≠ 0 → IsIso q := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  intro q hq
  obtain ⟨f, rfl⟩ := F.map_surjective q
  let f0 : σ.obj x ⟶ σ.obj x := f.hom
  have hfunit :
      IsUnit f0.hom.hom := by
    by_contra hfnonunit
    have hfJ :
        f0.hom.hom ∈
          Ring.jacobson (Module.End R (σ.obj x)) :=
      (OpConjecture.mem_end_jacobson_iff_not_isUnit
        (σ.indecomposable x) (σ.finiteLength x)
        f0.hom.hom).2 hfnonunit
    have hzero :=
      quotientMap_radicalEndomorphism_eq_zero
        σ hS hx f0 hfJ
    have hf0 :
        (ObjectProperty.homMk f0 :
          σ.addPoint hx ⟶ σ.addPoint hx) = f :=
      rfl
    rw [hf0] at hzero
    exact hq hzero
  have hfbij :
      Function.Bijective f0.hom.hom :=
    (Module.End.isUnit_iff f0.hom.hom).1 hfunit
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map f0) := by
    change IsIso f0.hom
    exact
      (ConcreteCategory.isIso_iff_bijective f0.hom).2
        hfbij
  letI : IsIso f0 :=
    isIso_of_reflects_iso f0 U
  letI :
      IsIso
        ((ObjectProperty.ι
          (σ.generated S).carrier).map f) := by
    change IsIso f0
    infer_instance
  letI : IsIso f :=
    isIso_of_reflects_iso f
      (ObjectProperty.ι (σ.generated S).carrier)
  infer_instance

/-- The surviving point has division-like endomorphisms in the factor
category whenever the deleted-point radical factorization property holds. -/
theorem quotientPoint_isIso_of_ne_zero_of_factorization
    {S : Set ι} {x : ι} (hx : x ∈ S)
    (hfactor : σ.DeletedPointRadicalFactorization S x) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    ∀ q :
        End
        ((CategoryTheory.Quotient.functor I.rel).obj
          (σ.addPoint hx)),
      q ≠ 0 → IsIso q := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  intro q hq
  obtain ⟨f, rfl⟩ := F.map_surjective q
  let f0 : σ.obj x ⟶ σ.obj x := f.hom
  have hfunit :
      IsUnit f0.hom.hom := by
    by_contra hfnonunit
    have hfJ :
        f0.hom.hom ∈
          Ring.jacobson (Module.End R (σ.obj x)) :=
      (OpConjecture.mem_end_jacobson_iff_not_isUnit
        (σ.indecomposable x) (σ.finiteLength x)
        f0.hom.hom).2 hfnonunit
    have hzero :=
      quotientMap_radicalEndomorphism_eq_zero_of_factorization
        σ hx hfactor f0 hfJ
    have hf0 :
        (ObjectProperty.homMk f0 :
          σ.addPoint hx ⟶ σ.addPoint hx) = f :=
      rfl
    rw [hf0] at hzero
    exact hq hzero
  have hfbij :
      Function.Bijective f0.hom.hom :=
    (Module.End.isUnit_iff f0.hom.hom).1 hfunit
  let U := forget₂ (FGModuleCat R) (ModuleCat R)
  letI : IsIso (U.map f0) := by
    change IsIso f0.hom
    exact
      (ConcreteCategory.isIso_iff_bijective f0.hom).2
        hfbij
  letI : IsIso f0 :=
    isIso_of_reflects_iso f0 U
  letI :
      IsIso
        ((ObjectProperty.ι
          (σ.generated S).carrier).map f) := by
    change IsIso f0
    infer_instance
  letI : IsIso f :=
    isIso_of_reflects_iso f
      (ObjectProperty.ι (σ.generated S).carrier)
  infer_instance

/-- At a relative split-projective deletion, the lower support is again
quotient closed and the quotient functor kills every Jacobson-radical
endomorphism of the removed point. -/
theorem relativeSplitProjective_deletion_quotientRadicalVanishing
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (hproj : σ.IsRelativeSplitProjective S x) :
    σ.qClosure.IsClosed (S \ {x}) ∧
      ∀ (f : σ.obj x ⟶ σ.obj x)
        (_hf :
          f.hom.hom ∈
            Ring.jacobson (Module.End R (σ.obj x))),
        let I := σ.factorThroughAddIdeal S (S \ {x})
        letI : Preadditive
            (CategoryTheory.Quotient I.rel) :=
          I.quotientPreadditive
        letI :
            (CategoryTheory.Quotient.functor I.rel).Additive :=
          CategoryTheory.Quotient.functor_additive I.rel
            (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
              I.add_compatible f₁ f₂ g₁ g₂ hf hg)
        (CategoryTheory.Quotient.functor I.rel).map
            (ObjectProperty.homMk f :
              σ.addPoint hx ⟶ σ.addPoint hx) =
          0 := by
  constructor
  · exact
      (relativeSplitProjective_deletion_radical_factorization
        σ hS hx hproj).1
  · intro f hf
    exact quotientMap_radicalEndomorphism_eq_zero
      σ hS hx f hf

/-- The endomorphism ring of the surviving point in
`add S / [add (S \ {x})]` has zero Jacobson radical.

Indeed the point remains nonzero in the quotient. A radical quotient
endomorphism lifts to an ambient endomorphism; if that lift were a unit, its
image would be a unit, contradicting properness of the quotient Jacobson
radical. The lift is therefore radical in the local ambient endomorphism
ring, so the one-point factorization theorem kills it. -/
theorem quotientPoint_jacobson_eq_bot
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    Ring.jacobson
        (End
          ((CategoryTheory.Quotient.functor I.rel).obj
            (σ.addPoint hx))) =
      ⊥ := by
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  have hid_ne :
      F.map (𝟙 (σ.addPoint hx)) ≠ 0 := by
    intro hid
    have hmem :=
      (I.map_eq_zero_iff (𝟙 (σ.addPoint hx))).1 hid
    have hfac :=
      (mem_factorThroughAddIdeal_iff
        σ (𝟙 (σ.addPoint hx))).1 hmem
    rcases hfac with ⟨M, hM, left, right, hfactor⟩
    let r : Retract (σ.obj x) M :=
      { i := left
        r := right
        retract := hfactor }
    have hxlower :=
      index_mem_of_retract_inAdd σ r hM
    exact hxlower.2 rfl
  letI : Nontrivial (End (F.obj (σ.addPoint hx))) :=
    ⟨⟨F.map (𝟙 (σ.addPoint hx)), 0, hid_ne⟩⟩
  apply le_antisymm
  · intro q hq
    obtain ⟨f, rfl⟩ := F.map_surjective q
    let f0 : σ.obj x ⟶ σ.obj x := f.hom
    have hf_nonunit :
        ¬ IsUnit f0.hom.hom := by
      intro hfunit
      have hfbij :
          Function.Bijective f0.hom.hom :=
        (Module.End.isUnit_iff f0.hom.hom).1 hfunit
      let U := forget₂ (FGModuleCat R) (ModuleCat R)
      letI : IsIso (U.map f0) := by
        change IsIso f0.hom
        exact
          (ConcreteCategory.isIso_iff_bijective f0.hom).2
            hfbij
      letI : IsIso f0 :=
        isIso_of_reflects_iso f0 U
      letI :
          IsIso
            ((ObjectProperty.ι
              (σ.generated S).carrier).map f) := by
        change IsIso f0
        infer_instance
      letI : IsIso f :=
        isIso_of_reflects_iso f
          (ObjectProperty.ι (σ.generated S).carrier)
      have hmapunit :=
        (CategoryTheory.isUnit_iff_isIso
          (F.map f)).2 inferInstance
      have htop :
          Ring.jacobson
              (End (F.obj (σ.addPoint hx))) = ⊤ :=
        (Ring.jacobson
            (End (F.obj (σ.addPoint hx)))).eq_top_of_isUnit_mem
          hq hmapunit
      have hne :
          Ring.jacobson
              (End (F.obj (σ.addPoint hx))) ≠ ⊤ := by
        intro htop'
        have hjtop :
            Ideal.jacobson
                (⊥ :
                  Ideal
                    (End (F.obj (σ.addPoint hx)))) =
              ⊤ := by
          simpa only [Ideal.jacobson_bot] using htop'
        exact
          bot_ne_top
            ((Ideal.jacobson_eq_top_iff).1 hjtop)
      exact hne htop
    have hfJ :
        f0.hom.hom ∈
          Ring.jacobson (Module.End R (σ.obj x)) :=
      (OpConjecture.mem_end_jacobson_iff_not_isUnit
        (σ.indecomposable x) (σ.finiteLength x)
        f0.hom.hom).2 hf_nonunit
    have hzero :=
      quotientMap_radicalEndomorphism_eq_zero
        σ hS hx f0 hfJ
    have hf0 :
        (ObjectProperty.homMk f0 :
          σ.addPoint hx ⟶ σ.addPoint hx) = f :=
      rfl
    rw [hf0] at hzero
    exact hzero
  · exact bot_le

/-- Every object of the one-point factor quotient is isomorphic to a
chosen finite biproduct of copies of the surviving point. -/
theorem quotientObject_iso_pointBiproduct
    {S : Set ι} {x : ι} (hx : x ∈ S)
    (X : σ.AddCategory S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts
        (CategoryTheory.Quotient I.rel) :=
      σ.factorQuotientHasFiniteBiproducts S (S \ {x})
    let F := CategoryTheory.Quotient.functor I.rel
    ∃ J : FintypeCat.{0},
      Nonempty
        (F.obj X ≅
          ⨁ fun _ : J ↦ F.obj (σ.addPoint hx)) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S (S \ {x})
  let F := CategoryTheory.Quotient.functor I.rel
  obtain ⟨J, A, b, hpt, ⟨hb⟩, hA⟩ :=
    quotientObject_exists_pointBiproduct σ hx X
  let e :
      ∀ j, A j ≅ F.obj (σ.addPoint hx) :=
    fun j ↦ Classical.choice (hA j)
  exact
    ⟨J,
      ⟨eqToIso hpt.symm ≪≫
        biproduct.uniqueUpToIso A hb ≪≫
          biproduct.mapIso e⟩⟩

/-- The literal one-point factor category
`add S / [add (S \ {x})]` has zero categorical radical.

Every object is a finite biproduct of the surviving point, and every
nonzero endomorphism of that point is invertible. The generic finite-matrix
criterion therefore kills every radical morphism between arbitrary quotient
objects. -/
theorem quotientCategory_hasZeroRadical
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts
        (CategoryTheory.Quotient I.rel) :=
      σ.factorQuotientHasFiniteBiproducts S (S \ {x})
    OpConjecture.CategoricalRadical.HasZeroRadical
      (CategoryTheory.Quotient I.rel) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S (S \ {x})
  let F := CategoryTheory.Quotient.functor I.rel
  apply
    OpConjecture.CategoricalRadical.hasZeroRadical_of_isAdditivelyGeneratedBy
      (quotientPoint_isIso_of_ne_zero σ hS hx)
  intro Q
  obtain ⟨J, ⟨e⟩⟩ :=
    quotientObject_iso_pointBiproduct
      σ hx (F.objPreimage Q)
  exact
    ⟨J,
      ⟨(F.objObjPreimageIso Q).symm ≪≫ e⟩⟩

/-- The one-point factor category has zero categorical radical under the
single explicit radical-factorization hypothesis. -/
theorem quotientCategory_hasZeroRadical_of_factorization
    {S : Set ι} {x : ι} (hx : x ∈ S)
    (hfactor : σ.DeletedPointRadicalFactorization S x) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts
        (CategoryTheory.Quotient I.rel) :=
      σ.factorQuotientHasFiniteBiproducts S (S \ {x})
    OpConjecture.CategoricalRadical.HasZeroRadical
      (CategoryTheory.Quotient I.rel) := by
  dsimp only
  let I := σ.factorThroughAddIdeal S (S \ {x})
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    σ.factorQuotientHasFiniteBiproducts S (S \ {x})
  let F := CategoryTheory.Quotient.functor I.rel
  apply
    OpConjecture.CategoricalRadical.hasZeroRadical_of_isAdditivelyGeneratedBy
      (quotientPoint_isIso_of_ne_zero_of_factorization
        σ hx hfactor)
  intro Q
  obtain ⟨J, ⟨e⟩⟩ :=
    quotientObject_iso_pointBiproduct
      σ hx (F.objPreimage Q)
  exact
    ⟨J,
      ⟨(F.objObjPreimageIso Q).symm ≪≫ e⟩⟩

/-- A subobject-closed support has a cosemisimple one-point factor after
deleting any selected indecomposable. -/
theorem quotientCategory_hasZeroRadical_of_sClosed
    {S : Set ι} {x : ι}
    (hS : σ.sClosure.IsClosed S) (hx : x ∈ S) :
    let I := σ.factorThroughAddIdeal S (S \ {x})
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    letI : HasFiniteBiproducts
        (CategoryTheory.Quotient I.rel) :=
      σ.factorQuotientHasFiniteBiproducts S (S \ {x})
    OpConjecture.CategoricalRadical.HasZeroRadical
      (CategoryTheory.Quotient I.rel) := by
  apply quotientCategory_hasZeroRadical_of_factorization σ hx
  intro f hf
  exact
    radicalEndomorphism_factorsThroughAdd_sdiff_of_sClosed
      σ hS hx f hf

/-- Relative split-projective deletion packages both legality of the lower
support and zero Jacobson radical at the one surviving quotient point. -/
theorem relativeSplitProjective_deletion_quotientPoint_jacobson_eq_bot
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (hproj : σ.IsRelativeSplitProjective S x) :
    σ.qClosure.IsClosed (S \ {x}) ∧
      let I := σ.factorThroughAddIdeal S (S \ {x})
      letI : Preadditive (CategoryTheory.Quotient I.rel) :=
        I.quotientPreadditive
      letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
        CategoryTheory.Quotient.functor_additive I.rel
          (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
            I.add_compatible f₁ f₂ g₁ g₂ hf hg)
      Ring.jacobson
          (End
            ((CategoryTheory.Quotient.functor I.rel).obj
              (σ.addPoint hx))) =
        ⊥ := by
  constructor
  · exact
      (relativeSplitProjective_deletion_radical_factorization
        σ hS hx hproj).1
  · exact quotientPoint_jacobson_eq_bot σ hS hx

/-- A relative split-projective deletion is a legal quotient-closed
one-point step, and its literal factor category is cosemisimple in the
sense of having zero categorical radical. -/
theorem relativeSplitProjective_deletion_quotientCategory_hasZeroRadical
    {S : Set ι} {x : ι}
    (hS : σ.qClosure.IsClosed S) (hx : x ∈ S)
    (hproj : σ.IsRelativeSplitProjective S x) :
    σ.qClosure.IsClosed (S \ {x}) ∧
      let I := σ.factorThroughAddIdeal S (S \ {x})
      letI : Preadditive (CategoryTheory.Quotient I.rel) :=
        I.quotientPreadditive
      letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
        CategoryTheory.Quotient.functor_additive I.rel
          (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
            I.add_compatible f₁ f₂ g₁ g₂ hf hg)
      letI : HasFiniteBiproducts
          (CategoryTheory.Quotient I.rel) :=
        σ.factorQuotientHasFiniteBiproducts S (S \ {x})
      OpConjecture.CategoricalRadical.HasZeroRadical
        (CategoryTheory.Quotient I.rel) := by
  constructor
  · exact
      (relativeSplitProjective_deletion_radical_factorization
        σ hS hx hproj).1
  · exact quotientCategory_hasZeroRadical σ hS hx

end OpConjecture.IndecomposableSkeleton
