import OpConjecture.RepresentationTheory.TsukamotoRadicalSandwichBridge

/-!
# The radical-sandwich-to-cosemisimplicity converse

This file proves the reverse direction of Tsukamoto's Lemma 3.18.  A
radical-sandwich identity for two principal idempotent ideals forces the
corresponding additive factor category to have zero categorical radical.
The converse direction needs no Artinianity or containment hypothesis.

The proof first controls the endomorphism radical of the image of the
principal generator.  Finite retract generation then propagates this
vanishing to the entire factor category.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace OpConjecture.TsukamotoRadicalSandwichConverse

universe v u

section Categorical

variable {C : Type u} [Category.{v} C] [Preadditive C]

lemma isIso_one_sub_comp
    {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (𝟙 X - a ≫ b)] :
    IsIso (𝟙 Y - b ≫ a) :=
  CategoricalRadical.isIso_one_sub_comp a b

lemma isRadicalMorphism_precomp
    {W X Y : C} (a : W ⟶ X) (f : X ⟶ Y)
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    CategoricalRadical.IsRadicalMorphism (a ≫ f) := by
  intro g
  haveI :
      IsIso (𝟙 X - (f ≫ g) ≫ a) := by
    simpa only [Category.assoc] using hf (g ≫ a)
  simpa only [Category.assoc] using
    (isIso_one_sub_comp (f ≫ g) a)

lemma isRadicalMorphism_postcomp
    {X Y Z : C} (f : X ⟶ Y) (b : Y ⟶ Z)
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    CategoricalRadical.IsRadicalMorphism (f ≫ b) := by
  intro g
  simpa only [Category.assoc] using hf (b ≫ g)

lemma isRadicalMorphism_comp
    {W X Y Z : C} (a : W ⟶ X) (f : X ⟶ Y)
    (b : Y ⟶ Z)
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    CategoricalRadical.IsRadicalMorphism (a ≫ f ≫ b) := by
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp (a ≫ f) b
      (isRadicalMorphism_precomp a f hf)

variable [HasFiniteBiproducts C]

def IsFiniteRetractGeneratedBy (P : C) : Prop :=
  ∀ X : C, ∃ n : ℕ,
    Nonempty (Retract X (⨁ fun _ : Fin n ↦ P))

theorem radicalMorphism_eq_zero_between_biproducts_of_generatorEnd
    {P : C}
    (hP : ∀ a : End P,
      CategoricalRadical.IsRadicalMorphism a → a = 0)
    {J K : Type} [Fintype J] [Fintype K]
    (f :
      (⨁ fun _ : J ↦ P) ⟶
        ⨁ fun _ : K ↦ P)
    (hf : CategoricalRadical.IsRadicalMorphism f) :
    f = 0 := by
  have hc :
      ∀ j k, biproduct.components f j k = 0 := by
    intro j k
    exact hP _ <|
      isRadicalMorphism_comp
        (biproduct.ι (fun _ : J ↦ P) j)
        f
        (biproduct.π (fun _ : K ↦ P) k)
        hf
  rw [← biproduct.components_matrix f]
  simp only [hc]
  ext
  simp

theorem hasZeroRadical_of_isFiniteRetractGeneratedBy
    {P : C}
    (hP : ∀ a : End P,
      CategoricalRadical.IsRadicalMorphism a → a = 0)
    (hgen : IsFiniteRetractGeneratedBy P) :
    CategoricalRadical.HasZeroRadical C := by
  intro X Y f hf
  obtain ⟨n, ⟨rX⟩⟩ := hgen X
  obtain ⟨m, ⟨rY⟩⟩ := hgen Y
  let f' :
      (⨁ fun _ : Fin n ↦ P) ⟶
        ⨁ fun _ : Fin m ↦ P :=
    rX.r ≫ f ≫ rY.i
  have hf' :
      CategoricalRadical.IsRadicalMorphism f' :=
    isRadicalMorphism_comp rX.r f rY.i hf
  have hfzero : f' = 0 :=
    radicalMorphism_eq_zero_between_biproducts_of_generatorEnd
      hP f' hf'
  calc
    f = rX.i ≫ f' ≫ rY.r := by
      simp [f', Category.assoc]
    _ = 0 := by simp [hfzero]

end Categorical

section Ring

variable {R : Type u} [Ring R]

theorem isUnit_one_add_mul_of_corner_isUnit
    {p x : R} (hp : IsIdempotentElem p)
    (_hpx : p * x = x) (hxp : x * p = x)
    (y : R)
    (hu :
      IsUnit
        (show hp.Corner from
          ⟨p + p * y * x, by
            apply (Subsemigroup.mem_corner_iff hp).mpr
            constructor
            · simp only [mul_add, ← mul_assoc, hp.eq]
            · simp only [add_mul, hp.eq]
              rw [mul_assoc (p * y) x p, hxp]⟩)) :
    IsUnit (1 + y * x) := by
  let u : hp.Corner :=
    ⟨p + p * y * x, by
      apply (Subsemigroup.mem_corner_iff hp).mpr
      constructor
      · simp only [mul_add, ← mul_assoc, hp.eq]
      · simp only [add_mul, hp.eq]
        rw [mul_assoc (p * y) x p, hxp]⟩
  obtain ⟨v, huv, hvu⟩ :=
    isUnit_iff_exists.mp (show IsUnit u from hu)
  have huv' :
      (p + p * y * x) * v.1 = p :=
    congrArg Subtype.val huv
  have hvu' :
      v.1 * (p + p * y * x) = p :=
    congrArg Subtype.val hvu
  have hpv : p * v.1 = v.1 :=
    (Subsemigroup.mem_corner_iff hp).mp v.property |>.1
  have hvp : v.1 * p = v.1 :=
    (Subsemigroup.mem_corner_iff hp).mp v.property |>.2
  have huv'' :
      v.1 + p * y * x * v.1 = p := by
    simpa only [add_mul, hpv, mul_assoc] using huv'
  have hvu'' :
      v.1 + v.1 * y * x = p := by
    simpa only [mul_add, ← mul_assoc, hvp] using hvu'
  let q : R := 1 - p
  let t : R := q * y * x
  let u₀ : R := p + p * y * x
  let v₀ : R := v.1
  have hq_sq : q * q = q := by
    dsimp only [q]
    noncomm_ring [hp.eq]
  have hpq : p * q = 0 := by
    dsimp only [q]
    rw [mul_sub, mul_one, hp.eq, sub_self]
  have hqp : q * p = 0 := by
    dsimp only [q]
    rw [sub_mul, one_mul, hp.eq, sub_self]
  have hxq : x * q = 0 := by
    dsimp only [q]
    rw [mul_sub, mul_one, hxp, sub_self]
  have hqv : q * v₀ = 0 := by
    dsimp only [q, v₀]
    rw [sub_mul, one_mul, hpv, sub_self]
  have hvq : v₀ * q = 0 := by
    dsimp only [q, v₀]
    rw [mul_sub, mul_one, hvp, sub_self]
  have huq : u₀ * q = 0 := by
    dsimp only [u₀]
    simp only [add_mul, hpq, mul_assoc, hxq,
      mul_zero, add_zero]
  have hqu : q * u₀ = 0 := by
    dsimp only [u₀]
    simp only [mul_add, ← mul_assoc, hqp,
      zero_mul, zero_add]
  have hqt : q * t = t := by
    dsimp only [t]
    simp only [← mul_assoc, hq_sq]
  have htp : t * p = t := by
    dsimp only [t]
    rw [mul_assoc, hxp]
  have htq : t * q = 0 := by
    dsimp only [t]
    simp only [mul_assoc, hxq, mul_zero]
  have hut : u₀ * t = 0 := by
    dsimp only [t]
    simp only [← mul_assoc, huq, zero_mul]
  have hvt : v₀ * t = 0 := by
    dsimp only [t]
    simp only [← mul_assoc, hvq, zero_mul]
  have htt : t * t = 0 := by
    dsimp only [t]
    calc
      q * y * x * (q * y * x) =
          q * y * (x * q) * y * x := by
            noncomm_ring
      _ = 0 := by rw [hxq]; simp
  have htvt : t * v₀ * t = 0 := by
    rw [mul_assoc, hvt, mul_zero]
  have hvu₀ : v₀ * u₀ = p := by
    exact hvu'
  have htvu : t * v₀ * u₀ = t := by
    rw [mul_assoc, hvu₀, htp]
  have huv₀ : u₀ * v₀ = p := by
    exact huv'
  have hutv : u₀ * (t * v₀) = 0 := by
    rw [← mul_assoc, hut, zero_mul]
  have httv : t * (t * v₀) = 0 := by
    rw [← mul_assoc, htt, zero_mul]
  have hqtv : q * (t * v₀) = t * v₀ := by
    rw [← mul_assoc, hqt]
  have htvt' : (t * v₀) * t = 0 := by
    exact htvt
  have htvq : (t * v₀) * q = 0 := by
    rw [mul_assoc, hvq, mul_zero]
  have hpqsum : p + q = 1 := by
    dsimp only [q]
    abel
  have hdecomp :
      1 + y * x = u₀ + t + q := by
    dsimp only [u₀, t, q]
    noncomm_ring
  refine isUnit_iff_exists.mpr
    ⟨v₀ + q - t * v₀, ?_, ?_⟩
  · rw [hdecomp]
    noncomm_ring [huv₀, huq, hut, htq, htt,
      hqv, hq_sq, hqt, hutv, httv, hqtv,
      hpqsum]
  · rw [hdecomp]
    noncomm_ring [hvu₀, hvt, hvq, hqu, hqt,
      hq_sq, htvu, htvt', htvq, hpqsum]

end Ring

section PrincipalModules

open OpConjecture.TsukamotoRadicalSandwichBridge

variable {A : Type u} [Ring A]

local instance finiteProjectives_hasFiniteBiproducts :
    HasFiniteBiproducts (FiniteProjectives A) := by
  letI : HasFiniteBiproducts
      (AuslanderEquivalence.finiteAddClosure
        (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ)).FullSubcategory :=
    CategoricalAdditiveSubcategory.Subcategory.fullSubcategoryHasFiniteBiproducts
      (CategoricalRejective.finiteAddClosureSubcategory
        (ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ))
  exact
    CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
      (ObjectProperty.fullSubcategoryCongr
        (AuslanderEquivalence.finiteAddClosure_regular_eq_finiteProjective
          Aᵐᵒᵖ))

def cornerMap
    {B : Type v} [Ring B]
    (q : A →+* B)
    {e : A} (he : IsIdempotentElem e) :
    he.Corner →+* (he.map q).Corner where
  toFun c :=
    ⟨q c.1, by
      apply (Subsemigroup.mem_corner_iff (he.map q)).mpr
      have hc :=
        (Subsemigroup.mem_corner_iff he).mp c.property
      constructor
      · simpa only [map_mul] using congrArg q hc.1
      · simpa only [map_mul] using congrArg q hc.2⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' c d := by
    apply Subtype.ext
    exact map_mul q c.1 d.1
  map_zero' := by
    apply Subtype.ext
    exact map_zero q
  map_add' c d := by
    apply Subtype.ext
    exact map_add q c.1 d.1

theorem principalCornerEnd_sub
    {e : A} (he : IsIdempotentElem e)
    (c d : he.Corner) :
    principalCornerEnd he (c - d) =
      principalCornerEnd he c -
        principalCornerEnd he d := by
  rw [sub_eq_add_neg, principalCornerEnd_add,
    principalCornerEnd_neg, sub_eq_add_neg]

theorem map_principalCornerEnd_eq_iff_quotient_eq
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (c d : he.Corner) :
    let P := principalSubcategory he
    let Q := principalSubcategory hf
    let I :=
      CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
        P Q
    let F := CategoryTheory.Quotient.functor I.rel
    let q :=
      Ideal.Quotient.mk
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal
    F.map (principalCornerEnd he c) =
          F.map (principalCornerEnd he d) ↔
      q c.1 = q d.1 := by
  dsimp only
  let P := principalSubcategory he
  let Q := principalSubcategory hf
  let I :=
    CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
      P Q
  let F := CategoryTheory.Quotient.functor I.rel
  let q :=
    Ideal.Quotient.mk
      (Tsukamoto.principalTwoSidedIdeal f).asIdeal
  constructor
  · intro h
    have hrel :
        I.rel (principalCornerEnd he c)
          (principalCornerEnd he d) :=
      (CategoryTheory.Quotient.functor_map_eq_iff
        I.rel _ _).mp h
    have hfac :
        CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
          P Q (principalCornerEnd he (c - d)) := by
      change
        principalCornerEnd he (c - d) ∈
          I.hom (principalObject he) (principalObject he)
      rw [principalCornerEnd_sub]
      exact hrel
    have hmem :
        (c - d).1 ∈
          Tsukamoto.principalTwoSidedIdeal f :=
      corner_mem_twoSidedIdeal_of_factorsThrough
        he hf (c - d) hfac
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  · intro h
    have hmem :
        (c - d).1 ∈
          Tsukamoto.principalTwoSidedIdeal f := by
      change
        (c - d).1 ∈
          (Tsukamoto.principalTwoSidedIdeal f).asIdeal
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q ((c - d).1) = 0
      have hval : (c - d).1 = c.1 - d.1 := rfl
      rw [hval, map_sub, h, sub_self]
    have hfac :=
      factorsThrough_of_corner_mem_twoSidedIdeal
        he hf (c - d) hmem
    apply
      (CategoryTheory.Quotient.functor_map_eq_iff
        I.rel _ _).mpr
    change
      principalCornerEnd he c -
          principalCornerEnd he d ∈
        I.hom (principalObject he) (principalObject he)
    rw [← principalCornerEnd_sub]
    change
      CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
        P Q (principalCornerEnd he (c - d))
    simpa only [P, Q] using hfac

theorem quotient_corner_has_inverse_of_map_isIso
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (z : he.Corner) :
    let P := principalSubcategory he
    let Q := principalSubcategory hf
    let I :=
      CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
        P Q
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    let F := CategoryTheory.Quotient.functor I.rel
    let q :=
      Ideal.Quotient.mk
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal
    IsIso (F.map (principalCornerEnd he z)) →
      ∃ w : he.Corner,
        q (z * w).1 = q e ∧
          q (w * z).1 = q e := by
  dsimp only
  let P := principalSubcategory he
  let Q := principalSubcategory hf
  let I :=
    CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
      P Q
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  let q :=
    Ideal.Quotient.mk
      (Tsukamoto.principalTwoSidedIdeal f).asIdeal
  intro hzIso
  letI : IsIso (F.map (principalCornerEnd he z)) :=
    hzIso
  obtain ⟨g₀, hg₀⟩ :=
    F.map_surjective
      (inv (F.map (principalCornerEnd he z)))
  let w : he.Corner := cornerOfPrincipalEnd he g₀
  have hw :
      principalCornerEnd he w = g₀ :=
    principalCornerEnd_cornerOfPrincipalEnd he g₀
  have hzwComp :
      principalCornerEnd he (z * w) =
        principalCornerEnd he w ≫
          principalCornerEnd he z := by
    simpa only [End.mul_def] using
      principalCornerEnd_mul he z w
  have hwzComp :
      principalCornerEnd he (w * z) =
        principalCornerEnd he z ≫
          principalCornerEnd he w := by
    simpa only [End.mul_def] using
      principalCornerEnd_mul he w z
  have hzwMap :
      F.map (principalCornerEnd he (z * w)) =
        F.map (principalCornerEnd he (1 : he.Corner)) := by
    rw [hzwComp, F.map_comp, hw, hg₀,
      IsIso.inv_hom_id]
    have honeEnd :
        principalCornerEnd he (1 : he.Corner) =
          (𝟙 (principalObject he) :
            principalObject he ⟶ principalObject he) :=
      principalCornerEnd_one he
    rw [honeEnd]
    exact (F.map_id (principalObject he)).symm
  have hwzMap :
      F.map (principalCornerEnd he (w * z)) =
        F.map (principalCornerEnd he (1 : he.Corner)) := by
    rw [hwzComp, F.map_comp, hw, hg₀,
      IsIso.hom_inv_id]
    have honeEnd :
        principalCornerEnd he (1 : he.Corner) =
          (𝟙 (principalObject he) :
            principalObject he ⟶ principalObject he) :=
      principalCornerEnd_one he
    rw [honeEnd]
    exact (F.map_id (principalObject he)).symm
  refine ⟨w, ?_, ?_⟩
  · have h :=
      (map_principalCornerEnd_eq_iff_quotient_eq
        he hf (z * w) (1 : he.Corner)).mp hzwMap
    have hone : ((1 : he.Corner).1) = e := rfl
    simpa only [hone] using h
  · have h :=
      (map_principalCornerEnd_eq_iff_quotient_eq
        he hf (w * z) (1 : he.Corner)).mp hwzMap
    have hone : ((1 : he.Corner).1) = e := rfl
    simpa only [hone] using h

theorem quotient_corner_jacobson_eq_zero_of_radicalSandwichZero
    {e f : A}
    (hzero :
      Tsukamoto.RadicalSandwichZero
        (Tsukamoto.principalTwoSidedIdeal e)
        (Tsukamoto.principalTwoSidedIdeal f))
    (a :
      A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)
    (ha :
      a ∈ Ring.jacobson
        (A ⧸
          (Tsukamoto.principalTwoSidedIdeal f).asIdeal)) :
    let q :=
      Ideal.Quotient.mk
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal
    q e * a * q e = 0 := by
  let L := Tsukamoto.principalTwoSidedIdeal f
  let q := Ideal.Quotient.mk L.asIdeal
  let Hbar :=
    Tsukamoto.quotientImage
      (Tsukamoto.principalTwoSidedIdeal e) L
  have himage :
      Hbar =
        Tsukamoto.principalTwoSidedIdeal (q e) := by
    exact map_principalTwoSidedIdeal q e
  have hqe :
      q e ∈ Hbar.asIdeal := by
    rw [himage]
    exact
      TwoSidedIdeal.subset_span
        (Set.mem_singleton (q e))
  have hmem :
      q e * a * q e ∈
        Hbar.asIdeal *
          Ring.jacobson
            (A ⧸ L.asIdeal) *
          Hbar.asIdeal :=
    Ideal.mul_mem_mul
      (Ideal.mul_mem_mul hqe ha) hqe
  change
    Hbar.asIdeal *
          Ring.jacobson
            (A ⧸ L.asIdeal) *
          Hbar.asIdeal =
        ⊥ at hzero
  rw [hzero] at hmem
  exact Ideal.mem_bot.mp hmem

theorem quotientGenerator_radical_eq_zero_of_radicalSandwichZero
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hzero :
      Tsukamoto.RadicalSandwichZero
        (Tsukamoto.principalTwoSidedIdeal e)
        (Tsukamoto.principalTwoSidedIdeal f)) :
    let P := principalSubcategory he
    let Q := principalSubcategory hf
    let I :=
      CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
        P Q
    letI : Preadditive (CategoryTheory.Quotient I.rel) :=
      I.quotientPreadditive
    letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
      CategoryTheory.Quotient.functor_additive I.rel
        (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
          I.add_compatible f₁ f₂ g₁ g₂ hf hg)
    let F := CategoryTheory.Quotient.functor I.rel
    ∀ g : End (F.obj (principalObject he)),
      CategoricalRadical.IsRadicalMorphism g →
        g = 0 := by
  dsimp only
  let P := principalSubcategory he
  let Q := principalSubcategory hf
  let I :=
    CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
      P Q
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  let F := CategoryTheory.Quotient.functor I.rel
  let q :=
    Ideal.Quotient.mk
      (Tsukamoto.principalTwoSidedIdeal f).asIdeal
  let p := q e
  let hp : IsIdempotentElem p := he.map q
  intro g hg
  obtain ⟨g₀, hg₀⟩ := F.map_surjective g
  let c : he.Corner := cornerOfPrincipalEnd he g₀
  have hcEnd :
      principalCornerEnd he c = g₀ :=
    principalCornerEnd_cornerOfPrincipalEnd he g₀
  have hgc :
      F.map (principalCornerEnd he c) = g := by
    rw [hcEnd, hg₀]
  let x :
      A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal :=
    q c.1
  have hpx : p * x = x := by
    have hcLeft :
        e * c.1 = c.1 :=
      (Subsemigroup.mem_corner_iff he).mp c.property |>.1
    dsimp only [p, x]
    rw [← map_mul, hcLeft]
  have hxp : x * p = x := by
    have hcRight :
        c.1 * e = c.1 :=
      (Subsemigroup.mem_corner_iff he).mp c.property |>.2
    dsimp only [p, x]
    rw [← map_mul, hcRight]
  have hxJ :
      x ∈ Ring.jacobson
        (A ⧸
          (Tsukamoto.principalTwoSidedIdeal f).asIdeal) := by
    rw [← Ideal.jacobson_bot]
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
    let d : he.Corner :=
      -sandwichedCorner he r
    let z : he.Corner := 1 - d * c
    have hdcComp :
        principalCornerEnd he (d * c) =
          principalCornerEnd he c ≫
            principalCornerEnd he d := by
      simpa only [End.mul_def] using
        principalCornerEnd_mul he d c
    have honeEnd :
        principalCornerEnd he (1 : he.Corner) =
          (𝟙 (principalObject he) :
            principalObject he ⟶ principalObject he) :=
      principalCornerEnd_one he
    have hzEnd :
        principalCornerEnd he z =
          (𝟙 (principalObject he) :
              principalObject he ⟶ principalObject he) -
            principalCornerEnd he c ≫
              principalCornerEnd he d := by
      dsimp only [z]
      rw [principalCornerEnd_sub,
        honeEnd, hdcComp]
      rfl
    have hzMap :
        F.map (principalCornerEnd he z) =
          𝟙 (F.obj (principalObject he)) -
            g ≫ F.map (principalCornerEnd he d) := by
      rw [hzEnd, F.map_sub, F.map_comp, hgc]
      rw [F.map_id]
    have hzIso :
        IsIso (F.map (principalCornerEnd he z)) := by
      rw [hzMap]
      exact hg (F.map (principalCornerEnd he d))
    obtain ⟨w, hzw, hwz⟩ :=
      quotient_corner_has_inverse_of_map_isIso
        he hf z hzIso
    let zbar : hp.Corner := cornerMap q he z
    let wbar : hp.Corner := cornerMap q he w
    have hzbarUnit : IsUnit zbar := by
      apply isUnit_iff_exists.mpr
      refine ⟨wbar, ?_, ?_⟩
      · apply Subtype.ext
        change q (z * w).1 = q e
        exact hzw
      · apply Subtype.ext
        change q (w * z).1 = q e
        exact hwz
    have hzbar :
        zbar =
          (show hp.Corner from
            ⟨p + p * y * x, by
              apply
                (Subsemigroup.mem_corner_iff hp).mpr
              constructor
              · calc
                  p * (p + p * y * x) =
                      p * p + (p * p) * y * x := by
                        noncomm_ring
                  _ = p + p * y * x := by rw [hp.eq]
              · calc
                  (p + p * y * x) * p =
                      p * p + p * y * (x * p) := by
                        noncomm_ring
                  _ = p + p * y * x := by
                    rw [hp.eq, hxp]⟩) := by
      apply Subtype.ext
      dsimp only [zbar, z, d, cornerMap,
        sandwichedCorner, p, x]
      change
        q (e - (-(e * r * e)) * c.1) =
          q e + q e * y * q c.1
      rw [map_sub, map_mul, map_neg, map_mul,
        map_mul, hr]
      change
        p - -(p * y * p) * x =
          p + p * y * x
      noncomm_ring [hpx]
    rw [hzbar] at hzbarUnit
    have hfullUnit : IsUnit (1 + y * x) :=
      isUnit_one_add_mul_of_corner_isUnit
        hp hpx hxp y hzbarUnit
    obtain ⟨s, hsRight, hsLeft⟩ :=
      isUnit_iff_exists.mp hfullUnit
    refine ⟨s, ?_⟩
    apply Ideal.mem_bot.mpr
    have hs : s * (y * x) + s = 1 := by
      simpa only [mul_add, mul_one, add_comm] using hsLeft
    rw [mul_assoc s y x, hs, sub_self]
  have hcornerZero :
      p * x * p = 0 := by
    exact
      quotient_corner_jacobson_eq_zero_of_radicalSandwichZero
        hzero x hxJ
  have hxZero : x = 0 := by
    calc
      x = p * x * p := by rw [hpx, hxp]
      _ = 0 := hcornerZero
  have hcQuotientZero : q c.1 = q (0 : A) := by
    simpa only [x, map_zero] using hxZero
  have hcMapZero :
      F.map (principalCornerEnd he c) = 0 := by
    have h :=
      (map_principalCornerEnd_eq_iff_quotient_eq
        he hf c (0 : he.Corner)).mpr hcQuotientZero
    have hzeroEnd :
        principalCornerEnd he (0 : he.Corner) =
          (0 :
            principalObject he ⟶ principalObject he) :=
      principalCornerEnd_zero he
    calc
      F.map (principalCornerEnd he c) =
          F.map (principalCornerEnd he (0 : he.Corner)) :=
        h
      _ = F.map
          (0 :
            principalObject he ⟶ principalObject he) := by
        rw [hzeroEnd]
      _ = 0 := F.map_zero _ _
  exact hgc.symm.trans hcMapZero

theorem factorIsCosemisimple_of_radicalSandwichZero
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hzero :
      Tsukamoto.RadicalSandwichZero
        (Tsukamoto.principalTwoSidedIdeal e)
        (Tsukamoto.principalTwoSidedIdeal f)) :
    CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
      (principalSubcategory he)
      (principalSubcategory hf) := by
  let P := principalSubcategory he
  let Q := principalSubcategory hf
  let I :=
    CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
      P Q
  letI : Preadditive (CategoryTheory.Quotient I.rel) :=
    I.quotientPreadditive
  letI : (CategoryTheory.Quotient.functor I.rel).Additive :=
    CategoryTheory.Quotient.functor_additive I.rel
      (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦
        I.add_compatible f₁ f₂ g₁ g₂ hf hg)
  letI : HasFiniteBiproducts P.FullSubcategory :=
    CategoricalAdditiveSubcategory.Subcategory.fullSubcategoryHasFiniteBiproducts
      P
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    CategoricalAdditiveSubcategory.Subcategory.factorQuotientHasFiniteBiproducts
      P Q
  let F := CategoryTheory.Quotient.functor I.rel
  change
    CategoricalRadical.HasZeroRadical
      (CategoryTheory.Quotient I.rel)
  apply hasZeroRadical_of_isFiniteRetractGeneratedBy
    (P := F.obj (principalObject he))
  · exact
      quotientGenerator_radical_eq_zero_of_radicalSandwichZero
        he hf hzero
  · intro X
    let X₀ : P.FullSubcategory := X.as
    have hX :
        AuslanderEquivalence.finiteAddClosure
          (principalFiniteProjective he) X₀.obj := by
      exact X₀.property
    obtain ⟨presentation⟩ := hX
    let J := P.carrier.ι
    let eSum :
        J.obj
            (⨁ fun _ : Fin presentation.n ↦
              principalObject he) ≅
          ⨁ fun _ : Fin presentation.n ↦
            principalFiniteProjective he :=
      J.mapBiproduct
        (fun _ : Fin presentation.n ↦
          principalObject he)
    let r :
        Retract X₀
          (⨁ fun _ : Fin presentation.n ↦
            principalObject he) :=
      { i := ObjectProperty.homMk
          (presentation.retract.i ≫ eSum.inv)
        r := ObjectProperty.homMk
          (eSum.hom ≫ presentation.retract.r)
        retract := by
          apply J.map_injective
          change
            (presentation.retract.i ≫ eSum.inv) ≫
                (eSum.hom ≫ presentation.retract.r) =
              𝟙 X₀.obj
          simp only [Category.assoc, Iso.inv_hom_id_assoc,
            presentation.retract.retract] }
    let rMap := r.map F
    let rBiproduct :
        Retract
          (F.obj
            (⨁ fun _ : Fin presentation.n ↦
              principalObject he))
          (⨁ fun _ : Fin presentation.n ↦
            F.obj (principalObject he)) :=
      Retract.ofIso
        (F.mapBiproduct
          (fun _ : Fin presentation.n ↦
            principalObject he))
    have hFX : F.obj X₀ = X := by
      apply CategoryTheory.Quotient.ext
      rfl
    let rObject : Retract X (F.obj X₀) :=
      Retract.ofIso (eqToIso hFX.symm)
    exact
      ⟨presentation.n,
        ⟨rObject.trans (rMap.trans rBiproduct)⟩⟩

/-- Exact two-sided form of Tsukamoto's Lemma 3.18 for principal
idempotent ideals.  Artinianity is needed only in the forward direction. -/
theorem factorIsCosemisimple_iff_radicalSandwichZero
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    [IsArtinianRing
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)] :
    CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        (principalSubcategory he)
        (principalSubcategory hf) ↔
      Tsukamoto.RadicalSandwichZero
        (Tsukamoto.principalTwoSidedIdeal e)
        (Tsukamoto.principalTwoSidedIdeal f) :=
  ⟨radicalSandwichZero_of_factorIsCosemisimple
      he hf,
    factorIsCosemisimple_of_radicalSandwichZero
      he hf⟩

end PrincipalModules

end OpConjecture.TsukamotoRadicalSandwichConverse
