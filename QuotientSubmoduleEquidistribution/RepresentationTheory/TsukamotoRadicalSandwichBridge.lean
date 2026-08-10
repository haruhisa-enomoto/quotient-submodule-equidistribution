import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagAuslanderPackage
import QuotientSubmoduleEquidistribution.RepresentationTheory.GeneratorApproximationRejective
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Idempotents

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace QuotientSubmoduleEquidistribution.TsukamotoRadicalSandwichBridge

universe v u uK

section Categorical

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

end Categorical

section PrincipalModules

variable {A : Type u} [Ring A]

abbrev FiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ).FullSubcategory

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

def principalFiniteProjective
    {e : A} (he : IsIdempotentElem e) :
    FiniteProjectives A :=
  ⟨Tsukamoto.principalRightModule e,
    Tsukamoto.principalRightModule_mem_finiteProjectiveModules he⟩

def principalSubcategory
    {e : A} (he : IsIdempotentElem e) :
    CategoricalAdditiveSubcategory.Subcategory
      (FiniteProjectives A) :=
  CategoricalRejective.finiteAddClosureSubcategory
    (principalFiniteProjective he)

private theorem finiteAddClosure_self
    {D : Type u} [Category.{v} D] [Preadditive D]
    [HasFiniteBiproducts D] (X : D) :
    AuslanderEquivalence.finiteAddClosure X X := by
  refine ⟨{
    n := 1
    retract := Retract.ofIso
      (biproductUniqueIso
        (fun _ : Fin 1 ↦ X)).symm }⟩

def principalObject
    {e : A} (he : IsIdempotentElem e) :
    (principalSubcategory he).FullSubcategory :=
  ⟨principalFiniteProjective he,
    finiteAddClosure_self (principalFiniteProjective he)⟩

/-- The internal finite-projective subcategory and the literal ambient
module property `add(eA)` have exactly the same objects. -/
theorem principalSubcategory_carrier_iff_addPrincipal
    {e : A} (he : IsIdempotentElem e)
    (X : FiniteProjectives A) :
    (principalSubcategory he).carrier X ↔
      Tsukamoto.addPrincipalRightModule e X.obj := by
  exact
    IndecomposableSkeleton.LegalQuotientDeletionChain.finiteAddClosure_fullSubcategory_iff
        (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ)
        (principalFiniteProjective he) X

def principalCornerLinear
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner) :
    Tsukamoto.principalRightIdeal e →ₗ[Aᵐᵒᵖ]
      Tsukamoto.principalRightIdeal e where
  toFun x :=
    ⟨x.1 * op c.1, by
      have hc : e * c.1 = c.1 :=
        (Subsemigroup.mem_corner_iff he).mp c.property |>.1
      have hgen :
          op e ∈ Tsukamoto.principalRightIdeal e :=
        Ideal.subset_span (Set.mem_singleton (op e))
      have hmem :
          (x.1 * op c.1) * op e ∈
            Tsukamoto.principalRightIdeal e :=
        (Tsukamoto.principalRightIdeal e).mul_mem_left
          (x.1 * op c.1) hgen
      have hop : op c.1 * op e = op c.1 := by
        apply unop_injective
        simpa using hc
      simpa only [mul_assoc, hop] using hmem⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

def principalCornerEnd
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner) :
    End (principalObject he) :=
  ObjectProperty.homMk <|
    ObjectProperty.homMk <|
      ModuleCat.ofHom (principalCornerLinear he c)

@[simp]
theorem principalCornerEnd_apply
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner)
    (x : Tsukamoto.principalRightIdeal e) :
    (principalCornerEnd he c).hom.hom.hom x =
      ⟨x.1 * op c.1,
        (principalCornerLinear he c x).property⟩ :=
  rfl

@[simp]
theorem principalCornerEnd_mul
    {e : A} (he : IsIdempotentElem e)
    (c d : he.Corner) :
    principalCornerEnd he (c * d) =
      principalCornerEnd he c * principalCornerEnd he d := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change
    x.1 * op (c.1 * d.1) =
      (x.1 * op d.1) * op c.1
  rw [op_mul, mul_assoc]

@[simp]
theorem principalCornerEnd_one
    {e : A} (he : IsIdempotentElem e) :
    principalCornerEnd he 1 = 1 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change x.1 * op e = x.1
  exact
    Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
      he x.property

@[simp]
theorem principalCornerEnd_pow
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner) (n : ℕ) :
    principalCornerEnd he (c ^ n) =
      (principalCornerEnd he c) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero, principalCornerEnd_one]
  | succ n ih =>
      rw [pow_succ, principalCornerEnd_mul, ih, pow_succ]

theorem corner_pow_succ_val
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner) (n : ℕ) :
    (c ^ n.succ).1 = c.1 ^ n.succ := by
  induction n with
  | zero =>
      simp only [pow_one]
  | succ n ih =>
      calc
        (c ^ n.succ.succ).1 =
            (c ^ n.succ * c).1 :=
          congrArg Subtype.val
            (pow_succ c n.succ)
        _ = (c ^ n.succ).1 * c.1 := rfl
        _ = c.1 ^ n.succ * c.1 :=
          congrArg (· * c.1) ih
        _ = c.1 ^ n.succ.succ :=
          (pow_succ c.1 n.succ).symm

def principalGenerator
    {e : A} :
    Tsukamoto.principalRightIdeal e :=
  ⟨op e, Ideal.subset_span (Set.mem_singleton (op e))⟩

def cornerOfPrincipalEnd
    {e : A} (he : IsIdempotentElem e)
    (g : End (principalObject he)) :
    he.Corner := by
  let L :
      Tsukamoto.principalRightIdeal e →ₗ[Aᵐᵒᵖ]
        Tsukamoto.principalRightIdeal e :=
    g.hom.hom.hom
  let y := L principalGenerator
  refine ⟨unop y.1, ?_⟩
  apply (Subsemigroup.mem_corner_iff he).mpr
  constructor
  · have hyfixed :
        y.1 * op e = y.1 :=
      Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        he y.property
    have h := congrArg unop hyfixed
    simpa using h
  · have hgen :
        op e •
            (principalGenerator :
              Tsukamoto.principalRightIdeal e) =
          principalGenerator := by
      apply Subtype.ext
      change op e * op e = op e
      apply unop_injective
      simpa using he.eq
    have hlinear :=
      L.map_smul (op e) principalGenerator
    rw [hgen] at hlinear
    have h :=
      congrArg (fun z :
        Tsukamoto.principalRightIdeal e ↦ unop z.1)
        hlinear
    simpa [y] using h.symm

@[simp]
theorem principalCornerEnd_cornerOfPrincipalEnd
    {e : A} (he : IsIdempotentElem e)
    (g : End (principalObject he)) :
    principalCornerEnd he (cornerOfPrincipalEnd he g) = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  let L :
      Tsukamoto.principalRightIdeal e →ₗ[Aᵐᵒᵖ]
        Tsukamoto.principalRightIdeal e :=
    g.hom.hom.hom
  ext x
  have hx :
      x.1 •
          (principalGenerator :
            Tsukamoto.principalRightIdeal e) =
        x := by
    apply Subtype.ext
    change x.1 * op e = x.1
    exact
      Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        he x.property
  have hlinear :=
    L.map_smul x.1 principalGenerator
  rw [hx] at hlinear
  apply Subtype.ext
  change
    x.1 * op (unop (L principalGenerator).1) =
      (L x).1
  simpa using (congrArg Subtype.val hlinear).symm

private abbrev regularRightModule (A : Type u) [Ring A] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ

private abbrev principalIdealOpposite (f : A) : Ideal Aᵐᵒᵖ :=
  (Tsukamoto.principalTwoSidedIdeal f).asIdealOpposite

private abbrev principalIdealOppositeModule (f : A) :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalIdealOpposite f)

/-- Every linear map from `fA` to the regular module takes values in
the two-sided ideal `AfA`. -/
theorem principalMap_mem_twoSidedIdeal
    {f : A} (hf : IsIdempotentElem f)
    (L :
      Tsukamoto.principalRightIdeal f →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ)
    (x : Tsukamoto.principalRightIdeal f) :
    L x ∈ principalIdealOpposite f := by
  let gen :
      Tsukamoto.principalRightIdeal f :=
    principalGenerator
  have hgenFixed :
      op f • gen = gen := by
    apply Subtype.ext
    change op f * op f = op f
    apply unop_injective
    simpa using hf.eq
  have hLgenFixed := L.map_smul (op f) gen
  rw [hgenFixed] at hLgenFixed
  have hbase :
      unop (L gen) ∈
        Tsukamoto.principalTwoSidedIdeal f := by
    have hfix :
        unop (L gen) * f = unop (L gen) := by
      have h :=
        congrArg unop hLgenFixed
      simpa using h.symm
    have hfmem :
        f ∈ Tsukamoto.principalTwoSidedIdeal f :=
      TwoSidedIdeal.subset_span (Set.mem_singleton f)
    rw [← hfix]
    exact
      (Tsukamoto.principalTwoSidedIdeal f).mul_mem_left
        (unop (L gen)) f hfmem
  have hxgen :
      x.1 • gen = x := by
    apply Subtype.ext
    change x.1 * op f = x.1
    exact
      Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        hf x.property
  have hLx := L.map_smul x.1 gen
  rw [hxgen] at hLx
  rw [TwoSidedIdeal.mem_asIdealOpposite]
  have hright :
      unop (L gen) * unop x.1 ∈
        Tsukamoto.principalTwoSidedIdeal f :=
    (Tsukamoto.principalTwoSidedIdeal f).mul_mem_right
      (unop (L gen)) (unop x.1) hbase
  have h :=
    congrArg unop hLx
  simpa [h] using hright

def liftPrincipalMap
    {f : A} (hf : IsIdempotentElem f)
    (g :
      Tsukamoto.principalRightModule f ⟶
        regularRightModule A) :
    Tsukamoto.principalRightModule f ⟶
      principalIdealOppositeModule f :=
  ModuleCat.ofHom <|
    g.hom.codRestrict
      (principalIdealOpposite f)
      (principalMap_mem_twoSidedIdeal hf g.hom)

theorem liftPrincipalMap_comp_subtype
    {f : A} (hf : IsIdempotentElem f)
    (g :
      Tsukamoto.principalRightModule f ⟶
        regularRightModule A) :
    liftPrincipalMap hf g ≫
        ModuleCat.ofHom
          (Submodule.subtype (principalIdealOpposite f)) =
      g := by
  apply ModuleCat.hom_ext
  rfl

def liftFiniteAddMap
    {f : A} (hf : IsIdempotentElem f)
    {M : ModuleCat.{u} Aᵐᵒᵖ}
    (P : AuslanderEquivalence.FiniteAddPresentation
      (Tsukamoto.principalRightModule f) M)
    (g : M ⟶ regularRightModule A) :
    M ⟶ principalIdealOppositeModule f :=
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ ↦ Tsukamoto.principalRightModule f
  P.retract.i ≫
    biproduct.desc (fun j : Fin P.n ↦
      liftPrincipalMap hf
        (biproduct.ι E j ≫ P.retract.r ≫ g))

theorem liftFiniteAddMap_comp_subtype
    {f : A} (hf : IsIdempotentElem f)
    {M : ModuleCat.{u} Aᵐᵒᵖ}
    (P : AuslanderEquivalence.FiniteAddPresentation
      (Tsukamoto.principalRightModule f) M)
    (g : M ⟶ regularRightModule A) :
    liftFiniteAddMap hf P g ≫
        ModuleCat.ofHom
          (Submodule.subtype (principalIdealOpposite f)) =
      g := by
  let E : Fin P.n → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ ↦ Tsukamoto.principalRightModule f
  rw [show liftFiniteAddMap hf P g =
      P.retract.i ≫
        biproduct.desc (fun j : Fin P.n ↦
          liftPrincipalMap hf
            (biproduct.ι E j ≫ P.retract.r ≫ g)) by rfl,
    Category.assoc]
  have hdesc :
      biproduct.desc (fun j : Fin P.n ↦
          liftPrincipalMap hf
            (biproduct.ι E j ≫ P.retract.r ≫ g)) ≫
          ModuleCat.ofHom
            (Submodule.subtype (principalIdealOpposite f)) =
        P.retract.r ≫ g := by
    apply biproduct.hom_ext'
    intro j
    simp only [biproduct.ι_desc_assoc]
    exact liftPrincipalMap_comp_subtype hf _
  rw [hdesc]
  calc
    P.retract.i ≫ P.retract.r ≫ g =
        (P.retract.i ≫ P.retract.r) ≫ g := by
          rw [Category.assoc]
    _ = g := by
      rw [P.retract.retract, Category.id_comp]

/-- Factoring the corner multiplication map through an object of
`add(fA)` forces its corner element to belong to `AfA`. -/
theorem corner_mem_twoSidedIdeal_of_factorsThrough
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (c : he.Corner)
    (hfac :
      CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
        (principalSubcategory he)
        (principalSubcategory hf)
        (principalCornerEnd he c)) :
    c.1 ∈ Tsukamoto.principalTwoSidedIdeal f := by
  rcases hfac with
    ⟨M, hM, left, right, hfactor⟩
  have hMmod :
      AuslanderEquivalence.finiteAddClosure
        (Tsukamoto.principalRightModule f) M.obj :=
    (IndecomposableSkeleton.LegalQuotientDeletionChain.finiteAddClosure_fullSubcategory_iff
        (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ)
        (principalFiniteProjective hf) M).mp hM
  let P := hMmod.some
  let incE :
      Tsukamoto.principalRightModule e ⟶
        regularRightModule A :=
    ModuleCat.ofHom
      (Submodule.subtype
        (Tsukamoto.principalRightIdeal e))
  let left0 :
      Tsukamoto.principalRightModule e ⟶ M.obj :=
    left.hom
  let right0 :
      M.obj ⟶ Tsukamoto.principalRightModule e :=
    right.hom
  have hfactor0 :
      left0 ≫ right0 =
        ModuleCat.ofHom (principalCornerLinear he c) := by
    exact congrArg (fun k ↦ k.hom) hfactor
  let g : M.obj ⟶ regularRightModule A :=
    right0 ≫ incE
  let lift :
      M.obj ⟶ principalIdealOppositeModule f :=
    liftFiniteAddMap hf P g
  let x :
      Tsukamoto.principalRightIdeal e :=
    principalGenerator
  let y : M.obj := left0.hom x
  have hlift :
      ((lift.hom y :
          principalIdealOpposite f) : Aᵐᵒᵖ) =
        g.hom y := by
    have hcomp :=
      ConcreteCategory.congr_hom
        (liftFiniteAddMap_comp_subtype hf P g) y
    exact hcomp
  have hcorner :
      g.hom y = op c.1 := by
    have hpoint :=
      ConcreteCategory.congr_hom hfactor0 x
    have hpointVal :=
      congrArg
        (fun z :
          Tsukamoto.principalRightIdeal e ↦ (z : Aᵐᵒᵖ))
        hpoint
    have hcRight : c.1 * e = c.1 :=
      (Subsemigroup.mem_corner_iff he).mp c.property |>.2
    calc
      g.hom y =
          (right0.hom (left0.hom x)).1 := rfl
      _ =
          (principalCornerLinear he c x).1 :=
        hpointVal
      _ = op c.1 := by
        change op e * op c.1 = op c.1
        apply unop_injective
        simpa using hcRight
  rw [hcorner] at hlift
  have hmem :=
    TwoSidedIdeal.mem_asIdealOpposite.mp
      (lift.hom y).property
  have hval := congrArg unop hlift
  have hval' :
      unop (lift.hom y).1 = c.1 := by
    simpa using hval
  rw [hval'] at hmem
  exact hmem

def sandwichedCorner
    {e : A} (he : IsIdempotentElem e) (a : A) :
    he.Corner :=
  ⟨e * a * e, ⟨a, rfl⟩⟩

@[simp]
theorem principalCornerEnd_zero
    {e : A} (he : IsIdempotentElem e) :
    principalCornerEnd he 0 = 0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change x.1 * op (0 : A) = 0
  simp

@[simp]
theorem principalCornerEnd_add
    {e : A} (he : IsIdempotentElem e)
    (c d : he.Corner) :
    principalCornerEnd he (c + d) =
      principalCornerEnd he c +
        principalCornerEnd he d := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change
    x.1 * op (c.1 + d.1) =
      x.1 * op c.1 + x.1 * op d.1
  have hop : op (c.1 + d.1) =
      op c.1 + op d.1 := rfl
  rw [hop, mul_add]

@[simp]
theorem principalCornerEnd_neg
    {e : A} (he : IsIdempotentElem e)
    (c : he.Corner) :
    principalCornerEnd he (-c) =
      -principalCornerEnd he c := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change x.1 * op (-c.1) = -(x.1 * op c.1)
  have hop : op (-c.1) = -op c.1 := rfl
  rw [hop, mul_neg]

def principalLinearBetween
    {source target c : A}
    (htarget : target * c = c) :
    Tsukamoto.principalRightIdeal source →ₗ[Aᵐᵒᵖ]
      Tsukamoto.principalRightIdeal target where
  toFun x :=
    ⟨x.1 * op c, by
      have hgen :
          op target ∈
            Tsukamoto.principalRightIdeal target :=
        Ideal.subset_span
          (Set.mem_singleton (op target))
      have hmem :
          (x.1 * op c) * op target ∈
            Tsukamoto.principalRightIdeal target :=
        (Tsukamoto.principalRightIdeal target).mul_mem_left
          (x.1 * op c) hgen
      have hop : op c * op target = op c := by
        apply unop_injective
        simpa using htarget
      simpa only [mul_assoc, hop] using hmem⟩
  map_add' x y := Subtype.ext (add_mul _ _ _)
  map_smul' r x := Subtype.ext (mul_assoc _ _ _)

/-- The multiplication map by `e l f r e` factors through the single
principal module `fA`. -/
theorem sandwiched_generator_factorsThrough
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (l r : A) :
    CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
      (principalSubcategory he)
      (principalSubcategory hf)
      (principalCornerEnd he
        (sandwichedCorner he (l * f * r))) := by
  let αc : A := f * r * e
  let βc : A := e * l * f
  have hα : f * αc = αc := by
    dsimp only [αc]
    calc
      f * (f * r * e) = (f * f) * r * e := by
        noncomm_ring
      _ = f * r * e := by rw [hf.eq]
  have hβ : e * βc = βc := by
    dsimp only [βc]
    calc
      e * (e * l * f) = (e * e) * l * f := by
        noncomm_ring
      _ = e * l * f := by rw [he.eq]
  have hβα :
      βc * αc = e * (l * f * r) * e := by
    calc
      βc * αc =
          e * l * (f * f) * r * e := by
        dsimp only [αc, βc]
        noncomm_ring
      _ = e * (l * f * r) * e := by
        rw [hf.eq]
        noncomm_ring
  let left :
      principalFiniteProjective he ⟶
        principalFiniteProjective hf :=
    ObjectProperty.homMk <|
      ModuleCat.ofHom (principalLinearBetween hα)
  let right :
      principalFiniteProjective hf ⟶
        principalFiniteProjective he :=
    ObjectProperty.homMk <|
      ModuleCat.ofHom (principalLinearBetween hβ)
  refine
    ⟨principalFiniteProjective hf,
      finiteAddClosure_self (principalFiniteProjective hf),
      left, right, ?_⟩
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  change
    (x.1 * op αc) * op βc =
      x.1 * op (e * (l * f * r) * e)
  have hop :
      op αc * op βc =
        op (e * (l * f * r) * e) := by
    rw [← op_mul, hβα]
  rw [mul_assoc, hop]

/-- Conversely, every corner element in `AfA` defines an endomorphism
which factors through an object of `add(fA)`. -/
theorem factorsThrough_of_corner_mem_twoSidedIdeal
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (c : he.Corner)
    (hc :
      c.1 ∈ Tsukamoto.principalTwoSidedIdeal f) :
    CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
      (principalSubcategory he)
      (principalSubcategory hf)
      (principalCornerEnd he c) := by
  let I :=
    CategoricalAdditiveSubcategory.Subcategory.factorThroughIdeal
      (principalSubcategory he)
      (principalSubcategory hf)
  have hgeneral :
      ∀ {x : A},
        x ∈ Tsukamoto.principalTwoSidedIdeal f →
        ∀ l r : A,
          principalCornerEnd he
              (sandwichedCorner he (l * x * r)) ∈
            I.hom (principalObject he)
              (principalObject he) := by
    intro x hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        intro l r
        exact sandwiched_generator_factorsThrough
          he hf l r
    | zero =>
        intro l r
        have hs :
            sandwichedCorner he (l * 0 * r) =
              (0 : he.Corner) := by
          apply Subtype.ext
          change e * (l * 0 * r) * e = (0 : A)
          simp
        rw [hs, principalCornerEnd_zero]
        exact (I.hom _ _).zero_mem
    | add x y hx hy hix hiy =>
        intro l r
        have hs :
            sandwichedCorner he (l * (x + y) * r) =
              sandwichedCorner he (l * x * r) +
                sandwichedCorner he (l * y * r) := by
          apply Subtype.ext
          change
            e * (l * (x + y) * r) * e =
              e * (l * x * r) * e +
                e * (l * y * r) * e
          noncomm_ring
        rw [hs, principalCornerEnd_add]
        exact (I.hom _ _).add_mem (hix l r) (hiy l r)
    | neg x hx hix =>
        intro l r
        have hs :
            sandwichedCorner he (l * -x * r) =
              -sandwichedCorner he (l * x * r) := by
          apply Subtype.ext
          change
            e * (l * -x * r) * e =
              -(e * (l * x * r) * e)
          noncomm_ring
        rw [hs, principalCornerEnd_neg]
        exact (I.hom _ _).neg_mem (hix l r)
    | left_absorb a x hx hix =>
        intro l r
        have hs :
            sandwichedCorner he (l * (a * x) * r) =
              sandwichedCorner he ((l * a) * x * r) := by
          apply Subtype.ext
          change
            e * (l * (a * x) * r) * e =
              e * ((l * a) * x * r) * e
          noncomm_ring
        rw [hs]
        exact hix (l * a) r
    | right_absorb b x hx hix =>
        intro l r
        have hs :
            sandwichedCorner he (l * (x * b) * r) =
              sandwichedCorner he (l * x * (b * r)) := by
          apply Subtype.ext
          change
            e * (l * (x * b) * r) * e =
              e * (l * x * (b * r)) * e
          noncomm_ring
        rw [hs]
        exact hix l (b * r)
  have hmem :=
    hgeneral hc 1 1
  have hs :
      sandwichedCorner he (1 * c.1 * 1) = c := by
    apply Subtype.ext
    have hcLeft : e * c.1 = c.1 :=
      (Subsemigroup.mem_corner_iff he).mp c.property |>.1
    have hcRight : c.1 * e = c.1 :=
      (Subsemigroup.mem_corner_iff he).mp c.property |>.2
    change e * (1 * c.1 * 1) * e = c.1
    simp [hcLeft, hcRight]
  rw [hs] at hmem
  exact hmem

/-- The one direction of Tsukamoto Lemma 3.18 needed for a right-strong
heredity step: zero categorical radical of
`add(eA)/[add(fA)]` kills `e J(A/AfA) e`. -/
theorem quotient_corner_jacobson_sandwich_eq_zero
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    [IsArtinianRing
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)]
    (hzero :
      CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        (principalSubcategory he)
        (principalSubcategory hf))
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
  letI : HasFiniteBiproducts
      (CategoryTheory.Quotient I.rel) :=
    CategoricalAdditiveSubcategory.Subcategory.factorQuotientHasFiniteBiproducts P Q
  let F := CategoryTheory.Quotient.functor I.rel
  have hzero' :
      CategoricalRadical.HasZeroRadical
        (CategoryTheory.Quotient I.rel) := by
    exact hzero
  let q :=
    Ideal.Quotient.mk
      (Tsukamoto.principalTwoSidedIdeal f).asIdeal
  obtain ⟨r, hr⟩ :=
    Ideal.Quotient.mk_surjective a
  let c : he.Corner := sandwichedCorner he r
  have hcq :
      q c.1 = q e * a * q e := by
    dsimp only [c, sandwichedCorner]
    rw [map_mul, map_mul, hr]
  have hrad :
      CategoricalRadical.IsRadicalMorphism
        (F.map (principalCornerEnd he c)) := by
    apply
      CategoricalRadical.isRadicalMorphism_of_forall_comp_isNilpotent
    intro g
    obtain ⟨g₀, rfl⟩ := F.map_surjective g
    let d : he.Corner :=
      cornerOfPrincipalEnd he g₀
    have hg₀ :
        principalCornerEnd he d = g₀ :=
      principalCornerEnd_cornerOfPrincipalEnd he g₀
    let z : he.Corner := d * c
    have hcomp :
        End.of
            (F.map (principalCornerEnd he c) ≫
              F.map g₀) =
          F.map (principalCornerEnd he z) := by
      rw [← F.map_comp]
      apply congrArg F.map
      rw [← hg₀]
      set_option linter.unnecessarySimpa false in
        simpa [z, End.mul_def] using
          (principalCornerEnd_mul he d c).symm
    have hcJ :
        q c.1 ∈
          Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal) := by
      rw [hcq]
      have h₁ :=
        Ideal.mul_mem_left
          (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal))
          (q e) ha
      have h₂ :=
        Ideal.mul_mem_right (q e)
          (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal))
          h₁
      exact h₂
    have hzJ :
        q z.1 ∈
          Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal) := by
      have h :=
        Ideal.mul_mem_left
          (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal))
          (q d.1) hcJ
      change q (d.1 * c.1) ∈
        Ring.jacobson
          (A ⧸
            (Tsukamoto.principalTwoSidedIdeal f).asIdeal)
      rw [map_mul]
      exact h
    obtain ⟨n, hn⟩ :=
      (IsArtinianRing.isNilpotent_jacobson_bot
        (R :=
          A ⧸
            (Tsukamoto.principalTwoSidedIdeal f).asIdeal))
    have hn' :
        (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal)) ^ n =
          0 := by
      simpa only [Ideal.jacobson_bot] using hn
    let m := n.succ
    have hm' :
        (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal)) ^ m =
          0 := by
      dsimp only [m]
      rw [show n.succ = n + 1 by rfl,
        Submodule.pow_succ, hn', zero_mul]
    have hzpowMem :
        (q z.1) ^ m ∈
          (Ring.jacobson
            (A ⧸
              (Tsukamoto.principalTwoSidedIdeal f).asIdeal)) ^ m :=
      Ideal.pow_mem_pow hzJ m
    have hzpowZero :
        (q z.1) ^ m = 0 := by
      rw [hm'] at hzpowMem
      exact Ideal.mem_bot.mp hzpowMem
    have hzpowIdeal :
        z.1 ^ m ∈
          (Tsukamoto.principalTwoSidedIdeal f).asIdeal := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_pow] using hzpowZero
    have hzCornerIdeal :
        (z ^ m).1 ∈
          Tsukamoto.principalTwoSidedIdeal f := by
      rw [show m = n.succ by rfl,
        corner_pow_succ_val he z n]
      exact hzpowIdeal
    have hzFactors :=
      factorsThrough_of_corner_mem_twoSidedIdeal
        he hf (z ^ m) hzCornerIdeal
    have hzMapZero :
        F.map (principalCornerEnd he (z ^ m)) = 0 :=
      (I.map_eq_zero_iff
        (principalCornerEnd he (z ^ m))).2 hzFactors
    have hmapPow :
        ∀ k : ℕ,
          (End.of
            (F.map (principalCornerEnd he z))) ^ k =
            End.of
              (F.map ((principalCornerEnd he z) ^ k)) := by
      intro k
      induction k with
      | zero =>
          change
            𝟙 (F.obj (principalObject he)) =
              F.map (𝟙 (principalObject he))
          exact (F.map_id (principalObject he)).symm
      | succ k ih =>
          rw [pow_succ, pow_succ, ih, End.mul_def,
            End.mul_def, F.map_comp]
    refine ⟨m, ?_⟩
    rw [hcomp, hmapPow]
    rw [← principalCornerEnd_pow]
    exact hzMapZero
  have hcMapZero :
      F.map (principalCornerEnd he c) = 0 :=
    hzero' _ hrad
  have hcFactors :
      CategoricalAdditiveSubcategory.Subcategory.FactorsThrough
        P Q (principalCornerEnd he c) :=
    (I.map_eq_zero_iff
      (principalCornerEnd he c)).1 hcMapZero
  have hcIdeal :
      c.1 ∈ Tsukamoto.principalTwoSidedIdeal f :=
    corner_mem_twoSidedIdeal_of_factorsThrough
      he hf c hcFactors
  have hqcZero : q c.1 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hcIdeal
  exact hcq.symm.trans hqcZero

/-- Mapping a principal two-sided ideal along a ring homomorphism gives
the principal two-sided ideal generated by the image. -/
theorem map_principalTwoSidedIdeal
    {B : Type u} [Ring B]
    (q : A →+* B) (e : A) :
    TwoSidedIdeal.map q
        (Tsukamoto.principalTwoSidedIdeal e) =
      Tsukamoto.principalTwoSidedIdeal (q e) := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact
          TwoSidedIdeal.subset_span
            (Set.mem_singleton (q e))
    | zero =>
        set_option linter.unnecessarySimpa false in
          simpa using
            (TwoSidedIdeal.zero_mem
              (Tsukamoto.principalTwoSidedIdeal (q e)))
    | add x y hx hy hix hiy =>
        change
          q (x + y) ∈
            Tsukamoto.principalTwoSidedIdeal (q e)
        rw [map_add]
        exact
          (Tsukamoto.principalTwoSidedIdeal (q e)).add_mem
            hix hiy
    | neg x hx hix =>
        change
          q (-x) ∈
            Tsukamoto.principalTwoSidedIdeal (q e)
        rw [map_neg]
        exact
          (Tsukamoto.principalTwoSidedIdeal (q e)).neg_mem
            hix
    | left_absorb a x hx hix =>
        change
          q (a * x) ∈
            Tsukamoto.principalTwoSidedIdeal (q e)
        rw [map_mul]
        exact
          (Tsukamoto.principalTwoSidedIdeal (q e)).mul_mem_left
            (q a) (q x) hix
    | right_absorb b x hx hix =>
        change
          q (x * b) ∈
            Tsukamoto.principalTwoSidedIdeal (q e)
        rw [map_mul]
        exact
          (Tsukamoto.principalTwoSidedIdeal (q e)).mul_mem_right
            (q x) (q b) hix
  · apply TwoSidedIdeal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact
      TwoSidedIdeal.subset_span
        ⟨e,
          TwoSidedIdeal.subset_span
            (Set.mem_singleton e),
          rfl⟩

/-- If the generator `p` kills an ideal `J` on both sides, then the
whole principal two-sided ideal kills `J` on both sides. -/
theorem principalIdeal_sandwich_eq_bot
    {B : Type u} [Ring B]
    (p : B) (J : Ideal B) [J.IsTwoSided]
    (hcorner : ∀ j ∈ J, p * j * p = 0) :
    (Tsukamoto.principalTwoSidedIdeal p).asIdeal *
          J *
          (Tsukamoto.principalTwoSidedIdeal p).asIdeal =
        ⊥ := by
  let H := Tsukamoto.principalTwoSidedIdeal p
  have hpRight :
      ∀ {z : B}, z ∈ H →
        ∀ j ∈ J, p * j * z = 0 := by
    intro z hz
    induction hz using TwoSidedIdeal.span_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hcorner
    | zero =>
        intro j hj
        simp
    | add x y hx hy hix hiy =>
        intro j hj
        rw [mul_add, hix j hj, hiy j hj, add_zero]
    | neg x hx hix =>
        intro j hj
        rw [mul_neg, hix j hj, neg_zero]
    | left_absorb a x hx hix =>
        intro j hj
        have hja : j * a ∈ J :=
          Ideal.mul_mem_right a J hj
        calc
          p * j * (a * x) =
              p * (j * a) * x := by
            noncomm_ring
          _ = 0 := hix (j * a) hja
    | right_absorb b x hx hix =>
        intro j hj
        calc
          p * j * (x * b) =
              (p * j * x) * b := by
            noncomm_ring
          _ = 0 := by rw [hix j hj, zero_mul]
  have htriple :
      ∀ {x : B}, x ∈ H →
        ∀ j ∈ J, ∀ {z : B}, z ∈ H →
          x * j * z = 0 := by
    intro x hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact fun j hj z hz ↦ hpRight hz j hj
    | zero =>
        intro j hj z hz
        simp
    | add x y hx hy hix hiy =>
        intro j hj z hz
        rw [add_mul, add_mul, hix j hj hz,
          hiy j hj hz, zero_add]
    | neg x hx hix =>
        intro j hj z hz
        rw [neg_mul, neg_mul, hix j hj hz, neg_zero]
    | left_absorb a x hx hix =>
        intro j hj z hz
        calc
          a * x * j * z =
              a * (x * j * z) := by
            noncomm_ring
          _ = 0 := by rw [hix j hj hz, mul_zero]
    | right_absorb b x hx hix =>
        intro j hj z hz
        have hbj : b * j ∈ J :=
          Ideal.mul_mem_left J b hj
        calc
          x * b * j * z =
              x * (b * j) * z := by
            noncomm_ring
          _ = 0 := hix (b * j) hbj hz
  let K : Ideal B :=
    { carrier :=
        {y : B | ∀ z ∈ H, y * z = 0}
      zero_mem' := by
        intro z hz
        simp
      add_mem' := by
        intro x y hx hy z hz
        rw [add_mul, hx z hz, hy z hz, zero_add]
      smul_mem' := by
        intro a y hy z hz
        change (a * y) * z = 0
        rw [mul_assoc, hy z hz, mul_zero] }
  have hHJ :
      H.asIdeal * J ≤ K := by
    apply (Ideal.mul_le).mpr
    intro x hx j hj
    change ∀ z ∈ H, (x * j) * z = 0
    intro z hz
    exact htriple hx j hj hz
  apply le_antisymm
  · apply (Ideal.mul_le).mpr
    intro y hy z hz
    apply Ideal.mem_bot.mpr
    exact (hHJ hy) z hz
  · exact bot_le

/-- Exact right-handed Lemma 3.18 implication for principal idempotent
ideals, under the Artinian hypothesis on the lower quotient. -/
theorem radicalSandwichZero_of_factorIsCosemisimple
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    [IsArtinianRing
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)]
    (hzero :
      CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        (principalSubcategory he)
        (principalSubcategory hf)) :
    Tsukamoto.RadicalSandwichZero
      (Tsukamoto.principalTwoSidedIdeal e)
      (Tsukamoto.principalTwoSidedIdeal f) := by
  let I := Tsukamoto.principalTwoSidedIdeal f
  let q := Ideal.Quotient.mk I.asIdeal
  change
    (Tsukamoto.quotientImage
        (Tsukamoto.principalTwoSidedIdeal e) I).asIdeal *
          Ring.jacobson (A ⧸ I.asIdeal) *
          (Tsukamoto.quotientImage
            (Tsukamoto.principalTwoSidedIdeal e) I).asIdeal =
        ⊥
  have himage :
      Tsukamoto.quotientImage
          (Tsukamoto.principalTwoSidedIdeal e) I =
        Tsukamoto.principalTwoSidedIdeal (q e) := by
    exact map_principalTwoSidedIdeal q e
  rw [himage]
  apply principalIdeal_sandwich_eq_bot
  intro a ha
  exact
    quotient_corner_jacobson_sandwich_eq_zero
      he hf hzero a ha

/-- Carrier-level alignment with the literal properties `add(eA)` and
`add(fA)` is enough to apply the principal-subcategory bridge. -/
theorem radicalSandwichZero_of_aligned_factorIsCosemisimple
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    [IsArtinianRing
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)]
    (P Q :
      CategoricalAdditiveSubcategory.Subcategory
        (FiniteProjectives A))
    (hP :
      P.carrier =
        fun X ↦ Tsukamoto.addPrincipalRightModule e X.obj)
    (hQ :
      Q.carrier =
        fun X ↦ Tsukamoto.addPrincipalRightModule f X.obj)
    (hzero :
      CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        P Q) :
    Tsukamoto.RadicalSandwichZero
      (Tsukamoto.principalTwoSidedIdeal e)
      (Tsukamoto.principalTwoSidedIdeal f) := by
  have hPprincipal :
      P = principalSubcategory he := by
    apply CategoricalAdditiveSubcategory.Subcategory.ext
    intro X
    rw [hP]
    exact
      (principalSubcategory_carrier_iff_addPrincipal
        he X).symm
  have hQprincipal :
      Q = principalSubcategory hf := by
    apply CategoricalAdditiveSubcategory.Subcategory.ext
    intro X
    rw [hQ]
    exact
      (principalSubcategory_carrier_iff_addPrincipal
        hf X).symm
  rw [hPprincipal, hQprincipal] at hzero
  exact
    radicalSandwichZero_of_factorIsCosemisimple
      he hf hzero

/-- Finite-dimensional specialization: the Artinian quotient hypothesis
used above is automatic. -/
theorem radicalSandwichZero_of_factorIsCosemisimple_of_finiteDimensional
    {K : Type uK} [Field K] [Algebra K A]
    [FiniteDimensional K A]
    {e f : A} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (hzero :
      CategoricalAdditiveSubcategory.Subcategory.FactorIsCosemisimple
        (principalSubcategory he)
        (principalSubcategory hf)) :
    Tsukamoto.RadicalSandwichZero
      (Tsukamoto.principalTwoSidedIdeal e)
      (Tsukamoto.principalTwoSidedIdeal f) := by
  letI : IsArtinianRing
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal) :=
    IsArtinianRing.of_finite K
      (A ⧸
        (Tsukamoto.principalTwoSidedIdeal f).asIdeal)
  exact
    radicalSandwichZero_of_factorIsCosemisimple
      he hf hzero


end PrincipalModules

end QuotientSubmoduleEquidistribution.TsukamotoRadicalSandwichBridge
