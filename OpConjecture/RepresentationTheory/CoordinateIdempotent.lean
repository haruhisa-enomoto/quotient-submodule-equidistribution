import OpConjecture.RepresentationTheory.StrongHeredity
import OpConjecture.RepresentationTheory.GenericAdditiveRejective
import OpConjecture.RepresentationTheory.OnePointCosemisimple
import OpConjecture.ConvexGeometry.MaximalChains

/-!
# Coordinate idempotents for an additive generator

For a finite biproduct `G = ⨁ᵢ Xᵢ` and a
predicate `p` on the indices, the inclusion/projection of the restricted
biproduct defines an idempotent `eₚ ∈ End(G)`.  The representable module
`Hom(G, ⨁_{p i} Xᵢ)` is the principal right module `eₚ End(G)`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open MulOpposite

namespace OpConjecture.AuslanderEquivalence.CoordinateIdempotent

open OpConjecture.IndecomposableSkeleton

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]
  {ι : Type w} [Finite ι]

/-- The partial additive generator selected by `p`. -/
abbrev partialGenerator (X : ι → C) (p : ι → Prop) : C :=
  ⨁ Subtype.restrict p X

/-- The partial generator is canonically a retract of the full generator. -/
def partialGeneratorRetract (X : ι → C) (p : ι → Prop) :
    Retract (partialGenerator X p) (⨁ X) where
  i := biproduct.fromSubtype X p
  r := biproduct.toSubtype X p
  retract := biproduct.fromSubtype_toSubtype X p

/-- The coordinate projector onto the summands selected by `p`. -/
def coordinateProjector (X : ι → C) (p : ι → Prop) :
    End (⨁ X) :=
  biproduct.toSubtype X p ≫ biproduct.fromSubtype X p

/-- A coordinate projector is idempotent. -/
theorem coordinateProjector_isIdempotent
    (X : ι → C) (p : ι → Prop) :
    IsIdempotentElem (coordinateProjector X p) := by
  rw [IsIdempotentElem, End.mul_def]
  simp [coordinateProjector, Category.assoc]

/-- A selected coordinate injection is fixed by the projector. -/
theorem ι_coordinateProjector_of_mem
    (X : ι → C) (p : ι → Prop) (i : ι) (hi : p i) :
    biproduct.ι X i ≫ coordinateProjector X p =
      biproduct.ι X i := by
  classical
  simp [coordinateProjector, hi]

/-- An unselected coordinate injection is killed by the projector. -/
theorem ι_coordinateProjector_of_not_mem
    (X : ι → C) (p : ι → Prop) (i : ι) (hi : ¬ p i) :
    biproduct.ι X i ≫ coordinateProjector X p = 0 := by
  classical
  simp [coordinateProjector, hi]

/-- Nested subsets give nested coordinate projectors. -/
theorem coordinateProjector_comp_of_le
    (X : ι → C) {p q : ι → Prop}
    (hpq : ∀ i, p i → q i) :
    coordinateProjector X p ≫ coordinateProjector X q =
      coordinateProjector X p := by
  classical
  apply biproduct.hom_ext'
  intro i
  by_cases hi : p i
  · have hqi : q i := hpq i hi
    rw [← Category.assoc,
      ι_coordinateProjector_of_mem X p i hi,
      ι_coordinateProjector_of_mem X q i hqi]
  · rw [← Category.assoc,
      ι_coordinateProjector_of_not_mem X p i hi,
      zero_comp]

/-- The reverse composite of nested coordinate projectors also reduces
to the smaller projector. -/
theorem coordinateProjector_comp_of_le'
    (X : ι → C) {p q : ι → Prop}
    (hpq : ∀ i, p i → q i) :
    coordinateProjector X q ≫ coordinateProjector X p =
      coordinateProjector X p := by
  classical
  apply biproduct.hom_ext'
  intro i
  by_cases hi : p i
  · have hqi : q i := hpq i hi
    rw [← Category.assoc,
      ι_coordinateProjector_of_mem X q i hqi,
      ι_coordinateProjector_of_mem X p i hi]
  · by_cases hqi : q i
    · rw [← Category.assoc,
        ι_coordinateProjector_of_mem X q i hqi,
        ι_coordinateProjector_of_not_mem X p i hi]
    · rw [← Category.assoc,
        ι_coordinateProjector_of_not_mem X q i hqi,
        zero_comp,
        ι_coordinateProjector_of_not_mem X p i hi]

/-- Nested coordinate projectors generate nested principal two-sided
ideals of the endomorphism ring. -/
theorem principalTwoSidedIdeal_mono
    (X : ι → C) {p q : ι → Prop}
    (hpq : ∀ i, p i → q i) :
    Tsukamoto.principalTwoSidedIdeal (coordinateProjector X p) ≤
      Tsukamoto.principalTwoSidedIdeal (coordinateProjector X q) := by
  apply TwoSidedIdeal.span_le.mpr
  rw [Set.singleton_subset_iff]
  let I :=
    Tsukamoto.principalTwoSidedIdeal (coordinateProjector X q)
  have hq : coordinateProjector X q ∈ I :=
    TwoSidedIdeal.subset_span
      (Set.mem_singleton (coordinateProjector X q))
  have hm :
      coordinateProjector X q * coordinateProjector X p ∈ I :=
    I.mul_mem_right _ _ hq
  rw [End.mul_def, coordinateProjector_comp_of_le X hpq] at hm
  exact hm

/-- The full coordinate projector is the identity. -/
theorem coordinateProjector_eq_id_of_forall
    (X : ι → C) (p : ι → Prop) (hp : ∀ i, p i) :
    coordinateProjector X p = 𝟙 _ := by
  classical
  apply biproduct.hom_ext'
  intro i
  rw [ι_coordinateProjector_of_mem X p i (hp i)]
  simp

/-- The empty coordinate projector is zero. -/
theorem coordinateProjector_eq_zero_of_forall_not
    (X : ι → C) (p : ι → Prop) (hp : ∀ i, ¬ p i) :
    coordinateProjector X p = 0 := by
  classical
  change
    coordinateProjector X p =
      (0 : (⨁ X) ⟶ (⨁ X))
  apply biproduct.hom_ext'
  intro i
  rw [ι_coordinateProjector_of_not_mem X p i (hp i)]
  simp only [comp_zero]

section PrincipalModule

variable (X : ι → C) (p : ι → Prop)

local notation "G" => (⨁ X)
local notation "H" => partialGenerator X p
local notation "e" => coordinateProjector X p
local notation "Γ" => End G

/-- Postcomposition with the coordinate inclusion identifies
`Hom(G,H)` with the principal right ideal `eΓ`. -/
def homPartialGeneratorLinearEquiv :
    (G ⟶ H) ≃ₗ[Γᵐᵒᵖ] Tsukamoto.principalRightIdeal e where
  toFun f := by
    let x : Γᵐᵒᵖ :=
      op (f ≫ biproduct.fromSubtype X p)
    refine ⟨x, ?_⟩
    have he :
        op e ∈ Tsukamoto.principalRightIdeal e :=
      Ideal.subset_span (Set.mem_singleton (op e))
    have hxe :
        x * op e ∈ Tsukamoto.principalRightIdeal e :=
      (Tsukamoto.principalRightIdeal e).mul_mem_left x he
    have hfix : x * op e = x := by
      apply unop_injective
      change
        (f ≫ biproduct.fromSubtype X p) ≫ e =
          f ≫ biproduct.fromSubtype X p
      simp [coordinateProjector, Category.assoc]
    rwa [hfix] at hxe
  invFun x :=
    unop x.1 ≫ biproduct.toSubtype X p
  left_inv f := by
    change
      (f ≫ biproduct.fromSubtype X p) ≫
          biproduct.toSubtype X p =
        f
    rw [Category.assoc,
      biproduct.fromSubtype_toSubtype,
      Category.comp_id]
  right_inv x := by
    apply Subtype.ext
    apply unop_injective
    change
      (unop x.1 ≫ biproduct.toSubtype X p) ≫
          biproduct.fromSubtype X p =
        unop x.1
    have hx :=
      Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        (coordinateProjector_isIdempotent X p) x.property
    have hx' := congrArg unop hx
    change unop x.1 ≫ e = unop x.1 at hx'
    simpa [coordinateProjector, Category.assoc] using hx'
  map_add' f g := by
    apply Subtype.ext
    change
      op ((f + g) ≫ biproduct.fromSubtype X p) =
        op (f ≫ biproduct.fromSubtype X p) +
          op (g ≫ biproduct.fromSubtype X p)
    rw [Preadditive.add_comp]
    rfl
  map_smul' a f := by
    apply Subtype.ext
    apply unop_injective
    change
      (unop a ≫ f) ≫ biproduct.fromSubtype X p =
        unop
          (a *
            (op (f ≫ biproduct.fromSubtype X p) : Γᵐᵒᵖ))
    rw [MulOpposite.unop_mul, MulOpposite.unop_op,
      End.mul_def, Category.assoc]
    rfl

/-- Categorical form of the principal-right-module identification. -/
def homPartialGeneratorIsoPrincipalRightModule :
    (preadditiveCoyonedaObj G).obj H ≅
      Tsukamoto.principalRightModule e :=
  (homPartialGeneratorLinearEquiv X p).toModuleIso

/-- The additive closures of the representable partial generator and
the corresponding principal right module agree objectwise. -/
theorem finiteAddClosure_homPartialGenerator_iff
    (M : ModuleCat.{v} Γᵐᵒᵖ) :
    finiteAddClosure ((preadditiveCoyonedaObj G).obj H) M ↔
      finiteAddClosure (Tsukamoto.principalRightModule e) M :=
  finiteAddClosure_iff_of_iso
    (homPartialGeneratorIsoPrincipalRightModule X p)

end PrincipalModule

/-! ## Finite-skeleton specialization -/

section FiniteSkeleton

universe uR uι wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uι}
  (σ : IndecomposableSkeleton.{uR, uι, wR} R κ)
  [Finite κ]

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The finite-type additive generator, named locally for the coordinate
construction. -/
abbrev skeletonGenerator :=
  AuslanderEquivalence.FiniteTypeGenerator.additiveGenerator σ

/-- The corresponding Auslander algebra. -/
abbrev skeletonAuslanderAlgebra :=
  End (skeletonGenerator σ)

/-- The finite-projective Auslander target. -/
abbrev skeletonProjectiveTarget :=
  (AuslanderEquivalence.finiteProjectiveModules
    (skeletonAuslanderAlgebra σ)ᵐᵒᵖ).FullSubcategory

/-- The finite-type Auslander equivalence. -/
abbrev skeletonAuslanderEquivalence :
    FGModuleCat.{wR} R ≌ skeletonProjectiveTarget σ :=
  AuslanderEquivalence.FiniteTypeGenerator.auslanderEquivalence σ

local instance skeletonProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- The restricted biproduct is in the literal additive closure of its
selected skeleton support. -/
theorem partialGenerator_inAdd (p : κ → Prop) :
    σ.InAdd {i | p i} (partialGenerator σ.obj p) := by
  classical
  letI : Fintype (Subtype p) := Fintype.ofFinite _
  let ε : Subtype p ≃ Fin (Fintype.card (Subtype p)) :=
    Fintype.equivFin (Subtype p)
  let a : Fin (Fintype.card (Subtype p)) → κ :=
    fun t ↦ (ε.symm t).1
  refine ⟨{
    index := FintypeCat.of (Fin (Fintype.card (Subtype p)))
    label := a
    mem := fun t ↦ (ε.symm t).2
    iso := ?_ }⟩
  exact
    biproduct.whiskerEquiv ε
      (fun j ↦ eqToIso (by
        simp only [a, Equiv.symm_apply_apply,
          Subtype.restrict_apply]))

/-- The coordinate idempotent of the finite-type additive generator
corresponding to a predicate on indecomposable representatives. -/
abbrev skeletonCoordinateProjector (p : κ → Prop) :
    skeletonAuslanderAlgebra σ :=
  coordinateProjector σ.obj p

/-- The principal right module of a skeleton coordinate idempotent,
viewed as an object of the finite-projective Auslander target. -/
def principalProjectiveObject (p : κ → Prop) :
    skeletonProjectiveTarget σ :=
  ⟨Tsukamoto.principalRightModule
      (skeletonCoordinateProjector σ p),
    Tsukamoto.principalRightModule_mem_finiteProjectiveModules
      (coordinateProjector_isIdempotent σ.obj p)⟩

/-- The image of the selected partial additive generator under the
finite-type Auslander equivalence is the principal projective
`eₚ Γ`. -/
def auslanderImagePartialGeneratorIsoPrincipal
    (p : κ → Prop) :
    (skeletonAuslanderEquivalence σ).functor.obj
        (partialGenerator σ.obj p) ≅
      principalProjectiveObject σ p := by
  apply ObjectProperty.isoMk
  exact homPartialGeneratorIsoPrincipalRightModule σ.obj p

/-- Equivalently, the biproduct of the selected indecomposable
projectives in the Auslander target is the principal projective
`eₚ Γ`. -/
def selectedProjectiveBiproductIsoPrincipal
    (p : κ → Prop) :
    (⨁ fun i : Subtype p ↦
      (skeletonAuslanderEquivalence σ).functor.obj (σ.obj i.1)) ≅
      principalProjectiveObject σ p := by
  let E := skeletonAuslanderEquivalence σ
  let F := Subtype.restrict p σ.obj
  letI : PreservesBiproduct F E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  exact
    (E.functor.mapBiproduct F).symm.trans
      (auslanderImagePartialGeneratorIsoPrincipal σ p)

/-- Consequently, in the finite-projective target, the additive
closure of the selected indecomposable projectives is literally
`add(eₚ Γ)`. -/
theorem finiteAddClosure_selectedProjectives_iff_principal
    (p : κ → Prop) (P : skeletonProjectiveTarget σ) :
    finiteAddClosure
        (⨁ fun i : Subtype p ↦
          (skeletonAuslanderEquivalence σ).functor.obj (σ.obj i.1)) P ↔
      finiteAddClosure (principalProjectiveObject σ p) P := by
  exact finiteAddClosure_iff_of_iso
    (selectedProjectiveBiproductIsoPrincipal σ p)

/-- Inclusion of finite skeleton supports induces inclusion of the
associated principal two-sided ideals in the Auslander algebra. -/
theorem skeletonPrincipalTwoSidedIdeal_mono
    {p q : κ → Prop} (hpq : ∀ i, p i → q i) :
    Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ p) ≤
      Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ q) :=
  principalTwoSidedIdeal_mono σ.obj hpq

/-! ### Order reflection for the coordinate ideals -/

omit [Finite κ] in
private theorem inAdd_biprod_local
    {T : Set κ} {M N : FGModuleCat.{wR} R}
    (hM : σ.InAdd T M) (hN : σ.InAdd T N) :
    σ.InAdd T (M ⊞ N) := by
  let F : WalkingPair → FGModuleCat.{wR} R :=
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

omit [Finite κ] in
private theorem factorsThroughAdd_zero_local
    (T : Set κ) {X Y : FGModuleCat.{wR} R} :
    FactorsThroughAdd σ T (0 : X ⟶ Y) := by
  let F : Empty → FGModuleCat.{wR} R := Empty.elim
  let M : FGModuleCat.{wR} R := biproduct F
  have hM : σ.InAdd T M :=
    inAdd_biproduct σ (FintypeCat.of Empty) F
      (fun j ↦ j.elim)
  exact ⟨M, hM, 0, 0, by simp⟩

omit [Finite κ] in
private theorem factorsThroughAdd_add_local
    {T : Set κ} {X Y : FGModuleCat.{wR} R}
    {f g : X ⟶ Y}
    (hf : FactorsThroughAdd σ T f)
    (hg : FactorsThroughAdd σ T g) :
    FactorsThroughAdd σ T (f + g) := by
  rcases hf with ⟨M, hM, leftM, rightM, hfacM⟩
  rcases hg with ⟨N, hN, leftN, rightN, hfacN⟩
  refine ⟨M ⊞ N, inAdd_biprod_local σ hM hN,
    biprod.lift leftM leftN,
    biprod.desc rightM rightN, ?_⟩
  rw [biprod.lift_desc, hfacM, hfacN]

omit [Finite κ] in
private theorem factorsThroughAdd_neg_local
    {T : Set κ} {X Y : FGModuleCat.{wR} R}
    {f : X ⟶ Y}
    (hf : FactorsThroughAdd σ T f) :
    FactorsThroughAdd σ T (-f) := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  exact ⟨M, hM, -left, right, by simp [hfac]⟩

omit [Finite κ] in
private theorem factorsThroughAdd_precomp_local
    {T : Set κ} {X Y Z : FGModuleCat.{wR} R}
    (a : X ⟶ Y) {f : Y ⟶ Z}
    (hf : FactorsThroughAdd σ T f) :
    FactorsThroughAdd σ T (a ≫ f) := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  exact
    ⟨M, hM, a ≫ left, right,
      by rw [Category.assoc, hfac]⟩

omit [Finite κ] in
private theorem factorsThroughAdd_postcomp_local
    {T : Set κ} {X Y Z : FGModuleCat.{wR} R}
    {f : X ⟶ Y} (a : Y ⟶ Z)
    (hf : FactorsThroughAdd σ T f) :
    FactorsThroughAdd σ T (f ≫ a) := by
  rcases hf with ⟨M, hM, left, right, hfac⟩
  exact
    ⟨M, hM, left, right ≫ a,
      by rw [← Category.assoc, hfac]⟩

/-- Every endomorphism in the principal two-sided ideal generated by
`eₚ` factors through an object of `add p`. -/
theorem mem_skeletonPrincipalTwoSidedIdeal_factorsThroughAdd
    (p : κ → Prop) {f : skeletonAuslanderAlgebra σ}
    (hf :
      f ∈ Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ p)) :
    FactorsThroughAdd σ {i | p i} f := by
  induction hf using TwoSidedIdeal.span_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact
        ⟨partialGenerator σ.obj p,
          partialGenerator_inAdd σ p,
          biproduct.toSubtype σ.obj p,
          biproduct.fromSubtype σ.obj p,
          rfl⟩
  | zero =>
      exact factorsThroughAdd_zero_local σ _
  | add x y hx hy hfx hfy =>
      exact factorsThroughAdd_add_local σ hfx hfy
  | neg x hx hfx =>
      exact factorsThroughAdd_neg_local σ hfx
  | left_absorb a x hx hfx =>
      rw [End.mul_def]
      exact factorsThroughAdd_postcomp_local σ a hfx
  | right_absorb b x hx hfx =>
      rw [End.mul_def]
      exact factorsThroughAdd_precomp_local σ b hfx

/-- Coordinate principal ideals reflect support inclusion.  This is the
strictness input needed to turn a strict support chain into a strict
idempotent-ideal chain. -/
theorem skeletonPrincipalTwoSidedIdeal_le_iff
    {p q : κ → Prop} :
    Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ p) ≤
        Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ q) ↔
      ∀ i, p i → q i := by
  constructor
  · intro hpq i hi
    let Ip :=
      Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ p)
    have hep :
        skeletonCoordinateProjector σ p ∈ Ip :=
      TwoSidedIdeal.subset_span
        (Set.mem_singleton
          (skeletonCoordinateProjector σ p))
    have hfac :=
      mem_skeletonPrincipalTwoSidedIdeal_factorsThroughAdd
        σ q (hpq hep)
    rcases hfac with ⟨M, hM, left, right, hfactor⟩
    let rPartial :
        Retract (partialGenerator σ.obj p) M :=
      { i := biproduct.fromSubtype σ.obj p ≫ left
        r := right ≫ biproduct.toSubtype σ.obj p
        retract := by
          rw [Category.assoc, ← Category.assoc left,
            hfactor]
          simp [skeletonCoordinateProjector,
            coordinateProjector, Category.assoc] }
    let rCoordinate :
        Retract (σ.obj i) (partialGenerator σ.obj p) :=
      let eCoord :
          σ.obj i ≅
            Subtype.restrict p σ.obj ⟨i, hi⟩ :=
        eqToIso
          (Subtype.restrict_apply σ.obj p ⟨i, hi⟩).symm
      { i := eCoord.hom ≫
          biproduct.ι (Subtype.restrict p σ.obj) ⟨i, hi⟩
        r :=
          biproduct.π (Subtype.restrict p σ.obj) ⟨i, hi⟩ ≫
            eCoord.inv
        retract := by simp }
    exact
      index_mem_of_retract_inAdd σ
        (rCoordinate.trans rPartial) hM
  · exact skeletonPrincipalTwoSidedIdeal_mono σ

/-- Strict support inclusion is equivalent to strict inclusion of the
coordinate principal two-sided ideals. -/
theorem skeletonPrincipalTwoSidedIdeal_lt_iff
    {p q : κ → Prop} :
    Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ p) <
        Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ q) ↔
      ({i | p i} : Set κ) ⊂ {i | q i} := by
  rw [lt_iff_le_and_ne, Set.ssubset_iff_subset_ne]
  constructor
  · rintro ⟨hle, hne⟩
    refine ⟨(skeletonPrincipalTwoSidedIdeal_le_iff σ).1 hle, ?_⟩
    intro hpq
    apply hne
    apply le_antisymm hle
    apply (skeletonPrincipalTwoSidedIdeal_le_iff σ).2
    intro i hqi
    have hqp :
        ({i | q i} : Set κ) ⊆ {i | p i} := by
      rw [hpq]
    exact hqp hqi
  · rintro ⟨hle, hne⟩
    refine ⟨(skeletonPrincipalTwoSidedIdeal_le_iff σ).2 hle, ?_⟩
    intro hideals
    apply hne
    apply Set.Subset.antisymm hle
    intro i hqi
    exact
      (skeletonPrincipalTwoSidedIdeal_le_iff σ).1
        (hideals ▸ le_rfl) i hqi

/-! ### Packaging a support chain as an idempotent-ideal chain -/

/-- Any strict finite top-to-bottom support chain gives a literal
Tsukamoto idempotent-ideal chain in the Auslander algebra by taking the
coordinate principal ideals. -/
def idempotentIdealChainOfSupportChain
    {n : ℕ}
    (support : Fin (n + 1) → Set κ)
    (strictAnti : StrictAnti support)
    (top : support 0 = Set.univ)
    (bottom : support (Fin.last n) = ∅) :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) n where
  ideal i :=
    Tsukamoto.principalTwoSidedIdeal
      (skeletonCoordinateProjector σ (support i))
  strictAnti := by
    intro i j hij
    apply
      (skeletonPrincipalTwoSidedIdeal_lt_iff σ).2
    exact strictAnti hij
  top_eq := by
    have he :
        skeletonCoordinateProjector σ (support 0) =
          1 := by
      apply coordinateProjector_eq_id_of_forall
      intro i
      rw [top]
      trivial
    rw [he]
    change
      TwoSidedIdeal.span
          ({(1 : skeletonAuslanderAlgebra σ)} : Set _) =
        ⊤
    apply le_antisymm le_top
    intro x hx
    let I :=
      TwoSidedIdeal.span
        ({(1 : skeletonAuslanderAlgebra σ)} : Set _)
    have hOne : (1 : skeletonAuslanderAlgebra σ) ∈ I :=
      TwoSidedIdeal.subset_span
        (Set.mem_singleton (1 : skeletonAuslanderAlgebra σ))
    have hxI : x * 1 ∈ I :=
      I.mul_mem_left x 1 hOne
    simpa only [mul_one] using hxI
  bot_eq := by
    have he :
        skeletonCoordinateProjector σ
            (support (Fin.last n)) =
          0 := by
      apply coordinateProjector_eq_zero_of_forall_not
      intro i
      rw [bottom]
      change ¬ False
      exact not_false
    rw [he]
    change
      TwoSidedIdeal.span
          ({(0 : skeletonAuslanderAlgebra σ)} : Set _) =
        ⊥
    apply le_antisymm
    · apply TwoSidedIdeal.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact
        TwoSidedIdeal.zero_mem
          (⊥ : TwoSidedIdeal (skeletonAuslanderAlgebra σ))
    · exact bot_le
  idempotent i :=
    Tsukamoto.principalTwoSidedIdeal_isIdempotent
      (coordinateProjector_isIdempotent σ.obj (support i))

/-- The preceding chain comes with its coordinate-idempotent
presentation, so no existence-of-idempotent theorem is being assumed. -/
def idempotentPresentationOfSupportChain
    {n : ℕ}
    (support : Fin (n + 1) → Set κ)
    (strictAnti : StrictAnti support)
    (top : support 0 = Set.univ)
    (bottom : support (Fin.last n) = ∅) :
    (idempotentIdealChainOfSupportChain σ support
      strictAnti top bottom).IdempotentPresentation where
  generator i :=
    skeletonCoordinateProjector σ (support i)
  isIdempotent i :=
    coordinateProjector_isIdempotent σ.obj (support i)
  span_eq _ := rfl

/-- The supports in a saturated one-point deletion chain are strictly
antitone. -/
theorem saturatedSupportDeletionChain_strictAnti
    {E : Type*} [Fintype E]
    (d : OpConjecture.SetClosure.SaturatedSupportDeletionChain E) :
    StrictAnti d.support := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  rw [d.step i]
  refine lt_of_le_of_ne Set.sdiff_subset ?_
  intro hEq
  have hmem :
      d.removed i ∈
        d.support i.castSucc \ {d.removed i} := by
    rw [hEq]
    exact d.removed_mem i
  exact hmem.2 (Set.mem_singleton (d.removed i))

/-- A saturated support deletion chain therefore produces, without any
additional algebraic choice, the coordinate idempotent-ideal chain
needed on the Tsukamoto side. -/
def idempotentIdealChainOfSaturatedSupportDeletion
    [Fintype κ]
    (d : OpConjecture.SetClosure.SaturatedSupportDeletionChain κ) :
    Tsukamoto.IdempotentIdealChain
      (skeletonAuslanderAlgebra σ) (Fintype.card κ) :=
  idempotentIdealChainOfSupportChain σ d.support
    (saturatedSupportDeletionChain_strictAnti d)
    d.top d.bottom

end FiniteSkeleton

end OpConjecture.AuslanderEquivalence.CoordinateIdempotent
