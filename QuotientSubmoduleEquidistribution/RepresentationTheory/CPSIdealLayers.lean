import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateStandardKernelFiltration
import QuotientSubmoduleEquidistribution.RepresentationTheory.PrincipalIdealInAdd
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteAddMultiplicity
import QuotientSubmoduleEquidistribution.RepresentationTheory.IdealLayerRestriction
import QuotientSubmoduleEquidistribution.RepresentationTheory.QuotientIdealProjective
import QuotientSubmoduleEquidistribution.RepresentationTheory.AuslanderOppositeArtinian
import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagStrongHeredity
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Positive CPS ideal layers for coordinate deletion chains

This file completes the literal positive-multiplicity comparison used in the
manuscript's CPS/Tsukamoto proof path. Its two generic inputs are:

* strictness of an idempotent ideal chain makes every literal ideal layer
  nonzero;
* membership in `add Δ` produces the required literal finite power through
  the project-local Krull--Schmidt/local-endomorphism theorem.

For coordinate deletion chains, the trace kernel is identified with the
kernel of a principal-module quotient map. This realizes the standard as a
principal right module over the quotient algebra and the literal ideal layer
as the corresponding finite projective two-sided ideal. A maximal
quotient-closed flag therefore supplies the complete positive
`RightStandardModuleChainData`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe uA vC uC vD uD

variable {A : Type uA} [Ring A] {n : ℕ}

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A strict ideal-chain layer cannot be the zero module. -/
theorem rightIdealLayer_not_isZero
    (H : IdempotentIdealChain A n) (i : Fin n) :
    ¬ IsZero (rightIdealLayer H i) := by
  intro hzero
  letI : Epi (rightChainInclusion H i) :=
    epi_of_isZero_cokernel (rightChainInclusion H i) hzero
  have hsurjective : Function.Surjective (rightChainInclusion H i) :=
    (ModuleCat.epi_iff_surjective (rightChainInclusion H i)).mp inferInstance
  obtain ⟨a, haUpper, haLower⟩ :=
    SetLike.exists_of_lt
      (H.strictAnti (Fin.castSucc_lt_succ : i.castSucc < i.succ))
  let x : H.ideal i.castSucc := ⟨a, haUpper⟩
  obtain ⟨y, hy⟩ := hsurjective x
  apply haLower
  have hyValue : (y : A) = a :=
    congrArg Subtype.val hy
  simpa [hyValue] using y.property

/-- A literal layer in an idempotent-ideal chain is the image of the
upper ideal in the quotient by the lower ideal, with scalars restricted
back to the original ring. -/
def rightIdealLayerRestrictedQuotientImageIsoForChain
    (H : IdempotentIdealChain A n) (i : Fin n) :
    rightIdealLayer H i ≅
      QuotientSubmoduleEquidistribution.Tsukamoto.restrictedQuotientImageRightModule
        (H.ideal i.succ) (H.ideal i.castSucc) :=
  QuotientSubmoduleEquidistribution.Tsukamoto.rightIdealLayerRestrictedQuotientImageIso
    (H.ideal i.succ) (H.ideal i.castSucc)
    ((H.strictAnti (Fin.castSucc_lt_succ : i.castSucc < i.succ)).le)

/-- The exact multiplicity upgrade refining `finiteAddClosure X`:
every finite retract of a finite power of `X` is itself a finite power of
`X`.  For an indecomposable finite-length module this follows from the
Krull--Schmidt theorem (equivalently, from freeness of finitely generated
projectives over the local ring `End(X)`). -/
def FiniteAddHasMultiplicity
    {S : Type uA} [Ring S]
    (X : ModuleCat.{uA} S) : Prop :=
  ∀ Y : ModuleCat.{uA} S,
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure X Y →
      ∃ m : ℕ, Nonempty (Y ≅ ⨁ fun _ : Fin m ↦ X)

/-- Module-category form of the finite-add multiplicity theorem.  The
tracked theorem is stated in `FGModuleCat`; the full-subcategory comparison
and preservation of finite biproducts remove that bundling here. -/
theorem finiteAddClosure_is_biproduct_moduleCat
    {R : Type uA} [Ring R] [IsNoetherianRing R]
    (X Y : ModuleCat.{uA} R)
    (hXfinite : IsFiniteLength R X)
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X)
    (hYfinite : IsFiniteLength R Y)
    (hYadd :
      QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure X Y) :
    ∃ m : ℕ, Nonempty (Y ≅ ⨁ fun _ : Fin m ↦ X) := by
  letI : IsNoetherian R X :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
  letI : IsNoetherian R Y :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hYfinite).1
  letI : Module.Finite R X := inferInstance
  letI : Module.Finite R Y := inferInstance
  let Xfg : FGModuleCat.{uA} R := FGModuleCat.of R X
  let Yfg : FGModuleCat.{uA} R := FGModuleCat.of R Y
  have hYaddFG :
      QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure Xfg Yfg :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalQuotientDeletionChain.finiteAddClosure_fullSubcategory_iff
        (ModuleCat.isFG R) Xfg Yfg).mpr hYadd
  obtain ⟨m, ⟨e⟩⟩ :=
    QuotientSubmoduleEquidistribution.FiniteAddMultiplicity.finiteAddClosure_is_biproduct
      Xfg Yfg hXindec hYfinite hYaddFG
  let Q := ModuleCat.isFG.{uA} R
  let F : Fin m → Q.FullSubcategory := fun _ ↦ Xfg
  letI : PreservesBiproduct F Q.ι := inferInstance
  exact
    ⟨m, ⟨Q.ι.mapIso e ≪≫ Q.ι.mapBiproduct F⟩⟩

/-- Finite length and indecomposability discharge the formerly abstract
multiplicity interface. -/
theorem finiteAddHasMultiplicity_of_finiteLength_indecomposable
    {R : Type uA} [Ring R] [IsNoetherianRing R]
    (X : ModuleCat.{uA} R)
    (hXfinite : IsFiniteLength R X)
    (hXindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R X) :
    FiniteAddHasMultiplicity X := by
  intro Y hYadd
  obtain ⟨P⟩ := hYadd
  have hYfinite : IsFiniteLength R Y := by
    let F : Fin P.n → ModuleCat.{uA} R := fun _ ↦ X
    have hPowerFinite :
        IsFiniteLength R ((⨁ F) : ModuleCat.{uA} R) := by
      letI : IsNoetherian R X :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).1
      letI : IsArtinian R X :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp hXfinite).2
      have hPi : IsFiniteLength R (∀ _ : Fin P.n, X) :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mpr
          ⟨inferInstance, inferInstance⟩)
      exact
        (ModuleCat.biproductIsoPi F).toLinearEquiv.symm.isFiniteLength hPi
    exact hPowerFinite.of_injective
      (f := P.retract.i.hom)
      (ModuleCat.mono_iff_injective P.retract.i |>.mp inferInstance)
  exact
    finiteAddClosure_is_biproduct_moduleCat
      X Y hXfinite hXindec hYfinite ⟨P⟩

/-- A finite-add presentation can be transported through a functor which
preserves finite biproducts. -/
def mapFiniteAddPresentation
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteBiproducts F]
    {X Y : C}
    (P : QuotientSubmoduleEquidistribution.AuslanderEquivalence.FiniteAddPresentation X Y) :
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.FiniteAddPresentation
      (F.obj X) (F.obj Y) := by
  letI : PreservesBiproduct (fun _ : Fin P.n ↦ X) F := inferInstance
  exact
    { n := P.n
      retract :=
        (P.retract.map F).trans
          (Retract.ofIso (F.mapBiproduct (fun _ : Fin P.n ↦ X))) }

/-- Functors preserving finite biproducts preserve `finiteAddClosure`. -/
theorem finiteAddClosure_map
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [PreservesFiniteBiproducts F]
    {X Y : C}
    (h : QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure X Y) :
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure
      (F.obj X) (F.obj Y) := by
  obtain ⟨P⟩ := h
  exact ⟨mapFiniteAddPresentation F P⟩

/-- Membership in a finite additive closure is invariant under replacing
the target by an isomorphic object. -/
theorem finiteAddClosure_target_of_iso
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X Y : C} (e : X ≅ Y)
    (h : QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure G X) :
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure G Y := by
  obtain ⟨P⟩ := h
  exact
    ⟨{
      n := P.n
      retract := (Retract.ofIso e.symm).trans P.retract }⟩

/-- The principal-ideal finite-add result survives restriction of scalars.
This is the abstract engine for viewing a quotient-ring principal ideal as
an `A`-module layer. -/
theorem restrictedPrincipalIdeal_mem_add
    {B : Type uA} [Ring B]
    (q : A →+* B) (e : B)
    (hfinite :
      Module.Finite Bᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e))
    (hprojective :
      QuotientSubmoduleEquidistribution.Tsukamoto.IsRightProjectiveIdeal
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e)) :
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure
      ((ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule e))
      ((ModuleCat.restrictScalars (RingHom.op q)).obj
        (ModuleCat.of Bᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e))) := by
  apply finiteAddClosure_map
    (ModuleCat.restrictScalars (RingHom.op q))
  exact
    QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal_mem_add_of_finite_projective
      e hfinite hprojective

/-- A literal quotient-ring realization of one CPS layer.  These are the
four algebraic statements needed to invoke the principal-ideal theorem:
the standard is `eB`, the layer is `BeB`, and the latter is finite
projective over `B`. -/
structure QuotientPrincipalLayerRealization
    {B : Type uA} [Ring B]
    (q : A →+* B) (e : B)
    (standard layer : ModuleCat.{uA} Aᵐᵒᵖ) where
  standardIso :
    standard ≅
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule e)
  layerIso :
    layer ≅
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (ModuleCat.of Bᵐᵒᵖ
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e))
  finiteIdeal :
    Module.Finite Bᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e)
  projectiveIdeal :
    QuotientSubmoduleEquidistribution.Tsukamoto.IsRightProjectiveIdeal
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal e)

/-- A quotient-principal realization immediately gives the precise
`layer ∈ add(standard)` assertion consumed by the CPS constructor. -/
theorem QuotientPrincipalLayerRealization.layer_mem_add
    {B : Type uA} [Ring B]
    {q : A →+* B} {e : B}
    {standard layer : ModuleCat.{uA} Aᵐᵒᵖ}
    (P : QuotientPrincipalLayerRealization q e standard layer) :
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure standard layer := by
  have hRestricted :=
    restrictedPrincipalIdeal_mem_add q e P.finiteIdeal P.projectiveIdeal
  have hLayer :
      QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure
        ((ModuleCat.restrictScalars (RingHom.op q)).obj
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule e)) layer :=
    finiteAddClosure_target_of_iso P.layerIso.symm hRestricted
  exact
    (QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure_iff_of_iso
      P.standardIso).mpr hLayer

/-- A nonzero quotient of a finite-length indecomposable projective module
is indecomposable.  The proof lifts an idempotent of the quotient to the
projective source and uses locality of its endomorphism ring. -/
theorem indecomposable_of_surjective_from_indec_projective
    {R : Type uA} [Ring R]
    {P Y : Type uA}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Y] [Module R Y]
    [Module.Projective R P]
    (hPfinite : IsFiniteLength R P)
    (hPindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R P)
    [Nontrivial Y]
    (q : P →ₗ[R] Y) (hq : Function.Surjective q) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Y := by
  letI : Nontrivial P := hPindec.nontrivial
  letI : IsLocalRing (Module.End R P) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable hPfinite hPindec
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property q (f.comp q) hq
  have eq_one_of_surjective :
      ∀ (t : Module.End R Y), IsIdempotentElem t →
        Function.Surjective t → t = 1 := by
    intro t ht htsurj
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := htsurj y
    have htx := DFunLike.congr_fun ht x
    simpa [Module.End.mul_apply] using htx
  have hsum : IsUnit (g + (1 - g)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hgun | hg'un
  · right
    apply eq_one_of_surjective f hf
    have hgsurj : Function.Surjective g :=
      ((Module.End.isUnit_iff g).mp hgun).2
    have hcompSurj : Function.Surjective (q.comp g) :=
      hq.comp hgsurj
    rw [hg] at hcompSurj
    intro y
    obtain ⟨p, hp⟩ := hcompSurj y
    exact ⟨q p, hp⟩
  · left
    let f' : Module.End R Y := 1 - f
    let g' : Module.End R P := 1 - g
    have hg' : q.comp g' = f'.comp q := by
      apply LinearMap.ext
      intro p
      have hp := DFunLike.congr_fun hg p
      change q (g p) = f (q p) at hp
      change q (p - g p) = q p - f (q p)
      rw [map_sub, hp]
    have hg'surj : Function.Surjective g' :=
      ((Module.End.isUnit_iff g').mp hg'un).2
    have hf'surj : Function.Surjective f' := by
      have hcompSurj : Function.Surjective (q.comp g') :=
        hq.comp hg'surj
      rw [hg'] at hcompSurj
      intro y
      obtain ⟨p, hp⟩ := hcompSurj y
      exact ⟨q p, hp⟩
    have hf'idempotent : IsIdempotentElem f' :=
      IsIdempotentElem.one_sub hf
    have hf'one : f' = 1 :=
      eq_one_of_surjective f' hf'idempotent hf'surj
    exact sub_eq_self.mp hf'one

/-- The biproduct indexed by the empty finite type is zero in `ModuleCat`. -/
theorem isZero_biproduct_fin_zero
    (X : ModuleCat.{uA} Aᵐᵒᵖ) :
    IsZero (⨁ fun _ : Fin 0 ↦ X) := by
  let F : Fin 0 → ModuleCat.{uA} Aᵐᵒᵖ := fun _ ↦ X
  have hPi : IsZero (ModuleCat.of Aᵐᵒᵖ (∀ i : Fin 0, F i)) :=
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance
  exact hPi.of_iso (ModuleCat.biproductIsoPi F)

/-- A nonzero object cannot be a zero-fold biproduct. -/
theorem multiplicity_pos_of_iso
    {X Y : ModuleCat.{uA} Aᵐᵒᵖ} {m : ℕ}
    (hY : ¬ IsZero Y)
    (e : Y ≅ ⨁ fun _ : Fin m ↦ X) :
    0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  exact hY ((isZero_biproduct_fin_zero X).of_iso e)

/-- The CPS chain datum follows formally once every layer belongs to the
finite additive closure of its standard and standards have the required
multiplicity property.  Strictness of the ideal chain supplies positivity;
it need not be assumed separately. -/
def rightStandardModuleChainDataOfFiniteAdd
    (H : IdempotentIdealChain A n)
    (D : OrderedHighestWeightStructure
      (ModuleCat.{uA} Aᵐᵒᵖ) (Fin n))
    (hadd : ∀ i : Fin n,
      QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure
        ((D.standard i).object) (rightIdealLayer H i))
    (hmultiplicity : ∀ i : Fin n,
      FiniteAddHasMultiplicity ((D.standard i).object)) :
    RightStandardModuleChainData H := by
  classical
  let multiplicity : Fin n → ℕ := fun i ↦
    (hmultiplicity i (rightIdealLayer H i) (hadd i)).choose
  let layerIso : ∀ i : Fin n,
      rightIdealLayer H i ≅
        ⨁ fun _ : Fin (multiplicity i) ↦ (D.standard i).object :=
    fun i ↦
      (hmultiplicity i (rightIdealLayer H i) (hadd i)).choose_spec.some
  exact
    { highestWeight := D
      multiplicity := multiplicity
      multiplicity_pos := fun i ↦
        multiplicity_pos_of_iso
          (rightIdealLayer_not_isZero H i) (layerIso i)
      layer_iso_standard_biproduct := layerIso }

/-- Concrete finite-length form: the new finite-add multiplicity theorem
supplies all multiplicity isomorphisms, so the only layer-specific input is
membership in `add(Δᵢ)`. -/
def rightStandardModuleChainDataOfFiniteLengthFiniteAdd
    [IsNoetherianRing Aᵐᵒᵖ]
    (H : IdempotentIdealChain A n)
    (D : OrderedHighestWeightStructure
      (ModuleCat.{uA} Aᵐᵒᵖ) (Fin n))
    (hstandardFinite : ∀ i : Fin n,
      IsFiniteLength Aᵐᵒᵖ (D.standard i).object)
    (hstandardIndecomposable : ∀ i : Fin n,
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Aᵐᵒᵖ (D.standard i).object)
    (hadd : ∀ i : Fin n,
      QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteAddClosure
        ((D.standard i).object) (rightIdealLayer H i)) :
    RightStandardModuleChainData H :=
  rightStandardModuleChainDataOfFiniteAdd H D hadd
    (fun i ↦
      finiteAddHasMultiplicity_of_finiteLength_indecomposable
        (D.standard i).object (hstandardFinite i)
        (hstandardIndecomposable i))

/-! ## Quotient maps for principal right modules and ideal images -/

variable {B : Type uA} [Ring B]

/-- The quotient-induced linear map from `eA` to `q(e)B`, with the target
restricted back to an `A`-module. -/
def principalRightIdealQuotientMap
    (q : A →+* B) (e : A) :
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e →ₗ[Aᵐᵒᵖ]
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule (q e)) where
  toFun x := by
    refine ⟨RingHom.op q x.1, ?_⟩
    change
      RingHom.op q x.1 ∈
        Ideal.span ({op (q e)} : Set Bᵐᵒᵖ)
    have hx := Ideal.mem_map_of_mem (RingHom.op q) x.property
    simpa [QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal,
      Ideal.map_span] using hx
  map_add' x y :=
    Subtype.ext (map_add (RingHom.op q) x.1 y.1)
  map_smul' r x :=
    Subtype.ext (map_mul (RingHom.op q) r x.1)

/-- Categorical form of `principalRightIdealQuotientMap`. -/
def principalRightModuleQuotientMap
    (q : A →+* B) (e : A) :
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule e ⟶
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule (q e)) :=
  ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    (principalRightIdealQuotientMap q e)

theorem principalRightModuleQuotientMap_surjective
    (q : A →+* B) (hq : Function.Surjective q)
    (e : A) (he : IsIdempotentElem e) :
    Function.Surjective (principalRightModuleQuotientMap q e) := by
  intro y
  obtain ⟨a, ha⟩ := hq (unop y.1)
  let xval : Aᵐᵒᵖ := op (e * a)
  have hxmem :
      xval ∈ QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e := by
    have hgen :
        op e ∈ QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e :=
      Ideal.subset_span (Set.mem_singleton (op e))
    have hmul :=
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal e).mul_mem_left
        (op a) hgen
    simpa [xval] using hmul
  refine ⟨⟨xval, hxmem⟩, ?_⟩
  apply Subtype.ext
  change RingHom.op q xval = y.1
  apply unop_injective
  change q (e * a) = unop y.1
  rw [map_mul, ha]
  have hyfix :=
    QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
      (he.map q) y.property
  have hyfix' := congrArg unop hyfix
  change q e * unop y.1 = unop y.1 at hyfix'
  exact hyfix'

/-- The quotient map from an ideal to its quotient image, in its natural
semilinear form. -/
def rightIdealToQuotientImageSemilinear
    (J I : TwoSidedIdeal A) :
    I →ₛₗ[RingHom.op (Ideal.Quotient.mk J.asIdeal)]
      QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J where
  toFun x :=
    ⟨Ideal.Quotient.mk J.asIdeal x.1,
      TwoSidedIdeal.subset_span ⟨x.1, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' r x := by
    apply Subtype.ext
    exact map_mul (Ideal.Quotient.mk J.asIdeal) x.1 (unop r)

theorem rightIdealToQuotientImageSemilinear_surjective
    (J I : TwoSidedIdeal A) :
    Function.Surjective (rightIdealToQuotientImageSemilinear J I) := by
  intro y
  obtain ⟨x, hx, hxy⟩ :=
    (QuotientSubmoduleEquidistribution.Tsukamoto.mem_twoSidedIdeal_map_iff_of_surjective
      (Ideal.Quotient.mk J.asIdeal) Ideal.Quotient.mk_surjective I y.1).mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- A finite ideal has finite quotient image over the quotient ring. -/
theorem quotientImage_finite
    (J I : TwoSidedIdeal A) [Module.Finite Aᵐᵒᵖ I] :
    Module.Finite (A ⧸ J.asIdeal)ᵐᵒᵖ
      (QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J) := by
  let qop := RingHom.op (Ideal.Quotient.mk J.asIdeal)
  letI : RingHomSurjective qop := ⟨by
    intro y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unop y)
    refine ⟨op a, ?_⟩
    apply unop_injective
    exact ha⟩
  exact Module.Finite.of_surjective
    (rightIdealToQuotientImageSemilinear J I)
    (rightIdealToQuotientImageSemilinear_surjective J I)

/-- Every two-sided ideal is finite as a right module when the opposite
ring is Noetherian.  This is the explicit instance bridge needed for
coordinate ideals, whose underlying module is not found automatically
by typeclass search. -/
theorem twoSidedIdeal_finite_right
    [IsNoetherianRing Aᵐᵒᵖ]
    (I : TwoSidedIdeal A) :
    Module.Finite Aᵐᵒᵖ I := by
  exact Module.Finite.of_injective
    (TwoSidedIdeal.subtypeMop I)
    (TwoSidedIdeal.subtypeMop_injective I)

end QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent

open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe uR uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Fintype κ]

local notation "Γ" => skeletonAuslanderAlgebra σ

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

local instance coordinateCPSProjectiveTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- The biproduct of singleton coordinate projectives selected by `T` is
the principal right module of the aggregate coordinate projector. -/
def selectedCoordinateProjectiveBiproductIsoPrincipalRightModule
    (T : Set κ) :
    (⨁ fun j : T ↦ (coordinateProjective σ j.1).obj) ≅
      QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T)) := by
  let P :=
    QuotientSubmoduleEquidistribution.AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  let I := P.ι
  let E := skeletonAuslanderEquivalence σ
  let F : T → skeletonProjectiveTarget σ :=
    fun j ↦ E.functor.obj (σ.obj j.1)
  letI : PreservesBiproduct F I :=
    preservesBiproduct_of_preservesProduct I
  exact
    (biproduct.mapIso (fun j : T ↦
      (I.mapIso (auslanderImageIsoCoordinateProjective σ j.1)).symm)) ≪≫
      (I.mapBiproduct F).symm ≪≫
      I.mapIso (selectedProjectiveBiproductIsoPrincipal σ (fun k ↦ k ∈ T))

/-! ## The coordinate trace is the quotient-map kernel -/

/-- Every map from the aggregate selected principal projective has image
in the coordinate trace. -/
theorem range_le_coordinateProjectiveTrace_of_principalRightModule
    (T : Set κ) (r : κ)
    (g : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
          (skeletonCoordinateProjector σ (fun k ↦ k ∈ T)) ⟶
        (coordinateProjective σ r).obj) :
    LinearMap.range g.hom ≤ coordinateProjectiveTrace σ T r := by
  let e := selectedCoordinateProjectiveBiproductIsoPrincipalRightModule σ T
  let p := coordinateStandardProjection σ T r
  have hz : e.hom ≫ g ≫ p = 0 := by
    apply biproduct.hom_ext'
    intro j
    let f : (coordinateProjective σ j.1).obj ⟶
        (coordinateProjective σ r).obj :=
      biproduct.ι (fun j : T ↦ (coordinateProjective σ j.1).obj) j ≫
        e.hom ≫ g
    simpa [f, p, Category.assoc] using
      (comp_coordinateStandardProjection_eq_zero
        σ T r j.1 j.2 f)
  have hgp : g ≫ p = 0 := by
    apply (cancel_epi e.hom).mp
    simpa [Category.assoc] using hz
  rintro y ⟨x, rfl⟩
  have hx := congrArg
    (fun f : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
          (skeletonCoordinateProjector σ (fun k ↦ k ∈ T)) ⟶
        coordinateStandardQuotient σ T r ↦ f.hom x) hgp
  change
    Submodule.mkQ (coordinateProjectiveTrace σ T r) (g.hom x) = 0
    at hx
  exact (Submodule.Quotient.mk_eq_zero
    (coordinateProjectiveTrace σ T r)).mp hx

/-- The value of a map out of a selected coordinate projective lies in
the two-sided ideal generated by the selected aggregate projector. -/
theorem map_coordinateProjective_mem_supportIdeal
    (T : Set κ) (r j : κ) (hj : j ∈ T)
    (f : (coordinateProjective σ j).obj ⟶
      (coordinateProjective σ r).obj)
    (x : (coordinateProjective σ j).obj) :
    unop (f.hom x).1 ∈
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T)) := by
  let ej := skeletonCoordinateProjector σ (fun k ↦ k = j)
  let eT := skeletonCoordinateProjector σ (fun k ↦ k ∈ T)
  let J := QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal eT
  have hejJ : ej ∈ J := by
    have hmono :
        QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal ej ≤ J :=
      skeletonPrincipalTwoSidedIdeal_mono σ (by
        rintro k rfl
        exact hj)
    exact hmono
      (TwoSidedIdeal.subset_span (Set.mem_singleton ej))
  let ge : (coordinateProjective σ j).obj :=
    ⟨op ej,
      Ideal.subset_span (Set.mem_singleton (op ej))⟩
  have hej : IsIdempotentElem ej :=
    coordinateProjector_isIdempotent σ.obj (fun k ↦ k = j)
  have hgefix : op ej • ge = ge := by
    apply Subtype.ext
    change op ej * op ej = op ej
    apply unop_injective
    simpa using hej.eq
  have hfgfix : op ej • f.hom ge = f.hom ge := by
    rw [← map_smul, hgefix]
  have hfgval :
      unop (f.hom ge).1 * ej = unop (f.hom ge).1 := by
    exact congrArg (fun z ↦ unop z.1) hfgfix
  have hfgJ : unop (f.hom ge).1 ∈ J := by
    have hmul := J.mul_mem_left (unop (f.hom ge).1) ej hejJ
    rwa [hfgval] at hmul
  have hxgen : x.1 • ge = x := by
    apply Subtype.ext
    exact
      QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
        hej x.property
  have hfx : f.hom x = x.1 • f.hom ge := by
    rw [← map_smul, hxgen]
  have hfxval :
      unop (f.hom x).1 =
        unop (f.hom ge).1 * unop x.1 := by
    exact congrArg (fun z ↦ unop z.1) hfx
  rw [hfxval]
  exact J.mul_mem_right _ _ hfgJ

/-- The coordinate trace is killed by quotienting by the selected
coordinate ideal. -/
theorem coordinateProjectiveTrace_le_ker_principalRightIdealQuotientMap
    (T : Set κ) (r : κ) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))
    let q := Ideal.Quotient.mk J.asIdeal
    coordinateProjectiveTrace σ T r ≤
      LinearMap.ker
        (principalRightIdealQuotientMap q
          (skeletonCoordinateProjector σ (fun k ↦ k = r))) := by
  dsimp only
  rw [coordinateProjectiveTrace]
  refine iSup_le fun j ↦ iSup_le fun hj ↦ iSup_le fun f ↦ ?_
  rintro y ⟨x, rfl⟩
  change
    principalRightIdealQuotientMap
      (Ideal.Quotient.mk
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal)
      (skeletonCoordinateProjector σ (fun k ↦ k = r))
      (f.hom x) = 0
  apply Subtype.ext
  change
    op (Ideal.Quotient.mk
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal
      (unop (f.hom x).1)) = 0
  apply unop_injective
  change
    Ideal.Quotient.mk
      (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal
      (unop (f.hom x).1) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact map_coordinateProjective_mem_supportIdeal σ T r j hj f x

/-- The canonical element `eᵣ a z b` of the target coordinate
projective. -/
def coordinateSandwichedElement
    (r : κ) (a z b : Γ) :
    (coordinateProjective σ r).obj := by
  let er := skeletonCoordinateProjector σ (fun k ↦ k = r)
  refine ⟨op (er * a * z * b), ?_⟩
  have hgen :
      op er ∈ QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal er :=
    Ideal.subset_span (Set.mem_singleton (op er))
  have hmul :=
    (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal er).mul_mem_left
      (op (a * z * b)) hgen
  change op (er * (a * z * b)) ∈
    QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal er
  simpa only [mul_assoc, ← op_mul] using hmul

/-- Every element of the selected two-sided ideal, after sandwiching on
the left by the target coordinate idempotent, lies in the trace. -/
theorem coordinateSandwichedElement_mem_trace_of_mem_supportIdeal
    (T : Set κ) (r : κ) (z : Γ)
    (hz : z ∈ QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
      (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))) :
    ∀ a b : Γ,
      coordinateSandwichedElement σ r a z b ∈
        coordinateProjectiveTrace σ T r := by
  let eT := skeletonCoordinateProjector σ (fun k ↦ k ∈ T)
  let er := skeletonCoordinateProjector σ (fun k ↦ k = r)
  induction hz using TwoSidedIdeal.span_induction with
  | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst z
      intro a b
      have her : IsIdempotentElem er :=
        coordinateProjector_isIdempotent σ.obj (fun k ↦ k = r)
      have htarget : er * (er * a) = er * a := by
        rw [← mul_assoc, her.eq]
      let g : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule eT ⟶
          (coordinateProjective σ r).obj :=
        ConcreteCategory.ofHom (C := ModuleCat Γᵐᵒᵖ)
          (QuotientSubmoduleEquidistribution.TsukamotoRadicalSandwichBridge.principalLinearBetween
            (source := eT) (target := er) htarget)
      have hg :=
        range_le_coordinateProjectiveTrace_of_principalRightModule
          σ T r g
      let xb : QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal eT :=
        ⟨op (eT * b), by
          have hgen :
              op eT ∈ QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal eT :=
            Ideal.subset_span (Set.mem_singleton (op eT))
          have hmul :=
            (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightIdeal eT).mul_mem_left
              (op b) hgen
          simpa only [← op_mul] using hmul⟩
      apply hg
      refine ⟨xb, ?_⟩
      apply Subtype.ext
      change op (eT * b) * op (er * a) =
        op (er * a * eT * b)
      apply unop_injective
      change (er * a) * (eT * b) = er * a * eT * b
      simp only [mul_assoc]
  | zero =>
      intro a b
      have heq : coordinateSandwichedElement σ r a 0 b = 0 := by
        apply Subtype.ext
        change op (er * a * 0 * b) = 0
        apply unop_injective
        simp only [unop_op, MulOpposite.unop_zero, mul_zero, zero_mul]
      rw [heq]
      exact (coordinateProjectiveTrace σ T r).zero_mem
  | add x y hx hy ihx ihy =>
      intro a b
      have heq :
          coordinateSandwichedElement σ r a (x + y) b =
            coordinateSandwichedElement σ r a x b +
              coordinateSandwichedElement σ r a y b := by
        apply Subtype.ext
        change
          op (er * a * (x + y) * b) =
            op (er * a * x * b) + op (er * a * y * b)
        apply unop_injective
        simp only [unop_op, MulOpposite.unop_add, mul_add, add_mul]
      rw [heq]
      exact (coordinateProjectiveTrace σ T r).add_mem
        (ihx a b) (ihy a b)
  | neg x hx ih =>
      intro a b
      have heq :
          coordinateSandwichedElement σ r a (-x) b =
            -coordinateSandwichedElement σ r a x b := by
        apply Subtype.ext
        change op (er * a * (-x) * b) = -op (er * a * x * b)
        apply unop_injective
        simp only [unop_op, MulOpposite.unop_neg, mul_neg, neg_mul]
      rw [heq]
      exact (coordinateProjectiveTrace σ T r).neg_mem (ih a b)
  | left_absorb c y hy ih =>
      intro a b
      have heq :
          coordinateSandwichedElement σ r a (c * y) b =
            coordinateSandwichedElement σ r (a * c) y b := by
        apply Subtype.ext
        change
          op (er * a * (c * y) * b) =
            op (er * (a * c) * y * b)
        apply unop_injective
        simp only [unop_op, mul_assoc]
      rw [heq]
      exact ih (a * c) b
  | right_absorb c y hy ih =>
      intro a b
      have heq :
          coordinateSandwichedElement σ r a (y * c) b =
            coordinateSandwichedElement σ r a y (c * b) := by
        apply Subtype.ext
        change
          op (er * a * (y * c) * b) =
            op (er * a * y * (c * b))
        apply unop_injective
        simp only [unop_op, mul_assoc]
      rw [heq]
      exact ih a (c * b)

/-- Kernel membership for the quotient map forces membership in the
coordinate trace. -/
theorem mem_coordinateProjectiveTrace_of_principalRightIdealQuotientMap_eq_zero
    (T : Set κ) (r : κ)
    (x : (coordinateProjective σ r).obj)
    (hx :
      principalRightIdealQuotientMap
        (Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal)
        (skeletonCoordinateProjector σ (fun k ↦ k = r)) x = 0) :
    x ∈ coordinateProjectiveTrace σ T r := by
  let er := skeletonCoordinateProjector σ (fun k ↦ k = r)
  let z : Γ := unop x.1
  have hxq :
      Ideal.Quotient.mk
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal z = 0 := by
    have h := congrArg (fun y ↦ unop y.1) hx
    change
      Ideal.Quotient.mk
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))).asIdeal z = 0
      at h
    exact h
  have hz : z ∈
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hxq
  have hmem :=
    coordinateSandwichedElement_mem_trace_of_mem_supportIdeal
      σ T r z hz 1 1
  have her : IsIdempotentElem er :=
    coordinateProjector_isIdempotent σ.obj (fun k ↦ k = r)
  have hxfixOpp :=
    QuotientSubmoduleEquidistribution.Tsukamoto.mul_op_eq_self_of_mem_principalRightIdeal
      her x.property
  have hxfix : er * z = z := by
    exact congrArg unop hxfixOpp
  have heq : coordinateSandwichedElement σ r 1 z 1 = x := by
    apply Subtype.ext
    apply unop_injective
    change er * 1 * z * 1 = z
    simpa only [mul_one, one_mul] using hxfix
  rwa [heq] at hmem

theorem ker_principalRightIdealQuotientMap_le_coordinateProjectiveTrace
    (T : Set κ) (r : κ) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))
    let q := Ideal.Quotient.mk J.asIdeal
    LinearMap.ker
        (principalRightIdealQuotientMap q
          (skeletonCoordinateProjector σ (fun k ↦ k = r))) ≤
      coordinateProjectiveTrace σ T r := by
  dsimp only
  intro x hx
  apply mem_coordinateProjectiveTrace_of_principalRightIdealQuotientMap_eq_zero
    σ T r x
  exact hx

/-- Exact trace-kernel identification for the coordinate quotient map. -/
theorem coordinateProjectiveTrace_eq_ker_principalRightIdealQuotientMap
    (T : Set κ) (r : κ) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))
    let q := Ideal.Quotient.mk J.asIdeal
    coordinateProjectiveTrace σ T r =
      LinearMap.ker
        (principalRightIdealQuotientMap q
          (skeletonCoordinateProjector σ (fun k ↦ k = r))) := by
  dsimp only
  apply le_antisymm
  · exact
      coordinateProjectiveTrace_le_ker_principalRightIdealQuotientMap
        σ T r
  · exact
      ker_principalRightIdealQuotientMap_le_coordinateProjectiveTrace
        σ T r

/-- The trace-defined coordinate standard is the removed-coordinate
principal right module over the quotient by the selected support ideal,
with scalars restricted back to the Auslander algebra. -/
noncomputable def coordinateStandardQuotientIsoRestrictedPrincipalRightModule
    (T : Set κ) (r : κ) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))
    let q := Ideal.Quotient.mk J.asIdeal
    coordinateStandardQuotient σ T r ≅
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
          (q (skeletonCoordinateProjector σ (fun k ↦ k = r)))) := by
  dsimp only
  let er := skeletonCoordinateProjector σ (fun k ↦ k = r)
  let J :=
    QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
      (skeletonCoordinateProjector σ (fun k ↦ k ∈ T))
  let q := Ideal.Quotient.mk J.asIdeal
  let f := principalRightIdealQuotientMap q er
  have hf : Function.Surjective f :=
    principalRightModuleQuotientMap_surjective
      q Ideal.Quotient.mk_surjective er
        (coordinateProjector_isIdempotent σ.obj (fun k ↦ k = r))
  exact
    ((Submodule.quotEquivOfEq _ _
        (coordinateProjectiveTrace_eq_ker_principalRightIdealQuotientMap
          σ T r)) ≪≫ₗ
      f.quotKerEquivOfSurjective hf).toModuleIso

/-- Deletion-chain specialization of the standard/principal quotient
identification. -/
noncomputable def deletionCoordinateStandardQuotientIsoRestrictedPrincipalRightModule
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.succ))
    let q := Ideal.Quotient.mk J.asIdeal
    deletionCoordinateStandardQuotient σ d i ≅
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalRightModule
          (q (skeletonCoordinateProjector σ
            (fun k ↦ k = d.removed i)))) :=
  coordinateStandardQuotientIsoRestrictedPrincipalRightModule
    σ (d.support i.succ) (d.removed i)

/-- Splitting off one coordinate from a coordinate projector. -/
theorem coordinateProjector_sdiff_singleton_add
    {C : Type uR} [Category.{wR} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {k : Type uκ} [Finite k]
    (X : k → C) (S : Set k) (r : k) (hr : r ∈ S) :
    coordinateProjector X (fun j ↦ j ∈ S) =
      ((coordinateProjector X (fun j ↦ j ∈ S ∧ j ≠ r) :
          (⨁ X) ⟶ (⨁ X)) +
        (coordinateProjector X (fun j ↦ j = r) :
          (⨁ X) ⟶ (⨁ X)) :
        (⨁ X) ⟶ (⨁ X)) := by
  classical
  apply biproduct.hom_ext'
  intro j
  erw [Preadditive.comp_add]
  by_cases hjr : j = r
  · subst j
    rw [ι_coordinateProjector_of_mem X (fun j ↦ j ∈ S) r hr,
      ι_coordinateProjector_of_not_mem X (fun j ↦ j ∈ S ∧ j ≠ r) r (by simp),
      ι_coordinateProjector_of_mem X (fun j ↦ j = r) r (by simp),
      zero_add]
  · by_cases hjS : j ∈ S
    · rw [ι_coordinateProjector_of_mem X (fun j ↦ j ∈ S) j hjS,
        ι_coordinateProjector_of_mem X (fun j ↦ j ∈ S ∧ j ≠ r) j ⟨hjS, hjr⟩,
        ι_coordinateProjector_of_not_mem X (fun j ↦ j = r) j hjr,
        add_zero]
    · rw [ι_coordinateProjector_of_not_mem X (fun j ↦ j ∈ S) j hjS,
        ι_coordinateProjector_of_not_mem X (fun j ↦ j ∈ S ∧ j ≠ r) j (by simp [hjS]),
        ι_coordinateProjector_of_not_mem X (fun j ↦ j = r) j hjr,
        add_zero]

/-- The upper deletion-step projector is the sum of the lower projector
and the removed singleton projector. -/
theorem deletionStep_coordinateProjector_eq_add
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    skeletonCoordinateProjector σ (d.support i.castSucc) =
      ((skeletonCoordinateProjector σ (d.support i.succ) : Γ) +
        (skeletonCoordinateProjector σ
          (fun j ↦ j = d.removed i) : Γ)) := by
  have h :=
    coordinateProjector_sdiff_singleton_add
      σ.obj (d.support i.castSucc) (d.removed i) (d.removed_mem i)
  rw [d.step i]
  exact h

/-- After quotienting by the lower support ideal, the upper coordinate
projector becomes the removed singleton projector. -/
theorem deletionStep_quotient_coordinateProjector_eq_removed
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.succ))
    let q := Ideal.Quotient.mk J.asIdeal
    q (skeletonCoordinateProjector σ (d.support i.castSucc)) =
      q (skeletonCoordinateProjector σ
        (fun j ↦ j = d.removed i)) := by
  dsimp only
  rw [deletionStep_coordinateProjector_eq_add σ d i]
  have hzero :
      Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal
          (skeletonCoordinateProjector σ (d.support i.succ)) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact
      TwoSidedIdeal.subset_span
        (Set.mem_singleton
          (skeletonCoordinateProjector σ (d.support i.succ)))
  calc
    Ideal.Quotient.mk
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal
        ((skeletonCoordinateProjector σ (d.support i.succ) : Γ) +
          skeletonCoordinateProjector σ (fun j ↦ j = d.removed i)) =
      Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal
          (skeletonCoordinateProjector σ (d.support i.succ)) +
        Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal
          (skeletonCoordinateProjector σ (fun j ↦ j = d.removed i)) :=
        map_add
          (Ideal.Quotient.mk
            (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
              (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal)
          _ _
    _ = _ := by rw [hzero, zero_add]

/-- The quotient image of the upper support ideal is literally the
principal two-sided ideal of the removed singleton projector. -/
theorem deletionStep_quotientImage_eq_principalRemoved
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    let I :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.castSucc))
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.succ))
    let q := Ideal.Quotient.mk J.asIdeal
    QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J =
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (q (skeletonCoordinateProjector σ
          (fun j ↦ j = d.removed i))) := by
  dsimp only
  calc
    QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (d.support i.castSucc)))
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (d.support i.succ))) =
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal
          (skeletonCoordinateProjector σ (d.support i.castSucc))) :=
      QuotientSubmoduleEquidistribution.TsukamotoRadicalSandwichBridge.map_principalTwoSidedIdeal
        _ _
    _ = _ := congrArg QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
      (deletionStep_quotient_coordinateProjector_eq_removed σ d i)

/-- The literal right ideal layer at a deletion step is the restricted
principal ideal generated by the removed singleton projector in the
corresponding quotient algebra. -/
noncomputable def deletionCoordinateRightIdealLayerIsoRestrictedPrincipalIdeal
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.succ))
    let q := Ideal.Quotient.mk J.asIdeal
    rightIdealLayer
        (idempotentIdealChainOfSaturatedSupportDeletion σ d) i ≅
      (ModuleCat.restrictScalars (RingHom.op q)).obj
        (ModuleCat.of ((Γ ⧸ J.asIdeal)ᵐᵒᵖ)
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (q (skeletonCoordinateProjector σ
              (fun j ↦ j = d.removed i))))) := by
  dsimp only
  let H := idempotentIdealChainOfSaturatedSupportDeletion σ d
  let e₁ := rightIdealLayerRestrictedQuotientImageIsoForChain H i
  refine e₁ ≪≫ eqToIso ?_
  change
    (ModuleCat.restrictScalars
      (RingHom.op
        (Ideal.Quotient.mk
          (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
            (skeletonCoordinateProjector σ (d.support i.succ))).asIdeal))).obj
        (ModuleCat.of _
          (QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage
            (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
              (skeletonCoordinateProjector σ (d.support i.castSucc)))
            (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
              (skeletonCoordinateProjector σ (d.support i.succ))))) = _
  rw [deletionStep_quotientImage_eq_principalRemoved σ d i]

/-- At one deletion step, finiteness and right-projectivity of the upper
coordinate ideal give the complete quotient-principal realization of
the standard and the literal ideal layer. -/
noncomputable def deletionCoordinateQuotientPrincipalLayerRealization
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    (hupperFinite :
      Module.Finite Γᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (d.support i.castSucc))))
    (hupperProjective :
      QuotientSubmoduleEquidistribution.Tsukamoto.IsRightProjectiveIdeal
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ (d.support i.castSucc)))) :
    let J :=
      QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
        (skeletonCoordinateProjector σ (d.support i.succ))
    let q := Ideal.Quotient.mk J.asIdeal
    let er := skeletonCoordinateProjector σ
      (fun k ↦ k = d.removed i)
    QuotientPrincipalLayerRealization q (q er)
      (deletionCoordinateStandardQuotient σ d i)
      (rightIdealLayer
        (idempotentIdealChainOfSaturatedSupportDeletion σ d) i) := by
  dsimp only
  let I :=
    QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
      (skeletonCoordinateProjector σ (d.support i.castSucc))
  let J :=
    QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
      (skeletonCoordinateProjector σ (d.support i.succ))
  let q := Ideal.Quotient.mk J.asIdeal
  let er := skeletonCoordinateProjector σ
    (fun k ↦ k = d.removed i)
  letI : Module.Finite Γᵐᵒᵖ I := hupperFinite
  have hJI : J ≤ I := by
    apply skeletonPrincipalTwoSidedIdeal_mono σ
    intro k hk
    rw [d.step i] at hk
    exact hk.1
  have hJidem : QuotientSubmoduleEquidistribution.Tsukamoto.IsIdempotentIdeal J :=
    QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal_isIdempotent
      (coordinateProjector_isIdempotent σ.obj (d.support i.succ))
  have hquotFinite :
      Module.Finite (Γ ⧸ J.asIdeal)ᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J) :=
    quotientImage_finite J I
  have hquotProjective :
      QuotientSubmoduleEquidistribution.Tsukamoto.IsRightProjectiveIdeal
        (QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J) :=
    QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage_isRightProjectiveIdeal
      J I hJI hJidem hupperProjective
  have hEq :
      QuotientSubmoduleEquidistribution.Tsukamoto.quotientImage I J =
        QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal (q er) :=
    deletionStep_quotientImage_eq_principalRemoved σ d i
  refine
    { standardIso :=
        deletionCoordinateStandardQuotientIsoRestrictedPrincipalRightModule
          σ d i
      layerIso :=
        deletionCoordinateRightIdealLayerIsoRestrictedPrincipalIdeal
          σ d i
      finiteIdeal := ?_
      projectiveIdeal := ?_ }
  · rw [← hEq]
    exact hquotFinite
  · rw [← hEq]
    exact hquotProjective

/-- The coordinate standard quotient is nonzero: its projection still
maps onto the simple top belonging to the deleted coordinate. -/
theorem deletionCoordinateStandardQuotient_nontrivial
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    Nontrivial (deletionCoordinateStandardQuotient σ d i) := by
  let r := d.removed i
  let P := coordinateProjectiveCover σ hfinite r
  let q : (coordinateProjective σ r).obj ⟶
      coordinateSimple σ r := P.map
  have hkill : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (coordinateProjective σ j).obj ⟶
        (coordinateProjective σ r).obj,
        f ≫ q = 0 := by
    intro j hj f
    apply hom_coordinateSimple_eq_zero_of_ne σ hfinite
    intro hjr
    subst j
    exact (removed_not_mem_later_support d (i := i) le_rfl) hj
  let u : deletionCoordinateStandardQuotient σ d i ⟶
      coordinateSimple σ r :=
    coordinateStandardDesc σ (d.support i.succ) r q hkill
  have hqu : deletionCoordinateStandardProjection σ d i ≫ u = q :=
    coordinateStandardProjection_desc
      σ (d.support i.succ) r q hkill
  letI : Epi q := P.essentialEpi.1
  letI : Epi u := epi_of_epi_fac hqu
  letI : Simple (coordinateSimple σ r) :=
    coordinateSimple_isSimple σ hfinite r
  letI : Nontrivial (coordinateSimple σ r) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact Simple.not_isZero (coordinateSimple σ r)
      ((ModuleCat.isZero_iff_subsingleton).2 hsub)
  exact
    ((ModuleCat.epi_iff_surjective u).mp inferInstance).nontrivial

/-- Every coordinate standard quotient is indecomposable.  It is a
nonzero quotient of the finite-length indecomposable singleton coordinate
projective. -/
theorem deletionCoordinateStandardQuotient_indecomposable
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Γᵐᵒᵖ
      (deletionCoordinateStandardQuotient σ d i) := by
  let r := d.removed i
  let hP := coordinateProjective_isFiniteProjective σ r
  letI : Module.Projective Γᵐᵒᵖ (coordinateProjective σ r).obj :=
    (IsProjective.iff_projective
      (coordinateProjective σ r).obj).mpr hP.2
  letI : Nontrivial (deletionCoordinateStandardQuotient σ d i) :=
    deletionCoordinateStandardQuotient_nontrivial σ hfinite d i
  exact
    indecomposable_of_surjective_from_indec_projective
      (hfinite r) (coordinateProjective_indecomposable σ r)
      (deletionCoordinateStandardProjection σ d i).hom
      ((ModuleCat.epi_iff_surjective
        (deletionCoordinateStandardProjection σ d i)).mp inferInstance)

/-- Coordinate specialization of the multiplicity reduction.  Given the
trace-kernel filtration, literal layer membership in `add(Δᵢ)` produces the
complete standard-module chain data; the declarations below derive that
membership from the quotient-principal realization. -/
def deletionCoordinateRightStandardModuleChainData
    [IsNoetherianRing Γᵐᵒᵖ]
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (hkernel :
      DeletionCoordinateStandardKernelFiltration σ hfinite d)
    (hadd : ∀ i : Fin (Fintype.card κ),
      finiteAddClosure
        (deletionCoordinateStandardQuotient σ d i)
        (rightIdealLayer
          (idempotentIdealChainOfSaturatedSupportDeletion σ d) i)) :
    RightStandardModuleChainData
      (idempotentIdealChainOfSaturatedSupportDeletion σ d) := by
  let D :=
    deletionCoordinateOrderedHighestWeightStructure
      σ hfinite d hkernel
  exact
    rightStandardModuleChainDataOfFiniteLengthFiniteAdd
      (idempotentIdealChainOfSaturatedSupportDeletion σ d)
      D
      (deletionCoordinateStandardQuotient_isFiniteLength
        σ hfinite d)
      (deletionCoordinateStandardQuotient_indecomposable
        σ hfinite d)
      hadd

/-- Fully structured quotient-ring version of the coordinate constructor.
For every deletion step, a realization of the standard as `eB` and the
layer as the finite projective ideal `BeB` supplies the completed positive
CPS layer comparison. -/
def deletionCoordinateRightStandardModuleChainDataOfQuotientRealizations
    [IsNoetherianRing Γᵐᵒᵖ]
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (hkernel :
      DeletionCoordinateStandardKernelFiltration σ hfinite d)
    (B : Fin (Fintype.card κ) → Type wR)
    [∀ i, Ring (B i)]
    (q : ∀ i, Γ →+* B i)
    (e : ∀ i, B i)
    (P : ∀ i,
      QuotientPrincipalLayerRealization (q i) (e i)
        (deletionCoordinateStandardQuotient σ d i)
        (rightIdealLayer
          (idempotentIdealChainOfSaturatedSupportDeletion σ d) i)) :
    RightStandardModuleChainData
      (idempotentIdealChainOfSaturatedSupportDeletion σ d) :=
  deletionCoordinateRightStandardModuleChainData
    σ hfinite d hkernel (fun i ↦ (P i).layer_mem_add)

/-- End-to-end coordinate CPS constructor.  The only ideal-theoretic
inputs left are finiteness and right-projectivity of each nonfinal upper
coordinate ideal; quotient projectivity, the literal layer comparison,
and positive standard multiplicity are derived internally. -/
noncomputable def
    deletionCoordinateRightStandardModuleChainDataOfFiniteProjectiveUpperIdeals
    [IsNoetherianRing Γᵐᵒᵖ]
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (hkernel :
      DeletionCoordinateStandardKernelFiltration σ hfinite d)
    (hupperFinite : ∀ i : Fin (Fintype.card κ),
      Module.Finite Γᵐᵒᵖ
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ
            (d.support i.castSucc))))
    (hupperProjective : ∀ i : Fin (Fintype.card κ),
      QuotientSubmoduleEquidistribution.Tsukamoto.IsRightProjectiveIdeal
        (QuotientSubmoduleEquidistribution.Tsukamoto.principalTwoSidedIdeal
          (skeletonCoordinateProjector σ
            (d.support i.castSucc)))) :
    RightStandardModuleChainData
      (idempotentIdealChainOfSaturatedSupportDeletion σ d) :=
  deletionCoordinateRightStandardModuleChainData
    σ hfinite d hkernel (fun i ↦
      (deletionCoordinateQuotientPrincipalLayerRealization
        σ d i (hupperFinite i) (hupperProjective i)).layer_mem_add)

end QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalQuotientDeletionChain

open QuotientSubmoduleEquidistribution.AuslanderEquivalence
open QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent
open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe uR uι wR uK

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {ι : Type uι}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{uR, uι, wR} R ι)
  [Fintype ι]
  {K : Type uK} [Field K] [Algebra K R]
  [∀ i : ι, Module K (σ.obj i)]
  [∀ i : ι, IsScalarTower K R (σ.obj i)]
  [∀ i : ι, FiniteDimensional K (σ.obj i)]

local notation "Γ" => skeletonAuslanderAlgebra σ

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

include K

/-- A maximal quotient-closed flag under the paper's finite-dimensional
skeleton hypotheses canonically supplies the positive literal right CPS
ideal-layer comparison, hence complete right standard-module chain data. -/
noncomputable def flagRightStandardModuleChainData
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    RightStandardModuleChainData
      (flagIdealChain (K := K) σ s) := by
  let d := FlagSourceChain (K := K) σ s
  letI : IsArtinianRing Γᵐᵒᵖ :=
    isArtinianRing_skeletonAuslanderAlgebra_op (K := K) σ
  let hfinite : ∀ i : ι,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj :=
    coordinateProjective_isFiniteLength σ
  exact
    deletionCoordinateRightStandardModuleChainDataOfFiniteProjectiveUpperIdeals
      σ hfinite d.toSaturatedSupport
      (legalDeletionCoordinateStandardKernelFiltration σ hfinite d)
      (fun i ↦ twoSidedIdeal_finite_right _)
      (fun i ↦ flagIdealChain_rightProjective (K := K) σ s i)

/-- The manuscript's complete right-handed CPS/Tsukamoto route: the
positive standard-layer data above and the already verified strong-heredity
conditions produce the right-strongly quasi-hereditary structure. -/
noncomputable def flagRightStronglyQuasiHereditaryViaCPS
    (s : QuotientSubmoduleEquidistribution.SetClosure.ClosedFlag σ.qClosure) :
    RightStronglyQuasiHereditaryAlgebra
      (skeletonAuslanderAlgebra σ) (Fin (Fintype.card ι)) :=
  rightStronglyQuasiHereditary_of_chain
    (flagIdealChain (K := K) σ s)
    (flagRightStandardModuleChainData (K := K) σ s)
    (flagIdealChain_isRightStrongHeredity (K := K) σ s)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalQuotientDeletionChain
