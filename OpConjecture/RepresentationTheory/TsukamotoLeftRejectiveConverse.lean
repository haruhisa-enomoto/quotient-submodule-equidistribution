import OpConjecture.CategoryTheory.RejectiveOpposite
import OpConjecture.RepresentationTheory.TsukamotoRejectiveConverse
import OpConjecture.RepresentationTheory.TsukamotoLeftRejectiveBridge
import OpConjecture.RepresentationTheory.MaximalFlagAuslanderPackage
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The left projective-ideal-to-rejective converse

Finite-projective Hom duality transports the right-handed Tsukamoto converse
over the opposite ring and proves the full left-handed equivalence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace OpConjecture.Tsukamoto

universe vC vD uC uD u

variable {A : Type u} [Ring A]

private abbrev FiniteProjectives (A : Type u) [Ring A] :=
  (AuslanderEquivalence.finiteProjectiveModules
    Aᵐᵒᵖ).FullSubcategory

private instance finiteProjectives_hasFiniteBiproducts
    (A : Type u) [Ring A] :
    HasFiniteBiproducts (FiniteProjectives A) := by
  letI :
      HasFiniteBiproducts
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

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

private theorem finiteAddClosure_op
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure
      (Opposite.op G) (Opposite.op X) := by
  obtain ⟨P⟩ := h
  let E : Fin P.n → C := fun _ ↦ G
  let Eop : Fin P.n → Cᵒᵖ :=
    fun j ↦ Opposite.op (E j)
  let biproductOpIso :
      Opposite.op (biproduct E) ≅ biproduct Eop :=
    (biproduct.isoCoproduct E).op.symm ≪≫
      opCoproductIsoProduct E ≪≫
      (biproduct.isoProduct Eop).symm
  exact ⟨{
    n := P.n
    retract :=
      P.retract.op.trans
        (Retract.ofIso biproductOpIso) }⟩

private theorem finiteAddClosure_unop
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C}
    (h :
      AuslanderEquivalence.finiteAddClosure
        (Opposite.op G) (Opposite.op X)) :
    AuslanderEquivalence.finiteAddClosure G X := by
  obtain ⟨P⟩ := h
  let E : Fin P.n → C := fun _ ↦ G
  let Eop : Fin P.n → Cᵒᵖ :=
    fun j ↦ Opposite.op (E j)
  let biproductOpIso :
      Opposite.op (biproduct E) ≅ biproduct Eop :=
    (biproduct.isoCoproduct E).op.symm ≪≫
      opCoproductIsoProduct E ≪≫
      (biproduct.isoProduct Eop).symm
  exact ⟨{
    n := P.n
    retract :=
      (P.retract.op.map (unopUnop C)).trans
        (Retract.ofIso biproductOpIso.unop) }⟩

private theorem finiteAddClosure_op_iff
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C]
    {G X : C} :
    AuslanderEquivalence.finiteAddClosure
        (Opposite.op G) (Opposite.op X) ↔
      AuslanderEquivalence.finiteAddClosure G X :=
  ⟨finiteAddClosure_unop, finiteAddClosure_op⟩

private theorem finiteAddClosure_map_functor
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Preadditive C]
    [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts C]
    [HasFiniteBiproducts D]
    (E : C ≌ D)
    {G X : C}
    (h : AuslanderEquivalence.finiteAddClosure G X) :
    AuslanderEquivalence.finiteAddClosure
      (E.functor.obj G) (E.functor.obj X) := by
  obtain ⟨P⟩ := h
  letI :
      PreservesBiproduct
        (fun _ : Fin P.n ↦ G) E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  exact ⟨{
    n := P.n
    retract :=
      (P.retract.map E.functor).trans
        (Retract.ofIso
          (E.functor.mapBiproduct
            (fun _ : Fin P.n ↦ G))) }⟩

private theorem finiteAddClosure_map_equivalence_iff
    {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Preadditive C]
    [Category.{vD} D] [Preadditive D]
    [HasFiniteBiproducts C]
    [HasFiniteBiproducts D]
    (E : C ≌ D)
    {G X : C} :
    AuslanderEquivalence.finiteAddClosure
        (E.functor.obj G) (E.functor.obj X) ↔
      AuslanderEquivalence.finiteAddClosure G X := by
  constructor
  · intro h
    have h' :=
      finiteAddClosure_map_functor E.symm h
    have h'' :
        AuslanderEquivalence.finiteAddClosure
          G (E.inverse.obj (E.functor.obj X)) :=
      (AuslanderEquivalence.finiteAddClosure_iff_of_iso
        (E.unitIso.app G)).mpr h'
    obtain ⟨P⟩ := h''
    exact ⟨{
      n := P.n
      retract :=
        (Retract.ofIso (E.unitIso.app X)).trans
          P.retract }⟩
  · exact finiteAddClosure_map_functor E

private instance finiteAddClosure_isClosedUnderIsomorphisms
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasFiniteBiproducts C] (G : C) :
    (AuslanderEquivalence.finiteAddClosure G).IsClosedUnderIsomorphisms where
  of_iso {X Y} i hX := by
    obtain ⟨P⟩ := hX
    exact ⟨{
      n := P.n
      retract :=
        (Retract.ofIso i.symm).trans P.retract }⟩

private instance finiteProjective_isClosedUnderIsomorphisms
    (R : Type u) [Ring R] :
    (AuslanderEquivalence.finiteProjectiveModules R).IsClosedUnderIsomorphisms where
  of_iso {X Y} i hX := by
    have hAddX :
        AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of R R) X :=
      (AuslanderEquivalence.finiteAddClosure_regular_iff
        R X).mpr hX
    obtain ⟨P⟩ := hAddX
    apply
      (AuslanderEquivalence.finiteAddClosure_regular_iff
        R Y).mp
    exact ⟨{
      n := P.n
      retract :=
        (Retract.ofIso i.symm).trans P.retract }⟩

private theorem isLeftRejective_of_isRightRejective_op
    {C : Type uC} [Category.{vC} C]
    (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms]
    (h : CategoricalRejective.IsRightRejective P.op) :
    CategoricalRejective.IsLeftRejective P := by
  have hOpOp :
      CategoricalRejective.IsLeftRejective P.op.op :=
    CategoricalRejective.isLeftRejective_op_of_isRightRejective h
  have hImage :=
    CategoricalRejective.Equivalence.isLeftRejective_image
      (opOpEquivalence C) P.op.op hOpOp
  have hProperty :
      CategoricalRejective.imageProperty
          (opOpEquivalence C) P.op.op =
        P := by
    funext X
    rfl
  rw [hProperty] at hImage
  exact hImage

private theorem finiteProjective_restrictScalars_inverseImage
    {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    (AuslanderEquivalence.finiteProjectiveModules R).inverseImage
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor =
      AuslanderEquivalence.finiteProjectiveModules S := by
  funext M
  apply propext
  let E :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let i :
      E.functor.obj (ModuleCat.of S S) ≅
        ModuleCat.of R R :=
    ModuleCat.restrictScalarsIsoOfEquiv e
  calc
    AuslanderEquivalence.finiteProjectiveModules R
          (E.functor.obj M) ↔
        AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of R R) (E.functor.obj M) :=
      (AuslanderEquivalence.finiteAddClosure_regular_iff
        R (E.functor.obj M)).symm
    _ ↔
        AuslanderEquivalence.finiteAddClosure
          (E.functor.obj (ModuleCat.of S S))
          (E.functor.obj M) :=
      (AuslanderEquivalence.finiteAddClosure_iff_of_iso
        i).symm
    _ ↔
        AuslanderEquivalence.finiteAddClosure
          (ModuleCat.of S S) M :=
      finiteAddClosure_map_equivalence_iff E
    _ ↔
        AuslanderEquivalence.finiteProjectiveModules S M :=
      AuslanderEquivalence.finiteAddClosure_regular_iff S M

private def finiteProjectiveRestrictScalarsEquivalence
    {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    (AuslanderEquivalence.finiteProjectiveModules S).FullSubcategory ≌
      (AuslanderEquivalence.finiteProjectiveModules R).FullSubcategory :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    e).congrFullSubcategory
    (finiteProjective_restrictScalars_inverseImage e)

private abbrev regularRightModule (A : Type u) [Ring A] :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ Aᵐᵒᵖ

private def regularDualScalarRingEquiv :
    A ≃+*
      (End (Opposite.op (regularRightModule A)))ᵐᵒᵖ where
  toFun a :=
    op
      (ModuleCat.ofHom
        (LinearMap.mulRight Aᵐᵒᵖ (op a))).op
  invFun f :=
    unop (f.unop.unop.hom (1 : Aᵐᵒᵖ))
  left_inv a := by
    simp
  right_inv f := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change
      x * f.unop.unop.hom 1 =
        f.unop.unop.hom x
    simpa using
      (f.unop.unop.hom.map_smul x (1 : Aᵐᵒᵖ)).symm
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x * (op a + op b) =
      x * op a + x * op b
    exact mul_add x (op a) (op b)
  map_mul' a b := by
    apply MulOpposite.unop_injective
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp

private theorem oppositeFiniteProjective_eq_finiteAddClosure :
    (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ).op =
      AuslanderEquivalence.finiteAddClosure
        (Opposite.op (regularRightModule A)) := by
  funext X
  apply propext
  induction X with
  | op X =>
      exact
        (AuslanderEquivalence.finiteAddClosure_regular_iff
          Aᵐᵒᵖ X).symm.trans
          finiteAddClosure_op_iff.symm

private def regularHomDualityEquivalence :
    (FiniteProjectives A)ᵒᵖ ≌
      (AuslanderEquivalence.finiteProjectiveModules A).FullSubcategory :=
  (ObjectProperty.opEquivalence
      (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ)).symm |>.trans <|
    (ObjectProperty.fullSubcategoryCongr
      (oppositeFiniteProjective_eq_finiteAddClosure
        (A := A))) |>.trans <|
    (AuslanderEquivalence.auslanderEquivalence
      (Opposite.op (regularRightModule A))) |>.trans <|
    finiteProjectiveRestrictScalarsEquivalence
      (regularDualScalarRingEquiv (A := A))

private def doubleOpRingEquiv :
    A ≃+* (Aᵐᵒᵖ)ᵐᵒᵖ where
  toFun a := op (op a)
  invFun a := unop (unop a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private instance doubleOpRingHomInvPair :
    RingHomInvPair
      (doubleOpRingEquiv (A := A)).toRingHom
      (doubleOpRingEquiv (A := A)).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv
    (doubleOpRingEquiv (A := A))

private instance doubleOpRingHomInvPairSymm :
    RingHomInvPair
      (doubleOpRingEquiv (A := A)).symm.toRingHom
      (doubleOpRingEquiv (A := A)).toRingHom :=
  RingHomInvPair.of_ringEquiv
    (doubleOpRingEquiv (A := A)).symm

private theorem principalTwoSidedIdeal_op
    (e : A) :
    principalTwoSidedIdeal (op e) =
      (principalTwoSidedIdeal e).op := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact TwoSidedIdeal.mem_op_iff.mpr <|
      TwoSidedIdeal.subset_span
        (Set.mem_singleton e)
  · let J := principalTwoSidedIdeal (op e)
    have hJ : J.unop.op = J := by
      apply SetLike.ext
      intro x
      simp
    change
      (principalTwoSidedIdeal e).op ≤ J
    rw [← hJ]
    exact
      (TwoSidedIdeal.opOrderIso (R := A)).monotone <| by
        apply TwoSidedIdeal.span_le.mpr
        rw [Set.singleton_subset_iff]
        exact TwoSidedIdeal.mem_unop_iff.mpr <|
          TwoSidedIdeal.subset_span
            (Set.mem_singleton (op e))

private def principalIdealOpSemilinearEquiv
    (e : A) :
    principalTwoSidedIdeal e ≃ₛₗ[
      (doubleOpRingEquiv (A := A)).toRingHom]
      principalTwoSidedIdeal (op e) where
  toFun x :=
    ⟨op x.1, by
      rw [principalTwoSidedIdeal_op]
      exact TwoSidedIdeal.mem_op_iff.mpr x.2⟩
  invFun x :=
    ⟨unop x.1, by
      have hx :
          x.1 ∈ (principalTwoSidedIdeal e).op := by
        rw [← principalTwoSidedIdeal_op]
        exact x.2
      exact TwoSidedIdeal.mem_op_iff.mp hx⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext rfl

private theorem rightProjective_op_of_leftProjective
    (e : A)
    (h :
      IsLeftProjectiveIdeal
        (principalTwoSidedIdeal e)) :
    IsRightProjectiveIdeal
      (principalTwoSidedIdeal (op e)) := by
  letI :
      Module.Projective A
        (principalTwoSidedIdeal e) := h
  let σ := doubleOpRingEquiv (A := A)
  letI : RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv σ
  letI : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
    RingHomInvPair.of_ringEquiv σ.symm
  exact Module.Projective.of_equiv
    (principalIdealOpSemilinearEquiv e)

private def oppositeRingProjectiveDualityEquivalence :
    FiniteProjectives Aᵐᵒᵖ ≌ (FiniteProjectives A)ᵒᵖ :=
  (finiteProjectiveRestrictScalarsEquivalence
      (doubleOpRingEquiv (A := A))).trans
    (regularHomDualityEquivalence (A := A)).symm

private theorem idempotent_op
    {e : A} (he : IsIdempotentElem e) :
    IsIdempotentElem (op e) := by
  rw [isIdempotentElem_iff]
  apply unop_injective
  simpa using he.eq

private def principalFiniteProjective
    {e : A} (he : IsIdempotentElem e) :
    FiniteProjectives A :=
  ⟨principalRightModule e,
    principalRightModule_mem_finiteProjectiveModules he⟩

private abbrev principalRegularDualModule
    (e : A) :
    Module A
      (Opposite.op (regularRightModule A) ⟶
        Opposite.op (principalRightModule e)) :=
  Module.compHom
    (Opposite.op (regularRightModule A) ⟶
      Opposite.op (principalRightModule e))
    (regularDualScalarRingEquiv (A := A)).toRingHom

attribute [local instance] principalRegularDualModule

private abbrev principalRegularDoubleOpDualModule
    (e : A) :
    Module (Aᵐᵒᵖ)ᵐᵒᵖ
      (Opposite.op (regularRightModule A) ⟶
        Opposite.op (principalRightModule e)) :=
  Module.compHom
    (Opposite.op (regularRightModule A) ⟶
      Opposite.op (principalRightModule e))
    (doubleOpRingEquiv (A := A)).symm.toRingHom

attribute [local instance] principalRegularDoubleOpDualModule

private def principalRightGenerator (e : A) :
    principalRightIdeal e :=
  ⟨op e,
    Ideal.subset_span (Set.mem_singleton (op e))⟩

private def principalDualLinearEquiv
    {e : A} (he : IsIdempotentElem e) :
    (Opposite.op (regularRightModule A) ⟶
        Opposite.op (principalRightModule e)) ≃ₗ[(Aᵐᵒᵖ)ᵐᵒᵖ]
      principalRightIdeal (op e) where
  toFun f :=
    ⟨op (f.unop.hom (principalRightGenerator e)), by
      let g :
          (Opposite.unop
            (Opposite.op (principalRightModule e)) :
              Type u) :=
        principalRightGenerator e
      have hg : op e • g = g := by
        apply Subtype.ext
        change op e * op e = op e
        apply unop_injective
        simpa using he.eq
      have hf :
          op e * f.unop.hom g =
            f.unop.hom g := by
        change op e • f.unop.hom g =
          f.unop.hom g
        rw [← f.unop.hom.map_smul, hg]
      rw [← show
          op (f.unop.hom g) * op (op e) =
            op (f.unop.hom g) by
        apply unop_injective
        exact hf]
      exact
        (principalRightIdeal (op e)).mul_mem_left
          (op (f.unop.hom g))
          (Ideal.subset_span
            (Set.mem_singleton (op (op e))))⟩
  invFun x :=
    (ModuleCat.ofHom
      ((LinearMap.mulRight Aᵐᵒᵖ (unop x.1)).comp
        (Submodule.subtype (principalRightIdeal e)))).op
  left_inv f := by
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let g :
        (Opposite.unop
          (Opposite.op (principalRightModule e)) :
            Type u) :=
      principalRightGenerator e
    have hx : x.1 * op e = x.1 :=
      mul_op_eq_self_of_mem_principalRightIdeal
        he x.property
    calc
      x.1 * f.unop.hom g =
          f.unop.hom (x.1 • g) := by
            rw [f.unop.hom.map_smul]
            rfl
      _ = f.unop.hom x := by
        congr 2
        apply Subtype.ext
        exact hx
  right_inv x := by
    apply Subtype.ext
    exact
      mul_op_eq_self_of_mem_principalRightIdeal
        (idempotent_op he) x.property
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' r f := by
    apply Subtype.ext
    rfl

private def principalDualIso
    {e : A} (he : IsIdempotentElem e) :
    (oppositeRingProjectiveDualityEquivalence
        (A := A)).inverse.obj
          (Opposite.op (principalFiniteProjective he)) ≅
      principalFiniteProjective (idempotent_op he) := by
  apply ObjectProperty.isoMk
  dsimp [
    oppositeRingProjectiveDualityEquivalence,
    regularHomDualityEquivalence,
    finiteProjectiveRestrictScalarsEquivalence]
  change
    ModuleCat.of (Aᵐᵒᵖ)ᵐᵒᵖ
        (Opposite.op (regularRightModule A) ⟶
          Opposite.op (principalRightModule e)) ≅
      principalRightModule (op e)
  exact (principalDualLinearEquiv he).toModuleIso

private theorem internalPrincipalAdd_iff_literal
    {e : A} (he : IsIdempotentElem e)
    (X : FiniteProjectives A) :
    AuslanderEquivalence.finiteAddClosure
        (principalFiniteProjective he) X ↔
      addPrincipalRightModule e X.obj := by
  exact
    IndecomposableSkeleton.LegalQuotientDeletionChain.finiteAddClosure_fullSubcategory_iff
        (AuslanderEquivalence.finiteProjectiveModules Aᵐᵒᵖ)
        (principalFiniteProjective he) X

private theorem internalPrincipalAdd_eq_literal
    {e : A} (he : IsIdempotentElem e) :
    AuslanderEquivalence.finiteAddClosure
        (principalFiniteProjective he) =
      (fun X : FiniteProjectives A ↦
        addPrincipalRightModule e X.obj) := by
  funext X
  exact propext (internalPrincipalAdd_iff_literal he X)

private theorem duality_imageProperty_principal
    {e : A} (he : IsIdempotentElem e) :
    CategoricalRejective.imageProperty
        (oppositeRingProjectiveDualityEquivalence (A := A))
      (fun X : FiniteProjectives Aᵐᵒᵖ ↦
          addPrincipalRightModule (op e) X.obj) =
      ObjectProperty.op
        (fun X : FiniteProjectives A ↦
          addPrincipalRightModule e X.obj) := by
  funext X
  apply propext
  induction X with
  | op X =>
      let E :=
        oppositeRingProjectiveDualityEquivalence (A := A)
      let G : FiniteProjectives Aᵐᵒᵖ :=
        principalFiniteProjective (idempotent_op he)
      let H : FiniteProjectives A :=
        principalFiniteProjective he
      change
        addPrincipalRightModule (op e)
            (E.inverse.obj (Opposite.op X)).obj ↔
          addPrincipalRightModule e X.obj
      rw [← internalPrincipalAdd_iff_literal
          (idempotent_op he)
          (E.inverse.obj (Opposite.op X)),
        ← internalPrincipalAdd_iff_literal he X]
      exact
        (AuslanderEquivalence.finiteAddClosure_iff_of_iso
            (principalDualIso he).symm).trans <|
          (finiteAddClosure_map_equivalence_iff E.symm).trans <|
            finiteAddClosure_op_iff

/-- Finite-dimensional left-handed converse to Tsukamoto's
projectivity/rejectivity bridge. -/
theorem principalTwoSidedIdeal_leftRejective_of_finiteDimensional
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    {e : A} (he : IsIdempotentElem e)
    (hprojective :
      IsLeftProjectiveIdeal
        (principalTwoSidedIdeal e)) :
    CategoricalRejective.IsLeftRejective
      (fun X : FiniteProjectives A ↦
        addPrincipalRightModule e X.obj) := by
  let E :=
    oppositeRingProjectiveDualityEquivalence (A := A)
  have hRightProjective :
      IsRightProjectiveIdeal
        (principalTwoSidedIdeal (op e)) :=
    rightProjective_op_of_leftProjective e hprojective
  have hRight :
      CategoricalRejective.IsRightRejective
        (fun X : FiniteProjectives Aᵐᵒᵖ ↦
          addPrincipalRightModule (op e) X.obj) :=
    principalTwoSidedIdeal_rightRejective_of_finiteDimensional
      (A := Aᵐᵒᵖ) (k := k)
      (idempotent_op he) hRightProjective
  have hRightInternal :
      CategoricalRejective.IsRightRejective
        (AuslanderEquivalence.finiteAddClosure
          (principalFiniteProjective (idempotent_op he))) := by
    rw [internalPrincipalAdd_eq_literal
      (A := Aᵐᵒᵖ) (idempotent_op he)]
    exact hRight
  have hImage :=
    CategoricalRejective.Equivalence.isRightRejective_image
      E
      (AuslanderEquivalence.finiteAddClosure
        (principalFiniteProjective (idempotent_op he)))
      hRightInternal
  rw [internalPrincipalAdd_eq_literal
    (A := Aᵐᵒᵖ) (idempotent_op he)] at hImage
  rw [duality_imageProperty_principal he] at hImage
  have hInternalOp :
      CategoricalRejective.IsRightRejective
        (AuslanderEquivalence.finiteAddClosure
          (principalFiniteProjective he)).op := by
    rw [internalPrincipalAdd_eq_literal he]
    exact hImage
  have hLeft :
      CategoricalRejective.IsLeftRejective
        (AuslanderEquivalence.finiteAddClosure
          (principalFiniteProjective he)) :=
    isLeftRejective_of_isRightRejective_op
      (AuslanderEquivalence.finiteAddClosure
        (principalFiniteProjective he))
      hInternalOp
  rw [internalPrincipalAdd_eq_literal he] at hLeft
  exact hLeft

/-- The full finite-dimensional left-handed Tsukamoto equivalence. -/
theorem addPrincipalRightModule_leftRejective_iff_leftProjectiveIdeal
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    {e : A} (he : IsIdempotentElem e) :
    CategoricalRejective.IsLeftRejective
        (fun X : FiniteProjectives A ↦
          addPrincipalRightModule e X.obj) ↔
      IsLeftProjectiveIdeal
        (principalTwoSidedIdeal e) := by
  constructor
  · exact
      _root_.OpConjecture.Tsukamoto.LeftBridge.principalTwoSidedIdeal_leftProjective_of_literal_leftRejective
        he
  · exact
      principalTwoSidedIdeal_leftRejective_of_finiteDimensional
        (k := k) he

namespace IdempotentIdealChain

variable {n : ℕ} (H : IdempotentIdealChain A n)

/-- Ambient left rejectivity of all nonfinal principal-module terms
presented by an idempotent ideal chain. -/
def PrincipalLeftTermsAreRejective
    (P : H.IdempotentPresentation) : Prop :=
  ∀ i : Fin n,
    CategoricalRejective.IsLeftRejective
      (fun X :
        (AuslanderEquivalence.finiteProjectiveModules
          Aᵐᵒᵖ).FullSubcategory ↦
        addPrincipalRightModule
          (P.generator i.castSucc) X.obj)

/-- The left-handed termwise projectivity/rejectivity equivalence for an
idempotent ideal chain. -/
theorem principalLeftTermsAreRejective_iff_leftProjective
    {k : Type u} [Field k] [Algebra k A]
    [FiniteDimensional k A]
    (P : H.IdempotentPresentation) :
    H.PrincipalLeftTermsAreRejective P ↔
      ∀ i : Fin n,
        IsLeftProjectiveIdeal (H.ideal i.castSucc) := by
  constructor
  · intro h i
    have hi :=
      (addPrincipalRightModule_leftRejective_iff_leftProjectiveIdeal
        (k := k) (P.isIdempotent i.castSucc)).mp
        (h i)
    rw [P.span_eq i.castSucc] at hi
    exact hi
  · intro h i
    apply
      (addPrincipalRightModule_leftRejective_iff_leftProjectiveIdeal
        (k := k) (P.isIdempotent i.castSucc)).mpr
    rw [P.span_eq i.castSucc]
    exact h i

end IdempotentIdealChain

end OpConjecture.Tsukamoto
