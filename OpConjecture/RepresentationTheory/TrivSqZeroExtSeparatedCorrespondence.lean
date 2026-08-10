import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedData
import OpConjecture.RepresentationTheory.TrivSqZeroExtSeparatedFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Object correspondence for separated square-zero data

For a module over a semisimple-base trivial square-zero extension, this file
constructs its abstract separated datum, proves that the datum is generated
by the square-zero action, and reconstructs the original module up to
isomorphism.  Conversely, a generated separated datum is recovered, up to
isomorphism, from the top and module radical of its reconstructed module.

This is the object-side essential-surjectivity statement behind the standard
separated-representation correspondence.  It is independent of any choice of
quiver coordinates or classification of modules.
-/

set_option autoImplicit false

noncomputable section

open scoped RightActions
open CategoryTheory

namespace OpConjecture.TrivSqZeroExtSeparatedCorrespondence

open TrivSqZeroExtRadical
open TrivSqZeroExtSeparatedData

universe u v w

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S]

/-- The additive identification of `J` with the augmentation ideal. -/
def idealInr :
    J →+ augmentationIdeal (S := S) (J := J) where
  toFun j := ⟨TrivSqZeroExt.inr j, rfl⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    exact TrivSqZeroExt.inr_add S x y

/-- The module top, retaining its original trivial-extension scalar
structure. -/
abbrev moduleTopR
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    ModuleCat.{w} (TrivSqZeroExt S J) :=
  ModuleCat.of (TrivSqZeroExt S J)
    (X ⧸ Module.jacobson (TrivSqZeroExt S J) X)

/-- The module radical, retaining its original trivial-extension scalar
structure. -/
abbrev moduleRadicalR
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    ModuleCat.{w} (TrivSqZeroExt S J) :=
  ModuleCat.of (TrivSqZeroExt S J)
    (Module.jacobson (TrivSqZeroExt S J) X)

/-- The module top with scalars restricted to `S`. -/
abbrev moduleTopS
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) : ModuleCat.{w} S :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.inlHom S J)).obj
    (moduleTopR (S := S) (J := J) X)

/-- The module radical with scalars restricted to `S`. -/
abbrev moduleRadicalS
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) : ModuleCat.{w} S :=
  (ModuleCat.restrictScalars (TrivSqZeroExt.inlHom S J)).obj
    (moduleRadicalR (S := S) (J := J) X)

/-- The action of the square-zero ideal from the module top into the module
radical. -/
def moduleAction
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    J →+ (moduleTopS (S := S) (J := J) X →+
      moduleRadicalS (S := S) (J := J) X) :=
  (radicalActionFamily (S := S) (J := J) (X := X)).comp
    (idealInr (S := S) (J := J))

theorem moduleAction_left_smul
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    ∀ (s : S) (j : J)
      (q : moduleTopS (S := S) (J := J) X),
      moduleAction (S := S) (J := J) X (s • j) q =
        s • moduleAction (S := S) (J := J) X j q := by
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  intro s j q
  obtain ⟨x, rfl⟩ := RX.mkQ_surjective q
  apply Subtype.ext
  change (TrivSqZeroExt.inr (s • j) : TrivSqZeroExt S J) • x =
    (TrivSqZeroExt.inl s : TrivSqZeroExt S J) •
      ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x)
  rw [← mul_smul, TrivSqZeroExt.inl_mul_inr]

theorem moduleAction_right_smul
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    ∀ (j : J) (s : S)
      (q : moduleTopS (S := S) (J := J) X),
      moduleAction (S := S) (J := J) X (j <• s) q =
        moduleAction (S := S) (J := J) X j (s • q) := by
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  intro j s q
  obtain ⟨x, rfl⟩ := RX.mkQ_surjective q
  apply Subtype.ext
  change (TrivSqZeroExt.inr (j <• s) : TrivSqZeroExt S J) • x =
    (TrivSqZeroExt.inr j : TrivSqZeroExt S J) •
      ((TrivSqZeroExt.inl s : TrivSqZeroExt S J) • x)
  rw [← mul_smul, TrivSqZeroExt.inr_mul_inl]

/-- The abstract separated datum of a module. -/
abbrev moduleSeparatedData
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    SeparatedData.{u, v, w} (S := S) (J := J) :=
  { top := moduleTopS (S := S) (J := J) X
    radical := moduleRadicalS (S := S) (J := J) X
    action := moduleAction (S := S) (J := J) X
    action_left_smul := moduleAction_left_smul X
    action_right_smul := moduleAction_right_smul X }

/-- The separated datum of every module is generated: its radical is spanned
by the images of the square-zero action maps. -/
theorem moduleSeparatedData_isGenerated
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    IsGenerated (moduleSeparatedData (S := S) (J := J) X) := by
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  let TX := X ⧸ RX
  letI : Module S RX := Module.compHom RX i
  letI : Module S TX := Module.compHom TX i
  let AR : Submodule S RX := Submodule.span S
    {d : RX | ∃ (j : J) (t : TX),
      radicalAction (idealInr (S := S) (J := J) j) t = d}
  change Submodule.span S
    {d : RX | ∃ (j : J) (t : TX),
      radicalAction (idealInr (S := S) (J := J) j) t = d} = ⊤
  change AR = ⊤
  apply Submodule.eq_top_iff'.mpr
  intro y
  have hy : (y : X) ∈
      augmentationIdeal (S := S) (J := J) •
        (⊤ : Submodule (TrivSqZeroExt S J) X) := by
    have hy' := y.property
    change (y : X) ∈ Module.jacobson (TrivSqZeroExt S J) X at hy'
    rw [module_jacobson_eq_radicalPart] at hy'
    exact hy'
  have hmem : ∃ hz : (y : X) ∈
      Module.jacobson (TrivSqZeroExt S J) X,
      (⟨(y : X), hz⟩ : Module.jacobson (TrivSqZeroExt S J) X) ∈
        AR := by
    refine Submodule.smul_induction_on
      (p := fun z ↦ ∃ hz : z ∈ Module.jacobson (TrivSqZeroExt S J) X,
        (⟨z, hz⟩ : Module.jacobson (TrivSqZeroExt S J) X) ∈ AR)
      hy ?_ ?_
    · intro a ha x _
      have hz : a • x ∈ Module.jacobson (TrivSqZeroExt S J) X := by
        rw [module_jacobson_eq_radicalPart]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      refine ⟨hz, ?_⟩
      apply Submodule.subset_span (R := S)
        (s := {d : RX | ∃ (j : J) (t : TX),
          radicalAction (idealInr (S := S) (J := J) j) t = d})
      refine ⟨a.snd,
        (Module.jacobson (TrivSqZeroExt S J) X).mkQ x, ?_⟩
      apply Subtype.ext
      change (TrivSqZeroExt.inr a.snd : TrivSqZeroExt S J) • x = a • x
      rw [← eq_inr_snd_of_mem_augmentationIdeal ha]
    · rintro x z ⟨hxj, hxr⟩ ⟨hzj, hzr⟩
      have hxzj : x + z ∈ Module.jacobson (TrivSqZeroExt S J) X :=
        Submodule.add_mem _ hxj hzj
      refine ⟨hxzj, ?_⟩
      exact Submodule.add_mem AR hxr hzr
  obtain ⟨_, hmem⟩ := hmem
  exact hmem

/-- Every module over the trivial square-zero extension is isomorphic to the
module reconstructed from its abstract top, radical, and radical action. -/
def reconstructedModuleIso
    (X : ModuleCat.{w} (TrivSqZeroExt S J)) :
    reconstructedModuleCat
      (moduleSeparatedData (S := S) (J := J) X) ≅ X := by
  let i := TrivSqZeroExt.inlHom S J
  letI : Module S X := Module.compHom X i
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  let TX := X ⧸ RX
  letI : Module S RX := Module.compHom RX i
  letI : Module S TX := Module.compHom TX i
  let qX : X →ₗ[S] TX :=
    { toFun := RX.mkQ
      map_add' := fun _ _ ↦ map_add RX.mkQ _ _
      map_smul' := fun s x ↦
        RX.mkQ.map_smul (TrivSqZeroExt.inl s) x }
  let hlift := IsSemisimpleModule.lifting_property
    qX RX.mkQ_surjective (LinearMap.id (R := S) (M := TX))
  let sX := Classical.choose hlift
  have hsX := Classical.choose_spec hlift
  have hsection (t : TX) : qX (sX t) = t := by
    have h := LinearMap.congr_fun hsX t
    exact h
  let projX : X →ₗ[S] RX :=
    { toFun := fun x ↦ ⟨x - sX (qX x), by
          apply (Submodule.Quotient.mk_eq_zero RX).mp
          change qX (x - sX (qX x)) = 0
          rw [map_sub, hsection, sub_self]⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change (x + y) - sX (qX (x + y)) =
          (x - sX (qX x)) + (y - sX (qX y))
        simp only [map_add]
        abel
      map_smul' := by
        intro s x
        apply Subtype.ext
        change s • x - sX (qX (s • x)) =
          s • (x - sX (qX x))
        simp only [map_smul, smul_sub] }
  have haction (j : J) (t : TX) :
      (show X from (moduleAction (S := S) (J := J) X j t).val) =
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • sX t := by
    calc
      (show X from (moduleAction (S := S) (J := J) X j t).val) =
          (show X from (moduleAction (S := S) (J := J) X j
            (qX (sX t))).val) := by rw [hsection]
      _ = (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • sX t := by
        change ((radicalAction (idealInr (S := S) (J := J) j)
          (qX (sX t))).val : X) = _
        simpa [qX, idealInr] using congrArg Subtype.val
          (radicalAction_mk
            (r := idealInr (S := S) (J := J) j) (sX t))
  have hinr_radical (j : J) (d : RX) :
      (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • d.val = 0 :=
    augmentation_smul_module_jacobson_eq_zero
      (TrivSqZeroExt.inr j)
      ((mem_augmentationIdeal_iff
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J)).mpr rfl)
      d.val d.property
  have hs_smul (s : S) (x : X) :
      s • x = (TrivSqZeroExt.inl s : TrivSqZeroExt S J) • x := rfl
  have hs_smul_radical (s : S) (d : RX) :
      ((s • d : RX) : X) =
        (TrivSqZeroExt.inl s : TrivSqZeroExt S J) • (d : X) := rfl
  let D := moduleSeparatedData (S := S) (J := J) X
  let topId : D.top ≃ₗ[S] TX :=
    { toFun := fun t ↦ t
      invFun := fun t ↦ t
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let radId : D.radical ≃ₗ[S] RX :=
    { toFun := fun d ↦ ⟨d.val, d.property⟩
      invFun := fun d ↦ ⟨d.val, d.property⟩
      left_inv := fun d ↦ by cases d; rfl
      right_inv := fun d ↦ by cases d; rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hactionD (j : J) (t : D.top) :
      ((radId (D.action j t) : RX) : X) =
        (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • sX (topId t) := by
    exact haction j (topId t)
  letI : SMul (TrivSqZeroExt S J) (Reconstructed D) :=
    reconstructedSMul D
  letI : Module (TrivSqZeroExt S J) (Reconstructed D) :=
    reconstructedModule D
  let fLin : @LinearMap (TrivSqZeroExt S J) (TrivSqZeroExt S J)
      _ _ (RingHom.id (TrivSqZeroExt S J)) (Reconstructed D) X
      _ _ (reconstructedModule D) X.isModule :=
    { toFun := fun z ↦ sX (topId z.1) + (radId z.2 : RX)
      map_add' := by
        intro x y
        change sX (topId (x.1 + y.1)) +
            ((radId (x.2 + y.2) : RX) : X) =
          (sX (topId x.1) + (radId x.2 : RX)) +
            (sX (topId y.1) + (radId y.2 : RX))
        rw [map_add, map_add, map_add]
        simp only [Submodule.coe_add]
        abel
      map_smul' := by
        intro r z
        change sX (topId (r.fst • z.1)) +
          ((radId (r.fst • z.2 + D.action r.snd z.1) : RX) : X) =
          r • (sX (topId z.1) + (radId z.2 : RX))
        rw [topId.map_smul, sX.map_smul, radId.map_add,
          radId.map_smul]
        simp only [Submodule.coe_add]
        rw [hs_smul, hs_smul_radical]
        rw [hactionD]
        conv_rhs =>
          rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq r]
        rw [add_smul, smul_add, smul_add, hinr_radical, add_zero]
        abel }
  let f : reconstructedModuleCat D ⟶ X := ModuleCat.ofHom fLin
  apply LinearEquiv.toModuleIso
  apply LinearEquiv.ofBijective f.hom
  constructor
  · intro x y hxy
    change fLin x = fLin y at hxy
    dsimp only [fLin] at hxy
    change sX (topId x.1) + ((radId x.2 : RX) : X) =
      sX (topId y.1) + ((radId y.2 : RX) : X) at hxy
    have hq := congrArg qX hxy
    change qX (sX (topId x.1) + (radId x.2 : RX)) =
      qX (sX (topId y.1) + (radId y.2 : RX)) at hq
    rw [map_add, map_add, hsection, hsection] at hq
    have hxrad : qX ((radId x.2 : RX) : X) = 0 :=
      (Submodule.Quotient.mk_eq_zero RX).mpr (radId x.2).property
    have hyrad : qX ((radId y.2 : RX) : X) = 0 :=
      (Submodule.Quotient.mk_eq_zero RX).mpr (radId y.2).property
    rw [hxrad, hyrad, add_zero, add_zero] at hq
    apply Prod.ext
    · exact topId.injective hq
    · apply Subtype.ext
      have htop : x.1 = y.1 := topId.injective hq
      rw [htop] at hxy
      have hrad : radId x.2 = radId y.2 :=
        Subtype.ext (add_left_cancel hxy)
      exact congrArg Subtype.val (radId.injective hrad)
  · intro x
    refine ⟨(topId.symm (qX x), radId.symm (projX x)), ?_⟩
    dsimp only [f, fLin, ModuleCat.ofHom]
    change sX (topId (topId.symm (qX x))) +
      (radId (radId.symm (projX x)) : RX) = x
    rw [topId.apply_symm_apply, radId.apply_symm_apply]
    change sX (qX x) + (x - sX (qX x)) = x
    abel

/-- The actual module radical of a generated reconstruction is linearly
equivalent to its declared radical. -/
def reconstructedRadicalEquiv
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsGenerated D) :
    (moduleSeparatedData (S := S) (J := J)
      (reconstructedModuleCat D)).radical ≃ₗ[S] D.radical where
  toFun x := (show Reconstructed D from x.val).2
  invFun d := ⟨(0, d), by
    change (0, d) ∈
      Module.jacobson (TrivSqZeroExt S J) (Reconstructed D)
    rw [module_jacobson_eq_declaredRadical_of_generated D hD]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    let z : Reconstructed D := x.val
    have hzj : z ∈
        Module.jacobson (TrivSqZeroExt S J) (Reconstructed D) :=
      x.property
    have hzd : z ∈ declaredRadical D := by
      rw [← module_jacobson_eq_declaredRadical_of_generated D hD]
      exact hzj
    apply Prod.ext
    · change (0 : D.top) = z.1
      exact hzd.symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s x := by
    change ((TrivSqZeroExt.inl s : TrivSqZeroExt S J) •
      (show Reconstructed D from x.val)).2 =
        s • (show Reconstructed D from x.val).2
    change s • (show Reconstructed D from x.val).2 +
      D.action 0 (show Reconstructed D from x.val).1 =
        s • (show Reconstructed D from x.val).2
    simp

/-- The actual module top of a generated reconstruction is linearly
equivalent to its declared top. -/
def reconstructedTopEquiv
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsGenerated D) :
    (moduleSeparatedData (S := S) (J := J)
      (reconstructedModuleCat D)).top ≃ₗ[S] D.top := by
  let i := TrivSqZeroExt.inlHom S J
  let X := Reconstructed D
  let RX := Module.jacobson (TrivSqZeroExt S J) X
  letI : Module S X := Module.compHom X i
  letI : Module S (X ⧸ RX) := Module.compHom (X ⧸ RX) i
  let fstMap : X →ₗ[S] D.top :=
    { toFun := Prod.fst
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro s x
        change ((TrivSqZeroExt.inl s : TrivSqZeroExt S J) • x).1 =
          s • x.1
        rfl }
  have hzero : ∀ x : X, x ∈ RX → fstMap x = 0 := by
    intro x hx
    change x.1 = 0
    have hx' : x ∈ declaredRadical D := by
      rw [← module_jacobson_eq_declaredRadical_of_generated D hD]
      exact hx
    exact hx'
  let fAdd : (X ⧸ RX) →+ D.top :=
    QuotientAddGroup.lift RX.toAddSubgroup fstMap.toAddHom hzero
  let f : (X ⧸ RX) →ₗ[S] D.top :=
    { toFun := fAdd
      map_add' := fAdd.map_add
      map_smul' := by
        intro s q
        obtain ⟨x, rfl⟩ := RX.mkQ_surjective q
        change (s • x).1 = s • x.1
        rfl }
  let g : D.top →ₗ[S] (X ⧸ RX) :=
    { toFun := fun t ↦ RX.mkQ (t, 0)
      map_add' := by
        intro x y
        simpa using map_add RX.mkQ (x, 0) (y, 0)
      map_smul' := by
        intro s t
        change RX.mkQ (s • t, 0) =
          (TrivSqZeroExt.inl s : TrivSqZeroExt S J) • RX.mkQ (t, 0)
        rw [← RX.mkQ.map_smul]
        change RX.mkQ (s • t, 0) =
          RX.mkQ (s • t, s • (0 : D.radical) + D.action 0 t)
        simp }
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        obtain ⟨x, rfl⟩ := RX.mkQ_surjective q
        apply (Submodule.Quotient.eq RX).mpr
        change (f (RX.mkQ x), 0) - x ∈
          Module.jacobson (TrivSqZeroExt S J) (Reconstructed D)
        rw [module_jacobson_eq_declaredRadical_of_generated D hD]
        change f (RX.mkQ x) - x.1 = 0
        change x.1 - x.1 = 0
        exact sub_self x.1
      right_inv := by
        intro t
        rfl
      map_add' := f.map_add
      map_smul' := f.map_smul }

/-- A generated separated datum is recovered, as separated data, from the
actual top and radical of its reconstructed module. -/
def reconstructedSeparatedDataIso
    (D : SeparatedData.{u, v, w} (S := S) (J := J))
    (hD : IsGenerated D) :
    moduleSeparatedData (S := S) (J := J) (reconstructedModuleCat D) ≅ D := by
  let eTop := reconstructedTopEquiv (S := S) (J := J) D hD
  let eRad := reconstructedRadicalEquiv (S := S) (J := J) D hD
  refine
    { hom := ⟨(eTop.toLinearMap, eRad.toLinearMap), ?_⟩
      inv := ⟨(eTop.symm.toLinearMap, eRad.symm.toLinearMap), ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro j q
    let RX := Module.jacobson (TrivSqZeroExt S J) (Reconstructed D)
    obtain ⟨x, rfl⟩ := RX.mkQ_surjective q
    change ((TrivSqZeroExt.inr j : TrivSqZeroExt S J) • x).2 =
      D.action j x.1
    change (0 : S) • x.2 + D.action j x.1 = D.action j x.1
    simp
  · intro j t
    apply Subtype.ext
    change (0, D.action j t) =
      (TrivSqZeroExt.inr j : TrivSqZeroExt S J) • (t, 0)
    change (0, D.action j t) =
      ((0 : S) • t, (0 : S) • (0 : D.radical) + D.action j t)
    simp
  · apply Subtype.ext
    apply Prod.ext
    · ext x
      exact eTop.symm_apply_apply x
    · ext x
      exact eRad.symm_apply_apply x
  · apply Subtype.ext
    apply Prod.ext
    · ext x
      exact eTop.apply_symm_apply x
    · ext x
      exact eRad.apply_symm_apply x

end OpConjecture.TrivSqZeroExtSeparatedCorrespondence
