import OpConjecture.RepresentationTheory.ExtClassReflection
import OpConjecture.RepresentationTheory.ExtMatrixBridge
import OpConjecture.RepresentationTheory.TwoSourceRankCore
import OpConjecture.RepresentationTheory.NoParallelExtOne
import OpConjecture.RepresentationTheory.LoewyTwoGabrielClassification
import OpConjecture.RepresentationTheory.LevelThreeExhaustive
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The two-source, one-target Ext bridge

This file scalarizes a radical extension whose semisimple top has two
isotypic blocks and whose radical is one simple block.  Yoneda compatibility
and Fitting reflection reduce its multiplicities to the elementary
two-source rank core.  In the paper's finite-skeleton setting this discharges
the one-nonsimple length-three control.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.YonedaExtReflection

universe w v u

variable {K : Type u} [Field K]
  {C : Type v} [Category.{w} C] [Abelian C] [Linear K C]
  [HasFiniteBiproducts C] [HasExt C]

/-! ## A heterogeneous two-source `Ext` matrix -/

/-- Restrict an extension along the left inclusion into a binary biproduct. -/
def extBiprodLeft
    {X X' Y : C} (xi : Ext (X ⊞ X') Y 1) : Ext X Y 1 :=
  (Ext.mk₀ biprod.inl).comp xi (zero_add 1)

/-- Restrict an extension along the right inclusion into a binary biproduct. -/
def extBiprodRight
    {X X' Y : C} (xi : Ext (X ⊞ X') Y 1) : Ext X' Y 1 :=
  (Ext.mk₀ biprod.inr).comp xi (zero_add 1)

omit [HasFiniteBiproducts C] in
theorem ext_eq_of_extBiprodLeft_right_eq
    {X X' Y : C} {xi eta : Ext (X ⊞ X') Y 1}
    (hleft : extBiprodLeft xi = extBiprodLeft eta)
    (hright : extBiprodRight xi = extBiprodRight eta) :
    xi = eta := by
  apply Ext.biprodAddEquiv.injective
  exact Prod.ext hleft hright

/-- A block diagonal categorical endomorphism on a binary biproduct. -/
def blockDiagonalBiprodEnd
    {X X' : C} (a : X ⟶ X) (b : X' ⟶ X') :
    (X ⊞ X') ⟶ (X ⊞ X') :=
  biprod.map a b

omit [HasFiniteBiproducts C] [HasExt C] in
theorem blockDiagonalBiprodEnd_comp
    {X X' : C} (a a' : X ⟶ X) (b b' : X' ⟶ X') :
    blockDiagonalBiprodEnd a b ≫ blockDiagonalBiprodEnd a' b' =
      blockDiagonalBiprodEnd (a ≫ a') (b ≫ b') := by
  ext <;> simp [blockDiagonalBiprodEnd]

omit [HasFiniteBiproducts C] [HasExt C] in
theorem blockDiagonalBiprodEnd_zero
    {X X' : C} :
    blockDiagonalBiprodEnd (0 : X ⟶ X) (0 : X' ⟶ X') = 0 := by
  ext <;> simp [blockDiagonalBiprodEnd]

omit [HasFiniteBiproducts C] [HasExt C] in
theorem blockDiagonalBiprodEnd_id
    {X X' : C} :
    blockDiagonalBiprodEnd (𝟙 X) (𝟙 X') = 𝟙 _ := by
  ext <;> simp [blockDiagonalBiprodEnd]

omit [HasFiniteBiproducts C] [HasExt C] in
theorem blockDiagonalBiprodEnd_eq_zero_iff
    {X X' : C} (a : X ⟶ X) (b : X' ⟶ X') :
    blockDiagonalBiprodEnd a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · simpa [blockDiagonalBiprodEnd] using
        congrArg (fun z ↦ biprod.inl ≫ z ≫ biprod.fst) h
    · simpa [blockDiagonalBiprodEnd] using
        congrArg (fun z ↦ biprod.inr ≫ z ≫ biprod.snd) h
  · rintro ⟨rfl, rfl⟩
    exact blockDiagonalBiprodEnd_zero

omit [HasFiniteBiproducts C] [HasExt C] in
theorem blockDiagonalBiprodEnd_eq_id_iff
    {X X' : C} (a : X ⟶ X) (b : X' ⟶ X') :
    blockDiagonalBiprodEnd a b = 𝟙 _ ↔ a = 𝟙 _ ∧ b = 𝟙 _ := by
  constructor
  · intro h
    constructor
    · simpa [blockDiagonalBiprodEnd] using
        congrArg (fun z ↦ biprod.inl ≫ z ≫ biprod.fst) h
    · simpa [blockDiagonalBiprodEnd] using
        congrArg (fun z ↦ biprod.inr ≫ z ≫ biprod.snd) h
  · rintro ⟨rfl, rfl⟩
    exact blockDiagonalBiprodEnd_id

theorem ext_compatibility_of_two_scalarized_matrix_commute
    {I J : Type} [Fintype I] [Fintype J]
    (X X' Y : C)
    (ell : Ext X Y 1 →ₗ[K] K) (hell : Function.Injective ell)
    (ell' : Ext X' Y 1 →ₗ[K] K) (hell' : Function.Injective ell')
    (xi :
      Ext
        ((⨁ fun _ : I ↦ X) ⊞ (⨁ fun _ : J ↦ X'))
        (⨁ fun _ : Unit ↦ Y) 1)
    (P : Matrix I I K) (Q : Matrix J J K)
    (R : Matrix Unit Unit K)
    (hleft :
      R * scalarizedExtMatrix X Y ell (extBiprodLeft xi) =
        scalarizedExtMatrix X Y ell (extBiprodLeft xi) * P)
    (hright :
      R * scalarizedExtMatrix X' Y ell' (extBiprodRight xi) =
        scalarizedExtMatrix X' Y ell' (extBiprodRight xi) * Q) :
    xi.comp
          (Ext.mk₀ (scalarBiproductEnd Y R)) (add_zero 1) =
      (Ext.mk₀
          (blockDiagonalBiprodEnd
            (scalarBiproductEnd X P)
            (scalarBiproductEnd X' Q))).comp
        xi (zero_add 1) := by
  apply ext_eq_of_extBiprodLeft_right_eq
  · change
      extBiprodLeft
          (xi.comp (Ext.mk₀ (scalarBiproductEnd Y R)) (add_zero 1)) =
        extBiprodLeft
          ((Ext.mk₀
              (blockDiagonalBiprodEnd
                (scalarBiproductEnd X P)
                (scalarBiproductEnd X' Q))).comp
            xi (zero_add 1))
    calc
      _ = (extBiprodLeft xi).comp
          (Ext.mk₀ (scalarBiproductEnd Y R)) (add_zero 1) := by
        exact
          (Ext.comp_assoc_of_third_deg_zero
            (Ext.mk₀ biprod.inl) xi
            (Ext.mk₀ (scalarBiproductEnd Y R)) (zero_add 1)).symm
      _ = (Ext.mk₀ (scalarBiproductEnd X P)).comp
          (extBiprodLeft xi) (zero_add 1) :=
        ext_compatibility_of_scalarized_matrix_commute
          X Y ell hell (extBiprodLeft xi) P R hleft
      _ = _ := by
        unfold extBiprodLeft
        rw [← Ext.comp_assoc_of_second_deg_zero,
          Ext.mk₀_comp_mk₀]
        simp [blockDiagonalBiprodEnd]
  · change
      extBiprodRight
          (xi.comp (Ext.mk₀ (scalarBiproductEnd Y R)) (add_zero 1)) =
        extBiprodRight
          ((Ext.mk₀
              (blockDiagonalBiprodEnd
                (scalarBiproductEnd X P)
                (scalarBiproductEnd X' Q))).comp
            xi (zero_add 1))
    calc
      _ = (extBiprodRight xi).comp
          (Ext.mk₀ (scalarBiproductEnd Y R)) (add_zero 1) := by
        exact
          (Ext.comp_assoc_of_third_deg_zero
            (Ext.mk₀ biprod.inr) xi
            (Ext.mk₀ (scalarBiproductEnd Y R)) (zero_add 1)).symm
      _ = (Ext.mk₀ (scalarBiproductEnd X' Q)).comp
          (extBiprodRight xi) (zero_add 1) :=
        ext_compatibility_of_scalarized_matrix_commute
          X' Y ell' hell' (extBiprodRight xi) Q R hright
      _ = _ := by
        unfold extBiprodRight
        rw [← Ext.comp_assoc_of_second_deg_zero,
          Ext.mk₀_comp_mk₀]
        simp [blockDiagonalBiprodEnd]

/--
The two scalarized rows of an extension with heterogeneous isotypic source
blocks and one isotypic target block form an idempotent-indecomposable
two-source representation whenever compatible endpoint idempotents are
trivial.
-/
theorem twoSource_scalarizedExtLinearMaps_isIdempotentIndecomposable
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X X' Y : C) (hX : 𝟙 X ≠ 0) (hX' : 𝟙 X' ≠ 0)
    (hY : 𝟙 Y ≠ 0)
    (ell : Ext X Y 1 →ₗ[K] K) (hell : Function.Injective ell)
    (ell' : Ext X' Y 1 →ₗ[K] K) (hell' : Function.Injective ell')
    (xi :
      Ext
        ((⨁ fun _ : I ↦ X) ⊞ (⨁ fun _ : J ↦ X'))
        (⨁ fun _ : Unit ↦ Y) 1)
    (hendpoint :
      ∀ (a₁ :
          (⨁ fun _ : Unit ↦ Y) ⟶ (⨁ fun _ : Unit ↦ Y))
        (a₃ :
          ((⨁ fun _ : I ↦ X) ⊞ (⨁ fun _ : J ↦ X')) ⟶
            ((⨁ fun _ : I ↦ X) ⊞ (⨁ fun _ : J ↦ X'))),
        a₁ ≫ a₁ = a₁ →
        a₃ ≫ a₃ = a₃ →
        xi.comp (Ext.mk₀ a₁) (add_zero 1) =
          (Ext.mk₀ a₃).comp xi (zero_add 1) →
        (a₁ = 0 ∧ a₃ = 0) ∨
          (a₁ = 𝟙 _ ∧ a₃ = 𝟙 _)) :
    LoewyTwoRankCore.IsTwoSourceIdempotentIndecomposable
      (scalarizedExtLinearMap X Y ell (extBiprodLeft xi))
      (scalarizedExtLinearMap X' Y ell' (extBiprodRight xi)) := by
  classical
  intro p q r hp hq hr hrf hrg
  let P : Matrix I I K := LinearMap.toMatrix' p
  let Q : Matrix J J K := LinearMap.toMatrix' q
  let R : Matrix Unit Unit K := LinearMap.toMatrix' r
  have hP : P * P = P := by
    simpa only [P, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hp
  have hQ : Q * Q = Q := by
    simpa only [Q, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hq
  have hR : R * R = R := by
    simpa only [R, LinearMap.toMatrix'_comp] using
      congrArg LinearMap.toMatrix' hr
  have hleft :
      R * scalarizedExtMatrix X Y ell (extBiprodLeft xi) =
        scalarizedExtMatrix X Y ell (extBiprodLeft xi) * P := by
    simpa only [R, P, scalarizedExtLinearMap,
      LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
      congrArg LinearMap.toMatrix' hrf
  have hright :
      R * scalarizedExtMatrix X' Y ell' (extBiprodRight xi) =
        scalarizedExtMatrix X' Y ell' (extBiprodRight xi) * Q := by
    simpa only [R, Q, scalarizedExtLinearMap,
      LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using
      congrArg LinearMap.toMatrix' hrg
  have hPend :
      scalarBiproductEnd X P ≫ scalarBiproductEnd X P =
        scalarBiproductEnd X P := by
    rw [scalarBiproductEnd_comp, hP]
  have hQend :
      scalarBiproductEnd X' Q ≫ scalarBiproductEnd X' Q =
        scalarBiproductEnd X' Q := by
    rw [scalarBiproductEnd_comp, hQ]
  have hRend :
      scalarBiproductEnd Y R ≫ scalarBiproductEnd Y R =
        scalarBiproductEnd Y R := by
    rw [scalarBiproductEnd_comp, hR]
  have hblock :
      blockDiagonalBiprodEnd
          (scalarBiproductEnd X P) (scalarBiproductEnd X' Q) ≫
        blockDiagonalBiprodEnd
          (scalarBiproductEnd X P) (scalarBiproductEnd X' Q) =
      blockDiagonalBiprodEnd
          (scalarBiproductEnd X P) (scalarBiproductEnd X' Q) := by
    rw [blockDiagonalBiprodEnd_comp, hPend, hQend]
  have hext :=
    ext_compatibility_of_two_scalarized_matrix_commute
      X X' Y ell hell ell' hell' xi P Q R hleft hright
  rcases hendpoint
      (scalarBiproductEnd Y R)
      (blockDiagonalBiprodEnd
        (scalarBiproductEnd X P) (scalarBiproductEnd X' Q))
      hRend hblock hext with hzero | hone
  · left
    have hRzero : R = 0 :=
      (scalarBiproductEnd_eq_zero_iff Y hY R).mp hzero.1
    have hblocks :=
      (blockDiagonalBiprodEnd_eq_zero_iff
        (scalarBiproductEnd X P) (scalarBiproductEnd X' Q)).mp hzero.2
    have hPzero : P = 0 :=
      (scalarBiproductEnd_eq_zero_iff X hX P).mp hblocks.1
    have hQzero : Q = 0 :=
      (scalarBiproductEnd_eq_zero_iff X' hX' Q).mp hblocks.2
    exact ⟨by
      apply LinearMap.toMatrix'.injective
      simpa only [P, map_zero] using hPzero, by
      apply LinearMap.toMatrix'.injective
      simpa only [Q, map_zero] using hQzero, by
      apply LinearMap.toMatrix'.injective
      simpa only [R, map_zero] using hRzero⟩
  · right
    have hRone : R = 1 :=
      (scalarBiproductEnd_eq_id_iff Y hY R).mp hone.1
    have hblocks :=
      (blockDiagonalBiprodEnd_eq_id_iff
        (scalarBiproductEnd X P) (scalarBiproductEnd X' Q)).mp hone.2
    have hPone : P = 1 :=
      (scalarBiproductEnd_eq_id_iff X hX P).mp hblocks.1
    have hQone : Q = 1 :=
      (scalarBiproductEnd_eq_id_iff X' hX' Q).mp hblocks.2
    exact ⟨by
      apply LinearMap.toMatrix'.injective
      simpa only [P, LinearMap.toMatrix'_id] using hPone, by
      apply LinearMap.toMatrix'.injective
      simpa only [Q, LinearMap.toMatrix'_id] using hQone, by
      apply LinearMap.toMatrix'.injective
      simpa only [R, LinearMap.toMatrix'_id] using hRone⟩

/-!
## Reflection from an indecomposable middle module
-/

universe x

/--
Short-exact-sequence wrapper for the heterogeneous two-source matrix.
Fitting reflection on the indecomposable middle term supplies exactly the
endpoint-idempotent condition consumed above.
-/
theorem shortExact_twoSource_scalarizedExtLinearMaps_isIdempotentIndecomposable
    {R₀ : Type x} [Ring R₀] [Algebra K R₀] [Small.{v} R₀]
    {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (X X' Y M : ModuleCat.{v} R₀)
    (hX : 𝟙 X ≠ 0) (hX' : 𝟙 X' ≠ 0) (hY : 𝟙 Y ≠ 0)
    (f : (⨁ fun _ : Unit ↦ Y) ⟶ M)
    (g : M ⟶ ((⨁ fun _ : I ↦ X) ⊞ (⨁ fun _ : J ↦ X')))
    (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [IsNoetherian R₀ M] [IsArtinian R₀ M]
    (hM : OpConjecture.Foundation.IsIndecomposableModule R₀ M)
    (ell : Ext X Y 1 →ₗ[K] K) (hell : Function.Injective ell)
    (ell' : Ext X' Y 1 →ₗ[K] K) (hell' : Function.Injective ell') :
    LoewyTwoRankCore.IsTwoSourceIdempotentIndecomposable
      (scalarizedExtLinearMap X Y ell
        (extBiprodLeft hS.extClass))
      (scalarizedExtLinearMap X' Y ell'
        (extBiprodRight hS.extClass)) := by
  apply twoSource_scalarizedExtLinearMaps_isIdempotentIndecomposable
    X X' Y hX hX' hY ell hell ell' hell' hS.extClass
  intro a₁ a₃ ha₁ ha₃ hcompat
  exact endpoint_idempotents_trivial_of_extClass_compatibility
    hS hM a₁ a₃ ha₁ ha₃ hcompat

end OpConjecture.YonedaExtReflection

namespace OpConjecture.TwoTypeSemisimple

universe uR uM uS uT

variable {R : Type uR} [Ring R]
  {M : Type uM} [AddCommGroup M] [Module R M]
  {S : Type uS} [AddCommGroup S] [Module R S]
  {T : Type uT} [AddCommGroup T] [Module R T]

/-- A finite semisimple module all of whose simple submodules have one of
two nonisomorphic types splits as a finite power of the first type times a
finite power of the second. -/
theorem exists_twoTypeDecomposition
    [IsSemisimpleModule R M] [Module.Finite R M]
    [IsSimpleModule R S] [IsSimpleModule R T]
    (htypes :
      ∀ (L : Submodule R M),
        [IsSimpleModule R L] →
        Nonempty (L ≃ₗ[R] S) ∨ Nonempty (L ≃ₗ[R] T)) :
    ∃ (n m : ℕ),
      Nonempty (M ≃ₗ[R] ((Fin n → S) × (Fin m → T))) := by
  let C : Submodule R M := isotypicComponent R M S
  obtain ⟨N, hCN⟩ := exists_isCompl C
  have hCisotypic : IsIsotypicOfType R C S :=
    IsIsotypicOfType.isotypicComponent R M S
  have hNisotypic : IsIsotypicOfType R N T := by
    rw [isIsotypicOfType_submodule_iff]
    intro L hLN hLsimple
    rcases htypes L with hLS | hLT
    · have hLC : L ≤ C := by
        exact le_sSup hLS
      have hLbot : L ≤ ⊥ := by
        rw [← hCN.inf_eq_bot]
        exact le_inf hLC hLN
      have hLeq : L = ⊥ := bot_unique hLbot
      have hLne : L ≠ ⊥ :=
        (Submodule.nontrivial_iff_ne_bot).mp
          (IsSimpleModule.nontrivial R L)
      exact False.elim (hLne hLeq)
    · exact hLT
  obtain ⟨n, ⟨eC⟩⟩ := hCisotypic.linearEquiv_fun
  obtain ⟨m, ⟨eN⟩⟩ := hNisotypic.linearEquiv_fun
  refine ⟨n, m, ⟨?_⟩⟩
  exact
    (C.prodEquivOfIsCompl N hCN).symm.trans
      (eC.prodCongr eN)

end OpConjecture.TwoTypeSemisimple

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v}
  (sigma : IndecomposableSkeleton.{u, v, w} R iota)

/-- Every simple quotient of a representative occurs as a simple direct
summand type of its semisimple top. -/
theorem exists_simpleTopSubmodule_linearEquiv_simpleQuotient
    {j : iota} (Q : sigma.SimpleQuotient j) :
    ∃ L : Submodule R (sigma.moduleTop j),
      IsSimpleModule R L ∧
        Nonempty (L ≃ₗ[R] sigma.obj Q.index) := by
  letI : IsSimpleModule R (sigma.obj Q.index) :=
    (simple_iff_isSimpleModule_fg (sigma.obj Q.index)).mp Q.simple
  letI : IsSemisimpleModule R (sigma.obj Q.index) := by
    infer_instance
  letI : IsSemisimpleModule R (sigma.moduleTop j) :=
    sigma.moduleTop_isSemisimple j
  letI : Epi Q.map := Q.epi
  have hQsurj : Function.Surjective Q.map.hom.hom :=
    (fg_epi_iff_surjective Q.map).mp inferInstance
  have hradKer :
      sigma.moduleRadical j ≤ LinearMap.ker Q.map.hom.hom := by
    exact
      IsSemisimpleModule.jacobson_le_ker
        R R (sigma.obj j) (sigma.obj Q.index) Q.map.hom.hom
  let qTop :
      sigma.moduleTop j →ₗ[R] sigma.obj Q.index :=
    (sigma.moduleRadical j).liftQ Q.map.hom.hom hradKer
  have hqTopSurj : Function.Surjective qTop := by
    intro y
    obtain ⟨x, hx⟩ := hQsurj y
    refine ⟨(sigma.moduleRadical j).mkQ x, ?_⟩
    simpa [qTop, Submodule.liftQ_apply] using hx
  obtain ⟨L, ⟨eL⟩⟩ :=
    IsSemisimpleModule.exists_submodule_linearEquiv_quotient
      (LinearMap.ker qTop)
  let e : L ≃ₗ[R] sigma.obj Q.index :=
    eL.trans (qTop.quotKerEquivOfSurjective hqTopSurj)
  have hLsimple : IsSimpleModule R L :=
    IsSimpleModule.congr e
  exact ⟨L, hLsimple, ⟨e⟩⟩

/-- If all simple quotients of `j` have one of two displayed skeleton
indices, then every simple submodule of the semisimple top has one of those
two module types. -/
theorem simpleTopSubmodule_type_eq_left_or_right
    {j s t : iota}
    (hquotients :
      ∀ Q : sigma.SimpleQuotient j,
        Q.index = s ∨ Q.index = t)
    (L : Submodule R (sigma.moduleTop j))
    (hL : IsSimpleModule R L) :
    Nonempty (L ≃ₗ[R] sigma.obj s) ∨
      Nonempty (L ≃ₗ[R] sigma.obj t) := by
  letI : IsSemisimpleModule R (sigma.moduleTop j) :=
    sigma.moduleTop_isSemisimple j
  letI : IsSimpleModule R L := hL
  obtain ⟨c, hLc⟩ := exists_isCompl L
  let p : sigma.moduleTop j →ₗ[R] L :=
    Submodule.projectionOnto L c hLc
  have hp : Function.Surjective p :=
    Submodule.projectionOnto_surjective hLc
  letI : Module.Finite R L :=
    Module.Finite.of_surjective p hp
  let ML : FGModuleCat.{w} R := FGModuleCat.of R L
  have hMLindec : OpConjecture.Foundation.IsIndecomposableModule R ML :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨l, ⟨e⟩⟩ := sigma.complete ML hMLindec
  let q : sigma.obj j →ₗ[R] sigma.moduleTop j :=
    (sigma.moduleRadical j).mkQ
  let f : sigma.obj j ⟶ sigma.obj l :=
    FGModuleCat.ofHom (e.hom.hom.hom.comp (p.comp q))
  have hfSurj : Function.Surjective f.hom.hom := by
    intro y
    obtain ⟨z, rfl⟩ := (FGModuleCat.isoToLinearEquiv e).surjective y
    obtain ⟨t, rfl⟩ := hp z
    obtain ⟨a, rfl⟩ := (sigma.moduleRadical j).mkQ_surjective t
    exact ⟨a, rfl⟩
  letI : Epi f :=
    (fg_epi_iff_surjective f).mpr hfSurj
  have hMLsimple : Simple ML :=
    (simple_iff_isSimpleModule_fg ML).mpr hL
  have hlsimple : Simple (sigma.obj l) :=
    (Simple.iff_of_iso e).mp hMLsimple
  let Q : sigma.SimpleQuotient j := {
    index := l
    simple := hlsimple
    map := f
    epi := inferInstance }
  rcases hquotients Q with hls | hlt
  · change l = s at hls
    subst l
    exact Or.inl ⟨FGModuleCat.isoToLinearEquiv e⟩
  · change l = t at hlt
    subst l
    exact Or.inr ⟨FGModuleCat.isoToLinearEquiv e⟩

end OpConjecture.IndecomposableSkeleton

namespace OpConjecture.YonedaTwoSourceReduction

universe x

variable {A : Type x} [Ring A]
  {iota : Type x} [IsNoetherianRing Aᵐᵒᵖ]
  (sigma :
    _root_.OpConjecture.IndecomposableSkeleton.{x, x, x}
      Aᵐᵒᵖ iota)
  (K : Type x) [Field K]
  [Algebra K A] [FiniteDimensional K A]

open LoewyTwoRankCore

/-!
`topMultiplicityBounds_of_twoTypeDecomposition` is the module-facing
endpoint.  The hypotheses exhibit the radical as one simple skeleton object
and the top as two finite isotypic blocks.  No-parallel `Ext¹` scalarizes the
two rows, Yoneda reflection transfers indecomposability of the module to the
two-source representation, and the rank core bounds both multiplicities.
-/
theorem topMultiplicityBounds_of_twoTypeDecomposition
    (hnoParallel : NoParallelExtOne sigma K)
    {j s t r : iota}
    (hs : Simple (sigma.obj s))
    (ht : Simple (sigma.obj t))
    (hr : Simple (sigma.obj r))
    (eRadical :
      (sigma.obj r) ≃ₗ[Aᵐᵒᵖ] sigma.moduleRadical j)
    (n m : ℕ)
    (eTop :
      ((Fin n → sigma.obj s) × (Fin m → sigma.obj t))
        ≃ₗ[Aᵐᵒᵖ] sigma.moduleTop j) :
    n ≤ 1 ∧ m ≤ 1 := by
  let leftIso :
      ((⨁ fun _ : Fin n ↦ (sigma.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (Fin n → sigma.obj s) :=
    ModuleCat.biproductIsoPi
      (fun _ : Fin n ↦ (sigma.obj s).obj)
  let rightIso :
      ((⨁ fun _ : Fin m ↦ (sigma.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (Fin m → sigma.obj t) :=
    ModuleCat.biproductIsoPi
      (fun _ : Fin m ↦ (sigma.obj t).obj)
  let topIso :
      (((⨁ fun _ : Fin n ↦ (sigma.obj s).obj) ⊞
          (⨁ fun _ : Fin m ↦ (sigma.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (sigma.moduleTop j) :=
    biprod.mapIso leftIso rightIso ≪≫
      ModuleCat.biprodIsoProd
        (ModuleCat.of Aᵐᵒᵖ (Fin n → sigma.obj s))
        (ModuleCat.of Aᵐᵒᵖ (Fin m → sigma.obj t)) ≪≫
      eTop.toModuleIso
  let radicalIso :
      ((⨁ fun _ : Unit ↦ (sigma.obj r).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (sigma.moduleRadical j) :=
    ModuleCat.biproductIsoPi
        (fun _ : Unit ↦ (sigma.obj r).obj) ≪≫
      (LinearEquiv.funUnique Unit Aᵐᵒᵖ (sigma.obj r)).toModuleIso ≪≫
      eRadical.toModuleIso
  let eRadical :
      ((⨁ fun _ : Unit ↦ (sigma.obj r).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle :
      (sigma.obj j) ≃ₗ[Aᵐᵒᵖ] (sigma.obj j) :=
    LinearEquiv.refl Aᵐᵒᵖ (sigma.obj j)
  let eTop :
      ((((⨁ fun _ : Fin n ↦ (sigma.obj s).obj) ⊞
          (⨁ fun _ : Fin m ↦ (sigma.obj t).obj)) :
          ModuleCat.{x} Aᵐᵒᵖ)) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion :
      sigma.moduleRadical j →ₗ[Aᵐᵒᵖ] sigma.obj j :=
    (sigma.moduleRadical j).subtype
  let topProjection :
      sigma.obj j →ₗ[Aᵐᵒᵖ] sigma.moduleTop j :=
    (sigma.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (sigma.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{x} Aᵐᵒᵖ) :=
    ModuleCat.shortComplexOfConj
      eRadical eMiddle eTop radicalInclusion topProjection
      hexact.linearMap_comp_eq_zero
  have hSC : SC.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact
      eRadical eMiddle eTop radicalInclusion topProjection
      hexact (sigma.moduleRadical j).subtype_injective
      (sigma.moduleRadical j).mkQ_surjective
  have hSC' :
      (ShortComplex.mk SC.f SC.g SC.zero).ShortExact := by
    simpa only [SC] using hSC
  letI : IsNoetherian Aᵐᵒᵖ (sigma.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength j)).1
  letI : IsArtinian Aᵐᵒᵖ (sigma.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength j)).2
  have hExtLeft := hnoParallel hs hr
  have hExtRight := hnoParallel ht hr
  letI : FiniteDimensional K
      (Ext (sigma.obj s).obj (sigma.obj r).obj 1) :=
    hExtLeft.1
  letI : FiniteDimensional K
      (Ext (sigma.obj t).obj (sigma.obj r).obj 1) :=
    hExtRight.1
  obtain ⟨ell, hell⟩ :=
    YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExtLeft.2
  obtain ⟨ell', hell'⟩ :=
    YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExtRight.2
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj s) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj s)).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj t) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj t)).mp ht
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj r) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj r)).mp hr
  letI : Simple (sigma.obj s).obj :=
    (simple_iff_isSimpleModule' (sigma.obj s).obj).mpr inferInstance
  letI : Simple (sigma.obj t).obj :=
    (simple_iff_isSimpleModule' (sigma.obj t).obj).mpr inferInstance
  letI : Simple (sigma.obj r).obj :=
    (simple_iff_isSimpleModule' (sigma.obj r).obj).mpr inferInstance
  have hsNonzero : 𝟙 (sigma.obj s).obj ≠ 0 :=
    CategoryTheory.id_nonzero (sigma.obj s).obj
  have htNonzero : 𝟙 (sigma.obj t).obj ≠ 0 :=
    CategoryTheory.id_nonzero (sigma.obj t).obj
  have hrNonzero : 𝟙 (sigma.obj r).obj ≠ 0 :=
    CategoryTheory.id_nonzero (sigma.obj r).obj
  let leftArrow : (Fin n → K) →ₗ[K] (Unit → K) :=
    YonedaExtReflection.scalarizedExtLinearMap
      (sigma.obj s).obj (sigma.obj r).obj ell
      (YonedaExtReflection.extBiprodLeft hSC'.extClass)
  let rightArrow : (Fin m → K) →ₗ[K] (Unit → K) :=
    YonedaExtReflection.scalarizedExtLinearMap
      (sigma.obj t).obj (sigma.obj r).obj ell'
      (YonedaExtReflection.extBiprodRight hSC'.extClass)
  have harrows :
      IsTwoSourceIdempotentIndecomposable leftArrow rightArrow :=
    YonedaExtReflection.shortExact_twoSource_scalarizedExtLinearMaps_isIdempotentIndecomposable
      (sigma.obj s).obj (sigma.obj t).obj (sigma.obj r).obj
      (sigma.obj j).obj hsNonzero htNonzero hrNonzero
      SC.f SC.g SC.zero hSC' (sigma.indecomposable j)
      ell hell ell' hell'
  have htarget : Module.finrank K (Unit → K) = 1 := by
    simp
  have hbounds :=
    twoSource_source_finrank_le_one htarget harrows
  simpa [leftArrow, rightArrow] using hbounds

/-- If both displayed simple top types actually occur, the two-source bounds
say that each occurs exactly once.  Together with `eTop`, this identifies the
top with one copy of each of the two displayed types. -/
theorem topMultiplicity_eq_one_of_twoTypeDecomposition
    (hnoParallel : NoParallelExtOne sigma K)
    {j s t r : iota}
    (hs : Simple (sigma.obj s))
    (ht : Simple (sigma.obj t))
    (hr : Simple (sigma.obj r))
    (eRadical :
      (sigma.obj r) ≃ₗ[Aᵐᵒᵖ] sigma.moduleRadical j)
    (n m : ℕ)
    (eTop :
      ((Fin n → sigma.obj s) × (Fin m → sigma.obj t))
        ≃ₗ[Aᵐᵒᵖ] sigma.moduleTop j)
    (hn : 0 < n) (hm : 0 < m) :
    n = 1 ∧ m = 1 := by
  have hbounds :=
    topMultiplicityBounds_of_twoTypeDecomposition
      sigma K hnoParallel hs ht hr eRadical n m eTop
  omega

/--
Exact one-nonsimple branched-length control.  If every simple quotient of an
indecomposable has one of two displayed simple types, its radical is simple,
and its semisimple top is not simple, then no-parallel `Ext¹` and the
two-source rank core force the top to have length two.  Hence the module has
composition length three.
-/
theorem compositionLength_eq_three_of_two_simpleQuotientTypes
    (hnoParallel : NoParallelExtOne sigma K)
    {j s t : iota}
    (hs : Simple (sigma.obj s))
    (ht : Simple (sigma.obj t))
    (hquotients :
      ∀ Q : sigma.SimpleQuotient j,
        Q.index = s ∨ Q.index = t)
    (hrad : IsSimpleModule Aᵐᵒᵖ (sigma.moduleRadical j))
    (htop : ¬ IsSimpleModule Aᵐᵒᵖ (sigma.moduleTop j)) :
    sigma.compositionLength j = 3 := by
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj s) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj s)).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj t) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj t)).mp ht
  letI : IsSemisimpleModule Aᵐᵒᵖ (sigma.moduleTop j) :=
    sigma.moduleTop_isSemisimple j
  obtain ⟨n, m, ⟨eTop⟩⟩ :=
    TwoTypeSemisimple.exists_twoTypeDecomposition
      (R := Aᵐᵒᵖ) (M := sigma.moduleTop j)
      (S := sigma.obj s) (T := sigma.obj t)
      (fun L hL ↦
        sigma.simpleTopSubmodule_type_eq_left_or_right
          hquotients L hL)
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.moduleRadical j) := hrad
  let Rad : FGModuleCat.{x} Aᵐᵒᵖ :=
    FGModuleCat.of Aᵐᵒᵖ (sigma.moduleRadical j)
  have hRadIndec : OpConjecture.Foundation.IsIndecomposableModule Aᵐᵒᵖ Rad :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨r, ⟨eRad⟩⟩ := sigma.complete Rad hRadIndec
  have hRadSimpleCat : Simple Rad :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Rad).2 inferInstance
  have hrSimple : Simple (sigma.obj r) :=
    (Simple.iff_of_iso eRad).mp hRadSimpleCat
  let eRadical :
      sigma.obj r ≃ₗ[Aᵐᵒᵖ] sigma.moduleRadical j :=
    (FGModuleCat.isoToLinearEquiv eRad).symm
  have hbounds : n ≤ 1 ∧ m ≤ 1 :=
    topMultiplicityBounds_of_twoTypeDecomposition
      sigma K hnoParallel hs ht hrSimple eRadical n m eTop.symm
  have htopLengthFormula :
      Module.length Aᵐᵒᵖ (sigma.moduleTop j) =
        (n : ℕ∞) + (m : ℕ∞) := by
    rw [eTop.length_eq, Module.length_prod,
      Module.length_pi_of_fintype,
      Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  have hnm : n + m ≤ 2 := by omega
  have htopLengthLe :
      Module.length Aᵐᵒᵖ (sigma.moduleTop j) ≤ 2 := by
    rw [htopLengthFormula, ← ENat.coe_add]
    exact ENat.coe_le_coe.mpr hnm
  letI : Nontrivial (sigma.obj j) :=
    (sigma.indecomposable j).nontrivial
  letI : IsArtinian Aᵐᵒᵖ (sigma.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength j)).2
  have hJneTop : sigma.moduleRadical j ≠ ⊤ :=
    (Module.jacobson_lt_top Aᵐᵒᵖ (sigma.obj j)).ne
  letI : Nontrivial (sigma.moduleTop j) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hJneTop
      (Submodule.Quotient.subsingleton_iff.mp hsub)
  have htopLengthPos :
      0 < Module.length Aᵐᵒᵖ (sigma.moduleTop j) :=
    Module.length_pos_iff.mpr inferInstance
  have hnmNeZero : n + m ≠ 0 := by
    intro hzero
    have hlengthZero :
        Module.length Aᵐᵒᵖ (sigma.moduleTop j) = 0 := by
      rw [htopLengthFormula, ← ENat.coe_add, hzero]
      rfl
    exact (ne_of_gt htopLengthPos) hlengthZero
  have hnmNeOne : n + m ≠ 1 := by
    intro hone
    have hlengthOne :
        Module.length Aᵐᵒᵖ (sigma.moduleTop j) = 1 := by
      rw [htopLengthFormula, ← ENat.coe_add, hone]
      rfl
    exact htop (Module.length_eq_one_iff.mp hlengthOne)
  have hnmEq : n + m = 2 := by omega
  have htopLength :
      Module.length Aᵐᵒᵖ (sigma.moduleTop j) = 2 := by
    rw [htopLengthFormula, ← ENat.coe_add, hnmEq]
    rfl
  have hjLength : Module.length Aᵐᵒᵖ (sigma.obj j) = 3 := by
    rw [Module.length_eq_add_of_exact
      (sigma.moduleRadical j).subtype
      (sigma.moduleRadical j).mkQ
      (sigma.moduleRadical j).subtype_injective
      (sigma.moduleRadical j).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (sigma.moduleRadical j)),
      Module.length_eq_one Aᵐᵒᵖ (sigma.moduleRadical j),
      htopLength]
    norm_num
  rw [← ENat.coe_inj, sigma.coe_compositionLength]
  exact hjLength

include K in
/-- The exact formerly-named one-nonsimple length-three control for a finite
complete skeleton.  Closedness restricts the simple quotient types to the
two displayed simple members and makes the radical simple; the theorem above
then supplies the missing length bound. -/
theorem oneNonsimpleLengthThreeControl_of_finiteSkeleton
    [IsAlgClosed K] [Finite iota] :
    sigma.OneNonsimpleLengthThreeControl := by
  intro S _hcard hclosed x s t _hxs _hxt _hst hS hxn hss htt htop
  have hxmem : x ∈ S := by
    rw [hS]
    simp
  have hrad : IsSimpleModule Aᵐᵒᵖ (sigma.moduleRadical x) :=
    sigma.moduleRadical_isSimple_of_oneNonsimple
      hclosed hS hxmem hss htt hxn
  have hquotients :
      ∀ Q : sigma.SimpleQuotient x,
        Q.index = s ∨ Q.index = t := by
    intro Q
    exact
      sigma.simpleQuotient_index_eq_left_or_right_of_oneNonsimple
        hclosed hS hxmem hxn hss htt Q
  have hnoParallel : NoParallelExtOne sigma K :=
    OpConjecture.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
      K A sigma
  exact
    compositionLength_eq_three_of_two_simpleQuotientTypes
      sigma K hnoParallel hss htt hquotients hrad htop

end OpConjecture.YonedaTwoSourceReduction

namespace OpConjecture.YonedaTwoSourceReduction

universe x

/--
Under the paper's hypotheses, only the two-nonsimple long-uniserial control
remains in the quotient-side five-family exhaustiveness theorem.
-/
theorem qClosedTriple_existsUnique_familyKind_of_longUniserialControl
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {iota : Type x} [Finite iota]
      (sigma :
        _root_.OpConjecture.IndecomposableSkeleton.{x, x, x}
          Aᵐᵒᵖ iota),
      sigma.TwoNonsimpleLongUniserialControl →
      ∀ {S : Set iota}, S.ncard = 3 → sigma.qClosure.IsClosed S →
        ∃! k : _root_.OpConjecture.IndecomposableSkeleton.QTripleFamilyKind,
          sigma.IsQTripleFamilyKind S k := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  intro iota _ sigma hlong S hcard hclosed
  exact
    sigma.qClosedTriple_existsUnique_familyKind_of_longControls
      (OpConjecture.LoewyTwoGabrielClassification.isotypicLoewyTwoIndecomposablesHaveSimpleTop
        K A sigma)
      (oneNonsimpleLengthThreeControl_of_finiteSkeleton sigma K)
      hlong hcard hclosed

end OpConjecture.YonedaTwoSourceReduction

namespace OpConjecture.YonedaTwoSourceReduction

universe x

/-- Paper-scope wrapper: over an algebraically closed field, a finite
complete right-module skeleton satisfies the one-nonsimple length-three
control with no separate `Ext¹` hypothesis. -/
theorem oneNonsimpleLengthThreeControl_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {iota : Type x} [Finite iota]
      (sigma :
        _root_.OpConjecture.IndecomposableSkeleton.{x, x, x}
          Aᵐᵒᵖ iota),
      sigma.OneNonsimpleLengthThreeControl := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  intro iota _ sigma
  exact
    oneNonsimpleLengthThreeControl_of_finiteSkeleton
      sigma K

end OpConjecture.YonedaTwoSourceReduction
