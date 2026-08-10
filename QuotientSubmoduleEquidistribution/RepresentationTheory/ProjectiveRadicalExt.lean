import QuotientSubmoduleEquidistribution.RepresentationTheory.ExtForkSemisimpleLayers
import QuotientSubmoduleEquidistribution.RepresentationTheory.NakayamaRepresentationFiniteBridge
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.ProjectiveRadicalExt

universe u v

variable {K R : Type u}
  [Field K] [Ring R] [Algebra K R] [Small.{u} R]

/-- The radical inclusion and top projection, with the top identified with
an externally chosen simple module. -/
abbrev radicalPresentation
    {P S : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfConj
    (LinearEquiv.refl R (Module.jacobson R P))
    (LinearEquiv.refl R P)
    eTop.symm
    (Module.jacobson R P).subtype
    (Module.jacobson R P).mkQ
    (LinearMap.exact_subtype_mkQ
      (Module.jacobson R P)).linearMap_comp_eq_zero

omit [Small R] in
theorem radicalPresentation_shortExact
    {P S : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S) :
    (radicalPresentation eTop).ShortExact :=
  ModuleCat.shortComplexOfConj_shortExact
    (LinearEquiv.refl R (Module.jacobson R P))
    (LinearEquiv.refl R P)
    eTop.symm
    (Module.jacobson R P).subtype
    (Module.jacobson R P).mkQ
    (LinearMap.exact_subtype_mkQ (Module.jacobson R P))
    (Module.jacobson R P).subtype_injective
    (Module.jacobson R P).mkQ_surjective

/-- Exact-sequence dimension shifting is injective as soon as every map
from the projective middle term kills the displayed kernel. -/
theorem extClass_precomp_bijective_of_projective_middle_of_restrict_zero
    {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    {T : ModuleCat.{u} R}
    (hRestrict : ∀ g : S.X₂ ⟶ T, S.f ≫ g = 0) :
    Function.Bijective
      (hS.extClass.precompOfLinear K T (add_zero 1)) := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hker :
        hS.extClass.comp (x - y) (add_zero 1) = 0 := by
      change
        (hS.extClass.precompOfLinear K T (add_zero 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ :=
      Ext.contravariant_sequence_exact₁
        hS T (x - y) (add_zero 1) hker
    have hzComp :
        (Ext.mk₀ S.f).comp z (zero_add 0) = 0 := by
      rw [← Ext.mk₀_linearEquiv₀_apply (R := K) z,
        Ext.mk₀_comp_mk₀]
      simpa using congrArg Ext.mk₀
        (hRestrict (Ext.linearEquiv₀ (R := K) z))
    rw [hzComp] at hz
    simpa using hz.symm
  · intro x
    obtain ⟨z, hz⟩ :=
      Ext.contravariant_sequence_exact₃ hS T x
        (Ext.eq_zero_of_projective _) (add_zero 1)
    exact ⟨z, hz⟩

omit [Small R] in
/-- Every map from a module to a semisimple module kills its Jacobson
radical. -/
theorem radical_inclusion_comp_eq_zero
    {P T : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup T] [Module R T]
    [IsSemisimpleModule R T]
    (g : ModuleCat.of R P ⟶ ModuleCat.of R T) :
    ModuleCat.ofHom (Module.jacobson R P).subtype ≫ g = 0 := by
  apply ModuleCat.hom_ext
  ext x
  have hx : (x : P) ∈ LinearMap.ker g.hom :=
    IsSemisimpleModule.jacobson_le_ker R R P T g.hom x.2
  simpa using hx

omit [Small R] in
/-- Maps from a module to a semisimple target are exactly maps from its
semisimple top. -/
def topHomLinearEquivHom
    {M T : Type u}
    [AddCommGroup M] [Module R M]
    [AddCommGroup T] [Module R T]
    [IsSemisimpleModule R T] :
    (ModuleCat.of R (M ⧸ Module.jacobson R M) ⟶ ModuleCat.of R T) ≃ₗ[K]
      (ModuleCat.of R M ⟶ ModuleCat.of R T) where
  toFun f := ModuleCat.ofHom (f.hom.comp (Module.jacobson R M).mkQ)
  invFun g := ModuleCat.ofHom <|
    (Module.jacobson R M).liftQ g.hom
      (IsSemisimpleModule.jacobson_le_ker R R M T g.hom)
  left_inv f := by
    apply ModuleCat.hom_ext
    ext x
    simp
  right_inv g := by
    apply ModuleCat.hom_ext
    ext x
    simp
  map_add' f g := by
    apply ModuleCat.hom_ext
    rfl
  map_smul' a f := by
    apply ModuleCat.hom_ext
    rfl

/-- The projective radical-layer theorem at its natural level: maps from
`rad P` to a semisimple module are canonically identified with degree-one
extensions of the chosen simple top by that module. -/
def radicalHomLinearEquivExtOne
    {P S T : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [Projective (ModuleCat.of R P)]
    [IsSemisimpleModule R T]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S) :
    (ModuleCat.of R (Module.jacobson R P) ⟶ ModuleCat.of R T) ≃ₗ[K]
      Ext (ModuleCat.of R S) (ModuleCat.of R T) 1 :=
  (Ext.linearEquiv₀ (R := K)).symm.trans
    (LinearEquiv.ofBijective
      ((radicalPresentation_shortExact eTop).extClass.precompOfLinear
        K (ModuleCat.of R T) (add_zero 1))
      (extClass_precomp_bijective_of_projective_middle_of_restrict_zero
        (radicalPresentation_shortExact eTop)
        (fun g ↦ radical_inclusion_comp_eq_zero g)))

/-- The full first-radical-layer identification: maps from
`top (rad P) = rad P / rad (rad P)` to a semisimple module are canonically
the same as degree-one extensions of `top P` by that module. -/
def radicalTopHomLinearEquivExtOne
    {P S T : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [Projective (ModuleCat.of R P)]
    [IsSemisimpleModule R T]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S) :
    (ModuleCat.of R
        (Module.jacobson R P ⧸
          Module.jacobson R (Module.jacobson R P)) ⟶
      ModuleCat.of R T) ≃ₗ[K]
      Ext (ModuleCat.of R S) (ModuleCat.of R T) 1 :=
  (topHomLinearEquivHom (K := K) (R := R)
      (M := Module.jacobson R P) (T := T)).trans
    (radicalHomLinearEquivExtOne (K := K) (R := R) eTop)

theorem finrank_extOne_eq_finrank_radicalTopHom
    {P S T : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [Projective (ModuleCat.of R P)]
    [IsSemisimpleModule R T]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S)
    [FiniteDimensional K
      (ModuleCat.of R
          (Module.jacobson R P ⧸
            Module.jacobson R (Module.jacobson R P)) ⟶
        ModuleCat.of R T)]
    [FiniteDimensional K
      (Ext (ModuleCat.of R S) (ModuleCat.of R T) 1)] :
    Module.finrank K (Ext (ModuleCat.of R S) (ModuleCat.of R T) 1) =
      Module.finrank K
        (ModuleCat.of R
            (Module.jacobson R P ⧸
              Module.jacobson R (Module.jacobson R P)) ⟶
          ModuleCat.of R T) :=
  LinearEquiv.finrank_eq
    (radicalTopHomLinearEquivExtOne (K := K) (R := R) eTop).symm

theorem radicalHomLinearEquivExtOne_apply
    {P S T : Type u}
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    [AddCommGroup T] [Module R T]
    [Projective (ModuleCat.of R P)]
    [IsSemisimpleModule R T]
    (eTop : (P ⧸ Module.jacobson R P) ≃ₗ[R] S)
    (f : ModuleCat.of R (Module.jacobson R P) ⟶ ModuleCat.of R T) :
    radicalHomLinearEquivExtOne (K := K) (R := R) eTop f =
      (radicalPresentation_shortExact eTop).extClass.comp
        (Ext.mk₀ f) (add_zero 1) := by
  rfl

section SkeletonForks

variable {A : Type u}
  [Ring A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  {kappa : Type v}
  (tau : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} A kappa)

open QuotientSubmoduleEquidistribution.GabrielArrowBridge
open QuotientSubmoduleEquidistribution.ExtDegreeNakayamaReduction

/-- Restriction of a surjective module map to module radicals. -/
def radicalMapOfSurjective
    {M N : Type u}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    Module.jacobson A M →ₗ[A] Module.jacobson A N :=
  (f.domRestrict (Module.jacobson A M)).codRestrict
    (Module.jacobson A N)
    (fun x ↦ Module.map_jacobson_le f ⟨x, x.2, rfl⟩)

omit [IsNoetherianRing A] [IsArtinianRing A] in
/-- Over an Artinian source, a surjection maps the source radical onto the
target radical. -/
theorem radicalMapOfSurjective_surjective
    {M N : Type u}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    [IsArtinian A M]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Surjective (radicalMapOfSurjective f) := by
  have hmap :=
    QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
      f hf
  intro y
  have hy : (y : N) ∈ Submodule.map f (Module.jacobson A M) := by
    rw [hmap]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  simpa [radicalMapOfSurjective] using hxy

omit [IsArtinianRing A] in
/-- Every nonzero finite module has an epimorphism to a chosen simple
representative in a complete indecomposable skeleton. -/
theorem exists_surjective_to_chosen_simple
    {M : Type u}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    ∃ s : tau.SimpleIndex,
      ∃ q : M →ₗ[A] tau.obj s.1,
        Function.Surjective q := by
  have hbot : (⊥ : Submodule A M) ≠ ⊤ := bot_ne_top
  obtain ⟨C, hC, _⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left hbot
  let S : FGModuleCat.{u} A := FGModuleCat.of A (M ⧸ C)
  letI : IsSimpleModule A (M ⧸ C) :=
    isSimpleModule_iff_isCoatom.mpr hC
  have hSIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A S :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨j, ⟨e⟩⟩ := tau.complete S hSIndec
  have hTarget : IsSimpleModule A (tau.obj j) :=
    IsSimpleModule.congr (FGModuleCat.isoToLinearEquiv e).symm
  have hTargetSimple : Simple (tau.obj j) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj j)).mpr hTarget
  let s : tau.SimpleIndex := ⟨j, hTargetSimple⟩
  let q : M →ₗ[A] tau.obj s.1 :=
    (FGModuleCat.isoToLinearEquiv e).toLinearMap.comp C.mkQ
  refine ⟨s, q, ?_⟩
  exact (FGModuleCat.isoToLinearEquiv e).surjective.comp C.mkQ_surjective

omit [IsArtinianRing A] in
/-- A decomposable nonzero finite module has a quotient which is a direct
sum of two chosen simple modules. -/
theorem exists_epi_to_biprod_chosen_simples_of_not_indec
    {M : Type u}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M]
    (hNotIndec : ¬ QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A M) :
    ∃ p q : tau.SimpleIndex,
      ∃ f : ModuleCat.of A M ⟶ (tau.obj p.1).obj ⊞ (tau.obj q.1).obj,
        Epi f := by
  have hnotAll :
      ¬ ∀ N Q : Submodule A M,
        IsCompl N Q → N = ⊥ ∨ Q = ⊥ := by
    intro hall
    exact hNotIndec
      (QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl hall)
  push Not at hnotAll
  obtain ⟨N, Q, hNQ, hNne, hQne⟩ := hnotAll
  letI : Nontrivial N := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hNne
  letI : Nontrivial Q := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hQne
  obtain ⟨p, fP, hfP⟩ :=
    exists_surjective_to_chosen_simple tau (M := N)
  obtain ⟨q, fQ, hfQ⟩ :=
    exists_surjective_to_chosen_simple tau (M := Q)
  let eNQ : (N × Q) ≃ₗ[A] M := N.prodEquivOfIsCompl Q hNQ
  let f : M →ₗ[A] tau.obj p.1 × tau.obj q.1 :=
    (fP.prodMap fQ).comp eNQ.symm.toLinearMap
  have hf : Function.Surjective f := by
    have hprod : Function.Surjective (fP.prodMap fQ) := by
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := hfP x
      obtain ⟨b, rfl⟩ := hfQ y
      exact ⟨⟨a, b⟩, rfl⟩
    change Function.Surjective
      ((fP.prodMap fQ).comp eNQ.symm.toLinearMap)
    exact hprod.comp eNQ.symm.surjective
  let Fprod : ModuleCat.of A M ⟶
      ModuleCat.of A (tau.obj p.1 × tau.obj q.1) :=
    ModuleCat.ofHom f
  haveI : Epi Fprod :=
    (ModuleCat.epi_iff_surjective Fprod).mpr hf
  let F : ModuleCat.of A M ⟶
      (tau.obj p.1).obj ⊞ (tau.obj q.1).obj :=
    Fprod ≫
      (ModuleCat.biprodIsoProd
        (tau.obj p.1).obj (tau.obj q.1).obj).inv
  haveI : Epi F := by
    dsimp only [F]
    infer_instance
  exact ⟨p, q, F, inferInstance⟩

omit [IsNoetherianRing A] [IsArtinianRing A] in
private theorem fst_comp_ne_zero_of_epi
    {X P Q : ModuleCat.{u} A}
    [Simple P]
    (q : X ⟶ P ⊞ Q) [Epi q] :
    q ≫ biprod.fst ≠ 0 := by
  intro hzero
  have hfst : (biprod.fst : P ⊞ Q ⟶ P) = 0 := by
    apply (cancel_epi q).mp
    simpa using hzero
  exact CategoryTheory.id_nonzero P <| by
    calc
      𝟙 P = biprod.inl ≫ (biprod.fst : P ⊞ Q ⟶ P) := by simp
      _ = biprod.inl ≫ 0 := by rw [hfst]
      _ = 0 := by simp

omit [IsNoetherianRing A] [IsArtinianRing A] in
private theorem snd_comp_ne_zero_of_epi
    {X P Q : ModuleCat.{u} A}
    [Simple Q]
    (q : X ⟶ P ⊞ Q) [Epi q] :
    q ≫ biprod.snd ≠ 0 := by
  intro hzero
  have hsnd : (biprod.snd : P ⊞ Q ⟶ Q) = 0 := by
    apply (cancel_epi q).mp
    simpa using hzero
  exact CategoryTheory.id_nonzero Q <| by
    calc
      𝟙 Q = biprod.inr ≫ (biprod.snd : P ⊞ Q ⟶ Q) := by simp
      _ = biprod.inr ≫ 0 := by rw [hsnd]
      _ = 0 := by simp

omit [IsArtinianRing A] in
/-- Two distinct simple summands in a semisimple quotient of the radical of
an indecomposable projective cover force two outgoing Ext--Gabriel arrows. -/
theorem outgoing_extGabrielFork_of_projective_radical_quotient_distinct
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (s p q : tau.SimpleIndex) (hpq : p ≠ q)
    {P : Type u} [AddCommGroup P] [Module A P]
    [Projective (ModuleCat.of A P)]
    (eTop : (P ⧸ Module.jacobson A P) ≃ₗ[A] tau.obj s.1)
    (radQuot :
      ModuleCat.of A (Module.jacobson A P) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj q.1).obj)
    [Epi radQuot] :
    HasOutgoingExtGabrielFork (K := K) tau := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSimpleModule A (tau.obj q.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj q.1)).mp q.2
  letI : IsSemisimpleModule A (tau.obj p.1) := by infer_instance
  letI : IsSemisimpleModule A (tau.obj q.1) := by infer_instance
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  letI : Simple (tau.obj q.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj q.1).obj).mpr inferInstance
  letI : Nontrivial (tau.obj p.1) :=
    IsSimpleModule.nontrivial A (tau.obj p.1)
  letI : Nontrivial (tau.obj q.1) :=
    IsSimpleModule.nontrivial A (tau.obj q.1)
  let fP :
      ModuleCat.of A (Module.jacobson A P) ⟶ (tau.obj p.1).obj :=
    radQuot ≫ biprod.fst
  let fQ :
      ModuleCat.of A (Module.jacobson A P) ⟶ (tau.obj q.1).obj :=
    radQuot ≫ biprod.snd
  let eP := radicalHomLinearEquivExtOne (K := K) (R := A)
    (T := tau.obj p.1) eTop
  let eQ := radicalHomLinearEquivExtOne (K := K) (R := A)
    (T := tau.obj q.1) eTop
  let etaP : ExtOne tau s p := eP fP
  let etaQ : ExtOne tau s q := eQ fQ
  have hfP : fP ≠ 0 := fst_comp_ne_zero_of_epi radQuot
  have hfQ : fQ ≠ 0 := snd_comp_ne_zero_of_epi radQuot
  have hetaP : etaP ≠ 0 := by
    intro hzero
    apply hfP
    apply eP.injective
    simpa [etaP] using hzero
  have hetaQ : etaQ ≠ 0 := by
    intro hzero
    apply hfQ
    apply eQ.injective
    simpa [etaQ] using hzero
  letI : FiniteDimensional K (ExtOne tau s p) := hFinite s p
  letI : FiniteDimensional K (ExtOne tau s q) := hFinite s q
  letI : Nontrivial (ExtOne tau s p) := ⟨etaP, 0, hetaP⟩
  letI : Nontrivial (ExtOne tau s q) := ⟨etaQ, 0, hetaQ⟩
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨0, Module.finrank_pos⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, q, ⟨0, Module.finrank_pos⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  apply hpq
  exact congrArg (ExtGabrielArrowIndex.target tau) hab

omit [IsNoetherianRing A] [IsArtinianRing A] in
private theorem linearIndependent_fst_snd_comp_of_epi
    {X T : ModuleCat.{u} A}
    [Simple T]
    (radQuot : X ⟶ T ⊞ T) [Epi radQuot] :
    LinearIndependent K
      ![radQuot ≫ (biprod.fst : T ⊞ T ⟶ T),
        radQuot ≫ (biprod.snd : T ⊞ T ⟶ T)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hab' :
      a • (biprod.fst : T ⊞ T ⟶ T) +
          b • (biprod.snd : T ⊞ T ⟶ T) = 0 := by
    apply (cancel_epi radQuot).mp
    simpa using hab
  have haMorph : a • 𝟙 T = 0 := by
    calc
      a • 𝟙 T =
          biprod.inl ≫
            (a • (biprod.fst : T ⊞ T ⟶ T) +
              b • (biprod.snd : T ⊞ T ⟶ T)) := by simp
      _ = biprod.inl ≫ 0 := by rw [hab']
      _ = 0 := by simp
  have hbMorph : b • 𝟙 T = 0 := by
    calc
      b • 𝟙 T =
          biprod.inr ≫
            (a • (biprod.fst : T ⊞ T ⟶ T) +
              b • (biprod.snd : T ⊞ T ⟶ T)) := by simp
      _ = biprod.inr ≫ 0 := by rw [hab']
      _ = 0 := by simp
  constructor
  · rcases smul_eq_zero.mp haMorph with ha | hid
    · exact ha
    · exact (CategoryTheory.id_nonzero T hid).elim
  · rcases smul_eq_zero.mp hbMorph with hb | hid
    · exact hb
    · exact (CategoryTheory.id_nonzero T hid).elim

omit [IsArtinianRing A] in
/-- Two copies of one chosen simple in a semisimple radical quotient force
two parallel outgoing Ext--Gabriel arrows. -/
theorem outgoing_parallel_extGabrielFork_of_projective_radical_quotient
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (s p : tau.SimpleIndex)
    {P : Type u} [AddCommGroup P] [Module A P]
    [Projective (ModuleCat.of A P)]
    (eTop : (P ⧸ Module.jacobson A P) ≃ₗ[A] tau.obj s.1)
    (radQuot :
      ModuleCat.of A (Module.jacobson A P) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj p.1).obj)
    [Epi radQuot] :
    HasOutgoingExtGabrielFork (K := K) tau := by
  letI : IsSimpleModule A (tau.obj p.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj p.1)).mp p.2
  letI : IsSemisimpleModule A (tau.obj p.1) := by infer_instance
  letI : Simple (tau.obj p.1).obj :=
    (simple_iff_isSimpleModule' (tau.obj p.1).obj).mpr inferInstance
  let f₀ :
      ModuleCat.of A (Module.jacobson A P) ⟶ (tau.obj p.1).obj :=
    radQuot ≫ biprod.fst
  let f₁ :
      ModuleCat.of A (Module.jacobson A P) ⟶ (tau.obj p.1).obj :=
    radQuot ≫ biprod.snd
  let e := radicalHomLinearEquivExtOne (K := K) (R := A)
    (T := tau.obj p.1) eTop
  let eta₀ : ExtOne tau s p := e f₀
  let eta₁ : ExtOne tau s p := e f₁
  have hLIHom : LinearIndependent K ![f₀, f₁] := by
    simpa [f₀, f₁] using
      (linearIndependent_fst_snd_comp_of_epi
        (K := K) (A := A) radQuot)
  have hLIExt : LinearIndependent K ![eta₀, eta₁] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    apply (LinearIndependent.pair_iff.mp hLIHom) a b
    apply e.injective
    simpa [eta₀, eta₁] using hab
  letI : FiniteDimensional K (ExtOne tau s p) := hFinite s p
  have hdim : 2 ≤ Module.finrank K (ExtOne tau s p) := by
    have hcard := hLIExt.fintype_card_le_finrank
    simpa using hcard
  have hzero : 0 < Module.finrank K (ExtOne tau s p) := by omega
  have hone : 1 < Module.finrank K (ExtOne tau s p) := by omega
  let a : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨0, hzero⟩⟩
  let b : ExtGabrielArrowIndex (K := K) tau :=
    ⟨s, p, ⟨1, hone⟩⟩
  refine ⟨a, b, ?_, rfl⟩
  intro hab
  have hindices :=
    congrArg
      (fun z : ExtGabrielArrowIndex (K := K) tau ↦ (z.2.2 : Nat))
      hab
  simp [a, b] at hindices

omit [IsArtinianRing A] in
/-- The complete outgoing radical-fork extraction.  If a chosen
indecomposable has simple top and decomposable nonzero radical, a projective
cover maps its first radical layer onto two simple quotients of that radical;
the preceding multiplicity theorem then produces an outgoing Ext--Gabriel
fork (including the repeated-simple case). -/
theorem outgoing_of_decomposable_radical
    (hFinite : FiniteExtOneSupport (K := K) tau)
    (i : kappa)
    (hTop : IsSimpleModule A (tau.moduleTop i))
    (hRadical : tau.moduleRadical i ≠ ⊥)
    (hNotIndec :
      ¬ QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A (tau.moduleRadical i)) :
    HasOutgoingExtGabrielFork (K := K) tau := by
  let Top : FGModuleCat.{u} A := FGModuleCat.of A (tau.moduleTop i)
  have hTopSimple : Simple Top :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Top).mpr hTop
  have hTopIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A Top :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨sRaw, ⟨eTopM⟩⟩ := tau.complete Top hTopIndec
  have hsSimple : Simple (tau.obj sRaw) :=
    (Simple.iff_of_iso eTopM).mp hTopSimple
  let s : tau.SimpleIndex := ⟨sRaw, hsSimple⟩
  obtain ⟨proj, hProj, f, hf⟩ :=
    QuotientSubmoduleEquidistribution.NakayamaRepresentationFiniteBridge.exists_epi_from_indec_projective_of_simpleTop
      tau i hTop
  letI : CategoryTheory.Projective (tau.obj proj) := hProj
  letI : Module.Projective A (tau.obj proj) :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.ProjectiveSimpleRank.moduleProjective_of_fgProjective
      (tau.obj proj) hProj
  letI : Nontrivial (tau.obj proj) :=
    (tau.indecomposable proj).nontrivial
  letI : IsLocalRing (Module.End A (tau.obj proj)) :=
    QuotientSubmoduleEquidistribution.Foundation.isLocalRing_end_of_isIndecomposable
      (tau.finiteLength proj) (tau.indecomposable proj)
  letI : IsSimpleModule A (tau.obj s.1) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (tau.obj s.1)).mp s.2
  let qM : tau.obj i ⟶ Top :=
    FGModuleCat.ofHom (tau.moduleRadical i).mkQ
  haveI : Epi qM :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective qM).mpr
      (tau.moduleRadical i).mkQ_surjective
  let topMap : tau.obj proj ⟶ tau.obj s.1 :=
    f ≫ qM ≫ eTopM.hom
  haveI : Epi topMap := by
    dsimp only [topMap]
    infer_instance
  have htopSurj : Function.Surjective topMap.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective topMap).mp
      inferInstance
  let eTopP :
      (tau.obj proj ⧸ Module.jacobson A (tau.obj proj)) ≃ₗ[A]
        tau.obj s.1 :=
    QuotientSubmoduleEquidistribution.ProjectiveSimpleTop.topLinearEquivOfSurjectiveToSimple
      topMap.hom.hom htopSurj
  letI : IsArtinian A (tau.obj proj) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (tau.finiteLength proj)).2
  have hfSurj : Function.Surjective f.hom.hom :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective f).mp hf
  let rMap : tau.moduleRadical proj →ₗ[A] tau.moduleRadical i :=
    radicalMapOfSurjective f.hom.hom
  have hrMap : Function.Surjective rMap :=
    radicalMapOfSurjective_surjective f.hom.hom hfSurj
  letI : Nontrivial (tau.moduleRadical i) := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hRadical
  obtain ⟨p, q, radQuotM, hradQuotM⟩ :=
    exists_epi_to_biprod_chosen_simples_of_not_indec
      tau hNotIndec
  letI : Epi radQuotM := hradQuotM
  let rMapCat :
      ModuleCat.of A (tau.moduleRadical proj) ⟶
        ModuleCat.of A (tau.moduleRadical i) :=
    ModuleCat.ofHom rMap
  haveI : Epi rMapCat :=
    (ModuleCat.epi_iff_surjective rMapCat).mpr hrMap
  let radQuotP :
      ModuleCat.of A (tau.moduleRadical proj) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj q.1).obj :=
    rMapCat ≫ radQuotM
  haveI : Epi radQuotP := by
    dsimp only [radQuotP]
    infer_instance
  let radQuotP' :
      ModuleCat.of A (Module.jacobson A (tau.obj proj)) ⟶
        (tau.obj p.1).obj ⊞ (tau.obj q.1).obj :=
    radQuotP
  haveI : Epi radQuotP' := by
    dsimp only [radQuotP']
    exact (inferInstance : Epi radQuotP)
  by_cases hpq : p = q
  · subst q
    letI : Epi radQuotP' := by
      dsimp only [radQuotP', radQuotP]
      infer_instance
    exact
      outgoing_parallel_extGabrielFork_of_projective_radical_quotient
        tau hFinite s p (P := tau.obj proj)
          (radQuot := radQuotP') eTopP
  · letI : Epi radQuotP' := by
      dsimp only [radQuotP', radQuotP]
      infer_instance
    exact
      outgoing_extGabrielFork_of_projective_radical_quotient_distinct
        tau hFinite s p q hpq (P := tau.obj proj)
          (radQuot := radQuotP') eTopP

end SkeletonForks

end QuotientSubmoduleEquidistribution.ProjectiveRadicalExt
