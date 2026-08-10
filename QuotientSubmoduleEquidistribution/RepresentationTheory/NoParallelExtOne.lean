import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Prod
import QuotientSubmoduleEquidistribution.RepresentationTheory.BottomTwoSimpleTop
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteDimensionalAlgebra
import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoRankCore

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.NoParallelExtOne

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A section of the quotient map forces the class of a short exact sequence to vanish. -/
theorem extClass_eq_zero_of_section
    {S : ShortComplex C} (hS : S.ShortExact)
    (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    hS.extClass = 0 := by
  calc
    hS.extClass =
        (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) := by simp
    _ = (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by rw [hs]
    _ = (Ext.mk₀ s).comp
          ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1))
          (zero_add 1) := by
      rw [Ext.mk₀_comp_mk₀_assoc]
    _ = 0 := by simp

variable {R : Type u} [Ring R]

/-- A nonzero extension of one simple module by another has indecomposable middle term. -/
theorem indecomposable_middle_of_extClass_ne_zero
    [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    [IsSimpleModule R S.X₁] [IsSimpleModule R S.X₃]
    [IsArtinian R S.X₂]
    (hne : hS.extClass ≠ 0) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R S.X₂ := by
  have hlen : Module.length R S.X₂ = 2 := by
    rw [Module.length_eq_add_of_exact S.f.hom S.g.hom
      hS.moduleCat_injective_f hS.moduleCat_surjective_g]
    · rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R S.X₁),
        Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R S.X₃)]
      norm_num
    · exact (LinearMap.exact_iff.mpr hS.exact.moduleCat_range_eq_ker.symm)
  apply
    QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.isIndecomposableModule_of_length_eq_two_of_jacobson_ne_bot
      hlen
  intro hjac
  letI : IsSemisimpleModule R S.X₂ :=
    (IsArtinian.isSemisimpleModule_iff_jacobson R S.X₂).2 hjac
  obtain ⟨s, hs⟩ :=
    IsSemisimpleModule.lifting_property S.g.hom
      hS.moduleCat_surjective_g (LinearMap.id : S.X₃ →ₗ[R] S.X₃)
  apply hne
  apply extClass_eq_zero_of_section hS (ModuleCat.ofHom s)
  apply ModuleCat.hom_ext
  simpa [LinearMap.comp_apply] using hs

/-! ## Explicit finite pushouts of a projective presentation -/

namespace PushoutExtension

variable {P S T : Type v}
  [AddCommGroup P] [AddCommGroup S] [AddCommGroup T]
  [Module R P] [Module R S] [Module R T]

/-- The relation `(f x, -x)` used to push a kernel presentation out along `f`. -/
def relationMap (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    LinearMap.ker p →ₗ[R] T × P :=
  f.prod (-(LinearMap.ker p).subtype)

def relation (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Submodule R (T × P) :=
  LinearMap.range (relationMap p f)

abbrev middle (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :=
  (T × P) ⧸ relation p f

instance [Module.Finite R T] [Module.Finite R P]
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Module.Finite R (middle p f) := by
  infer_instance

def inclusion (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    T →ₗ[R] middle p f :=
  (relation p f).mkQ.comp (LinearMap.inl R T P)

def presentationMap (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    P →ₗ[R] middle p f :=
  (relation p f).mkQ.comp (LinearMap.inr R T P)

private theorem relation_le_projectionPre_ker
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    relation p f ≤
      (p.comp (LinearMap.snd R T P)).ker := by
  rintro y ⟨x, rfl⟩
  simp [relationMap]

def projection (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    middle p f →ₗ[R] S :=
  Submodule.liftQ (relation p f)
    (p.comp (LinearMap.snd R T P))
    (relation_le_projectionPre_ker p f)

@[simp]
theorem inclusion_apply
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (t : T) :
    inclusion p f t = (relation p f).mkQ (t, 0) := rfl

@[simp]
theorem presentationMap_apply
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (x : P) :
    presentationMap p f x = (relation p f).mkQ (0, x) := rfl

@[simp]
theorem projection_mkQ
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) (y : T × P) :
    projection p f ((relation p f).mkQ y) = p y.2 := rfl

theorem inclusion_injective
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Function.Injective (inclusion p f) := by
  rw [← LinearMap.ker_eq_bot]
  ext t
  constructor
  · intro ht
    have hmem : (t, 0) ∈ relation p f := by
      simpa [inclusion] using ht
    obtain ⟨x, hx⟩ := hmem
    have hxP : -(x : P) = 0 := by
      simpa [relationMap] using congrArg Prod.snd hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      simpa using congrArg Neg.neg hxP
    have hxT : f x = t := by
      simpa [relationMap] using congrArg Prod.fst hx
    simpa [hx0] using hxT.symm
  · rintro rfl
    simp

theorem projection_surjective
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    Function.Surjective (projection p f) := by
  intro s
  obtain ⟨x, rfl⟩ := hp s
  exact ⟨(relation p f).mkQ (0, x), projection_mkQ p f (0, x)⟩

theorem exact_inclusion_projection
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    Function.Exact (inclusion p f) (projection p f) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      have hyp : p y.2 = 0 := by
        change projection p f ((relation p f).mkQ y) = 0 at hy
        rw [show projection p f ((relation p f).mkQ y) = p y.2 from
          projection_mkQ p f y] at hy
        exact hy
      let x : LinearMap.ker p := ⟨y.2, hyp⟩
      refine ⟨y.1 + f x, ?_⟩
      apply (Submodule.Quotient.eq (relation p f)).mpr
      refine ⟨x, ?_⟩
      ext
      · simp [relationMap, x]
      · simp [relationMap, x]
  · rintro _ ⟨t, rfl⟩
    change projection p f ((relation p f).mkQ (t, 0)) = 0
    simpa using projection_mkQ p f (t, 0)

abbrev shortComplex
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    ShortComplex (ModuleCat.{v} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (inclusion p f) (projection p f) (by
      ext t
      change projection p f ((relation p f).mkQ (t, 0)) = 0
      simpa using projection_mkQ p f (t, 0))

theorem shortExact
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (shortComplex p f).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact exact_inclusion_projection p f
  · exact inclusion_injective p f
  · exact projection_surjective p hp f

theorem presentation_relation
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    (inclusion p f).comp f =
      (presentationMap p f).comp (LinearMap.ker p).subtype := by
  ext x
  change (relation p f).mkQ (f x, 0) =
    (relation p f).mkQ (0, (x : P))
  apply (Submodule.Quotient.eq (relation p f)).mpr
  exact ⟨x, by ext <;> simp [relationMap]⟩

def fromPresentation
    (p : P →ₗ[R] S) (f : LinearMap.ker p →ₗ[R] T) :
    p.shortComplexKer ⟶ shortComplex p f where
  τ₁ := ModuleCat.ofHom f
  τ₂ := ModuleCat.ofHom (presentationMap p f)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply ModuleCat.hom_ext
    exact presentation_relation p f
  comm₂₃ := by
    apply ModuleCat.hom_ext
    ext x
    exact projection_mkQ p f (0, x)

/-- The explicit pushout realizes the connecting image of `f`. -/
theorem extClass_eq_precomp
    [Small.{v} R]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f : LinearMap.ker p →ₗ[R] T) :
    (shortExact p hp f).extClass =
      (LinearMap.shortExact_shortComplexKer hp).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom f)) (add_zero 1) := by
  have hnat :=
    ShortComplex.ShortExact.extClass_naturality
      (LinearMap.shortExact_shortComplexKer hp)
      (shortExact p hp f) (fromPresentation p f)
  dsimp [fromPresentation] at hnat
  rw [Ext.mk₀_id_comp] at hnat
  exact hnat.symm

/-- Every `Ext¹` class is represented by one of the explicit pushouts. -/
theorem exists_pushout_with_extClass_eq
    [Small.{v} R]
    [Module.Free R P]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (x : Ext (ModuleCat.of R S) (ModuleCat.of R T) 1) :
    ∃ f : LinearMap.ker p →ₗ[R] T,
      (shortExact p hp f).extClass = x := by
  letI : Projective (ModuleCat.of R P) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
  let hbase := LinearMap.shortExact_shortComplexKer hp
  obtain ⟨x₀, hx₀⟩ :=
    Ext.contravariant_sequence_exact₃ hbase (ModuleCat.of R T) x
      (Ext.eq_zero_of_projective _) (rfl : 1 + 0 = 1)
  let f : LinearMap.ker p →ₗ[R] T :=
    (Ext.addEquiv₀ x₀).hom
  refine ⟨f, ?_⟩
  rw [extClass_eq_precomp p hp f]
  change hbase.extClass.comp
      (Ext.mk₀ (Ext.addEquiv₀ x₀)) (add_zero 1) = x
  rw [Ext.mk₀_addEquiv₀_apply]
  exact hx₀

/-- Isomorphic nonsplit pushout middles determine proportional `Ext¹` classes. -/
theorem extClasses_proportional_of_middle_iso
    {K : Type u} [Field K] [IsAlgClosed K] [Algebra K R]
    [Small.{v} R]
    [IsSimpleModule R T] [IsSimpleModule R S]
    [FiniteDimensional K (End (ModuleCat.of R T))]
    [FiniteDimensional K (End (ModuleCat.of R S))]
    (p : P →ₗ[R] S) (hp : Function.Surjective p)
    (f g : LinearMap.ker p →ₗ[R] T)
    (hgne : (shortExact p hp g).extClass ≠ 0)
    (e : ModuleCat.of R (middle p f) ≅ ModuleCat.of R (middle p g)) :
    ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧
      c • (shortExact p hp f).extClass =
        d • (shortExact p hp g).extClass := by
  let Sf := shortComplex p f
  let Sg := shortComplex p g
  let hf := shortExact p hp f
  let hg := shortExact p hp g
  letI : Mono Sf.f := hf.mono_f
  letI : Epi Sf.g := hf.epi_g
  letI : Mono Sg.f := hg.mono_f
  letI : Epi Sg.g := hg.epi_g
  have hcross : Sf.f ≫ e.hom ≫ Sg.g = 0 := by
    by_contra hne
    letI : IsIso (Sf.f ≫ e.hom ≫ Sg.g) :=
      isIso_of_hom_simple hne
    let s : Sg.X₃ ⟶ Sg.X₂ :=
      inv (Sf.f ≫ e.hom ≫ Sg.g) ≫ Sf.f ≫ e.hom
    have hs : s ≫ Sg.g = 𝟙 Sg.X₃ := by
      simp [s, Category.assoc]
    exact hgne (extClass_eq_zero_of_section hg s hs)
  let a₁ : Sf.X₁ ⟶ Sg.X₁ :=
    hg.exact.lift (Sf.f ≫ e.hom) (by simpa [Category.assoc] using hcross)
  have ha₁comm : a₁ ≫ Sg.f = Sf.f ≫ e.hom := by
    exact hg.exact.lift_f _ _
  let a₃ : Sf.X₃ ⟶ Sg.X₃ :=
    hf.exact.desc (e.hom ≫ Sg.g) hcross
  have ha₃comm : Sf.g ≫ a₃ = e.hom ≫ Sg.g := by
    exact hf.exact.g_desc _ _
  have ha₁ne : a₁ ≠ 0 := by
    intro ha₁
    have hcomp : Sf.f ≫ e.hom = 0 := by
      rw [← ha₁comm, ha₁, zero_comp]
    have hSf : Sf.f = 0 := by
      rw [← cancel_mono e.hom]
      simpa using hcomp
    apply id_nonzero Sf.X₁
    rw [← cancel_mono Sf.f]
    simp [hSf]
  have ha₃ne : a₃ ≠ 0 := by
    intro ha₃
    have hcomp : e.hom ≫ Sg.g = 0 := by
      rw [← ha₃comm, ha₃, comp_zero]
    have hSg : Sg.g = 0 := by
      rw [← cancel_epi e.hom]
      simpa using hcomp
    apply id_nonzero Sg.X₃
    rw [← cancel_epi Sg.g]
    simp [hSg]
  letI : IsIso a₁ := isIso_of_hom_simple ha₁ne
  letI : IsIso a₃ := isIso_of_hom_simple ha₃ne
  let φ : Sf ⟶ Sg :=
    { τ₁ := a₁
      τ₂ := e.hom
      τ₃ := a₃
      comm₁₂ := ha₁comm
      comm₂₃ := ha₃comm.symm }
  have hnat :=
    ShortComplex.ShortExact.extClass_naturality hf hg φ
  letI : FiniteDimensional K (Sf.X₁ ⟶ Sf.X₁) :=
    show FiniteDimensional K (End (ModuleCat.of R T)) from inferInstance
  letI : FiniteDimensional K (Sf.X₃ ⟶ Sf.X₃) :=
    show FiniteDimensional K (End (ModuleCat.of R S)) from inferInstance
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id K a₁
  obtain ⟨d, hd⟩ :=
    endomorphism_simple_eq_smul_id K a₃
  have hcne : c ≠ 0 := by
    intro hc0
    apply ha₁ne
    rw [← hc, hc0, zero_smul]
  have hdne : d ≠ 0 := by
    intro hd0
    apply ha₃ne
    rw [← hd, hd0, zero_smul]
  refine ⟨c, d, hcne, hdne, ?_⟩
  dsimp [φ] at hnat
  rw [← hc, ← hd] at hnat
  rw [Ext.mk₀_smul, Ext.comp_smul, Ext.comp_mk₀_id,
    Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] at hnat
  exact hnat

end PushoutExtension

/-! ## Linear and categorical orbit separation -/

theorem affine_parameter_eq_of_proportional
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    {x y : V} (hxy : LinearIndependent K ![x, y])
    {a b c d : K} (hc : c ≠ 0)
    (h : c • (x + a • y) = d • (x + b • y)) :
    a = b := by
  have hcoeff : c = d ∧ c * a = d * b :=
    hxy.eq_of_pair (by simpa [smul_add, smul_smul] using h)
  rw [← hcoeff.1] at hcoeff
  exact mul_left_cancel₀ hc hcoeff.2

def moduleCatIsoOfLinearEquiv
    {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    ModuleCat.of R M ≅ ModuleCat.of R N where
  hom := ModuleCat.ofHom e
  inv := ModuleCat.ofHom e.symm
  hom_inv_id := by
    apply ModuleCat.hom_ext
    ext x
    simp
  inv_hom_id := by
    apply ModuleCat.hom_ext
    ext x
    simp

def moduleCatHomRestrict
    {K R M N : Type u}
    [Field K] [Ring R] [Algebra K R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    [Module K M] [Module K N]
    [IsScalarTower K R M] [IsScalarTower K R N] :
    (ModuleCat.of R M ⟶ ModuleCat.of R N) →ₗ[K]
      (M →ₗ[K] N) where
  toFun f := f.hom.restrictScalars K
  map_add' f g := by
    ext x
    rfl
  map_smul' r f := by
    ext x
    simp only [ModuleCat.hom_smul, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply]
    rfl

theorem moduleCatHomRestrict_injective
    {K R M N : Type u}
    [Field K] [Ring R] [Algebra K R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    [Module K M] [Module K N]
    [IsScalarTower K R M] [IsScalarTower K R N] :
    Function.Injective
      (moduleCatHomRestrict (K := K) (R := R) (M := M) (N := N)) := by
  intro f g h
  apply ModuleCat.hom_ext
  exact LinearMap.restrictScalars_injective (R := K) (S := R) h

theorem moduleFinite_moduleCatHom_of_finiteDimensional
    {K R M N : Type u}
    [Field K] [Ring R] [Algebra K R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    [Module K M] [Module K N]
    [IsScalarTower K R M] [IsScalarTower K R N]
    [FiniteDimensional K M] [FiniteDimensional K N] :
    Module.Finite K
      (ModuleCat.of R M ⟶ ModuleCat.of R N) := by
  exact Module.Finite.of_injective
    (moduleCatHomRestrict (K := K) (R := R) (M := M) (N := N))
    (moduleCatHomRestrict_injective
      (K := K) (R := R) (M := M) (N := N))

/-- `Ext¹` between finite modules over a finite-dimensional algebra is finite-dimensional. -/
theorem moduleFinite_ext_one_of_finiteDimensional
    {K R S T : Type u}
    [Field K] [Ring R] [Small.{u} R] [IsNoetherianRing R]
    [Algebra K R] [FiniteDimensional K R]
    [AddCommGroup S] [AddCommGroup T]
    [Module R S] [Module R T]
    [Module.Finite R S] [Module.Finite R T] :
    Module.Finite K
      (Ext (ModuleCat.of R S) (ModuleCat.of R T) 1) := by
  letI : Module K S := Module.restrictScalars K R S
  letI : Module K T := Module.restrictScalars K R T
  letI : IsScalarTower K R S := IsScalarTower.restrictScalars K R S
  letI : IsScalarTower K R T := IsScalarTower.restrictScalars K R T
  letI : FiniteDimensional K S := Module.Finite.trans R S
  letI : FiniteDimensional K T := Module.Finite.trans R T
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R S
  letI : Module.Finite R (LinearMap.ker p) := by
    rw [Module.Finite.iff_fg]
    exact Submodule.FG.of_le (Module.Finite.fg_top) le_top
  letI : IsScalarTower K R (LinearMap.ker p) :=
    IsScalarTower.of_algebraMap_smul (A := R) (fun r x ↦ by
      apply Subtype.ext
      exact IsScalarTower.algebraMap_smul R r (x : Fin n → R))
  letI : Module.Finite K (LinearMap.ker p) :=
    Module.Finite.trans R (LinearMap.ker p)
  letI : Module.Finite K
      (ModuleCat.of R (LinearMap.ker p) ⟶ ModuleCat.of R T) :=
    moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := R)
  letI : Module.Finite K
      (Ext (ModuleCat.of R (LinearMap.ker p)) (ModuleCat.of R T) 0) :=
    Module.Finite.equiv (Ext.linearEquiv₀ (R := K)).symm
  letI : Projective (ModuleCat.of R (Fin n → R)) :=
    ModuleCat.projective_of_free
      (Module.Free.chooseBasis R (Fin n → R))
  let hbase := LinearMap.shortExact_shortComplexKer hp
  let δ := hbase.extClass.precompOfLinear K (ModuleCat.of R T)
      (add_comm 1 0)
  have hδ : Function.Surjective δ := by
    intro z
    exact Ext.contravariant_sequence_exact₃ hbase (ModuleCat.of R T) z
      (Ext.eq_zero_of_projective _) (rfl : 1 + 0 = 1)
  exact Module.Finite.of_surjective δ hδ

/-! ## The finite-isomorphism-class contradiction -/

theorem finrank_ext_one_le_one_of_finite_skeleton
    {K R S T : Type u} {ι : Type v}
    [Field K] [IsAlgClosed K]
    [Ring R] [Small.{u} R] [IsNoetherianRing R] [IsArtinianRing R]
    [Algebra K R]
    [AddCommGroup S] [AddCommGroup T]
    [Module R S] [Module R T]
    [Module.Finite R S] [Module.Finite R T]
    [IsSimpleModule R S] [IsSimpleModule R T]
    [FiniteDimensional K (End (ModuleCat.of R T))]
    [FiniteDimensional K (End (ModuleCat.of R S))]
    [FiniteDimensional K
      (Ext (ModuleCat.of R S) (ModuleCat.of R T) 1)]
    [Finite ι]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι) :
    Module.finrank K
      (Ext (ModuleCat.of R S) (ModuleCat.of R T) 1) ≤ 1 := by
  let E := Ext (ModuleCat.of R S) (ModuleCat.of R T) 1
  by_contra hle
  change ¬ Module.finrank K E ≤ 1 at hle
  have hdim : 2 ≤ Module.finrank K E := by omega
  letI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by omega) hdim)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  obtain ⟨y, hxy⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank
      (R := K) (M := E) (by omega) hx
  let ξ : K → E := fun a ↦ x + a • y
  have hξne (a : K) : ξ a ≠ 0 := by
    intro ha
    have hcoeff :=
      (LinearIndependent.pair_iff.mp hxy) 1 a (by simpa [ξ] using ha)
    exact one_ne_zero hcoeff.1
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R S
  have hexists (a : K) :
      ∃ f : LinearMap.ker p →ₗ[R] T,
        (PushoutExtension.shortExact p hp f).extClass = ξ a :=
    PushoutExtension.exists_pushout_with_extClass_eq p hp (ξ a)
  let f : K → (LinearMap.ker p →ₗ[R] T) :=
    fun a ↦ (hexists a).choose
  have hfclass (a : K) :
      (PushoutExtension.shortExact p hp (f a)).extClass = ξ a :=
    (hexists a).choose_spec
  let M : K → FGModuleCat.{u} R := fun a ↦
    FGModuleCat.of R (PushoutExtension.middle p (f a))
  have hMindec (a : K) :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (M a) := by
    apply indecomposable_middle_of_extClass_ne_zero
      (PushoutExtension.shortExact p hp (f a))
    rw [hfclass a]
    exact hξne a
  let index : K → ι := fun a ↦
    (σ.complete (M a) (hMindec a)).choose
  let toRep (a : K) : M a ≅ σ.obj (index a) :=
    (σ.complete (M a) (hMindec a)).choose_spec.some
  obtain ⟨a, b, hab, habIndex⟩ :=
    Finite.exists_ne_map_eq_of_infinite index
  have toRepB : M b ≅ σ.obj (index a) := by
    simpa [habIndex] using toRep b
  let eFG : M a ≅ M b := (toRep a).trans toRepB.symm
  let e :
      ModuleCat.of R (PushoutExtension.middle p (f a)) ≅
        ModuleCat.of R (PushoutExtension.middle p (f b)) :=
    moduleCatIsoOfLinearEquiv (FGModuleCat.isoToLinearEquiv eFG)
  obtain ⟨c, d, hc, _hd, hprop⟩ :=
    PushoutExtension.extClasses_proportional_of_middle_iso
      (K := K) (R := R) p hp (f a) (f b)
      (by rw [hfclass b]; exact hξne b) e
  have hab' : a = b := by
    apply affine_parameter_eq_of_proportional hxy hc
    simpa [hfclass a, hfclass b, ξ] using hprop
  exact hab hab'

/-- Paper-facing no-parallel-`Ext¹` theorem for a finite complete right-module skeleton. -/
theorem noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type v} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} Aᵐᵒᵖ ι),
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.NoParallelExtOne σ K := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsArtinianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isArtinianRing_op_of_finiteDimensional K A
  intro ι _ σ s t hs ht
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj s) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (σ.obj t) :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp ht
  letI : Module K (σ.obj s) :=
    Module.restrictScalars K Aᵐᵒᵖ (σ.obj s)
  letI : Module K (σ.obj t) :=
    Module.restrictScalars K Aᵐᵒᵖ (σ.obj t)
  letI : IsScalarTower K Aᵐᵒᵖ (σ.obj s) :=
    IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj s)
  letI : IsScalarTower K Aᵐᵒᵖ (σ.obj t) :=
    IsScalarTower.restrictScalars K Aᵐᵒᵖ (σ.obj t)
  letI : FiniteDimensional K (σ.obj s) :=
    QuotientSubmoduleEquidistribution.finiteDimensional_rightFGModule K A (σ.obj s)
  letI : FiniteDimensional K (σ.obj t) :=
    QuotientSubmoduleEquidistribution.finiteDimensional_rightFGModule K A (σ.obj t)
  letI : FiniteDimensional K
      (End (ModuleCat.of Aᵐᵒᵖ (σ.obj s))) :=
    moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := Aᵐᵒᵖ)
  letI : FiniteDimensional K
      (End (ModuleCat.of Aᵐᵒᵖ (σ.obj t))) :=
    moduleFinite_moduleCatHom_of_finiteDimensional
      (K := K) (R := Aᵐᵒᵖ)
  letI : FiniteDimensional K
      (Ext (ModuleCat.of Aᵐᵒᵖ (σ.obj s))
        (ModuleCat.of Aᵐᵒᵖ (σ.obj t)) 1) :=
    moduleFinite_ext_one_of_finiteDimensional
      (K := K) (R := Aᵐᵒᵖ)
  constructor
  · infer_instance
  · exact finrank_ext_one_le_one_of_finite_skeleton
      (K := K) (R := Aᵐᵒᵖ)
      (S := σ.obj s) (T := σ.obj t) σ

end QuotientSubmoduleEquidistribution.NoParallelExtOne
