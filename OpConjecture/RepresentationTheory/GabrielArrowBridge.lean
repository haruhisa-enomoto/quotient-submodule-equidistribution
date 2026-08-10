import OpConjecture.RepresentationTheory.LevelTwoUnconditional
import OpConjecture.RepresentationTheory.NoParallelExtOne
import OpConjecture.RepresentationTheory.ExtClassReflection

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace OpConjecture.GabrielArrowBridge

universe u v

variable {K A : Type u} {ι : Type v}
  [Field K] [IsAlgClosed K]
  [Ring A] [Small.{u} A] [IsNoetherianRing A] [IsArtinianRing A]
  [Algebra K A]
  [Finite ι]
  (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} A ι)

abbrev ExtOne (s t : σ.SimpleIndex) :=
  Ext (ModuleCat.of A (σ.obj s.1)) (ModuleCat.of A (σ.obj t.1)) 1

/-- The arrow-support version of the Gabriel quiver.  Under the no-parallel
bound, an arrow is exactly an ordered pair of simple vertices with nonzero
`Ext¹`. -/
def GabrielArrowIndex :=
  {p : σ.SimpleIndex × σ.SimpleIndex // Nontrivial (ExtOne σ p.1 p.2)}

namespace GabrielArrowIndex

/-- Source of an arrow in the support-form Gabriel quiver. -/
def source (a : GabrielArrowIndex σ) : σ.SimpleIndex := a.1.1

/-- Target of an arrow in the support-form Gabriel quiver. -/
def target (a : GabrielArrowIndex σ) : σ.SimpleIndex := a.1.2

omit [IsArtinianRing A] [Finite ι] in
/-- The support-form Gabriel quiver has at most one arrow for each ordered
pair by construction.  Under `NoParallelExtSupport`, this is equivalent to
the usual multiplicity-bearing Ext-Gabriel quiver. -/
theorem source_target_injective :
    Function.Injective fun a : GabrielArrowIndex σ ↦
      (source σ a, target σ a) := by
  intro a b hab
  apply Subtype.ext
  simpa [source, target] using hab

end GabrielArrowIndex

def NoParallelExtSupport : Prop :=
  ∀ s t : σ.SimpleIndex,
    FiniteDimensional K (ExtOne σ s t) ∧
      Module.finrank K (ExtOne σ s t) ≤ 1

/-- A concrete total arrow type for the Ext-Gabriel quiver: the number of
arrows from `s` to `t` is definitionally `dim_K Ext¹(s,t)`. -/
def ExtGabrielArrowIndex :=
  Σ s : σ.SimpleIndex, Σ t : σ.SimpleIndex,
    Fin (Module.finrank K (ExtOne σ s t))

namespace ExtGabrielArrowIndex

/-- Source of an arrow in the multiplicity-bearing Ext-Gabriel quiver. -/
def source (a : ExtGabrielArrowIndex (K := K) σ) : σ.SimpleIndex := a.1

/-- Target of an arrow in the multiplicity-bearing Ext-Gabriel quiver. -/
def target (a : ExtGabrielArrowIndex (K := K) σ) : σ.SimpleIndex := a.2.1

end ExtGabrielArrowIndex

/-- Under the no-parallel bound, the multiplicity-bearing Ext quiver has
one arrow precisely at each nonzero Ext-support pair. -/
def extGabrielArrowEquivSupport
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    ExtGabrielArrowIndex (K := K) σ ≃ GabrielArrowIndex σ where
  toFun a := by
    let s := a.1
    let t := a.2.1
    let k := a.2.2
    letI : FiniteDimensional K (ExtOne σ s t) :=
      (hnoParallel s t).1
    have hpos : 0 < Module.finrank K (ExtOne σ s t) :=
      lt_of_le_of_lt (Nat.zero_le k.1) k.2
    letI : Nontrivial (ExtOne σ s t) :=
      Module.nontrivial_of_finrank_pos hpos
    exact ⟨(s, t), inferInstance⟩
  invFun a := by
    let s := a.1.1
    let t := a.1.2
    letI : FiniteDimensional K (ExtOne σ s t) :=
      (hnoParallel s t).1
    letI : Nontrivial (ExtOne σ s t) := a.2
    exact ⟨s, t, ⟨0, Module.finrank_pos⟩⟩
  left_inv a := by
    rcases a with ⟨s, t, k⟩
    have hpos : 0 < Module.finrank K (ExtOne σ s t) :=
      lt_of_le_of_lt (Nat.zero_le k.1) k.2
    change
      (⟨s, t, ⟨0, hpos⟩⟩ :
        ExtGabrielArrowIndex (K := K) σ) =
        ⟨s, t, k⟩
    congr 1
    congr 1
    apply Fin.ext
    have hk := (hnoParallel s t).2
    omega
  right_inv a := by
    apply Subtype.ext
    rfl

namespace ExtGabrielArrowIndex

omit [IsAlgClosed K] [IsArtinianRing A] [Finite ι] in
/-- Under the no-parallel bound, an Ext-Gabriel arrow is determined by its
ordered pair of endpoints. -/
theorem source_target_injective
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    Function.Injective fun a : ExtGabrielArrowIndex (K := K) σ ↦
      (source σ a, target σ a) := by
  intro a b hab
  apply (extGabrielArrowEquivSupport σ hnoParallel).injective
  apply Subtype.ext
  simpa [source, target, extGabrielArrowEquivSupport] using hab

end ExtGabrielArrowIndex

omit [IsNoetherianRing A] [IsArtinianRing A] in
/-- Vanishing of the derived `Ext¹` class of a short exact sequence
produces a section of its quotient map. -/
theorem exists_section_of_extClass_eq_zero
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    (hzero : hS.extClass = 0) :
    ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  have hobstruction :
      (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (rfl : 0 + 1 = 1) = 0 := by
    rw [hzero, Ext.comp_zero]
  obtain ⟨x₂, hx₂⟩ :=
    Ext.covariant_sequence_exact₃
      (X := S.X₃) hS (Ext.mk₀ (𝟙 S.X₃))
      (rfl : 0 + 1 = 1) hobstruction
  let s : S.X₃ ⟶ S.X₂ := Ext.addEquiv₀ x₂
  refine ⟨s, ?_⟩
  apply (Ext.mk₀_bijective S.X₃ S.X₃).1
  rw [← Ext.mk₀_comp_mk₀]
  simpa [s] using hx₂

omit [IsNoetherianRing A] [IsArtinianRing A] in
/-- A short exact sequence with indecomposable middle and nonzero ends has
nonzero `Ext¹` class. -/
theorem extClass_ne_zero_of_indec_middle
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact)
    [Nontrivial S.X₁] [Nontrivial S.X₃]
    (hM : OpConjecture.Foundation.IsIndecomposableModule A S.X₂) :
    hS.extClass ≠ 0 := by
  intro hzero
  obtain ⟨s, hs⟩ := exists_section_of_extClass_eq_zero hS hzero
  let p : Module.End A S.X₂ := s.hom.comp S.g.hom
  have hp : IsIdempotentElem p := by
    change p * p = p
    rw [Module.End.mul_eq_comp]
    ext z
    have hs' := congrArg (fun q : S.X₃ ⟶ S.X₃ ↦ q.hom) hs
    simpa [p, LinearMap.comp_apply] using
      congrArg s.hom (LinearMap.congr_fun hs' (S.g.hom z))
  rcases hM.eq_zero_or_eq_one_of_isIdempotentElem hp with hp₀ | hp₁
  · have hp₀cat : S.g ≫ s = 0 := by
      apply ModuleCat.hom_ext
      exact hp₀
    have hs₀ : s = 0 := by
      calc
        s = (𝟙 S.X₃) ≫ s := by simp
        _ = (s ≫ S.g) ≫ s := by rw [hs]
        _ = s ≫ (S.g ≫ s) := Category.assoc _ _ _
        _ = 0 := by rw [hp₀cat, comp_zero]
    have hid : 𝟙 S.X₃ = 0 := by rw [← hs]; simp [hs₀]
    obtain ⟨z, hz⟩ := exists_ne (0 : S.X₃)
    apply hz
    have happ := congrArg (fun q : S.X₃ ⟶ S.X₃ ↦ q.hom z) hid
    simpa using happ
  · have hp₁cat : S.g ≫ s = 𝟙 S.X₂ := by
      apply ModuleCat.hom_ext
      simpa [Module.End.one_eq_id] using hp₁
    have hf₀ : S.f = 0 := by
      calc
        S.f = S.f ≫ 𝟙 S.X₂ := by simp
        _ = S.f ≫ (S.g ≫ s) := by rw [hp₁cat]
        _ = (S.f ≫ S.g) ≫ s := (Category.assoc _ _ _).symm
        _ = 0 := by rw [S.zero, zero_comp]
    letI : Mono S.f := hS.mono_f
    have hid : 𝟙 S.X₁ = 0 := by
      rw [← cancel_mono S.f]
      simp [hf₀]
    obtain ⟨z, hz⟩ := exists_ne (0 : S.X₁)
    apply hz
    have happ := congrArg (fun q : S.X₁ ⟶ S.X₁ ↦ q.hom z) hid
    simpa using happ

namespace LengthTwo

def quotient (x : σ.LengthTwoIndex) : σ.SimpleQuotient x.1 :=
  Classical.choice (σ.exists_simpleQuotient x.1)

def submodule (x : σ.LengthTwoIndex) : σ.SimpleSubmodule x.1 :=
  Classical.choice (σ.exists_simpleSubmodule x.1)

def source (x : σ.LengthTwoIndex) : σ.SimpleIndex :=
  ⟨(quotient σ x).index, (quotient σ x).simple⟩

def target (x : σ.LengthTwoIndex) : σ.SimpleIndex :=
  ⟨(submodule σ x).index, (submodule σ x).simple⟩

private def topLinearEquiv (x : σ.LengthTwoIndex) :
    σ.moduleTop x.1 ≃ₗ[A] σ.obj (source σ x).1 := by
  let Q := quotient σ x
  letI : IsArtinian A (σ.obj x.1) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x.1)).2
  letI : IsSimpleModule A (σ.obj Q.index) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      Q.simple
  letI : Epi Q.map := Q.epi
  have hsurj : Function.Surjective Q.map.hom.hom :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective Q.map).mp
      inferInstance
  have htop : IsSimpleModule A (σ.moduleTop x.1) :=
    OpConjecture.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
      σ x.2
  have hradCoatom : IsCoatom (σ.moduleRadical x.1) :=
    isSimpleModule_iff_isCoatom.mp htop
  have hkerCoatom : IsCoatom (LinearMap.ker Q.map.hom.hom) :=
    LinearMap.isCoatom_ker_of_surjective hsurj
  have hradKer :
      σ.moduleRadical x.1 = LinearMap.ker Q.map.hom.hom := by
    exact
      ((hradCoatom.le_iff_eq hkerCoatom.ne_top).mp
        (sInf_le hkerCoatom)).symm
  exact
    (Submodule.quotEquivOfEq
      (σ.moduleRadical x.1) (LinearMap.ker Q.map.hom.hom) hradKer).trans
      (Q.map.hom.hom.quotKerEquivOfSurjective hsurj)

private def radicalLinearEquiv (x : σ.LengthTwoIndex) :
    σ.obj (target σ x).1 ≃ₗ[A] σ.moduleRadical x.1 :=
  (Classical.choice
    (OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_linearEquiv_simpleSubmodule
      σ x.2 (submodule σ x))).symm

def shortComplex (x : σ.LengthTwoIndex) :
    ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfConj
    (radicalLinearEquiv σ x)
    (LinearEquiv.refl A (σ.obj x.1))
    (topLinearEquiv σ x).symm
    (σ.moduleRadical x.1).subtype
    (σ.moduleRadical x.1).mkQ
    (LinearMap.exact_subtype_mkQ
      (σ.moduleRadical x.1)).linearMap_comp_eq_zero

omit [Small A] [IsArtinianRing A] [Finite ι] in
theorem shortExact (x : σ.LengthTwoIndex) :
    (shortComplex σ x).ShortExact :=
  ModuleCat.shortComplexOfConj_shortExact
    (radicalLinearEquiv σ x)
    (LinearEquiv.refl A (σ.obj x.1))
    (topLinearEquiv σ x).symm
    (σ.moduleRadical x.1).subtype
    (σ.moduleRadical x.1).mkQ
    (LinearMap.exact_subtype_mkQ (σ.moduleRadical x.1))
    (σ.moduleRadical x.1).subtype_injective
    (σ.moduleRadical x.1).mkQ_surjective

def extensionClass (x : σ.LengthTwoIndex) :
    ExtOne σ (source σ x) (target σ x) :=
  (shortExact σ x).extClass

omit [IsArtinianRing A] [Finite ι] in
theorem extensionClass_ne_zero (x : σ.LengthTwoIndex) :
    extensionClass σ x ≠ 0 := by
  let Q := quotient σ x
  let T := submodule σ x
  letI : IsSimpleModule A (σ.obj Q.index) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      Q.simple
  letI : IsSimpleModule A (σ.obj T.index) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      T.simple
  letI : Nontrivial (shortComplex σ x).X₁ := by
    dsimp [shortComplex, radicalLinearEquiv, target, submodule, T]
    exact (σ.indecomposable _).nontrivial
  letI : Nontrivial (shortComplex σ x).X₃ := by
    dsimp [shortComplex, topLinearEquiv, source, quotient, Q]
    exact (σ.indecomposable _).nontrivial
  exact extClass_ne_zero_of_indec_middle
    (shortExact σ x) (σ.indecomposable x.1)

def toGabrielArrow (x : σ.LengthTwoIndex) : GabrielArrowIndex σ :=
  ⟨(source σ x, target σ x),
    ⟨extensionClass σ x, 0, extensionClass_ne_zero σ x⟩⟩

omit [IsAlgClosed K] [IsArtinianRing A] [Finite ι] in
theorem toGabrielArrow_injective
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    Function.Injective (toGabrielArrow σ) := by
  intro x y hxy
  have hpairs :
      (source σ x, target σ x) =
        (source σ y, target σ y) :=
    congrArg Subtype.val hxy
  have hs : source σ x = source σ y :=
    congrArg Prod.fst hpairs
  have ht : target σ x = target σ y :=
    congrArg Prod.snd hpairs
  let S₁ := shortComplex σ x
  let S₂ := shortComplex σ y
  let h₁ := shortExact σ x
  let h₂ := shortExact σ y
  have hX₁ : S₁.X₁ = S₂.X₁ := by
    dsimp [S₁, S₂, shortComplex, radicalLinearEquiv, target, submodule]
    exact congrArg (fun z : σ.SimpleIndex ↦ ModuleCat.of A (σ.obj z.1)) ht
  have hX₃ : S₁.X₃ = S₂.X₃ := by
    dsimp [S₁, S₂, shortComplex, topLinearEquiv, source, quotient]
    exact congrArg (fun z : σ.SimpleIndex ↦ ModuleCat.of A (σ.obj z.1)) hs
  let b₁ : S₁.X₁ ⟶ S₂.X₁ := eqToHom hX₁
  let b₃ : S₁.X₃ ⟶ S₂.X₃ := eqToHom hX₃
  let ξ : Ext S₁.X₃ S₂.X₁ 1 :=
    h₁.extClass.comp (Ext.mk₀ b₁) (add_zero 1)
  let η : Ext S₁.X₃ S₂.X₁ 1 :=
    (Ext.mk₀ b₃).comp h₂.extClass (zero_add 1)
  obtain ⟨hfinite, hle⟩ :=
    hnoParallel (source σ x) (target σ y)
  letI : FiniteDimensional K (Ext S₁.X₃ S₂.X₁ 1) := by
    dsimp [S₁, S₂, shortComplex, topLinearEquiv,
      radicalLinearEquiv, source, target, quotient, submodule]
    exact hfinite
  have hξne : ξ ≠ 0 := by
    intro hzero
    apply extensionClass_ne_zero σ x
    have h := congrArg
      (fun z : Ext S₁.X₃ S₂.X₁ 1 ↦
        z.comp (Ext.mk₀ (inv b₁)) (add_zero 1)) hzero
    dsimp [ξ] at h
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] at h
    change h₁.extClass = 0
    simpa using h
  have hηne : η ≠ 0 := by
    intro hzero
    apply extensionClass_ne_zero σ y
    have h := congrArg
      (fun z : Ext S₁.X₃ S₂.X₁ 1 ↦
        (Ext.mk₀ (inv b₃)).comp z (zero_add 1)) hzero
    dsimp [η] at h
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] at h
    change h₂.extClass = 0
    simpa using h
  have hdim :
      Module.finrank K (Ext S₁.X₃ S₂.X₁ 1) = 1 := by
    letI : Nontrivial (Ext S₁.X₃ S₂.X₁ 1) :=
      ⟨ξ, 0, hξne⟩
    have hpos : 0 < Module.finrank K
        (Ext S₁.X₃ S₂.X₁ 1) :=
      Module.finrank_pos
    have hle' : Module.finrank K
        (Ext S₁.X₃ S₂.X₁ 1) ≤ 1 := by
      dsimp [S₁, S₂, shortComplex, topLinearEquiv,
        radicalLinearEquiv, source, target, quotient, submodule]
      exact hle
    omega
  obtain ⟨c, hcclass⟩ :=
    exists_smul_eq_of_finrank_eq_one hdim hξne η
  have hc : c ≠ 0 := by
    intro hc₀
    apply hηne
    rw [← hcclass, hc₀, zero_smul]
  let a₁ : S₁.X₁ ⟶ S₂.X₁ := c • b₁
  let a₃ : S₁.X₃ ⟶ S₂.X₃ := b₃
  have hcompat :
      h₁.extClass.comp (Ext.mk₀ a₁) (add_zero 1) =
        (Ext.mk₀ a₃).comp h₂.extClass (zero_add 1) := by
    dsimp [a₁, a₃, ξ, η]
    rw [Ext.mk₀_smul, Ext.comp_smul]
    exact hcclass
  obtain ⟨a₂, ha₁₂, ha₂₃⟩ :=
    OpConjecture.YonedaExtReflection.exists_middle_morphism_of_extClass_compatibility
      h₁ h₂ a₁ a₃ hcompat
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := a₁
      τ₂ := a₂
      τ₃ := a₃
      comm₁₂ := ha₁₂
      comm₂₃ := ha₂₃ }
  letI : Simple S₁.X₁ := by
    letI : IsSimpleModule A (σ.obj (target σ x).1) :=
      (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (target σ x).2
    change Simple (σ.obj (target σ x).1).obj
    exact (simple_iff_isSimpleModule' _).mpr inferInstance
  letI : Simple S₂.X₁ := by
    letI : IsSimpleModule A (σ.obj (target σ y).1) :=
      (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (target σ y).2
    change Simple (σ.obj (target σ y).1).obj
    exact (simple_iff_isSimpleModule' _).mpr inferInstance
  letI : IsIso b₁ := by dsimp [b₁]; infer_instance
  have hb₁ne : b₁ ≠ 0 := by
    intro hb₁
    apply CategoryTheory.id_nonzero S₁.X₁
    calc
      𝟙 S₁.X₁ = b₁ ≫ inv b₁ := (IsIso.hom_inv_id b₁).symm
      _ = (0 : S₁.X₁ ⟶ S₂.X₁) ≫ inv b₁ :=
        congrArg (fun q : S₁.X₁ ⟶ S₂.X₁ ↦ q ≫ inv b₁) hb₁
      _ = 0 := zero_comp
  have ha₁ne : a₁ ≠ 0 := by
    dsimp [a₁]
    exact smul_ne_zero hc hb₁ne
  letI : IsIso a₁ := isIso_of_hom_simple ha₁ne
  letI : IsIso a₃ := by dsimp [a₃]; infer_instance
  letI : IsIso φ.τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂
  let e : S₁.X₂ ≅ S₂.X₂ := asIso φ.τ₂
  apply Subtype.ext
  apply σ.eq_of_iso
  let eLinear : σ.obj x.1 ≃ₗ[A] σ.obj y.1 := by
    change S₁.X₂ ≃ₗ[A] S₂.X₂
    exact e.toLinearEquiv
  exact ⟨eLinear.toFGModuleCatIso⟩

omit [Finite ι] in
theorem toGabrielArrow_surjective :
    Function.Surjective (toGabrielArrow σ) := by
  intro a
  let s : σ.SimpleIndex := a.1.1
  let t : σ.SimpleIndex := a.1.2
  let E := ExtOne σ s t
  letI : Nontrivial E := a.2
  obtain ⟨ξ, hξne⟩ := exists_ne (0 : E)
  letI : IsSimpleModule A (σ.obj s.1) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      s.2
  letI : IsSimpleModule A (σ.obj t.1) :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      t.2
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A (σ.obj s.1)
  obtain ⟨f, hfclass⟩ :=
    OpConjecture.NoParallelExtOne.PushoutExtension.exists_pushout_with_extClass_eq
      p hp ξ
  let M : FGModuleCat.{u} A :=
    FGModuleCat.of A
      (OpConjecture.NoParallelExtOne.PushoutExtension.middle p f)
  have hMindec : OpConjecture.Foundation.IsIndecomposableModule A M := by
    apply OpConjecture.NoParallelExtOne.indecomposable_middle_of_extClass_ne_zero
      (OpConjecture.NoParallelExtOne.PushoutExtension.shortExact p hp f)
    rw [hfclass]
    exact hξne
  obtain ⟨j, ⟨e⟩⟩ := σ.complete M hMindec
  let S := OpConjecture.NoParallelExtOne.PushoutExtension.shortComplex p f
  let hshort : S.ShortExact :=
    OpConjecture.NoParallelExtOne.PushoutExtension.shortExact p hp f
  have hlengthM : Module.length A M = 2 := by
    rw [Module.length_eq_add_of_exact
      S.f.hom S.g.hom
      hshort.moduleCat_injective_f hshort.moduleCat_surjective_g]
    · rw [Module.length_eq_one_iff.mpr
          (inferInstance : IsSimpleModule A (σ.obj t.1)),
        Module.length_eq_one_iff.mpr
          (inferInstance : IsSimpleModule A (σ.obj s.1))]
      norm_num
    · exact
        (LinearMap.exact_iff.mpr hshort.exact.moduleCat_range_eq_ker.symm)
  have hj : σ.compositionLength j = 2 := by
    rw [← ENat.coe_inj, σ.coe_compositionLength]
    calc
      Module.length A (σ.obj j) = Module.length A M :=
        (LinearEquiv.length_eq (FGModuleCat.isoToLinearEquiv e)).symm
      _ = 2 := hlengthM
      _ = (2 : ℕ∞) := rfl
  let qLinear : σ.obj j →ₗ[A] σ.obj s.1 :=
    (OpConjecture.NoParallelExtOne.PushoutExtension.projection p f).comp
      (FGModuleCat.isoToLinearEquiv e).symm.toLinearMap
  have hqSurj : Function.Surjective qLinear := by
    intro z
    obtain ⟨m, hm⟩ :=
      OpConjecture.NoParallelExtOne.PushoutExtension.projection_surjective
        p hp f z
    refine ⟨(FGModuleCat.isoToLinearEquiv e) m, ?_⟩
    simpa [qLinear] using hm
  let qMap : σ.obj j ⟶ σ.obj s.1 := FGModuleCat.ofHom qLinear
  let Q : σ.SimpleQuotient j :=
    { index := s.1
      simple := s.2
      map := qMap
      epi :=
        (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective qMap).mpr
          hqSurj }
  let mLinear : σ.obj t.1 →ₗ[A] σ.obj j :=
    (FGModuleCat.isoToLinearEquiv e).toLinearMap.comp
      (OpConjecture.NoParallelExtOne.PushoutExtension.inclusion p f)
  have hmInj : Function.Injective mLinear :=
    (FGModuleCat.isoToLinearEquiv e).injective.comp
      (OpConjecture.NoParallelExtOne.PushoutExtension.inclusion_injective p f)
  let mMap : σ.obj t.1 ⟶ σ.obj j := FGModuleCat.ofHom mLinear
  let T : σ.SimpleSubmodule j :=
    { index := t.1
      simple := t.2
      map := mMap
      mono :=
        (_root_.OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective mMap).mpr
          hmInj }
  let x : σ.LengthTwoIndex := ⟨j, hj⟩
  have hsource : source σ x = s := by
    apply Subtype.ext
    exact
      _root_.OpConjecture.IndecomposableSkeleton.SimpleQuotient.index_eq_of_compositionLength_eq_two
        σ hj (quotient σ x) Q
  have htarget : target σ x = t := by
    apply Subtype.ext
    exact
      _root_.OpConjecture.IndecomposableSkeleton.SimpleSubmodule.index_eq_of_compositionLength_eq_two
        σ hj (submodule σ x) T
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact Prod.ext hsource htarget

def lengthTwoEquivGabrielArrow
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    σ.LengthTwoIndex ≃ GabrielArrowIndex σ :=
  Equiv.ofBijective (toGabrielArrow σ)
    ⟨toGabrielArrow_injective σ hnoParallel,
      toGabrielArrow_surjective σ⟩

/-- With multiplicities restored, length-two indecomposables are the arrows
of the Ext-definition of the Gabriel quiver. -/
def lengthTwoEquivExtGabrielArrow
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    σ.LengthTwoIndex ≃ ExtGabrielArrowIndex (K := K) σ :=
  Equiv.trans
    (lengthTwoEquivGabrielArrow σ hnoParallel)
    (extGabrielArrowEquivSupport σ hnoParallel).symm

omit [IsAlgClosed K] [Finite ι] in
theorem natCard_lengthTwoIndex_eq_gabrielArrowIndex
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    Nat.card σ.LengthTwoIndex = Nat.card (GabrielArrowIndex σ) :=
  Nat.card_congr (lengthTwoEquivGabrielArrow σ hnoParallel)

omit [IsAlgClosed K] [Finite ι] in
theorem natCard_lengthTwoIndex_eq_extGabrielArrowIndex
    (hnoParallel : NoParallelExtSupport (K := K) σ) :
    Nat.card σ.LengthTwoIndex =
      Nat.card (ExtGabrielArrowIndex (K := K) σ) :=
  Nat.card_congr (lengthTwoEquivExtGabrielArrow σ hnoParallel)

end LengthTwo

/-- The number of nonzero Ext-support pairs, which agrees with the arrow
count under the no-parallel hypothesis. -/
def gabrielArrowSupportCount : ℕ :=
  Nat.card (GabrielArrowIndex σ)

/-- The arrow count of the Gabriel quiver in its standard Ext-definition:
the multiplicity from `s` to `t` is `dim_K Ext¹(s,t)`. -/
def gabrielArrowCount : ℕ :=
  Nat.card (ExtGabrielArrowIndex (K := K) σ)

namespace RightModules

variable (K B : Type u)
  [Field K] [IsAlgClosed K]
  [Ring B] [Algebra K B] [FiniteDimensional K B]

theorem noParallelExtSupport_of_finiteDimensional_of_finiteSkeleton :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
    ∀ {ι : Type v} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ ι),
      NoParallelExtSupport (K := K) σ := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
  intro ι _ σ s t
  exact
    OpConjecture.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
      K B σ s.2 t.2

theorem natCard_lengthTwoIndex_eq_gabrielArrowCount :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
    ∀ {ι : Type v} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} Bᵐᵒᵖ ι),
      Nat.card σ.LengthTwoIndex =
        gabrielArrowCount (K := K) σ := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
  letI : IsArtinianRing Bᵐᵒᵖ :=
    OpConjecture.isArtinianRing_op_of_finiteDimensional K B
  intro ι _ σ
  exact
    LengthTwo.natCard_lengthTwoIndex_eq_extGabrielArrowIndex σ
      (noParallelExtSupport_of_finiteDimensional_of_finiteSkeleton K B σ)

theorem qLevelCount_two_formula_gabrielArrowCount :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι),
      σ.qClosure.levelCount 2 =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) σ := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
  intro ι _ σ
  rw [OpConjecture.LevelTwoUnconditional.qLevelCount_two_formula_of_finiteDimensional_of_finiteSkeleton
      K B σ,
    natCard_lengthTwoIndex_eq_gabrielArrowCount K B σ]

theorem sLevelCount_two_formula_gabrielArrowCount :
    letI : IsNoetherianRing Bᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
    ∀ {ι : Type u} [Finite ι]
      (σ : OpConjecture.IndecomposableSkeleton.{u, u, u} Bᵐᵒᵖ ι),
      σ.sClosure.levelCount 2 =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) σ := by
  letI : IsNoetherianRing Bᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K B
  intro ι _ σ
  rw [OpConjecture.LevelTwoUnconditional.sLevelCount_two_formula_of_finiteDimensional_of_finiteSkeleton
      K B σ,
    natCard_lengthTwoIndex_eq_gabrielArrowCount K B σ]

/-- Paper-facing canonical form of the bottom level-two formula.  The
displayed vertex and arrow counts use one fixed same-universe relabeling of
the canonical complete right-module skeleton; aligned level-polynomial
invariance transports both canonical closure counts to that model. -/
theorem qAndSLevelCount_two_formula_gabrielArrowCount_of_rightRepresentationFinite
    (K A : Type u)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : OpConjecture.IsRightRepresentationFinite.{u, u, u} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
    let κ :=
      OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ
    letI : Finite κ := hrep
    letI : Fintype κ := Fintype.ofFinite κ
    let σ :=
      OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
    let ι := ULift.{u} (Fin (Fintype.card κ))
    let e : ι ≃ κ :=
      Equiv.ulift.trans (Fintype.equivFin κ).symm
    let τ :
        OpConjecture.IndecomposableSkeleton.{u, u, u}
          Aᵐᵒᵖ ι :=
      OpConjecture.LevelTwoUnconditional.relabelIndecomposableSkeleton σ e
    (σ.qClosure.levelCount 2 =
        Nat.choose (Nat.card τ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) τ) ∧
      (σ.sClosure.levelCount 2 =
        Nat.choose (Nat.card τ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) τ) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    OpConjecture.isNoetherianRing_op_of_finiteDimensional K A
  let κ :=
    OpConjecture.CanonicalIndecomposableIndex.{u, u} Aᵐᵒᵖ
  letI : Finite κ := hrep
  letI : Fintype κ := Fintype.ofFinite κ
  let σ :=
    OpConjecture.rightIndecomposableSkeleton.{u, u, u} K A
  let ι := ULift.{u} (Fin (Fintype.card κ))
  let e : ι ≃ κ :=
    Equiv.ulift.trans (Fintype.equivFin κ).symm
  let τ :
      OpConjecture.IndecomposableSkeleton.{u, u, u}
        Aᵐᵒᵖ ι :=
    OpConjecture.LevelTwoUnconditional.relabelIndecomposableSkeleton σ e
  let E :
      OpConjecture.IndecomposableSkeleton.AlignedEquivalence σ τ :=
    OpConjecture.LevelTwoUnconditional.relabelAlignedEquivalence σ e
  have hqτ :
      τ.qClosure.levelCount 2 =
        Nat.choose (Nat.card τ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) τ :=
    qLevelCount_two_formula_gabrielArrowCount K A τ
  have hsτ :
      τ.sClosure.levelCount 2 =
        Nat.choose (Nat.card τ.SimpleIndex) 2 +
          gabrielArrowCount (K := K) τ :=
    sLevelCount_two_formula_gabrielArrowCount K A τ
  have hqPoly :
      σ.qClosure.levelPolynomial =
        τ.qClosure.levelPolynomial :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      σ τ E
  have hsPoly :
      σ.sClosure.levelPolynomial =
        τ.sClosure.levelPolynomial :=
    OpConjecture.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      σ τ E
  have hqLevel :
      σ.qClosure.levelCount 2 = τ.qClosure.levelCount 2 := by
    calc
      σ.qClosure.levelCount 2 =
          σ.qClosure.levelPolynomial.coeff 2 := by
        rw [OpConjecture.SetClosure.levelPolynomial_coeff]
      _ = τ.qClosure.levelPolynomial.coeff 2 :=
        congrArg (fun p ↦ p.coeff 2) hqPoly
      _ = τ.qClosure.levelCount 2 :=
        OpConjecture.SetClosure.levelPolynomial_coeff _ _
  have hsLevel :
      σ.sClosure.levelCount 2 = τ.sClosure.levelCount 2 := by
    calc
      σ.sClosure.levelCount 2 =
          σ.sClosure.levelPolynomial.coeff 2 := by
        rw [OpConjecture.SetClosure.levelPolynomial_coeff]
      _ = τ.sClosure.levelPolynomial.coeff 2 :=
        congrArg (fun p ↦ p.coeff 2) hsPoly
      _ = τ.sClosure.levelCount 2 :=
        OpConjecture.SetClosure.levelPolynomial_coeff _ _
  exact ⟨hqLevel.trans hqτ, hsLevel.trans hsτ⟩

end RightModules

end OpConjecture.GabrielArrowBridge
