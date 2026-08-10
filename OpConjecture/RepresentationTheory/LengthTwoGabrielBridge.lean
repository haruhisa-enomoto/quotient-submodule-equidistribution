import Mathlib.RingTheory.SimpleModule.Isotypic
import OpConjecture.RepresentationTheory.ContravariantTransport
import OpConjecture.RepresentationTheory.LengthTwoPairClosure

/-!
# Radical and isotypic reductions for the length-two pair

This file continues the collective pair-closure reduction.  It keeps the
Gabriel/no-parallel-arrow classification input separate from the
module-theoretic consequences of belonging to `Fac {x, top x}`.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.LengthTwoGabrielBridge

universe u v w

variable {R : Type u} [Ring R]

/--
For an epimorphism out of an Artinian module, the module Jacobson radical
maps onto the Jacobson radical of the target.

Mathlib's generic `Module.map_jacobson_of_ker_le` needs the kernel to lie
in the radical.  The Artinian hypothesis removes that restriction:
the quotient by the image of the source radical is a quotient of the
semisimple top.
-/
theorem map_jacobson_of_surjective_of_isArtinian
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [IsArtinian R M]
    (f : M →ₗ[R] N)
    (hf : Function.Surjective f) :
    Submodule.map f (Module.jacobson R M) =
      Module.jacobson R N := by
  let J : Submodule R M := Module.jacobson R M
  let I : Submodule R N := Submodule.map f J
  apply le_antisymm
  · exact Module.map_jacobson_le f
  · apply Module.jacobson_le_of_eq_bot
    let g : (M ⧸ J) →ₗ[R] (N ⧸ I) :=
      J.mapQ I f (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
    have hg : Function.Surjective g := by
      intro z
      refine Quotient.inductionOn' z ?_
      intro y
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨J.mkQ x, by
        change I.mkQ (f x) = I.mkQ (f x)
        rfl⟩
    letI : IsSemisimpleModule R (M ⧸ J) := by
      rw [IsArtinian.isSemisimpleModule_iff_jacobson]
      exact Module.jacobson_quotient_jacobson R M
    letI : IsSemisimpleModule R (N ⧸ I) :=
      IsSemisimpleModule.of_surjective g hg
    exact IsSemisimpleModule.jacobson_eq_bot R (N ⧸ I)

/--
A finite product of modules is isotypic of type `S` when every component
is.  A simple submodule has a nonzero coordinate projection, and that
projection identifies it with a simple submodule of one component.
-/
theorem isIsotypicOfType_pi
    {J : Type*} [Finite J]
    {M : J → Type*}
    [∀ t, AddCommGroup (M t)]
    [∀ t, Module R (M t)]
    {S : Type*} [AddCommGroup S] [Module R S]
    (hcomponent :
      ∀ t, IsIsotypicOfType R (M t) S) :
    IsIsotypicOfType R (∀ t, M t) S := by
  intro L hL
  letI : IsSimpleModule R L := hL
  letI : Nontrivial L :=
    IsSimpleModule.nontrivial R L
  obtain ⟨z, hz⟩ := exists_ne (0 : L)
  have hzval : z.1 ≠ 0 := by
    intro hzero
    apply hz
    apply Subtype.ext
    exact hzero
  have hcoordinate :
      ∃ t : J, z.1 t ≠ 0 := by
    by_contra h
    push Not at h
    apply hzval
    funext t
    exact h t
  obtain ⟨t, hzt⟩ := hcoordinate
  let f :
      L →ₗ[R] M t :=
    (LinearMap.proj t).comp L.subtype
  have hf : f ≠ 0 := by
    intro hzero
    have hzmap :
        f z = 0 := by rw [hzero]; rfl
    exact hzt hzmap
  have hfinj : Function.Injective f := by
    rcases f.injective_or_eq_zero with hinj | hzero
    · exact hinj
    · exact (hf hzero).elim
  let e :
      L ≃ₗ[R] LinearMap.range f :=
    LinearEquiv.ofInjective f hfinj
  have hrangeSimple :
      IsSimpleModule R (LinearMap.range f) :=
    IsSimpleModule.congr e.symm
  letI : IsSimpleModule R (LinearMap.range f) :=
    hrangeSimple
  obtain ⟨e'⟩ :=
    hcomponent t (LinearMap.range f)
  exact ⟨e.trans e'⟩

/--
An isotypic semisimple module has isotypic quotients.
-/
theorem IsIsotypicOfType.of_surjective_of_semisimple
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {S : Type*} [AddCommGroup S] [Module R S]
    [IsSemisimpleModule R M]
    (hM : IsIsotypicOfType R M S)
    (f : M →ₗ[R] N)
    (hf : Function.Surjective f) :
    IsIsotypicOfType R N S := by
  intro L hL
  letI : IsSimpleModule R L := hL
  obtain ⟨l, hl⟩ :=
    IsSemisimpleModule.lifting_property
      f hf L.subtype
  have hlinj : Function.Injective l := by
    intro x y hxy
    apply L.subtype_injective
    calc
      L.subtype x = f (l x) := by
        have := LinearMap.congr_fun hl x
        simpa using this.symm
      _ = f (l y) := by rw [hxy]
      _ = L.subtype y := by
        have := LinearMap.congr_fun hl y
        simpa using this
  let e :
      L ≃ₗ[R] LinearMap.range l :=
    LinearEquiv.ofInjective l hlinj
  have hrangeSimple :
      IsSimpleModule R (LinearMap.range l) :=
    IsSimpleModule.congr e.symm
  letI : IsSimpleModule R (LinearMap.range l) :=
    hrangeSimple
  obtain ⟨e'⟩ :=
    hM (LinearMap.range l)
  exact ⟨e.trans e'⟩

namespace IndecomposableSkeleton

variable [IsNoetherianRing R]
  {ι : Type v}
  (σ : OpConjecture.IndecomposableSkeleton.{u, v, w} R ι)

/--
The module radical of an indecomposable representative of composition
length two is simple.
-/
theorem moduleRadical_isSimple_of_compositionLength_eq_two
    {x : ι} (hx : σ.compositionLength x = 2) :
    IsSimpleModule R (σ.moduleRadical x) := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  have htotal :
      Module.length R (σ.obj x) = 2 := by
    rw [← σ.coe_compositionLength x, hx]
    norm_num
  have htop :
      IsSimpleModule R (σ.moduleTop x) :=
    OpConjecture.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
      σ hx
  have htopLength :
      Module.length R (σ.moduleTop x) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R (σ.moduleRadical x) +
          Module.length R (σ.moduleTop x) :=
    Module.length_eq_add_of_exact
      (σ.moduleRadical x).subtype
      (σ.moduleRadical x).mkQ
      (σ.moduleRadical x).subtype_injective
      (σ.moduleRadical x).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (σ.moduleRadical x))
  have hradLength :
      Module.length R (σ.moduleRadical x) = 1 := by
    rw [htotal, htopLength] at hlength
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R (σ.moduleRadical x) + 1 = 2 :=
        hlength.symm
      _ = 1 + 1 := by norm_num
  exact Module.length_eq_one_iff.mp hradLength

/--
The radical of a length-two indecomposable is the unique simple
submodule, expressed as a linear equivalence to any selected simple
submodule representative.
-/
theorem moduleRadical_linearEquiv_simpleSubmodule
    {x : ι} (hx : σ.compositionLength x = 2)
    (T : σ.SimpleSubmodule x) :
    Nonempty
      (σ.moduleRadical x ≃ₗ[R] σ.obj T.index) := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  letI : Mono T.map := T.mono
  have hTinj : Function.Injective T.map.hom.hom :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective
      T.map).mp inferInstance
  let A : Submodule R (σ.obj x) :=
    LinearMap.range T.map.hom.hom
  let eA :
      σ.obj T.index ≃ₗ[R] A :=
    LinearEquiv.ofInjective T.map.hom.hom hTinj
  have hAsimple : IsSimpleModule R A := by
    letI : IsSimpleModule R (σ.obj T.index) :=
      (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        _).mp T.simple
    exact IsSimpleModule.congr eA.symm
  have hAlength : Module.length R A = 1 :=
    Module.length_eq_one_iff.mpr hAsimple
  have htotal :
      Module.length R (σ.obj x) = 2 := by
    rw [← σ.coe_compositionLength x, hx]
    norm_num
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R A +
          Module.length R ((σ.obj x) ⧸ A) :=
    Module.length_eq_add_of_exact
      A.subtype A.mkQ A.subtype_injective
      A.mkQ_surjective
      (LinearMap.exact_subtype_mkQ A)
  have hquotLength :
      Module.length R ((σ.obj x) ⧸ A) = 1 := by
    rw [htotal, hAlength] at hlength
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R ((σ.obj x) ⧸ A) = 2 :=
        hlength.symm
      _ = 1 + 1 := by norm_num
  have hAcoatom : IsCoatom A :=
    isSimpleModule_iff_isCoatom.mp
      (Module.length_eq_one_iff.mp hquotLength)
  have hAatom : IsAtom A :=
    isSimpleModule_iff_isAtom.mp hAsimple
  have hradSimple :
      IsSimpleModule R (σ.moduleRadical x) :=
    moduleRadical_isSimple_of_compositionLength_eq_two
      σ hx
  have hradAtom :
      IsAtom (σ.moduleRadical x) :=
    isSimpleModule_iff_isAtom.mp hradSimple
  have hradA :
      σ.moduleRadical x = A := by
    have hle : σ.moduleRadical x ≤ A := by
      change Module.jacobson R (σ.obj x) ≤ A
      exact sInf_le hAcoatom
    rcases hAatom.le_iff.mp hle with
      hbot | heq
    · exact (hradAtom.ne_bot hbot).elim
    · exact heq
  exact ⟨
    (LinearEquiv.ofEq
      (σ.moduleRadical x) A hradA).trans eA.symm⟩

/--
The radical of a finite biproduct is semisimple whenever the radical of
each component is semisimple.

Only the easy inclusion of the radical into the product of the component
radicals is needed: it gives an injection into a semisimple module.
-/
theorem moduleRadical_sumOver_isSemisimple
    (J : FintypeCat.{0}) (a : J → ι)
    (hsemisimple :
      ∀ t : J,
        IsSemisimpleModule R
          (Module.jacobson R (σ.obj (a t)))) :
    IsSemisimpleModule R
      (Module.jacobson R (σ.sumOver J a)) := by
  letI : Fintype J := FintypeCat.fintype
  letI (t : J) :
      IsSemisimpleModule R
        (Module.jacobson R (σ.obj (a t))) :=
    hsemisimple t
  let e :
      σ.sumOver J a ≅
        FGModuleCat.of R (∀ t : J, σ.obj (a t)) :=
    _root_.OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  let sourceRadical :
      Submodule R (σ.sumOver J a) :=
    Module.jacobson R (σ.sumOver J a)
  let componentRadical (t : J) :
      Submodule R (σ.obj (a t)) :=
    Module.jacobson R (σ.obj (a t))
  let coordinate (t : J) :
      sourceRadical →ₗ[R] componentRadical t :=
    ((((LinearMap.proj t :
        (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t))).comp
          e.hom.hom.hom).domRestrict
      sourceRadical).codRestrict
        (componentRadical t) (fun z ↦ by
          apply
            Module.map_jacobson_le
              ((LinearMap.proj t :
                (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t)).comp
                  e.hom.hom.hom)
          exact ⟨z.1, z.2, rfl⟩)
  let diagonal :
      sourceRadical →ₗ[R] (∀ t : J, componentRadical t) :=
    LinearMap.pi coordinate
  have hdiagonal : Function.Injective diagonal := by
    intro z z' hzz'
    apply Subtype.ext
    apply
      (FGModuleCat.isoToLinearEquiv e).injective
    funext t
    exact
      congrArg Subtype.val
        (congrFun hzz' t)
  exact IsSemisimpleModule.of_injective diagonal hdiagonal

/--
The radical of a finite biproduct is isotypic of type `S` whenever the
radical of each component is isotypic of type `S`.
-/
theorem moduleRadical_sumOver_isIsotypicOfType
    (J : FintypeCat.{0}) (a : J → ι)
    {S : Type*} [AddCommGroup S] [Module R S]
    (hisotypic :
      ∀ t : J,
        IsIsotypicOfType R
          (Module.jacobson R (σ.obj (a t))) S) :
    IsIsotypicOfType R
      (Module.jacobson R (σ.sumOver J a)) S := by
  letI : Fintype J := FintypeCat.fintype
  let e :
      σ.sumOver J a ≅
        FGModuleCat.of R (∀ t : J, σ.obj (a t)) :=
    _root_.OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  let sourceRadical :
      Submodule R (σ.sumOver J a) :=
    Module.jacobson R (σ.sumOver J a)
  let componentRadical (t : J) :
      Submodule R (σ.obj (a t)) :=
    Module.jacobson R (σ.obj (a t))
  let coordinate (t : J) :
      sourceRadical →ₗ[R] componentRadical t :=
    ((((LinearMap.proj t :
        (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t))).comp
          e.hom.hom.hom).domRestrict
      sourceRadical).codRestrict
        (componentRadical t) (fun z ↦ by
          apply
            Module.map_jacobson_le
              ((LinearMap.proj t :
                (∀ s : J, σ.obj (a s)) →ₗ[R] σ.obj (a t)).comp
                  e.hom.hom.hom)
          exact ⟨z.1, z.2, rfl⟩)
  let diagonal :
      sourceRadical →ₗ[R] (∀ t : J, componentRadical t) :=
    LinearMap.pi coordinate
  have hdiagonal : Function.Injective diagonal := by
    intro z z' hzz'
    apply Subtype.ext
    apply
      (FGModuleCat.isoToLinearEquiv e).injective
    funext t
    exact
      congrArg Subtype.val
        (congrFun hzz' t)
  have hproduct :
      IsIsotypicOfType R
        (∀ t : J, componentRadical t) S :=
    isIsotypicOfType_pi (fun t ↦ hisotypic t)
  exact hproduct.of_injective diagonal hdiagonal

/--
For a presentation from a length-two object and its chosen simple top,
the radical of the presenting biproduct is semisimple.
-/
theorem facPresentation_sourceRadical_isSemisimple
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    {j : ι}
    (P :
      σ.FacPresentation ({x, Q.index} : Set ι) (σ.obj j)) :
    IsSemisimpleModule R
      (Module.jacobson R (σ.sumOver P.index P.label)) := by
  apply
    moduleRadical_sumOver_isSemisimple
      σ P.index P.label
  intro t
  have hlabel := P.mem t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabel
  rcases hlabel with hlabel | hlabel
  · have hlength :
        σ.compositionLength (P.label t) = 2 := by
      simpa [hlabel] using hx
    letI :
        IsSimpleModule R
          (Module.jacobson R (σ.obj (P.label t))) :=
      moduleRadical_isSimple_of_compositionLength_eq_two
        σ hlength
    infer_instance
  · letI : IsSimpleModule R (σ.obj (P.label t)) :=
      (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (by simpa [hlabel] using Q.simple)
    letI : IsSemisimpleModule R (σ.obj (P.label t)) :=
      inferInstance
    infer_instance

/--
For a presentation from a length-two object and its chosen simple top,
the radical of the presenting biproduct is isotypic of the selected
simple socle type.
-/
theorem facPresentation_sourceRadical_isIsotypicOfType
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (T : σ.SimpleSubmodule x)
    {j : ι}
    (P :
      σ.FacPresentation ({x, Q.index} : Set ι) (σ.obj j)) :
    IsIsotypicOfType R
      (Module.jacobson R (σ.sumOver P.index P.label))
      (σ.obj T.index) := by
  apply
    moduleRadical_sumOver_isIsotypicOfType
      σ P.index P.label
  intro t
  have hlabel := P.mem t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabel
  rcases hlabel with hlabel | hlabel
  · have hlength :
        σ.compositionLength (P.label t) = 2 := by
      simpa [hlabel] using hx
    have hsimple :
        IsSimpleModule R
          (Module.jacobson R (σ.obj (P.label t))) :=
      moduleRadical_isSimple_of_compositionLength_eq_two
        σ hlength
    letI :
        IsSimpleModule R
          (Module.jacobson R (σ.obj (P.label t))) :=
      hsimple
    have erad :
        Nonempty
          (Module.jacobson R (σ.obj (P.label t)) ≃ₗ[R]
            σ.obj T.index) := by
      rw [hlabel]
      exact
        moduleRadical_linearEquiv_simpleSubmodule
          σ hx T
    exact
      (IsIsotypicOfType.of_isSimpleModule R
        (Module.jacobson R (σ.obj (P.label t)))).of_linearEquiv_type
          erad.some
  · have hsimple :
        IsSimpleModule R (σ.obj (P.label t)) :=
      (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        _).mp (by simpa [hlabel] using Q.simple)
    letI : IsSimpleModule R (σ.obj (P.label t)) :=
      hsimple
    have hbot :
        Module.jacobson R (σ.obj (P.label t)) = ⊥ :=
      IsSimpleModule.jacobson_eq_bot R (σ.obj (P.label t))
    letI :
        Subsingleton
          (Module.jacobson R (σ.obj (P.label t))) := by
      rw [Submodule.subsingleton_iff_eq_bot]
      exact hbot
    exact
      IsIsotypicOfType.of_subsingleton
        R
        (Module.jacobson R (σ.obj (P.label t)))
        (σ.obj T.index)

/--
Every indecomposable generated by a length-two object and its chosen
simple top has semisimple module radical.

This is the first half of the Loewy-length-two reduction needed by the
Gabriel argument.  It is unconditional: no finite-type, splitness, or
algebraically-closed hypothesis occurs.
-/
theorem moduleRadical_isSemisimple_of_inFac_length_two_pair
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    {j : ι}
    (hj :
      σ.InFac ({x, Q.index} : Set ι) (σ.obj j)) :
    IsSemisimpleModule R (σ.moduleRadical j) := by
  obtain ⟨P⟩ := hj
  letI (t : P.index) : IsArtinian R (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of R
          (∀ t : P.index, σ.obj (P.label t)) :=
    _root_.OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI :
      IsArtinian R (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  letI :
      IsSemisimpleModule R
        (Module.jacobson R
          (σ.sumOver P.index P.label)) :=
    facPresentation_sourceRadical_isSemisimple σ hx Q P
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
      P.map).mp inferInstance
  have hradical :
      Submodule.map P.map.hom.hom
          (Module.jacobson R
            (σ.sumOver P.index P.label)) =
        σ.moduleRadical j :=
    map_jacobson_of_surjective_of_isArtinian
      P.map.hom.hom hsurj
  let sourceRadical :
      Submodule R (σ.sumOver P.index P.label) :=
    Module.jacobson R (σ.sumOver P.index P.label)
  let targetRadical :
      Submodule R (σ.obj j) :=
    σ.moduleRadical j
  let radicalMap :
      sourceRadical →ₗ[R] targetRadical :=
    (P.map.hom.hom.domRestrict sourceRadical).codRestrict
      targetRadical (fun z ↦ by
        apply Module.map_jacobson_le P.map.hom.hom
        exact ⟨z.1, z.2, rfl⟩)
  have hradicalMap :
      Function.Surjective radicalMap := by
    intro y
    have hy :
        y.1 ∈
          Submodule.map P.map.hom.hom sourceRadical := by
      rw [hradical]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact
    IsSemisimpleModule.of_surjective
      radicalMap hradicalMap

/--
Every indecomposable generated by `{x, top(x)}` has radical isotypic of
the selected simple socle of `x`.
-/
theorem moduleRadical_isIsotypicOfType_of_inFac_length_two_pair
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (T : σ.SimpleSubmodule x)
    {j : ι}
    (hj :
      σ.InFac ({x, Q.index} : Set ι) (σ.obj j)) :
    IsIsotypicOfType R
      (σ.moduleRadical j) (σ.obj T.index) := by
  obtain ⟨P⟩ := hj
  letI (t : P.index) : IsArtinian R (σ.obj (P.label t)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength (P.label t))).2
  let e :
      σ.sumOver P.index P.label ≅
        FGModuleCat.of R
          (∀ t : P.index, σ.obj (P.label t)) :=
    _root_.OpConjecture.IndecomposableSkeleton.biproductIsoPiFG _
  letI :
      IsArtinian R (σ.sumOver P.index P.label) :=
    (LinearEquiv.isArtinian_iff
      (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
  letI :
      IsSemisimpleModule R
        (Module.jacobson R
          (σ.sumOver P.index P.label)) :=
    facPresentation_sourceRadical_isSemisimple σ hx Q P
  have hsourceIsotypic :
      IsIsotypicOfType R
        (Module.jacobson R
          (σ.sumOver P.index P.label))
        (σ.obj T.index) :=
    facPresentation_sourceRadical_isIsotypicOfType
      σ hx Q T P
  letI : Epi P.map := P.epi
  have hsurj : Function.Surjective P.map.hom.hom :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
      P.map).mp inferInstance
  have hradical :
      Submodule.map P.map.hom.hom
          (Module.jacobson R
            (σ.sumOver P.index P.label)) =
        σ.moduleRadical j :=
    map_jacobson_of_surjective_of_isArtinian
      P.map.hom.hom hsurj
  let sourceRadical :
      Submodule R (σ.sumOver P.index P.label) :=
    Module.jacobson R (σ.sumOver P.index P.label)
  let targetRadical :
      Submodule R (σ.obj j) :=
    σ.moduleRadical j
  let radicalMap :
      sourceRadical →ₗ[R] targetRadical :=
    (P.map.hom.hom.domRestrict sourceRadical).codRestrict
      targetRadical (fun z ↦ by
        apply Module.map_jacobson_le P.map.hom.hom
        exact ⟨z.1, z.2, rfl⟩)
  have hradicalMap :
      Function.Surjective radicalMap := by
    intro y
    have hy :
        y.1 ∈
          Submodule.map P.map.hom.hom sourceRadical := by
      rw [hradical]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact
    _root_.OpConjecture.LengthTwoGabrielBridge.IsIsotypicOfType.of_surjective_of_semisimple
      hsourceIsotypic radicalMap hradicalMap

/--
The top of every indecomposable generated by `{x, top(x)}` is isotypic
of the chosen simple top type.

This upgrades the previously compiled statement about simple quotients
of the target to a statement about its whole semisimple top.  It still
does not assert multiplicity one.
-/
theorem moduleTop_isIsotypicOfType_of_inFac_length_two_pair
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    {j : ι}
    (hj :
      σ.InFac ({x, Q.index} : Set ι) (σ.obj j)) :
    IsIsotypicOfType R (σ.moduleTop j) (σ.obj Q.index) := by
  letI : IsSemisimpleModule R (σ.moduleTop j) :=
    σ.moduleTop_isSemisimple j
  intro m hm
  letI : IsSimpleModule R m := hm
  obtain ⟨c, hmc⟩ := exists_isCompl m
  let p :
      σ.moduleTop j →ₗ[R] m :=
    Submodule.projectionOnto m c hmc
  have hp : Function.Surjective p :=
    Submodule.projectionOnto_surjective hmc
  letI : Module.Finite R m :=
    Module.Finite.of_surjective p hp
  let M : FGModuleCat.{w} R :=
    FGModuleCat.of R m
  have hMindec :
      OpConjecture.Foundation.IsIndecomposableModule R M :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨l, ⟨e⟩⟩ :=
    σ.complete M hMindec
  let q :
      σ.obj j →ₗ[R] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  let f :
      σ.obj j ⟶ σ.obj l :=
    FGModuleCat.ofHom
      (e.hom.hom.hom.comp (p.comp q))
  have hfSurj : Function.Surjective f.hom.hom := by
    intro y
    obtain ⟨z, rfl⟩ :=
      (FGModuleCat.isoToLinearEquiv e).surjective y
    obtain ⟨t, rfl⟩ := hp z
    obtain ⟨s, rfl⟩ := (σ.moduleRadical j).mkQ_surjective t
    exact ⟨s, rfl⟩
  letI : Epi f :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective
      f).mpr hfSurj
  have hMsimple : Simple M :=
    (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      M).mpr hm
  have hlsimple : Simple (σ.obj l) :=
    (Simple.iff_of_iso e).mp hMsimple
  let L : σ.SimpleQuotient j := {
    index := l
    simple := hlsimple
    map := f
    epi := inferInstance }
  have hlQ :
      l = Q.index :=
    _root_.OpConjecture.IndecomposableSkeleton.simpleQuotient_index_eq_of_inFac_length_two_pair
      σ hx Q hj L
  subst l
  exact ⟨FGModuleCat.isoToLinearEquiv e⟩

/--
The remaining Gabriel/matrix-classification interface.

It says that an indecomposable whose top and semisimple radical are each
isotypic has simple top.  For a basic finite-dimensional algebra over an
algebraically closed field, representation-finiteness implies this by:

* no parallel Gabriel arrows, hence the relevant `Ext¹` space has
  dimension at most one;
* rank normal form for the single extension matrix.

The `D₄` highest-root module shows why both isotypic hypotheses are
essential: representation-finite indecomposables can have nonsimple top
when their radical has several simple types.
-/
def IsotypicLoewyTwoIndecomposablesHaveSimpleTop : Prop :=
  ∀ {j s t : ι},
    Simple (σ.obj s) →
    Simple (σ.obj t) →
    IsIsotypicOfType R (σ.moduleTop j) (σ.obj s) →
    IsSemisimpleModule R (σ.moduleRadical j) →
    IsIsotypicOfType R (σ.moduleRadical j) (σ.obj t) →
    IsSimpleModule R (σ.moduleTop j)

/--
The Gabriel/matrix interface supplies exactly the outstanding
top-multiplicity-one condition for a length-two pair.
-/
theorem pairFacTargetsHaveSimpleTop_of_isotypicLoewyTwo
    (hclassification :
      IsotypicLoewyTwoIndecomposablesHaveSimpleTop σ)
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (T : σ.SimpleSubmodule x) :
    σ.PairFacTargetsHaveSimpleTop x Q.index := by
  intro j hj
  exact
    hclassification Q.simple T.simple
      (moduleTop_isIsotypicOfType_of_inFac_length_two_pair
        σ hx Q hj)
      (moduleRadical_isSemisimple_of_inFac_length_two_pair
        σ hx Q hj)
      (moduleRadical_isIsotypicOfType_of_inFac_length_two_pair
        σ hx Q T hj)

/--
Conditional closure endpoint with only the standard
isotypic-Loewy-two classification left as input.
-/
theorem qClosure_isClosed_length_two_top_pair_of_isotypicLoewyTwo
    (hclassification :
      IsotypicLoewyTwoIndecomposablesHaveSimpleTop σ)
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (T : σ.SimpleSubmodule x) :
    σ.qClosure.IsClosed ({x, Q.index} : Set ι) :=
  _root_.OpConjecture.IndecomposableSkeleton.qClosure_isClosed_pair_of_targetsHaveSimpleTop
    σ hx Q
      (pairFacTargetsHaveSimpleTop_of_isotypicLoewyTwo
        σ hclassification hx Q T)

end IndecomposableSkeleton

universe uR uS vR vS wR wS

/--
Closedness transfers to the dual pair without any additional module
calculation.  This is the precise route by which the quotient-side
isotypic-Loewy-two theorem yields its submodule-side companion.
-/
theorem AlignedBiduality.sClosure_isClosed_iff_qClosure_image
    {R' : Type uR} [Ring R'] [IsNoetherianRing R']
    {S' : Type uS} [Ring S'] [IsNoetherianRing S']
    {ι' : Type vR} {κ : Type vS}
    (σ' :
      _root_.OpConjecture.IndecomposableSkeleton.{uR, vR, wR}
        R' ι')
    (τ :
      _root_.OpConjecture.IndecomposableSkeleton.{uS, vS, wS}
        S' κ)
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality
        σ' τ)
    (T : Set ι') :
    σ'.sClosure.IsClosed T ↔
      τ.qClosure.IsClosed
        (D.forward.labelEquiv '' T) := by
  constructor
  · intro hT
    apply τ.qClosure.isClosed_iff.2
    change
      τ.qClosure (D.forward.labelEquiv '' T) =
        D.forward.labelEquiv '' T
    rw [←
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality.image_sClosure_eq_qClosure
        σ' τ D T]
    exact congrArg
      (fun U : Set ι' ↦ D.forward.labelEquiv '' U)
      hT.closure_eq
  · intro hT
    apply σ'.sClosure.isClosed_iff.2
    apply D.forward.labelEquiv.injective.image_injective
    change
      D.forward.labelEquiv '' σ'.sClosure T =
        D.forward.labelEquiv '' T
    rw [
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality.image_sClosure_eq_qClosure
        σ' τ D T,
      hT.closure_eq]

/--
The small amount of objectwise data needed to dualize a length-two
submodule pair.  Concrete contragredient duality should construct this:
the dual of the chosen simple submodule is the chosen simple quotient,
and length is preserved.
-/
structure AlignedBiduality.LengthTwoSubPairData
    {R' : Type uR} [Ring R'] [IsNoetherianRing R']
    {S' : Type uS} [Ring S'] [IsNoetherianRing S']
    {ι' : Type vR} {κ : Type vS}
    (σ' :
      _root_.OpConjecture.IndecomposableSkeleton.{uR, vR, wR}
        R' ι')
    (τ :
      _root_.OpConjecture.IndecomposableSkeleton.{uS, vS, wS}
        S' κ)
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality
        σ' τ)
    (x s : ι') where
  length :
    τ.compositionLength (D.forward.labelEquiv x) = 2
  top :
    τ.SimpleQuotient (D.forward.labelEquiv x)
  top_index :
    top.index = D.forward.labelEquiv s
  socle :
    τ.SimpleSubmodule (D.forward.labelEquiv x)

/--
Dual conditional endpoint: once the quotient-side
isotypic-Loewy-two classification is available on the dual category,
the corresponding length-two socle pair is submodule closed.
-/
theorem AlignedBiduality.sClosure_isClosed_length_two_pair_of_dual_isotypicLoewyTwo
    {R' : Type uR} [Ring R'] [IsNoetherianRing R']
    {S' : Type uS} [Ring S'] [IsNoetherianRing S']
    {ι' : Type vR} {κ : Type vS}
    (σ' :
      _root_.OpConjecture.IndecomposableSkeleton.{uR, vR, wR}
        R' ι')
    (τ :
      _root_.OpConjecture.IndecomposableSkeleton.{uS, vS, wS}
        S' κ)
    (D :
      _root_.OpConjecture.IndecomposableSkeleton.AlignedBiduality
        σ' τ)
    {x s : ι'}
    (data : AlignedBiduality.LengthTwoSubPairData
      σ' τ D x s)
    (hclassification :
      IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        τ) :
    σ'.sClosure.IsClosed ({x, s} : Set ι') := by
  rw [
    AlignedBiduality.sClosure_isClosed_iff_qClosure_image
      σ' τ D]
  have hq :=
    IndecomposableSkeleton.qClosure_isClosed_length_two_top_pair_of_isotypicLoewyTwo
      τ hclassification data.length data.top data.socle
  have himage :
      D.forward.labelEquiv '' ({x, s} : Set ι') =
        ({D.forward.labelEquiv x,
          D.forward.labelEquiv s} : Set κ) := by
    rw [Set.image_insert_eq, Set.image_singleton]
  rw [himage]
  simpa [data.top_index] using hq

end OpConjecture.LengthTwoGabrielBridge
