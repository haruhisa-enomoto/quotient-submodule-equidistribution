import QuotientSubmoduleEquidistribution.RepresentationTheory.RingelImageQuotient

/-!
# Equivalence of Ringel's image quotient

This file proves the density, fullness, and faithfulness of the maintained
functor from strongly exact projective complexes modulo Ringel's null system
to torsionless modules modulo projectives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace QuotientSubmoduleEquidistribution.RingelEta

universe u u'

open QuotientSubmoduleEquidistribution.RingelStable
open QuotientSubmoduleEquidistribution.RingelStable.FaithfulCoreAdapter

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {S : Type u'} [Ring S] [IsNoetherianRing S]

private lemma fullSubcategory_add_hom
    {C : Type*} [Category C] [Preadditive C]
    {P : ObjectProperty C} {X Y : P.FullSubcategory}
    (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := by
  rfl

omit [IsNoetherianRing R] in
/-- Every finitely generated module admits a finite projective
presentation. -/
private theorem finiteProjectivePresentation_nonempty
    (X : FGModuleCat.{u} R) : Nonempty (ProjectivePresentation X) := by
  classical
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R X
  let P : FGModuleCat.{u} R := FGModuleCat.of R (Fin n → R)
  let q : P ⟶ X := FGModuleCat.ofHom p
  have hP : Projective P := by
    apply fgProjective_of_moduleProjective
    exact Module.Projective.of_basis (Pi.basisFun R (Fin n))
  have hq : Epi q :=
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).2 hp
  exact ⟨{ p := P, projective := hP, f := q, epi := hq }⟩

omit [IsNoetherianRing R] in
/-- A chosen finite projective presentation. -/
private def finiteProjectivePresentation
    (X : FGModuleCat.{u} R) : ProjectivePresentation X :=
  Classical.choice (finiteProjectivePresentation_nonempty X)

set_option backward.isDefEq.respectTransparency false in
/-- An epimorphic cover of the kernel remains exact after composing the
quotient map with a monomorphism. -/
private theorem exact_projective_kernel_cover_comp_mono
    {C : Type u} [Category C] [Abelian C]
    {P₁ P₀ M Q : C} (p : P₀ ⟶ M) [Epi p]
    (e : P₁ ⟶ kernel p) [Epi e]
    (j : M ⟶ Q) [Mono j] :
    (ShortComplex.mk (e ≫ kernel.ι p) (p ≫ j) (by simp)).Exact := by
  let kp : KernelFork (p ≫ j) :=
    KernelFork.ofι (kernel.ι p) (by simp)
  let hkp : IsLimit kp :=
    isKernelCompMono (kernelIsKernel p) j rfl
  let ek : kernel p ≅ kernel (p ≫ j) :=
    hkp.conePointUniqueUpToIso
      (limit.isLimit (parallelPair (p ≫ j) 0))
  have hek : ek.hom ≫ kernel.ι (p ≫ j) = kernel.ι p := by
    simp [ek, kp]
  have hlift :
      e ≫ ek.hom =
        kernel.lift (p ≫ j) (e ≫ kernel.ι p) (by simp) := by
    apply (cancel_mono (kernel.ι (p ≫ j))).1
    rw [Category.assoc, hek, kernel.lift_ι]
  apply (ShortComplex.exact_iff_epi_kernel_lift _).2
  rw [← hlift]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The map induced on images commutes with the image inclusions. -/
theorem ringelImage_map_comp_image_ι
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    {X Y : StronglyExactComplexCategory H} (f : X ⟶ Y) :
    (ringelImageFunctor H).map f ≫
        Abelian.image.ι ((stronglyExactUnderlyingFunctor H).obj Y).g =
      Abelian.image.ι ((stronglyExactUnderlyingFunctor H).obj X).g ≫
        ((stronglyExactUnderlyingFunctor H).map f).τ₃ := by
  simp [ringelImageFunctor, Abelian.im, ShortComplex.gFunctor, Arrow.mk,
    Arrow.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The map induced on images commutes with the epimorphic factors onto
those images. -/
theorem factorThruImage_comp_ringelImage_map
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    {X Y : StronglyExactComplexCategory H} (f : X ⟶ Y) :
    Abelian.factorThruImage
          ((stronglyExactUnderlyingFunctor H).obj X).g ≫
        (ringelImageFunctor H).map f =
      ((stronglyExactUnderlyingFunctor H).map f).τ₂ ≫
        Abelian.factorThruImage
          ((stronglyExactUnderlyingFunctor H).obj Y).g := by
  apply (cancel_mono
    (Abelian.image.ι ((stronglyExactUnderlyingFunctor H).obj Y).g)).1
  simp [ringelImageFunctor, Abelian.im, ShortComplex.gFunctor,
    Arrow.mk, Arrow.hom, Category.assoc]
  exact ((stronglyExactUnderlyingFunctor H).map f).comm₂₃.symm

set_option backward.isDefEq.respectTransparency false in
/-- Strong exactness says that the image inclusion of the second
differential is a left approximation by finite projectives. -/
theorem stronglyExact_image_leftApproximation
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (X : StronglyExactComplexCategory H)
    (Q : FGProjectives (R := R))
    (a : (ringelImageFunctor H).obj X ⟶ Q.obj) :
    ∃ b : X.obj.X₃ ⟶ Q,
      Abelian.image.ι ((stronglyExactUnderlyingFunctor H).obj X).g ≫
          b.hom = a := by
  let T := (stronglyExactUnderlyingFunctor H).obj X
  let e := Abelian.factorThruImage T.g
  let ta : X.obj.X₂ ⟶ Q :=
    ObjectProperty.homMk (e ≫ a)
  have hta : X.obj.f ≫ ta = 0 := by
    apply ObjectProperty.hom_ext
    change
      ((stronglyExactUnderlyingFunctor H).obj X).f ≫ e ≫ a = 0
    have hfe :
        ((stronglyExactUnderlyingFunctor H).obj X).f ≫ e = 0 := by
      apply (cancel_mono
        (Abelian.image.ι
          ((stronglyExactUnderlyingFunctor H).obj X).g)).1
      rw [Category.assoc, Abelian.image.fac, zero_comp]
      exact ((stronglyExactUnderlyingFunctor H).obj X).zero
    rw [← Category.assoc, hfe, zero_comp]
  have hdual0 :
      H.functor.map ta.op ≫ H.functor.map X.obj.f.op = 0 := by
    rw [← H.functor.map_comp, ← op_comp, hta, op_zero,
      H.functor.map_zero]
  let D := X.obj.homDual H
  let TD := (forgetProjectiveComplex (R := S)).obj D
  let HQ := H.functor.obj (Opposite.op Q)
  letI : Projective HQ.obj := HQ.property
  have hpzero :
      (H.functor.map ta.op).hom ≫ TD.g = 0 := by
    exact congrArg (fun z ↦ z.hom) hdual0
  let d₀ : HQ.obj ⟶ TD.X₁ :=
    X.property.2.liftFromProjective
      (H.functor.map ta.op).hom hpzero
  let d : HQ ⟶ H.functor.obj (Opposite.op X.obj.X₃) :=
    ObjectProperty.homMk d₀
  have hd :
      d ≫ H.functor.map X.obj.g.op =
        H.functor.map ta.op := by
    apply ObjectProperty.hom_ext
    exact X.property.2.liftFromProjective_comp
      (H.functor.map ta.op).hom hpzero
  let bop : Opposite.op Q ⟶ Opposite.op X.obj.X₃ :=
    H.functor.preimage d
  let b : X.obj.X₃ ⟶ Q := bop.unop
  have hgb : X.obj.g ≫ b = ta := by
    apply Quiver.Hom.op_inj
    apply H.functor.map_injective
    simp only [op_comp, Quiver.Hom.op_unop, H.functor.map_comp,
      b, bop, Functor.map_preimage, hd]
  refine ⟨b, ?_⟩
  apply (cancel_epi e).1
  rw [← Category.assoc, Abelian.image.fac]
  exact congrArg (fun z ↦ z.hom) hgb

set_option backward.isDefEq.respectTransparency false in
/-- Every map between the images of two strongly exact complexes lifts to
a morphism of complexes. -/
theorem ringelImageFunctor_map_surjective
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (X Y : StronglyExactComplexCategory H)
    (a : (ringelImageFunctor H).obj X ⟶
      (ringelImageFunctor H).obj Y) :
    ∃ f : X ⟶ Y, (ringelImageFunctor H).map f = a := by
  let TX := (stronglyExactUnderlyingFunctor H).obj X
  let TY := (stronglyExactUnderlyingFunctor H).obj Y
  let eX := Abelian.factorThruImage TX.g
  let uX := Abelian.image.ι TX.g
  let eY := Abelian.factorThruImage TY.g
  let uY := Abelian.image.ι TY.g
  letI : Projective TX.X₂ := X.obj.X₂.property
  let h₀ : TX.X₂ ⟶ TY.X₂ :=
    Projective.factorThru (eX ≫ a) eY
  have h₀e : h₀ ≫ eY = eX ≫ a :=
    Projective.factorThru_comp (eX ≫ a) eY
  have h₀g : h₀ ≫ TY.g = (eX ≫ a) ≫ uY := by
    rw [← Abelian.image.fac TY.g, ← Category.assoc, h₀e]
  have hfXe : TX.f ≫ eX = 0 := by
    apply (cancel_mono uX).1
    rw [Category.assoc, Abelian.image.fac, zero_comp]
    exact TX.zero
  have hz : (TX.f ≫ h₀) ≫ TY.g = 0 := by
    rw [Category.assoc, h₀g, ← Category.assoc, ← Category.assoc,
      hfXe, zero_comp, zero_comp]
  letI : Projective TX.X₁ := X.obj.X₁.property
  let h₁ : TX.X₁ ⟶ TY.X₁ :=
    Y.property.1.liftFromProjective (TX.f ≫ h₀) hz
  have h₁f : h₁ ≫ TY.f = TX.f ≫ h₀ :=
    Y.property.1.liftFromProjective_comp (TX.f ≫ h₀) hz
  obtain ⟨h₃, uh₃⟩ :=
    stronglyExact_image_leftApproximation H X Y.obj.X₃ (a ≫ uY)
  have uh₃' : uX ≫ h₃.hom = a ≫ uY := by
    simpa [uX, TX] using uh₃
  have euX : eX ≫ uX = TX.g := by
    simp [eX, uX]
  have h₀g' : h₀ ≫ TY.g = TX.g ≫ h₃.hom := by
    calc
      h₀ ≫ TY.g = (eX ≫ a) ≫ uY := h₀g
      _ = eX ≫ (a ≫ uY) := Category.assoc _ _ _
      _ = eX ≫ (uX ≫ h₃.hom) := by rw [uh₃']
      _ = (eX ≫ uX) ≫ h₃.hom := (Category.assoc _ _ _).symm
      _ = TX.g ≫ h₃.hom := by rw [euX]
  let h₁' : X.obj.X₁ ⟶ Y.obj.X₁ :=
    ObjectProperty.homMk h₁
  let h₀' : X.obj.X₂ ⟶ Y.obj.X₂ :=
    ObjectProperty.homMk h₀
  let h' : X.obj ⟶ Y.obj :=
    ShortComplex.Hom.mk h₁' h₀' h₃
      (by
        apply ObjectProperty.hom_ext
        exact h₁f)
      (by
        apply ObjectProperty.hom_ext
        exact h₀g')
  let h : X ⟶ Y := ObjectProperty.homMk h'
  refine ⟨h, ?_⟩
  apply (cancel_mono uY).1
  rw [ringelImage_map_comp_image_ι H h]
  exact uh₃

set_option backward.isDefEq.respectTransparency false in
/-- If the induced map on images factors through a projective, then the
original complex morphism belongs to Ringel's null ideal. -/
theorem ringelImage_reflects_factorsThroughProjective
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    {X Y : StronglyExactComplexCategory H} (h : X ⟶ Y)
    (hh : FactorsThroughProjective ((ringelImageFunctor H).map h)) :
    FactorsThroughRingelU h := by
  let TX := (stronglyExactUnderlyingFunctor H).obj X
  let TY := (stronglyExactUnderlyingFunctor H).obj Y
  let hu := (stronglyExactUnderlyingFunctor H).map h
  let qh := (ringelImageFunctor H).map h
  let eX := Abelian.factorThruImage TX.g
  let uX := Abelian.image.ι TX.g
  let eY := Abelian.factorThruImage TY.g
  let uY := Abelian.image.ι TY.g
  let P : FGProjectives (R := R) :=
    ⟨hh.middle, hh.projective⟩
  obtain ⟨a', ua'⟩ :=
    stronglyExact_image_leftApproximation H X P hh.left
  let aU : TX.X₃ ⟶ P.obj := a'.hom
  have ua'' : uX ≫ aU = hh.left := by
    simpa [uX, TX] using ua'
  letI : Projective P.obj := P.property
  let b' : P.obj ⟶ TY.X₂ :=
    Projective.factorThru hh.right eY
  have b'e : b' ≫ eY = hh.right :=
    Projective.factorThru_comp hh.right eY
  have euX : eX ≫ uX = TX.g := by
    simp [eX, uX]
  have euY : eY ≫ uY = TY.g := by
    simp [eY, uY]
  have qe : eX ≫ qh = hu.τ₂ ≫ eY := by
    simpa [eX, eY, qh, hu, TX, TY] using
      factorThruImage_comp_ringelImage_map H h
  have qu : qh ≫ uY = uX ≫ hu.τ₃ := by
    simpa [uX, uY, qh, hu, TX, TY] using
      ringelImage_map_comp_image_ι H h
  let t : TX.X₂ ⟶ TY.X₂ := (eX ≫ hh.left) ≫ b'
  have tg : t ≫ TY.g = hu.τ₂ ≫ TY.g := by
    calc
      t ≫ TY.g = t ≫ (eY ≫ uY) := by rw [euY]
      _ = ((eX ≫ hh.left) ≫ (b' ≫ eY)) ≫ uY := by
        simp only [t, Category.assoc]
      _ = ((eX ≫ hh.left) ≫ hh.right) ≫ uY := by rw [b'e]
      _ = (eX ≫ (hh.left ≫ hh.right)) ≫ uY :=
        congrArg (fun z ↦ z ≫ uY)
          (Category.assoc eX hh.left hh.right)
      _ = (eX ≫ qh) ≫ uY := by rw [hh.fac]
      _ = (hu.τ₂ ≫ eY) ≫ uY := by rw [qe]
      _ = hu.τ₂ ≫ TY.g := by rw [Category.assoc, euY]
  let k : TX.X₂ ⟶ TY.X₂ := hu.τ₂ - t
  have kg : k ≫ TY.g = 0 := by
    rw [Preadditive.sub_comp, tg, sub_self]
  letI : Projective TX.X₂ := X.obj.X₂.property
  let c : TX.X₂ ⟶ TY.X₁ :=
    Y.property.1.liftFromProjective k kg
  have cf : c ≫ TY.f = k :=
    Y.property.1.liftFromProjective_comp k kg
  have fXe : TX.f ≫ eX = 0 := by
    apply (cancel_mono uX).1
    rw [Category.assoc, euX, zero_comp]
    exact TX.zero
  have ft : TX.f ≫ t = 0 := by
    simp only [t, ← Category.assoc, fXe, zero_comp]
  have fc_f : (TX.f ≫ c) ≫ TY.f = TX.f ≫ hu.τ₂ := by
    rw [Category.assoc, cf]
    change TX.f ≫ (hu.τ₂ - t) = TX.f ≫ hu.τ₂
    rw [Preadditive.comp_sub, ft, sub_zero]
  have leftStalk_zero :
      (hu.τ₁ - TX.f ≫ c) ≫ TY.f = 0 := by
    rw [Preadditive.sub_comp, hu.comm₁₂, fc_f, sub_self]
  have ga : TX.g ≫ aU = eX ≫ hh.left := by
    calc
      TX.g ≫ aU = (eX ≫ uX) ≫ aU := by rw [euX]
      _ = eX ≫ (uX ≫ aU) := Category.assoc _ _ _
      _ = eX ≫ hh.left := by rw [ua'']
  have bg : b' ≫ TY.g = hh.right ≫ uY := by
    calc
      b' ≫ TY.g = b' ≫ (eY ≫ uY) := by rw [euY]
      _ = (b' ≫ eY) ≫ uY := (Category.assoc _ _ _).symm
      _ = hh.right ≫ uY := by rw [b'e]
  let bu : P.obj ⟶ TY.X₃ := hh.right ≫ uY
  have gh_eq :
      TX.g ≫ hu.τ₃ = TX.g ≫ (aU ≫ bu) := by
    calc
      TX.g ≫ hu.τ₃ = (eX ≫ uX) ≫ hu.τ₃ := by rw [euX]
      _ = eX ≫ (uX ≫ hu.τ₃) := Category.assoc _ _ _
      _ = eX ≫ (qh ≫ uY) := by rw [qu]
      _ = (eX ≫ qh) ≫ uY := (Category.assoc _ _ _).symm
      _ = (eX ≫ (hh.left ≫ hh.right)) ≫ uY := by rw [hh.fac]
      _ = ((eX ≫ hh.left) ≫ hh.right) ≫ uY :=
        congrArg (fun z ↦ z ≫ uY)
          (Category.assoc eX hh.left hh.right).symm
      _ = ((TX.g ≫ aU) ≫ hh.right) ≫ uY := by rw [ga]
      _ = TX.g ≫ (aU ≫ bu) := by
        simp only [bu, Category.assoc]
  let r : TX.X₃ ⟶ TY.X₃ := hu.τ₃ - aU ≫ bu
  have gr : TX.g ≫ r = 0 := by
    rw [Preadditive.comp_sub, gh_eq, sub_self]
  let c' : X.obj.X₂ ⟶ Y.obj.X₁ := ObjectProperty.homMk c
  let k' : X.obj.X₂ ⟶ Y.obj.X₂ := ObjectProperty.homMk k
  let ea' : X.obj.X₂ ⟶ P := ObjectProperty.homMk (eX ≫ hh.left)
  let b'' : P ⟶ Y.obj.X₂ := ObjectProperty.homMk b'
  let bu' : P ⟶ Y.obj.X₃ := ObjectProperty.homMk bu
  let r' : X.obj.X₃ ⟶ Y.obj.X₃ := ObjectProperty.homMk r
  let A₁ : X ⟶ elementaryStrongComplex H .leftStalk X.obj.X₁ :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk (𝟙 _) 0 0
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex])
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex]))
  let B₁ : elementaryStrongComplex H .leftStalk X.obj.X₁ ⟶ Y :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk (h.hom.τ₁ - X.obj.f ≫ c') 0 0
        (by
          apply ObjectProperty.hom_ext
          exact leftStalk_zero)
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex]))
  let A₂ : X ⟶ elementaryStrongComplex H .leftContractible X.obj.X₂ :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk X.obj.f (𝟙 _) 0
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex])
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex]))
  let B₂ : elementaryStrongComplex H .leftContractible X.obj.X₂ ⟶ Y :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk c' k' 0
        (by
          apply ObjectProperty.hom_ext
          exact cf)
        (by
          apply ObjectProperty.hom_ext
          exact kg))
  let A₃ : X ⟶ elementaryStrongComplex H .rightContractible P :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk 0 ea' a'
        (by
          apply ObjectProperty.hom_ext
          change (0 : TX.X₁ ⟶ P.obj) = TX.f ≫ (eX ≫ hh.left)
          rw [← Category.assoc, fXe, zero_comp])
        (by
          apply ObjectProperty.hom_ext
          change eX ≫ hh.left = TX.g ≫ aU
          exact ga.symm))
  let B₃ : elementaryStrongComplex H .rightContractible P ⟶ Y :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk 0 b'' bu'
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex])
        (by
          apply ObjectProperty.hom_ext
          change b' ≫ TY.g = bu
          exact bg))
  let A₄ : X ⟶ elementaryStrongComplex H .rightStalk Y.obj.X₃ :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk 0 0 r'
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex])
        (by
          apply ObjectProperty.hom_ext
          change (0 : TX.X₂ ⟶ TY.X₃) = TX.g ≫ r
          exact gr.symm))
  let B₄ : elementaryStrongComplex H .rightStalk Y.obj.X₃ ⟶ Y :=
    ObjectProperty.homMk
      (ShortComplex.Hom.mk 0 0 (𝟙 _)
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex])
        (by simp [elementaryStrongComplex, elementaryProjectiveComplex]))
  have hdecomp :
      h = ((A₁ ≫ B₁) + (A₂ ≫ B₂)) +
        ((A₃ ≫ B₃) + (A₄ ≫ B₄)) := by
    apply ObjectProperty.hom_ext
    apply ShortComplex.hom_ext
    · simp only [fullSubcategory_add_hom,
        ObjectProperty.FullSubcategory.comp_hom,
        ShortComplex.add_τ₁, ShortComplex.comp_τ₁]
      dsimp [A₁, B₁, A₂, B₂, A₃, B₃, A₄, B₄, c']
      simp
    · simp only [fullSubcategory_add_hom,
        ObjectProperty.FullSubcategory.comp_hom,
        ShortComplex.add_τ₂, ShortComplex.comp_τ₂]
      dsimp [A₁, B₁, A₂, B₂, A₃, B₃, A₄, B₄, k', ea', t, k, hu]
      simp
      apply ObjectProperty.hom_ext
      change ((stronglyExactUnderlyingFunctor H).map h).τ₂ =
        (((stronglyExactUnderlyingFunctor H).map h).τ₂ -
            eX ≫ hh.left ≫ b') +
          (eX ≫ hh.left) ≫ b'
      exact (sub_add_cancel _ _).symm
    · simp only [fullSubcategory_add_hom,
        ObjectProperty.FullSubcategory.comp_hom,
        ShortComplex.add_τ₃, ShortComplex.comp_τ₃]
      dsimp [A₁, B₁, A₂, B₂, A₃, B₃, A₄, B₄, bu', r', r, hu]
      simp
      apply ObjectProperty.hom_ext
      change ((stronglyExactUnderlyingFunctor H).map h).τ₃ =
        aU ≫ bu +
          (((stronglyExactUnderlyingFunctor H).map h).τ₃ - aU ≫ bu)
      rw [add_comm]
      exact (sub_add_cancel _ _).symm
  rw [hdecomp]
  exact
    (FactorsThroughRingelU.basic .leftStalk X.obj.X₁ A₁ B₁).add
        (FactorsThroughRingelU.basic .leftContractible X.obj.X₂ A₂ B₂) |>.add
      ((FactorsThroughRingelU.basic .rightContractible P A₃ B₃).add
        (FactorsThroughRingelU.basic .rightStalk Y.obj.X₃ A₄ B₄))

set_option backward.isDefEq.respectTransparency false in
/-- The image functor to the projective stable category is full. -/
instance ringelImageStableFunctor_full
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageStableFunctor H).Full where
  map_surjective {X Y} a := by
    obtain ⟨a₀, ha₀⟩ :=
      (projectiveStableFunctor (R := R)).map_surjective a.hom
    obtain ⟨f, hf⟩ := ringelImageFunctor_map_surjective H X Y a₀
    refine ⟨f, ?_⟩
    apply ObjectProperty.hom_ext
    change (projectiveStableFunctor (R := R)).map
      ((ringelImageFunctor H).map f) = a.hom
    rw [hf, ha₀]

set_option backward.isDefEq.respectTransparency false in
/-- The induced Ringel functor between the two quotients is full. -/
instance ringelImageQuotientFunctor_full
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageQuotientFunctor H).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ a
    obtain ⟨f, hf⟩ := (ringelImageStableFunctor H).map_surjective a
    exact ⟨(ringelComplexQuotientFunctor H).map f, hf⟩

set_option backward.isDefEq.respectTransparency false in
/-- The induced Ringel functor between the two quotients is faithful. -/
instance ringelImageQuotientFunctor_faithful
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageQuotientFunctor H).Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ α β hαβ
    obtain ⟨f, rfl⟩ :=
      (ringelComplexQuotientFunctor H).map_surjective α
    obtain ⟨g, rfl⟩ :=
      (ringelComplexQuotientFunctor H).map_surjective β
    change (ringelImageStableFunctor H).map f =
      (ringelImageStableFunctor H).map g at hαβ
    have hfac : Nonempty (FactorsThroughProjective
        ((ringelImageFunctor H).map f -
          (ringelImageFunctor H).map g)) :=
      (torsionlessStableQuotientFunctor_map_eq_iff
        ((ringelImageTorsionlessFunctor H).map f)
        ((ringelImageTorsionlessFunctor H).map g)).1 hαβ
    rcases hfac with ⟨hfac⟩
    have hu : FactorsThroughRingelU (f - g) :=
      ringelImage_reflects_factorsThroughProjective H (f - g) (by
        rw [(ringelImageFunctor H).map_sub]
        exact hfac)
    exact (ringelComplexQuotient_map_eq_iff H f g).2 ⟨hu⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every torsionless finite module is the image of a strongly exact
three-term complex of finite projectives. -/
private theorem stronglyExactComplex_exists_of_torsionless
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S))
    (M : FGModuleCat.{u} R) (hM : Torsionless M) :
    ∃ X : StronglyExactComplexCategory H,
      Nonempty ((ringelImageFunctor H).obj X ≅ M) := by
  obtain ⟨T, i, hT, hi⟩ := hM
  letI : Projective T := hT
  letI : Mono i := hi
  let P₀d := finiteProjectivePresentation M
  let P₀ : FGProjectives (R := R) :=
    ⟨P₀d.p, P₀d.projective⟩
  let p : P₀.obj ⟶ M := P₀d.f
  let P₁d := finiteProjectivePresentation (kernel p)
  let P₁ : FGProjectives (R := R) :=
    ⟨P₁d.p, P₁d.projective⟩
  let e : P₁.obj ⟶ kernel p := P₁d.f
  let f₀ : P₁.obj ⟶ P₀.obj := e ≫ kernel.ι p
  let f : P₁ ⟶ P₀ := ObjectProperty.homMk f₀
  let df : H.functor.obj (Opposite.op P₀) ⟶
      H.functor.obj (Opposite.op P₁) := H.functor.map f.op
  let Qd := finiteProjectivePresentation (kernel df.hom)
  let Q : FGProjectives (R := S) :=
    ⟨Qd.p, Qd.projective⟩
  let q : Q.obj ⟶ kernel df.hom := Qd.f
  let Paux : FGProjectives (R := R) :=
    (H.inverse.obj Q).unop
  let a : H.functor.obj (Opposite.op Paux) ⟶
      H.functor.obj (Opposite.op P₀) :=
    H.counitIso.hom.app Q ≫
      ObjectProperty.homMk (q ≫ kernel.ι df.hom)
  let gauxOp : Opposite.op Paux ⟶ Opposite.op P₀ :=
    H.functor.preimage a
  let gaux : P₀ ⟶ Paux := gauxOp.unop
  have hdual :
      H.functor.map gaux.op ≫ H.functor.map f.op = 0 := by
    calc
      H.functor.map gaux.op ≫ H.functor.map f.op =
          a ≫ H.functor.map f.op := by
        simp only [gaux, Quiver.Hom.op_unop, gauxOp,
          Functor.map_preimage]
      _ = 0 := by
        apply ObjectProperty.hom_ext
        dsimp [a, df]
        simp
  have hfgaux : f ≫ gaux = 0 := by
    apply Quiver.Hom.op_inj
    apply H.functor.map_injective
    simp only [op_comp, H.functor.map_comp, hdual, op_zero,
      H.functor.map_zero]
  have hkgaux : kernel.ι p ≫ gaux.hom = 0 := by
    have hu := congrArg (fun z ↦ z.hom) hfgaux
    change f.hom ≫ gaux.hom = 0 at hu
    have hu₀ : (e ≫ kernel.ι p) ≫ gaux.hom = 0 := by
      exact hu
    apply (cancel_epi e).1
    calc
      e ≫ (kernel.ι p ≫ gaux.hom) =
          (e ≫ kernel.ι p) ≫ gaux.hom :=
        (Category.assoc _ _ _).symm
      _ = 0 := hu₀
      _ = e ≫ 0 := comp_zero.symm
  let haux : M ⟶ Paux.obj :=
    Abelian.epiDesc p gaux.hom hkgaux
  let j : M ⟶ T ⊞ Paux.obj := biprod.lift i haux
  letI : Mono j := mono_of_mono_fac (biprod.lift_fst i haux)
  have hPminus : Projective (T ⊞ Paux.obj) := by
    letI : Projective Paux.obj := Paux.property
    infer_instance
  let Pminus : FGProjectives (R := R) :=
    ⟨T ⊞ Paux.obj, hPminus⟩
  let g₀ : P₀.obj ⟶ Pminus.obj := p ≫ j
  let g : P₀ ⟶ Pminus := ObjectProperty.homMk g₀
  have hzero : f ≫ g = 0 := by
    apply ObjectProperty.hom_ext
    dsimp [f, f₀, g, g₀]
    simp
  let C : ProjectiveComplex R := ShortComplex.mk f g hzero
  have hC : C.Exact := by
    change (ShortComplex.mk (e ≫ kernel.ι p) (p ≫ j) _).Exact
    exact exact_projective_kernel_cover_comp_mono p e j
  let snd' : Pminus ⟶ Paux :=
    ObjectProperty.homMk biprod.snd
  have hgsnd : g ≫ snd' = gaux := by
    apply ObjectProperty.hom_ext
    dsimp [g, g₀, snd', j, haux]
    simp
  have hHgsnd :
      H.functor.map snd'.op ≫ H.functor.map g.op = a := by
    calc
      H.functor.map snd'.op ≫ H.functor.map g.op =
          H.functor.map (g ≫ snd').op := by
        rw [op_comp, H.functor.map_comp]
      _ = H.functor.map gaux.op := by rw [hgsnd]
      _ = a := by
        simp only [gaux, Quiver.Hom.op_unop, gauxOp,
          Functor.map_preimage]
  have hzfull :
      H.functor.map g.op ≫ H.functor.map f.op = 0 := by
    rw [← H.functor.map_comp, ← op_comp, hzero, op_zero,
      H.functor.map_zero]
  have hdualZero :
      (H.functor.map g.op).hom ≫ df.hom = 0 := by
    simpa [df] using congrArg (fun z ↦ z.hom) hzfull
  have hfactor :
      (H.functor.map snd'.op).hom ≫
          kernel.lift df.hom (H.functor.map g.op).hom hdualZero =
        (H.counitIso.hom.app Q).hom ≫ q := by
    apply (cancel_mono (kernel.ι df.hom)).1
    rw [Category.assoc, kernel.lift_ι]
    simpa [a, Category.assoc] using
      congrArg (fun z ↦ z.hom) hHgsnd
  have hDual : (C.homDual H).Exact := by
    change (ShortComplex.mk
      (H.functor.map g.op).hom df.hom _).Exact
    apply (ShortComplex.exact_iff_epi_kernel_lift _).2
    exact epi_of_epi_fac hfactor
  let X : StronglyExactComplexCategory H := ⟨C, hC, hDual⟩
  refine ⟨X, ?_⟩
  let F : StrongEpiMonoFactorisation (p ≫ j) :=
    { I := M
      e := p
      m := j
      fac := rfl
      e_strong_epi := strongEpi_of_epi p
      m_mono := inferInstance }
  let imageIso : Abelian.image (p ≫ j) ≅ M :=
    IsImage.isoExt
      (Abelian.imageStrongEpiMonoFactorisation
        (p ≫ j)).toMonoIsImage
      F.toMonoIsImage
  exact ⟨imageIso⟩

set_option backward.isDefEq.respectTransparency false in
/-- The descended Ringel image functor is dense. -/
instance ringelImageQuotientFunctor_essSurj
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageQuotientFunctor H).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ :=
      stronglyExactComplex_exists_of_torsionless
        H Y.obj.as Y.property
    refine ⟨(ringelComplexQuotientFunctor H).obj X, ⟨?_⟩⟩
    change (ringelImageStableFunctor H).obj X ≅ Y
    exact ObjectProperty.isoMk _
      ((projectiveStableFunctor (R := R)).mapIso e)

/-- Ringel's descended image functor is an equivalence. -/
instance ringelImageQuotientFunctor_isEquivalence
    (H : (FGProjectives (R := R))ᵒᵖ ≌ FGProjectives (R := S)) :
    (ringelImageQuotientFunctor H).IsEquivalence where

end QuotientSubmoduleEquidistribution.RingelEta
