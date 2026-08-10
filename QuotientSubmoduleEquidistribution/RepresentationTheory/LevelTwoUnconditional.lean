import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoGabrielClassification
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthTwoContragredient
import QuotientSubmoduleEquidistribution.RepresentationTheory.LevelTwoCounting
import QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaConsequences

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LevelTwoUnconditional

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Reindex a complete duplicate-free indecomposable skeleton along an
equivalence of label types. -/
noncomputable def relabelIndecomposableSkeleton
    {R₂ : Type u} [Ring R₂] [IsNoetherianRing R₂]
    {κ : Type v} {ι₂ : Type w}
    (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R₂ κ)
    (e : ι₂ ≃ κ) :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, w, u} R₂ ι₂ where
  obj i := τ.obj (e i)
  indecomposable i := τ.indecomposable (e i)
  finiteLength i := τ.finiteLength (e i)
  eq_of_iso := by
    intro i j hij
    apply e.injective
    exact τ.eq_of_iso hij
  complete := by
    intro X hX
    obtain ⟨i, ⟨h⟩⟩ := τ.complete X hX
    refine ⟨e.symm i, ⟨h ≪≫ eqToIso ?_⟩⟩
    simp
  decomposes := by
    intro X
    obtain ⟨n, a, ⟨h⟩⟩ := τ.decomposes X
    refine ⟨n, fun t ↦ e.symm (a t),
      ⟨h ≪≫ biproduct.mapIso (fun t ↦ eqToIso ?_)⟩⟩
    simp

/-- Relabeling a skeleton is aligned with the identity equivalence of its
module category. -/
noncomputable def relabelAlignedEquivalence
    {R₂ : Type u} [Ring R₂] [IsNoetherianRing R₂]
    {κ : Type v} {ι₂ : Type w}
    (τ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R₂ κ)
    (e : ι₂ ≃ κ) :
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence
      τ (relabelIndecomposableSkeleton τ e) where
  categoryEquiv := CategoryTheory.Equivalence.refl
  labelEquiv := e.symm
  objIso k := eqToIso (by simp [relabelIndecomposableSkeleton])

/-- A unique simple quotient type makes the semisimple top isotypic. -/
theorem moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
    {j s : ι} (hunique : σ.HasUniqueSimpleQuotientType j s) :
    IsIsotypicOfType R (σ.moduleTop j) (σ.obj s) := by
  letI : IsSemisimpleModule R (σ.moduleTop j) :=
    σ.moduleTop_isSemisimple j
  intro m hm
  letI : IsSimpleModule R m := hm
  obtain ⟨c, hmc⟩ := exists_isCompl m
  let p : σ.moduleTop j →ₗ[R] m :=
    Submodule.projectionOnto m c hmc
  have hp : Function.Surjective p :=
    Submodule.projectionOnto_surjective hmc
  letI : Module.Finite R m :=
    Module.Finite.of_surjective p hp
  let M : FGModuleCat.{w} R := FGModuleCat.of R m
  have hMindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨l, ⟨e⟩⟩ := σ.complete M hMindec
  let q : σ.obj j →ₗ[R] σ.moduleTop j :=
    (σ.moduleRadical j).mkQ
  let f : σ.obj j ⟶ σ.obj l :=
    FGModuleCat.ofHom (e.hom.hom.hom.comp (p.comp q))
  have hfSurj : Function.Surjective f.hom.hom := by
    intro y
    obtain ⟨z, rfl⟩ :=
      (FGModuleCat.isoToLinearEquiv e).surjective y
    obtain ⟨t, rfl⟩ := hp z
    obtain ⟨a, rfl⟩ := (σ.moduleRadical j).mkQ_surjective t
    exact ⟨a, rfl⟩
  letI : Epi f :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      f).mpr hfSurj
  have hMsimple : Simple M :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      M).mpr hm
  have hlsimple : Simple (σ.obj l) :=
    (Simple.iff_of_iso e).mp hMsimple
  let L : σ.SimpleQuotient j := {
    index := l
    simple := hlsimple
    map := f
    epi := inferInstance }
  have hls : l = s := hunique.2 L
  subst l
  exact ⟨FGModuleCat.isoToLinearEquiv e⟩

/--
Every nonsimple indecomposable finite-length representative has an
indecomposable quotient whose module radical is simple.
-/
theorem exists_indecomposable_quotient_with_simple_radical
    {x : ι} (hx : ¬ Simple (σ.obj x)) :
    ∃ (j : ι) (f : σ.obj x ⟶ σ.obj j),
      Epi f ∧ IsSimpleModule R (σ.moduleRadical j) := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  let J : Submodule R (σ.obj x) :=
    Module.jacobson R (σ.obj x)
  have hJne : J ≠ ⊥ := by
    intro hJ
    letI : IsSemisimpleModule R (σ.obj x) :=
      (IsArtinian.isSemisimpleModule_iff_jacobson R (σ.obj x)).2 hJ
    have hxSimpleModule : IsSimpleModule R (σ.obj x) :=
      _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
        (σ.indecomposable x)
    exact hx
      ((_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
        (σ.obj x)).2 hxSimpleModule)
  obtain ⟨N, -, hNJ⟩ :=
    exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr hJne)
  let Jbar : Submodule R ((σ.obj x) ⧸ N) :=
    Submodule.map N.mkQ J
  let intervalEquiv :
      Submodule R ((σ.obj x) ⧸ N) ≃o Set.Ici N :=
    Submodule.comapMkQRelIso N
  have hJintervalAtom :
      IsAtom (⟨J, hNJ.le⟩ : Set.Ici N) :=
    (covBy_iff_atom_Ici hNJ.le).mp hNJ
  have hJbarAtom : IsAtom Jbar := by
    change IsAtom (intervalEquiv.symm ⟨J, hNJ.le⟩)
    exact (intervalEquiv.symm.isAtom_iff _).mpr hJintervalAtom
  have hJbarSimple : IsSimpleModule R Jbar :=
    isSimpleModule_iff_isAtom.mpr hJbarAtom
  letI : IsSimpleModule R Jbar := hJbarSimple
  have hradQuotient :
      Module.jacobson R ((σ.obj x) ⧸ N) = Jbar := by
    exact Module.jacobson_quotient_of_le hNJ.le
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((σ.obj x) ⧸ N)
  obtain ⟨n, a, ⟨e⟩⟩ := σ.decomposes Q
  let ePi :
      Q ≅ FGModuleCat.of R (∀ t : Fin n, σ.obj (a t)) :=
    e ≪≫
      _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.biproductIsoPiFG
        (fun t : Fin n ↦ σ.obj (a t))
  have eLin_apply (y : Q) :
      FGModuleCat.isoToLinearEquiv ePi y = ePi.hom.hom.hom y := rfl
  letI : Nontrivial Jbar := IsSimpleModule.nontrivial R Jbar
  obtain ⟨z, hz⟩ := exists_ne (0 : Jbar)
  have hzval : (z.1 : ((σ.obj x) ⧸ N)) ≠ 0 := by
    intro hzero
    apply hz
    apply Subtype.ext
    exact hzero
  have hez : ePi.hom.hom.hom z.1 ≠ 0 := by
    intro hzero
    apply hzval
    apply (FGModuleCat.isoToLinearEquiv ePi).injective
    rw [eLin_apply, eLin_apply]
    simpa using hzero
  have hcoordinate : ∃ t : Fin n, ePi.hom.hom.hom z.1 t ≠ 0 := by
    by_contra h
    push Not at h
    apply hez
    funext t
    exact h t
  obtain ⟨t, ht⟩ := hcoordinate
  let gLinear : Q →ₗ[R] σ.obj (a t) :=
    (LinearMap.proj (R := R) t).comp ePi.hom.hom.hom
  let g : Q ⟶ σ.obj (a t) := FGModuleCat.ofHom gLinear
  have g_apply (y : Q) :
      g.hom.hom y = ePi.hom.hom.hom y t := rfl
  have hgSurj : Function.Surjective g.hom.hom := by
    intro y
    obtain ⟨p, hp⟩ :=
      LinearMap.proj_surjective
        (R := R) (φ := fun r : Fin n ↦ σ.obj (a r)) t y
    obtain ⟨q, hq⟩ :=
      (FGModuleCat.isoToLinearEquiv ePi).surjective p
    refine ⟨q, ?_⟩
    rw [g_apply, ← eLin_apply, hq]
    simpa using hp
  letI : Epi g :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      g).mpr hgSurj
  let q : σ.obj x ⟶ Q := FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      q).mpr N.mkQ_surjective
  let f : σ.obj x ⟶ σ.obj (a t) := q ≫ g
  letI : Epi f := by
    dsimp only [f]
    infer_instance
  letI : IsArtinian R Q := by infer_instance
  have hgRadical :
      Submodule.map g.hom.hom Jbar =
        σ.moduleRadical (a t) := by
    rw [← hradQuotient]
    exact
      _root_.QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.map_jacobson_of_surjective_of_isArtinian
        g.hom.hom hgSurj
  let targetRadical : Submodule R (σ.obj (a t)) :=
    σ.moduleRadical (a t)
  let radicalMap : Jbar →ₗ[R] targetRadical :=
    (g.hom.hom.domRestrict Jbar).codRestrict
      targetRadical (fun y ↦ by
        apply Module.map_jacobson_le g.hom.hom
        rw [hradQuotient]
        exact ⟨y.1, y.2, rfl⟩)
  have hradicalMapSurj : Function.Surjective radicalMap := by
    intro y
    have hy : y.1 ∈ Submodule.map g.hom.hom Jbar := by
      rw [hgRadical]
      exact y.2
    obtain ⟨r, hr, hry⟩ := hy
    refine ⟨⟨r, hr⟩, ?_⟩
    apply Subtype.ext
    exact hry
  have hradicalMapNe : radicalMap ≠ 0 := by
    intro hzero
    have hzmap : radicalMap z = 0 := by rw [hzero]; rfl
    apply ht
    have hzmapval := congrArg Subtype.val hzmap
    simp only [radicalMap,
      LinearMap.domRestrict_apply, LinearMap.codRestrict_apply] at hzmapval
    rw [g_apply] at hzmapval
    simpa using hzmapval
  have hradicalMapInj : Function.Injective radicalMap :=
    (radicalMap.injective_or_eq_zero).resolve_right hradicalMapNe
  let radicalEquiv : Jbar ≃ₗ[R] targetRadical :=
    LinearEquiv.ofBijective radicalMap
      ⟨hradicalMapInj, hradicalMapSurj⟩
  have htargetSimple : IsSimpleModule R targetRadical :=
    IsSimpleModule.congr radicalEquiv.symm
  exact ⟨a t, f, inferInstance, htargetSimple⟩

/--
The isotypic-Loewy-two theorem closes the remaining mixed-pair gap:
the nonsimple member of a quotient-closed pair with a simple member has
composition length two.
-/
theorem compositionLength_eq_two_of_qClosed_pair_of_isotypicLoewyTwo
    (hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        σ)
    {x s : ι}
    (hclosed : σ.qClosure.IsClosed ({x, s} : Set ι))
    (hx : ¬ Simple (σ.obj x))
    (hs : Simple (σ.obj s)) :
    σ.compositionLength x = 2 := by
  have huniqueX : σ.HasUniqueSimpleQuotientType x s := by
    refine ⟨hs, ?_⟩
    intro Q
    have hmem : Q.index ∈ ({x, s} : Set ι) :=
      Q.mem_of_isClosed σ hclosed (by simp)
    rcases hmem with hQx | hQs
    · exfalso
      apply hx
      simpa [hQx] using Q.simple
    · exact hQs
  obtain ⟨j, f, hf, hradSimple⟩ :=
    exists_indecomposable_quotient_with_simple_radical σ hx
  letI : Epi f := hf
  have huniqueJ : σ.HasUniqueSimpleQuotientType j s := by
    refine ⟨hs, ?_⟩
    intro Q
    letI : Epi Q.map := Q.epi
    let Qx : σ.SimpleQuotient x := {
      index := Q.index
      simple := Q.simple
      map := f ≫ Q.map
      epi := by infer_instance }
    exact huniqueX.2 Qx
  have htopIsotypic :
      IsIsotypicOfType R (σ.moduleTop j) (σ.obj s) :=
    moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
      σ huniqueJ
  letI : IsSimpleModule R (σ.moduleRadical j) :=
    hradSimple
  let Rad : FGModuleCat.{w} R :=
    FGModuleCat.of R (σ.moduleRadical j)
  have hRadIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Rad :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨t, ⟨eRad⟩⟩ := σ.complete Rad hRadIndec
  have hRadSimpleCat : Simple Rad :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Rad).2 inferInstance
  have htSimple : Simple (σ.obj t) :=
    (Simple.iff_of_iso eRad).mp hRadSimpleCat
  have hradIsotypic :
      IsIsotypicOfType R (σ.moduleRadical j) (σ.obj t) :=
    (IsIsotypicOfType.of_isSimpleModule R
      (σ.moduleRadical j)).of_linearEquiv_type
      (FGModuleCat.isoToLinearEquiv eRad)
  letI : IsSemisimpleModule R (σ.moduleRadical j) := by
    infer_instance
  have htopSimple : IsSimpleModule R (σ.moduleTop j) :=
    hclassification hs htSimple htopIsotypic inferInstance hradIsotypic
  letI : IsArtinian R (σ.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength j)).2
  have hjLengthModule : Module.length R (σ.obj j) = 2 := by
    rw [Module.length_eq_add_of_exact
      (σ.moduleRadical j).subtype
      (σ.moduleRadical j).mkQ
      (σ.moduleRadical j).subtype_injective
      (σ.moduleRadical j).mkQ_surjective
      (LinearMap.exact_subtype_mkQ (σ.moduleRadical j)),
      Module.length_eq_one R (σ.moduleRadical j),
      Module.length_eq_one R (σ.moduleTop j)]
    norm_num
  have hjLength : σ.compositionLength j = 2 := by
    rw [← ENat.coe_inj]
    rw [σ.coe_compositionLength j]
    calc
      Module.length R (σ.obj j) = 2 := hjLengthModule
      _ = (2 : ℕ∞) := rfl
  exact
    QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.IndecomposableSkeleton.compositionLength_eq_two_of_qClosed_pair_of_epi
      σ hclosed hs f hjLength

universe x

/-- The exact quotient-side level-two classification under the paper's
finite-dimensional representation-finite hypotheses. -/
noncomputable def qLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι),
      σ.QLevelTwoClassification := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ
  let top : ∀ z : σ.LengthTwoIndex, σ.SimpleQuotient z.1 :=
    fun z ↦ Classical.choice (σ.exists_simpleQuotient z.1)
  apply σ.qLevelTwoClassification_of_local top
  · intro z s hclosed hz hs
    exact
      compositionLength_eq_two_of_qClosed_pair_of_isotypicLoewyTwo
        σ
        (QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.isotypicLoewyTwoIndecomposablesHaveSimpleTop
          K A σ)
        hclosed hz hs
  · intro z
    exact
      QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.qClosure_isClosed_length_two_top_pair
        K A σ z.2 (top z)
        (Classical.choice (σ.exists_simpleSubmodule z.1))

/-- The exact submodule-side level-two classification, obtained by
contragredient transport to a finite aligned skeleton over the opposite
algebra. -/
noncomputable def sLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι),
      σ.SLevelTwoClassification := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K Aᵐᵒᵖ
  intro ι _ σ
  let τCanonical :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{x, x, x} K Aᵐᵒᵖ
  let DCanonical :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality
      K Aᵐᵒᵖ σ τCanonical
  let τ :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
        (Aᵐᵒᵖ)ᵐᵒᵖ ι :=
    relabelIndecomposableSkeleton τCanonical
      DCanonical.forward.labelEquiv
  let D :=
    QuotientSubmoduleEquidistribution.Contragredient.alignedBiduality K Aᵐᵒᵖ σ τ
  let hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        τ :=
    QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.isotypicLoewyTwoIndecomposablesHaveSimpleTop
      K Aᵐᵒᵖ τ
  let socle : ∀ z : σ.LengthTwoIndex, σ.SimpleSubmodule z.1 :=
    fun z ↦ Classical.choice (σ.exists_simpleSubmodule z.1)
  apply σ.sLevelTwoClassification_of_local socle
  · intro z s hclosed hz hs
    have hzDual :
        ¬ Simple (τ.obj (D.forward.labelEquiv z)) := by
      intro hsimple
      apply hz
      rw [← σ.compositionLength_eq_one_iff_simple]
      rw [←
        QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
          σ τ D.forward]
      exact (τ.compositionLength_eq_one_iff_simple _).2 hsimple
    have hsDual :
        Simple (τ.obj (D.forward.labelEquiv s)) := by
      rw [← τ.compositionLength_eq_one_iff_simple]
      rw [
        QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
          σ τ D.forward]
      exact (σ.compositionLength_eq_one_iff_simple _).2 hs
    have hclosedImage :=
      (QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.AlignedBiduality.sClosure_isClosed_iff_qClosure_image
        σ τ D ({z, s} : Set ι)).1 hclosed
    rw [Set.image_insert_eq, Set.image_singleton] at hclosedImage
    have hzLengthDual :
        τ.compositionLength (D.forward.labelEquiv z) = 2 :=
      compositionLength_eq_two_of_qClosed_pair_of_isotypicLoewyTwo
        τ hclassification hclosedImage hzDual hsDual
    rw [←
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedAntiEquivalence.compositionLength_eq
        σ τ D.forward]
    exact hzLengthDual
  · intro z
    exact
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.AlignedBiduality.sClosure_isClosed_length_two_pair_of_dual_isotypicLoewyTwo
        σ τ D z.2 (socle z) hclassification

/-- The manuscript's exact quotient-side level-two formula under its
finite-dimensional representation-finite hypotheses. -/
theorem qLevelCount_two_formula_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι),
      σ.qClosure.levelCount 2 =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.LengthTwoIndex := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ
  exact σ.qLevelCount_two_formula
    (qLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
      K A σ)

/-- The manuscript's exact submodule-side level-two formula under its
finite-dimensional representation-finite hypotheses. -/
theorem sLevelCount_two_formula_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι),
      σ.sClosure.levelCount 2 =
        Nat.choose (Nat.card σ.SimpleIndex) 2 +
          Nat.card σ.LengthTwoIndex := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ
  exact σ.sLevelCount_two_formula
    (sLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
      K A σ)

/-- Unconditional equality of the quotient and submodule closure counts at
level two for a finite complete right-module skeleton. -/
theorem qLevelCount_two_eq_sLevelCount_two_of_finiteDimensional_of_finiteSkeleton
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {ι : Type x} [Finite ι]
      (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x} Aᵐᵒᵖ ι),
      σ.qClosure.levelCount 2 = σ.sClosure.levelCount 2 := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro ι _ σ
  exact σ.qLevelCount_two_eq_sLevelCount_two
    (qLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
      K A σ)
    (sLevelTwoClassification_of_finiteDimensional_of_finiteSkeleton
      K A σ)

/-- Paper-facing canonical form: conventional right representation
finiteness implies unconditional equality of the quotient and submodule
counts at level two.  A finite `ULift` relabeling places the canonical
isomorphism-class type in the universe accepted by the concrete
classification theorem; level-polynomial invariance transports the result
back to the canonical skeleton. -/
theorem qLevelCount_two_eq_sLevelCount_two_of_rightRepresentationFinite
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A]
    (hrep : QuotientSubmoduleEquidistribution.IsRightRepresentationFinite.{x, x, x} K A) :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    letI : Finite
        (QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{x, x} Aᵐᵒᵖ) :=
      hrep
    let σ :=
      QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{x, x, x} K A
    σ.qClosure.levelCount 2 = σ.sClosure.levelCount 2 := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  let κ :=
    QuotientSubmoduleEquidistribution.CanonicalIndecomposableIndex.{x, x} Aᵐᵒᵖ
  letI : Finite κ := hrep
  letI : Fintype κ := Fintype.ofFinite κ
  let σ :=
    QuotientSubmoduleEquidistribution.rightIndecomposableSkeleton.{x, x, x} K A
  let ι := ULift.{x} (Fin (Fintype.card κ))
  let e : ι ≃ κ :=
    Equiv.ulift.trans (Fintype.equivFin κ).symm
  let τ :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
        Aᵐᵒᵖ ι :=
    relabelIndecomposableSkeleton σ e
  let E :
      QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence σ τ :=
    relabelAlignedEquivalence σ e
  have hsmall :
      τ.qClosure.levelCount 2 =
        τ.sClosure.levelCount 2 :=
    qLevelCount_two_eq_sLevelCount_two_of_finiteDimensional_of_finiteSkeleton
      K A τ
  have hq :
      σ.qClosure.levelPolynomial =
        τ.qClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.quotientLevelPolynomial_eq
      σ τ E
  have hs :
      σ.sClosure.levelPolynomial =
        τ.sClosure.levelPolynomial :=
    QuotientSubmoduleEquidistribution.IndecomposableSkeleton.AlignedEquivalence.submoduleLevelPolynomial_eq
      σ τ E
  calc
    σ.qClosure.levelCount 2 =
        σ.qClosure.levelPolynomial.coeff 2 := by
      rw [QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff]
    _ = τ.qClosure.levelPolynomial.coeff 2 :=
      congrArg (fun p ↦ p.coeff 2) hq
    _ = τ.qClosure.levelCount 2 :=
      QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff _ _
    _ = τ.sClosure.levelCount 2 := hsmall
    _ = τ.sClosure.levelPolynomial.coeff 2 := by
      rw [QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff]
    _ = σ.sClosure.levelPolynomial.coeff 2 :=
      congrArg (fun p ↦ p.coeff 2) hs.symm
    _ = σ.sClosure.levelCount 2 :=
      QuotientSubmoduleEquidistribution.SetClosure.levelPolynomial_coeff _ _

end QuotientSubmoduleEquidistribution.LevelTwoUnconditional
