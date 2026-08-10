import QuotientSubmoduleEquidistribution.ConvexGeometry.Compact
import QuotientSubmoduleEquidistribution.RepresentationTheory.AdditiveSubcategory

/-!
# Approximations for quotient- and submodule-generated subcategories

This file directly proves the automatic contravariant-finiteness half of
Auslander--Smalø, Proposition 4.6(a), using the trace inclusion.  It proves
the dual covariant statement using the reject quotient, formalizes the
elementary finite-generation direction, and isolates the remaining
finite-`Fac` covariant-approximation theorem as an explicit property rather
than an axiom.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A right approximation of `X` by objects in the predicate `C`. -/
structure RightApproximation
    (C : FGModuleCat.{w} R → Prop) (X : FGModuleCat.{w} R) where
  object : FGModuleCat.{w} R
  mem : C object
  map : object ⟶ X
  factors :
    ∀ {Y : FGModuleCat.{w} R}, C Y → ∀ f : Y ⟶ X,
      ∃ g : Y ⟶ object, g ≫ map = f

/-- A left approximation of `X` by objects in the predicate `C`. -/
structure LeftApproximation
    (C : FGModuleCat.{w} R → Prop) (X : FGModuleCat.{w} R) where
  object : FGModuleCat.{w} R
  mem : C object
  map : X ⟶ object
  factors :
    ∀ {Y : FGModuleCat.{w} R}, C Y → ∀ f : X ⟶ Y,
      ∃ g : object ⟶ Y, map ≫ g = f

/-- Every target has a right `C`-approximation. -/
def IsContravariantlyFinite
    (C : FGModuleCat.{w} R → Prop) : Prop :=
  ∀ X, Nonempty (RightApproximation C X)

/-- Every source has a left `C`-approximation. -/
def IsCovariantlyFinite
    (C : FGModuleCat.{w} R → Prop) : Prop :=
  ∀ X, Nonempty (LeftApproximation C X)

/-- Both approximation conditions. -/
def IsFunctoriallyFinite
    (C : FGModuleCat.{w} R → Prop) : Prop :=
  IsContravariantlyFinite C ∧ IsCovariantlyFinite C

/-- The trace, bundled as a finitely generated module. -/
abbrev traceObject (S : Set ι) (X : FGModuleCat.{w} R) :
    FGModuleCat.{w} R :=
  FGModuleCat.of R (σ.trace S X)

/-- The canonical inclusion of the trace object. -/
def traceι (S : Set ι) (X : FGModuleCat.{w} R) :
    σ.traceObject S X ⟶ X :=
  ConcreteCategory.ofHom (σ.trace S X).subtype

namespace SelectedMapTo

/-- Flatten a finite family of selected maps into one selected map. -/
def flattenForApproximation
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X)) :
    σ.SelectedMapTo S X := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let J : FintypeCat.{0} :=
    FintypeCat.of (Σ t : outer, (pick t).index)
  let a : J → ι :=
    fun p ↦ (pick p.1).label p.2
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver J a :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  exact
    { index := J
      label := a
      mem := fun p ↦ (pick p.1).mem p.2
      map := flattenIso.inv ≫
        biproduct.desc (fun t ↦ (pick t).map) }

/-- Every member of a finite family factors through its flattened map. -/
theorem range_le_flattenForApproximation
    {S : Set ι} {X : FGModuleCat.{w} R}
    (F : Finset (σ.SelectedMapTo S X))
    (f : σ.SelectedMapTo S X) (hf : f ∈ F) :
    LinearMap.range f.map.hom.hom ≤
      LinearMap.range
        (flattenForApproximation σ F).map.hom.hom := by
  classical
  let outer : FintypeCat.{0} := FintypeCat.of (Fin F.card)
  let pick : outer → σ.SelectedMapTo S X :=
    fun t ↦ (F.equivFin.symm t).1
  let t : outer := F.equivFin ⟨f, hf⟩
  have hpick : pick t = f := by
    simp [pick, t]
  rw [← hpick]
  let flattenIso :
      (⨁ fun t : outer ↦
        σ.sumOver (pick t).index (pick t).label) ≅
        σ.sumOver
          (FintypeCat.of (Σ t : outer, (pick t).index))
          (fun p ↦ (pick p.1).label p.2) :=
    biproductBiproductIso
      (fun t : outer ↦ (pick t).index)
      (fun t s ↦ σ.obj ((pick t).label s))
  let e :
      σ.sumOver (pick t).index (pick t).label ⟶
        σ.sumOver
          (flattenForApproximation σ F).index
          (flattenForApproximation σ F).label :=
    biproduct.ι (fun t : outer ↦
      σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom
  have hfac :
      e ≫ (flattenForApproximation σ F).map =
        (pick t).map := by
    dsimp only [e, flattenForApproximation]
    change
      (biproduct.ι (fun t : outer ↦
          σ.sumOver (pick t).index (pick t).label) t ≫
        flattenIso.hom) ≫
          (flattenIso.inv ≫
            biproduct.desc (fun t ↦ (pick t).map)) =
        (pick t).map
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact biproduct.ι_desc _ _
  have hlinear := congrArg (fun q ↦ q.hom.hom) hfac
  simp only [FGModuleCat.hom_hom_comp] at hlinear
  rw [← hlinear]
  exact LinearMap.range_comp_le_range e.hom.hom
    (flattenForApproximation σ F).map.hom.hom

end SelectedMapTo

/-- The trace submodule is the range of one map from a finite direct sum
of selected representatives. -/
theorem exists_selectedMapTo_range_eq_trace
    (S : Set ι) (X : FGModuleCat.{w} R) :
    ∃ f : σ.SelectedMapTo S X,
      LinearMap.range f.map.hom.hom = σ.trace S X := by
  classical
  have hcompact :
      IsCompactElement (σ.trace S X) := by
    obtain ⟨G, hG⟩ :=
      IsNoetherian.noetherian (σ.trace S X)
    rw [← hG]
    exact Submodule.finset_span_isCompactElement G
  have hle :
      σ.trace S X ≤
        ⨆ f : σ.SelectedMapTo S X,
          LinearMap.range f.map.hom.hom :=
    le_rfl
  obtain ⟨F, hF⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
      (Submodule R X) hcompact
      (fun f : σ.SelectedMapTo S X ↦
        LinearMap.range f.map.hom.hom) hle
  let f := SelectedMapTo.flattenForApproximation σ F
  refine ⟨f, le_antisymm (range_le_trace σ f) ?_⟩
  refine hF.trans ?_
  refine iSup_le fun g ↦ iSup_le fun hg ↦ ?_
  exact SelectedMapTo.range_le_flattenForApproximation σ F g hg

/-- The trace object is itself generated by quotients of finite selected
sums. -/
theorem traceObject_inFac
    (S : Set ι) (X : FGModuleCat.{w} R) :
    σ.InFac S (σ.traceObject S X) := by
  classical
  obtain ⟨f, hf⟩ :=
    exists_selectedMapTo_range_eq_trace σ S X
  let qlin :
      σ.sumOver f.index f.label →ₗ[R] σ.trace S X :=
    f.map.hom.hom.codRestrict (σ.trace S X) fun y ↦
      range_le_trace σ f ⟨y, rfl⟩
  let q :
      σ.sumOver f.index f.label ⟶ σ.traceObject S X :=
    ConcreteCategory.ofHom qlin
  refine ⟨{
    index := f.index
    label := f.label
    mem := f.mem
    map := q
    epi := ?_ }⟩
  apply (fg_epi_iff_surjective q).2
  intro z
  have hz :
      (z : X) ∈ LinearMap.range f.map.hom.hom := by
    rw [hf]
    exact z.property
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- Every map from an object of `Fac(add S)` has image in the trace. -/
theorem range_le_trace_of_inFac
    {S : Set ι} {Y X : FGModuleCat.{w} R}
    (hY : σ.InFac S Y) (f : Y ⟶ X) :
    LinearMap.range f.hom.hom ≤ σ.trace S X := by
  obtain ⟨P⟩ := hY
  let g : σ.SelectedMapTo S X :=
    { index := P.index
      label := P.label
      mem := P.mem
      map := P.map ≫ f }
  intro y
  rintro ⟨x, rfl⟩
  letI : Epi P.map := P.epi
  obtain ⟨z, hz⟩ :=
    ((fg_epi_iff_surjective P.map).1 inferInstance) x
  have hg :
      f.hom.hom x = g.map.hom.hom z := by
    dsimp only [g]
    simp only [FGModuleCat.hom_hom_comp, LinearMap.comp_apply, hz]
  rw [hg]
  exact range_le_trace σ g ⟨z, rfl⟩

/-- Every `Fac(add S)` is contravariantly finite.  The right approximation
of `X` is the inclusion of its trace. -/
theorem inFac_isContravariantlyFinite
    (S : Set ι) :
    IsContravariantlyFinite (σ.InFac S) := by
  intro X
  refine ⟨{
    object := σ.traceObject S X
    mem := traceObject_inFac σ S X
    map := σ.traceι S X
    factors := ?_ }⟩
  intro Y hY f
  let glin :
      Y →ₗ[R] σ.trace S X :=
    f.hom.hom.codRestrict (σ.trace S X) fun y ↦
      range_le_trace_of_inFac σ hY f ⟨y, rfl⟩
  let g : Y ⟶ σ.traceObject S X :=
    ConcreteCategory.ofHom glin
  refine ⟨g, ?_⟩
  apply FGModuleCat.hom_ext
  ext y
  rfl

/-- The quotient by the reject, bundled as a finitely generated module. -/
abbrev rejectQuotientObject
    (S : Set ι) (X : FGModuleCat.{w} R) :
    FGModuleCat.{w} R :=
  FGModuleCat.of R (X ⧸ σ.reject S X)

/-- The canonical projection onto the quotient by the reject. -/
def rejectπ (S : Set ι) (X : FGModuleCat.{w} R) :
    X ⟶ σ.rejectQuotientObject S X :=
  ConcreteCategory.ofHom (σ.reject S X).mkQ

/-- For a finite-length target, the quotient by the reject embeds into one
finite selected sum. -/
theorem rejectQuotientObject_inSub
    (S : Set ι) (X : FGModuleCat.{w} R)
    (hX : IsFiniteLength R X) :
    σ.InSub S (σ.rejectQuotientObject S X) := by
  classical
  obtain ⟨F, hF⟩ := exists_finset_reject_eq σ S X hX
  let f := SelectedMapFrom.flattenFinset σ F
  have hker_le :
      LinearMap.ker f.map.hom.hom ≤
        ⨅ g ∈ F, LinearMap.ker g.map.hom.hom := by
    rw [le_iInf_iff]
    intro g
    rw [le_iInf_iff]
    intro hg
    exact SelectedMapFrom.ker_flattenFinset_le σ F g hg
  have hker :
      LinearMap.ker f.map.hom.hom = σ.reject S X :=
    le_antisymm (hker_le.trans_eq hF)
      (reject_le_ker σ f)
  let qlin :
      (X ⧸ σ.reject S X) →ₗ[R]
        σ.sumOver f.index f.label :=
    (σ.reject S X).liftQ f.map.hom.hom
      (reject_le_ker σ f)
  let q :
      σ.rejectQuotientObject S X ⟶
        σ.sumOver f.index f.label :=
    ConcreteCategory.ofHom qlin
  refine ⟨{
    index := f.index
    label := f.label
    mem := f.mem
    map := q
    mono := ?_ }⟩
  apply (fg_mono_iff_injective q).2
  apply LinearMap.ker_eq_bot.1
  exact Submodule.ker_liftQ_eq_bot
    (σ.reject S X) f.map.hom.hom
      (reject_le_ker σ f) hker.le

/-- Every map into an object of `Sub(add S)` kills the reject. -/
theorem reject_le_ker_of_inSub
    {S : Set ι} {X Y : FGModuleCat.{w} R}
    (hY : σ.InSub S Y) (f : X ⟶ Y) :
    σ.reject S X ≤ LinearMap.ker f.hom.hom := by
  obtain ⟨P⟩ := hY
  let g : σ.SelectedMapFrom S X :=
    { index := P.index
      label := P.label
      mem := P.mem
      map := f ≫ P.map }
  letI : Mono P.map := P.mono
  intro x hx
  rw [LinearMap.mem_ker]
  apply (fg_mono_iff_injective P.map).1 inferInstance
  have hg := reject_le_ker σ g hx
  rw [LinearMap.mem_ker] at hg
  simpa only [g, FGModuleCat.hom_hom_comp,
    LinearMap.comp_apply, map_zero] using hg

/-- If every finitely generated module has finite length, every
`Sub(add S)` is covariantly finite.  Its left approximation is the quotient
by the reject. -/
theorem inSub_isCovariantlyFinite
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (S : Set ι) :
    IsCovariantlyFinite (σ.InSub S) := by
  intro X
  refine ⟨{
    object := σ.rejectQuotientObject S X
    mem := rejectQuotientObject_inSub σ S X (hfinite X)
    map := σ.rejectπ S X
    factors := ?_ }⟩
  intro Y hY f
  let glin :
      (X ⧸ σ.reject S X) →ₗ[R] Y :=
    (σ.reject S X).liftQ f.hom.hom
      (reject_le_ker_of_inSub σ hY f)
  let g : σ.rejectQuotientObject S X ⟶ Y :=
    ConcreteCategory.ofHom glin
  refine ⟨g, ?_⟩
  apply FGModuleCat.hom_ext
  exact (σ.reject S X).liftQ_mkQ f.hom.hom
    (reject_le_ker_of_inSub σ hY f)

/-- On a quotient-closed support, literal additive membership and quotient
generation agree. -/
theorem inAdd_iff_inFac_of_qClosed
    {S : Set ι} (hS : σ.qClosure.IsClosed S)
    (X : FGModuleCat.{w} R) :
    σ.InAdd S X ↔ σ.InFac S X := by
  constructor
  · rintro ⟨P⟩
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := P.iso.inv
      epi := inferInstance }⟩
  · intro hX
    have h := inAdd_qSet_of_inFac σ hX
    have hq : σ.qSet S = S := hS.closure_eq
    rwa [hq] at h

/-- On a subobject-closed support, literal additive membership and
submodule generation agree. -/
theorem inAdd_iff_inSub_of_sClosed
    {S : Set ι} (hS : σ.sClosure.IsClosed S)
    (X : FGModuleCat.{w} R) :
    σ.InAdd S X ↔ σ.InSub S X := by
  constructor
  · rintro ⟨P⟩
    exact ⟨{
      index := P.index
      label := P.label
      mem := P.mem
      map := P.iso.hom
      mono := inferInstance }⟩
  · intro hX
    have h := inAdd_sSet_of_inSub σ hX
    have hs : σ.sSet S = S := hS.closure_eq
    rwa [hs] at h

/-- A literal quotient-closed additive subcategory is exactly
`Fac(add S)` for its indecomposable support `S`. -/
theorem quotientClosedAdditiveSubcategory_carrier_eq_inFac_support
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (C : QuotientClosedAdditiveSubcategory.{u, w} (R := R)) :
    C.1.carrier = σ.InFac (σ.support C.1) := by
  let S := σ.support C.1
  have hS : σ.qClosure.IsClosed S := by
    apply (qClosed_iff_generated_isClosedUnderQuotients σ S).2
    rw [generated_support σ C.1]
    exact C.2
  funext X
  apply propext
  rw [← inAdd_iff_inFac_of_qClosed σ hS X]
  dsimp only [S]
  change C.1.carrier X ↔
    (σ.generated (σ.support C.1)).carrier X
  rw [generated_support σ C.1]

/-- A literal subobject-closed additive subcategory is exactly
`Sub(add S)` for its indecomposable support `S`. -/
theorem subobjectClosedAdditiveSubcategory_carrier_eq_inSub_support
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (C : SubobjectClosedAdditiveSubcategory.{u, w} (R := R)) :
    C.1.carrier = σ.InSub (σ.support C.1) := by
  let S := σ.support C.1
  have hS : σ.sClosure.IsClosed S := by
    apply (sClosed_iff_generated_isClosedUnderSubobjects σ S).2
    rw [generated_support σ C.1]
    exact C.2
  funext X
  apply propext
  rw [← inAdd_iff_inSub_of_sClosed σ hS X]
  dsimp only [S]
  change C.1.carrier X ↔
    (σ.generated (σ.support C.1)).carrier X
  rw [generated_support σ C.1]

/-- Exact literal-subcategory form of the automatic
Auslander--Smalø contravariant-finiteness theorem. -/
theorem quotientClosedAdditiveSubcategory_isContravariantlyFinite
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (C : QuotientClosedAdditiveSubcategory.{u, w} (R := R)) :
    IsContravariantlyFinite C.1.carrier := by
  rw [quotientClosedAdditiveSubcategory_carrier_eq_inFac_support σ C]
  exact inFac_isContravariantlyFinite σ (σ.support C.1)

/-- Exact literal-subcategory form of the dual automatic covariant
finiteness theorem. -/
theorem subobjectClosedAdditiveSubcategory_isCovariantlyFinite
    (σ : IndecomposableSkeleton.{u, v, w} R ι)
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    (C : SubobjectClosedAdditiveSubcategory.{u, w} (R := R)) :
    IsCovariantlyFinite C.1.carrier := by
  rw [subobjectClosedAdditiveSubcategory_carrier_eq_inSub_support σ C]
  exact inSub_isCovariantlyFinite σ hfinite (σ.support C.1)

/-- Quotient generation is closed under postcomposition with an
epimorphism. -/
theorem inFac_of_epi
    {S : Set ι} {Y X : FGModuleCat.{w} R}
    (hY : σ.InFac S Y) (f : Y ⟶ X) [Epi f] :
    σ.InFac S X := by
  obtain ⟨P⟩ := hY
  letI : Epi P.map := P.epi
  exact ⟨{
    index := P.index
    label := P.label
    mem := P.mem
    map := P.map ≫ f
    epi := inferInstance }⟩

/-- A finite biproduct of quotient-generated objects is again
quotient-generated. -/
theorem inFac_biproduct
    {S : Set ι}
    (J : FintypeCat.{0}) (F : J → FGModuleCat.{w} R)
    (hF : ∀ j, σ.InFac S (F j)) :
    σ.InFac S (biproduct F) := by
  classical
  let inner : ∀ j : J, σ.FacPresentation S (F j) :=
    fun j ↦ Classical.choice (hF j)
  let K : FintypeCat.{0} :=
    FintypeCat.of (Σ j : J, (inner j).index)
  let a : K → ι :=
    fun p ↦ (inner p.1).label p.2
  let flattenIso :
      (⨁ fun j : J ↦
        σ.sumOver (inner j).index (inner j).label) ≅
        σ.sumOver K a :=
    biproductBiproductIso
      (fun j : J ↦ (inner j).index)
      (fun j t ↦ σ.obj ((inner j).label t))
  let q :
      σ.sumOver K a ⟶ biproduct F :=
    flattenIso.inv ≫ biproduct.map (fun j ↦ (inner j).map)
  refine ⟨{
    index := K
    label := a
    mem := fun p ↦ (inner p.1).mem p.2
    map := q
    epi := ?_ }⟩
  letI (j : J) : Epi (inner j).map := (inner j).epi
  dsimp only [q]
  infer_instance

/-- A finite additive generator for the ambient category: every object is a
quotient of a finite biproduct of copies of `G`. -/
def IsFiniteGenerator (G : FGModuleCat.{w} R) : Prop :=
  ∀ X : FGModuleCat.{w} R,
    ∃ (J : FintypeCat.{0})
      (p : (⨁ fun _ : J ↦ G) ⟶ X), Epi p

/-- In the same universe as the ring, the regular module is a finite
generator of `FGModuleCat`. -/
theorem regularObject_isFiniteGenerator
    (R : Type u) [Ring R] [IsNoetherianRing R] :
    IsFiniteGenerator (FGModuleCat.of R R) := by
  classical
  intro X
  obtain ⟨G, hG⟩ :=
    (inferInstance : Module.Finite R X).fg_top
  let J : FintypeCat.{0} := FintypeCat.of (Fin G.card)
  let pick (t : J) : X := (G.equivFin.symm t).1
  let q :
      (⨁ fun _ : J ↦ FGModuleCat.of R R) ⟶ X :=
    biproduct.desc fun t ↦
      ConcreteCategory.ofHom
        (LinearMap.toSpanSingleton R X (pick t))
  refine ⟨J, q, ?_⟩
  apply (fg_epi_iff_surjective q).2
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← hG, Submodule.span_le]
  intro x hx
  let t : J := G.equivFin ⟨x, hx⟩
  have hpick : pick t = x := by
    simp [pick, t]
  let y :=
    (biproduct.ι
      (fun _ : J ↦
        (FGModuleCat.of R R : FGModuleCat.{u} R)) t).hom.hom (1 : R)
  refine ⟨y, ?_⟩
  calc
    q.hom.hom y =
        ((biproduct.ι
          (fun _ : J ↦
            (FGModuleCat.of R R : FGModuleCat.{u} R)) t ≫ q).hom.hom) 1 := rfl
    _ =
        (LinearMap.toSpanSingleton R X (pick t)) 1 := by
      rw [biproduct.ι_desc]
      rfl
    _ = pick t :=
      LinearMap.toSpanSingleton_apply_one R X (pick t)
    _ = x := hpick

/-- A left approximation of a finite generator already forces one finite
subset of the chosen support to generate the whole quotient class.

This is the elementary `covariantly finite -> finite cover` direction in
Auslander--Smalø Proposition 4.6(c). -/
theorem finite_support_of_generator_leftApproximation
    {S : Set ι}
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    (L : LeftApproximation (σ.InFac S) G) :
    ∃ B : Set ι, B.Finite ∧ B ⊆ S ∧
      ∀ X : FGModuleCat.{w} R,
        σ.InFac S X → σ.InFac B X := by
  classical
  obtain ⟨P⟩ := L.mem
  let B : Set ι := Set.range P.label
  have hBfinite : B.Finite := Set.finite_range P.label
  have hBS : B ⊆ S := by
    rintro i ⟨t, rfl⟩
    exact P.mem t
  have hLB : σ.InFac B L.object :=
    ⟨{
      index := P.index
      label := P.label
      mem := fun t ↦ ⟨t, rfl⟩
      map := P.map
      epi := P.epi }⟩
  refine ⟨B, hBfinite, hBS, ?_⟩
  intro X hX
  obtain ⟨J, p, hp⟩ := hG X
  let pointMap (t : J) : G ⟶ X :=
    biproduct.ι (fun _ : J ↦ G) t ≫ p
  let factor (t : J) : L.object ⟶ X :=
    Classical.choose (L.factors hX (pointMap t))
  have factor_spec (t : J) :
      L.map ≫ factor t = pointMap t :=
    Classical.choose_spec (L.factors hX (pointMap t))
  let q : (⨁ fun _ : J ↦ L.object) ⟶ X :=
    biproduct.desc factor
  have hqepi : Epi q := by
    let a :
        (⨁ fun _ : J ↦ G) ⟶
          (⨁ fun _ : J ↦ L.object) :=
      biproduct.map (fun _ ↦ L.map)
    have ha : a ≫ q = p := by
      apply biproduct.hom_ext'
      intro t
      simpa only [a, q, pointMap, Category.assoc,
        biproduct.ι_map_assoc, biproduct.ι_desc] using
        factor_spec t
    letI : Epi p := hp
    haveI : Epi (a ≫ q) := ha ▸ inferInstance
    exact epi_of_epi a q
  letI : Epi q := hqepi
  have hsum :
      σ.InFac B (⨁ fun _ : J ↦ L.object) :=
    inFac_biproduct σ J (fun _ ↦ L.object) fun _ ↦ hLB
  exact inFac_of_epi σ hsum q

/-- Covariant finiteness of `Fac(add S)` forces a finite subset of `S` to
have the same quotient closure. -/
theorem isCovariantlyFinite_inFac_imp_exists_finite_generator
    {S : Set ι}
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    (hcov : IsCovariantlyFinite (σ.InFac S)) :
    ∃ B : Set ι, B.Finite ∧ B ⊆ S ∧
      σ.qClosure B = σ.qClosure S := by
  obtain ⟨L⟩ := hcov G
  obtain ⟨B, hBfinite, hBS, hgen⟩ :=
    finite_support_of_generator_leftApproximation σ G hG L
  refine ⟨B, hBfinite, hBS, Set.Subset.antisymm ?_ ?_⟩
  · exact qSet_monotone σ hBS
  · intro j hj
    exact hgen (σ.obj j) hj

/-- Thus functorial finiteness also forces a finite quotient generator. -/
theorem isFunctoriallyFinite_inFac_imp_exists_finite_generator
    {S : Set ι}
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    (hff : IsFunctoriallyFinite (σ.InFac S)) :
    ∃ B : Set ι, B.Finite ∧ B ⊆ S ∧
      σ.qClosure B = σ.qClosure S :=
  isCovariantlyFinite_inFac_imp_exists_finite_generator σ G hG hff.2

/-- Quotient generation depends only on the quotient closure of the
selected support. -/
theorem inFac_iff_of_qClosure_eq
    {S T : Set ι} (hST : σ.qClosure S = σ.qClosure T)
    (X : FGModuleCat.{w} R) :
    σ.InFac S X ↔ σ.InFac T X := by
  change σ.qSet S = σ.qSet T at hST
  constructor
  · rintro ⟨P⟩
    let Q : σ.FacPresentation (σ.qSet T) X :=
      { index := P.index
        label := P.label
        mem := fun t ↦ by
          rw [← hST]
          exact subset_qSet σ S (P.mem t)
        map := P.map
        epi := P.epi }
    exact inFac_trans σ Q
  · rintro ⟨P⟩
    let Q : σ.FacPresentation (σ.qSet S) X :=
      { index := P.index
        label := P.label
        mem := fun t ↦ by
          rw [hST]
          exact subset_qSet σ T (P.mem t)
        map := P.map
        epi := P.epi }
    exact inFac_trans σ Q

/-- The one genuinely classical input still needed for the forward
approximation direction: finitely generated quotient classes are
covariantly finite. -/
def FiniteFacCovariantlyFinite : Prop :=
  ∀ (B : Set ι), B.Finite →
    IsCovariantlyFinite (σ.InFac B)

/-- Functorial finiteness implies compactness, with no use of the missing
finite-cover theorem. -/
theorem isCompactElement_of_inFac_functoriallyFinite
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    {C : σ.qClosure.Closeds}
    (hff : IsFunctoriallyFinite (σ.InFac (C : Set ι))) :
    IsCompactElement C := by
  obtain ⟨B, hBfinite, -, hBC⟩ :=
    isFunctoriallyFinite_inFac_imp_exists_finite_generator
      σ G hG hff
  have hcompact :
      IsCompactElement (σ.qClosure.toCloseds B) :=
    QuotientSubmoduleEquidistribution.SetClosure.finiteClosure_isCompactElement
      (qClosure_isFinitary σ) hBfinite
  have hEq : σ.qClosure.toCloseds B = C := by
    apply Subtype.ext
    exact hBC.trans C.2.closure_eq
  exact hEq ▸ hcompact

/-- Assuming precisely the finite-cover/covariant-approximation input, compact
quotient-closed classes are functorially finite. -/
theorem inFac_functoriallyFinite_of_isCompactElement
    (hAS : FiniteFacCovariantlyFinite σ)
    {C : σ.qClosure.Closeds} (hcompact : IsCompactElement C) :
    IsFunctoriallyFinite (σ.InFac (C : Set ι)) := by
  obtain ⟨B, hBfinite, -, hBC⟩ :=
    QuotientSubmoduleEquidistribution.SetClosure.exists_finite_generator_of_isCompactElement
      hcompact
  have hclosure :
      σ.qClosure B = σ.qClosure (C : Set ι) := by
    rw [hBC, C.2.closure_eq]
  have hpred :
      σ.InFac B = σ.InFac (C : Set ι) := by
    funext X
    exact propext (inFac_iff_of_qClosure_eq σ hclosure X)
  constructor
  · exact inFac_isContravariantlyFinite σ (C : Set ι)
  · rw [← hpred]
    exact hAS B hBfinite

/-- Exact chosen-skeleton form of compactness versus functorial finiteness,
conditional only on the isolated Auslander--Smalø finite-cover theorem. -/
theorem isCompactElement_iff_inFac_functoriallyFinite
    (G : FGModuleCat.{w} R) (hG : IsFiniteGenerator G)
    (hAS : FiniteFacCovariantlyFinite σ)
    {C : σ.qClosure.Closeds} :
    IsCompactElement C ↔
      IsFunctoriallyFinite (σ.InFac (C : Set ι)) :=
  ⟨inFac_functoriallyFinite_of_isCompactElement σ hAS,
    isCompactElement_of_inFac_functoriallyFinite σ G hG⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton

namespace QuotientSubmoduleEquidistribution.SetClosure

variable {E : Type*} (c : SetClosure E)

/-- Pointwise irredundancy is exactly minimality of a set as a generator
of its own closure.  On an indecomposable skeleton this is the support-level
form of normality. -/
theorem isMinimalGenerator_closure_iff_pointwise
    (B : Set E) :
    c.IsMinimalGenerator B (c B) ↔
      ∀ ⦃b : E⦄, b ∈ B → b ∉ c (B \ {b}) := by
  constructor
  · intro h b hbB hb
    apply h.2 hbB
    apply Set.Subset.antisymm
    · exact c.monotone Set.sdiff_subset
    · apply c.closure_min
      · intro x hxB
        by_cases hxb : x = b
        · simpa [hxb] using hb
        · exact c.le_closure (B \ {b})
            ⟨hxB, by simpa using hxb⟩
      · exact c.isClosed_closure _
  · intro h
    refine ⟨rfl, ?_⟩
    intro b hbB heq
    apply h hbB
    rw [heq]
    exact c.le_closure B hbB

/-- Finite irredundant supports: the closure-theoretic model of
isomorphism classes of basic normal modules. -/
abbrev NormalFiniteSupport :=
  {B : Set E //
    B.Finite ∧ c.IsMinimalGenerator B (c B)}

/-- Compact closed sets, bundled for the normal-support classification. -/
abbrev CompactClosed :=
  {C : c.Closeds // IsCompactElement C}

/-- Finite normal supports are canonically equivalent to compact closed
sets.  For quotient closure, this is the support-level core of the
basic-normal-module classification. -/
def normalFiniteSupportEquivCompactClosed
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange) :
    c.NormalFiniteSupport ≃ c.CompactClosed where
  toFun B :=
    ⟨c.toCloseds B.1,
      finiteClosure_isCompactElement hfin B.2.1⟩
  invFun C :=
    ⟨c.extremePoints (C.1 : Set E), by
      have hbasis :=
        compact_extremePoints_basis hfin hae C.2
      refine ⟨hbasis.1, ?_⟩
      rw [hbasis.2.1]
      exact hbasis.2⟩
  left_inv B := by
    apply Subtype.ext
    exact
      (finite_minimalGenerator_eq_extremePoints
        hfin hae (c.isClosed_closure B.1) B.2.2).symm
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      (compact_extremePoints_basis hfin hae C.2).2.1

end QuotientSubmoduleEquidistribution.SetClosure
