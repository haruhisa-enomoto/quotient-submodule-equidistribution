import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateStandardKernelFiltration

/-!
# Highest-weight data from a coordinate right-rejective chain

This abstraction avoids any literal trace calculation.  At a deletion
step, the counit of the lower-term coreflector is used as the standard kernel
and its cokernel as the standard module.  An explicit coordinate-biproduct
presentation of each coreflector is the only chain-specific input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace QuotientSubmoduleEquidistribution.CPSLeftStandardLayers.Abstract

open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics
open QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent

universe uA uκ

variable {A : Type uA} [Ring A]
  {κ : Type uκ} [Fintype κ]

abbrev FiniteProjectives :=
  (AuslanderEquivalence.finiteProjectiveModules A).FullSubcategory

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

/-- An actual finite biproduct presentation by selected coordinates. -/
structure AddPresentation
    (P : κ → FiniteProjectives (A := A))
    (T : Set κ) (X : ModuleCat.{uA} A) where
  index : FintypeCat.{0}
  label : index → κ
  mem : ∀ t, label t ∈ T
  iso : X ≅ ⨁ fun t : index ↦ (P (label t)).obj

/-- All input needed to turn a saturated support deletion into an ordered
highest-weight structure.  `term i` is the coordinate additive subcategory
on `d.support i`, supplied with a right-rejective structure. -/
structure Input
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ) where
  projective : κ → FiniteProjectives (A := A)
  simple : κ → ModuleCat.{uA} A
  simple_isSimple : ∀ i, Simple (simple i)
  simple_complete :
    ∀ (S : ModuleCat.{uA} A), Simple S →
      ∃ i, Nonempty (S ≅ simple i)
  simple_nodup :
    ∀ {i j}, Nonempty (simple i ≅ simple j) → i = j
  hom_projective_simple_eq_zero_of_ne :
    ∀ {i j}, i ≠ j →
      ∀ f : (projective i).obj ⟶ simple j, f = 0
  cover : ∀ i, ProjectiveCover (simple i)
  coverIso : ∀ i, (cover i).object ≅ (projective i).obj
  finiteLength : ∀ i, IsFiniteLength A (projective i).obj
  term : Fin (Fintype.card κ + 1) →
    ObjectProperty (FiniteProjectives (A := A))
  termData : ∀ i, CategoricalRejective.RightRejectiveData (term i)
  coordinate_mem :
    ∀ i j, j ∈ d.support i → term i (projective j)
  presentation :
    ∀ i (X : FiniteProjectives (A := A)), term i X →
      AddPresentation (A := A) projective (d.support i) X.obj

namespace Input

variable {d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ}
  (I : Input (A := A) d)

local notation "n" => Fintype.card κ

/-- Vanishing of maps from a fixed object to every permitted layer passes
through a finite filtration by those layers. -/
theorem hom_eq_zero_of_filtered
    {ι : Type*} [LinearOrder ι]
    (layer : ι → ModuleCat.{uA} A)
    (allowed : ι → Prop)
    (P : ModuleCat.{uA} A)
    (hLayer : ∀ j, allowed j → ∀ f : P ⟶ layer j, f = 0)
    {X : ModuleCat.{uA} A}
    (hX : IsFilteredBy layer allowed X) :
    ∀ f : P ⟶ X, f = 0 := by
  induction hX with
  | zero X hzero =>
      intro f
      exact hzero.eq_of_tgt f 0
  | extension j hj f g zero exact tail ih =>
      intro q
      letI : Mono f := exact.mono_f
      have hqg : q ≫ g = 0 := ih (q ≫ g)
      let l := exact.exact.lift q hqg
      calc
        q = l ≫ f := (exact.exact.lift_f q hqg).symm
        _ = 0 ≫ f := congrArg (fun t ↦ t ≫ f) (hLayer j hj l)
        _ = 0 := zero_comp

/-- The chosen lower-term coreflector of the coordinate removed at `i`. -/
def kernelProjective (i : Fin n) : FiniteProjectives (A := A) :=
  let D := I.termData i.succ
  (D.coreflector.obj (I.projective (d.removed i))).obj

/-- The lower-term coreflector as an ambient left module. -/
abbrev kernel (i : Fin n) : ModuleCat.{uA} A :=
  (I.kernelProjective i).obj

/-- The monic coreflector counit into the removed coordinate projective. -/
def counit (i : Fin n) :
    I.kernel i ⟶ (I.projective (d.removed i)).obj :=
  let D := I.termData i.succ
  (D.adjunction.counit.app (I.projective (d.removed i))).hom

instance counit_mono (i : Fin n) : Mono (I.counit i) := by
  let D := I.termData i.succ
  haveI : Mono
      (D.adjunction.counit.app (I.projective (d.removed i))) :=
    D.counit_mono _
  rw [ModuleCat.mono_iff_injective]
  exact finiteProjective_mono_injective
    (D.adjunction.counit.app (I.projective (d.removed i)))

/-- The standard candidate is the cokernel of the lower-term coreflector
counit. -/
abbrev standardObject (i : Fin n) : ModuleCat.{uA} A :=
  cokernel (I.counit i)

/-- Projection from the chosen projective cover onto the standard
candidate. -/
def standardProjection (i : Fin n) :
    (I.cover (d.removed i)).object ⟶ I.standardObject i :=
  (I.coverIso (d.removed i)).hom ≫ cokernel.π (I.counit i)

instance standardProjection_epi (i : Fin n) :
    Epi (I.standardProjection i) := by
  dsimp [standardProjection]
  infer_instance

/-- Kernel inclusion, expressed in the actual chosen projective-cover
object. -/
def kernelι (i : Fin n) :
    I.kernel i ⟶ (I.cover (d.removed i)).object :=
  I.counit i ≫ (I.coverIso (d.removed i)).inv

theorem kernel_zero (i : Fin n) :
    I.kernelι i ≫ I.standardProjection i = 0 := by
  simp [kernelι, standardProjection, Category.assoc]

/-- The coreflector counit and its cokernel give the projective
presentation used by the highest-weight structure. -/
theorem kernel_shortExact (i : Fin n) :
    (ShortComplex.mk (I.kernelι i) (I.standardProjection i)
      (I.kernel_zero i)).ShortExact := by
  let c := I.counit i
  let S := ShortComplex.mk c (cokernel.π c) (cokernel.condition c)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel c }
  let T := ShortComplex.mk (I.kernelι i) (I.standardProjection i)
    (I.kernel_zero i)
  let e : S ≅ T :=
    ShortComplex.isoMk (Iso.refl _) (I.coverIso (d.removed i)).symm
      (Iso.refl _)
      (by simp [S, T, c, kernelι])
      (by simp [S, T, c, standardProjection])
  exact ShortComplex.shortExact_of_iso e hS

/-- The chosen coreflector has an actual coordinate-biproduct
presentation using labels surviving to the next support. -/
def kernelPresentation (i : Fin n) :
    AddPresentation I.projective (d.support i.succ) (I.kernel i) :=
  let D := I.termData i.succ
  I.presentation i.succ (I.kernelProjective i)
    (D.coreflector.obj (I.projective (d.removed i))).property

/-- The projective-cover map written with the coordinate projective itself
as source. -/
def coordinateCoverMap (j : κ) :
    (I.projective j).obj ⟶ I.simple j :=
  (I.coverIso j).inv ≫ (I.cover j).map

instance coordinateCoverMap_epi (j : κ) :
    Epi (I.coordinateCoverMap j) := by
  haveI : Epi (I.cover j).map := (I.cover j).essentialEpi.1
  dsimp [coordinateCoverMap]
  infer_instance

/-- A coordinate surviving after step `i` has no maps to simples removed no
later than step `i`. -/
theorem hom_simple_eq_zero_of_mem_later_support
    (i : Fin n) (j : κ) (hj : j ∈ d.support i.succ)
    (k : Fin n) (hki : k ≤ i)
    (f : (I.projective j).obj ⟶ I.simple (d.removed k)) :
    f = 0 := by
  apply I.hom_projective_simple_eq_zero_of_ne
  intro hjk
  subst j
  exact removed_not_mem_later_support d hki hj

/-- The simple-level vanishing propagates through every permitted finite
simple filtration. -/
theorem hom_eq_zero_of_mem_later_support_to_filtered
    (i : Fin n) (j : κ) (hj : j ∈ d.support i.succ)
    {X : ModuleCat.{uA} A}
    (hX : IsFilteredBy
      (fun k : Fin n ↦ I.simple (d.removed k))
      (fun k ↦ k ≤ i) X) :
    ∀ f : (I.projective j).obj ⟶ X, f = 0 := by
  apply hom_eq_zero_of_filtered _ _ _ _ hX
  intro k hki f
  exact I.hom_simple_eq_zero_of_mem_later_support i j hj k hki f

/-- The standard cokernel is right-orthogonal to every coordinate which
survives to the next term.  This follows directly from the coreflector
universal property, without identifying its image with a trace. -/
theorem hom_standardObject_eq_zero
    (i : Fin n) (j : κ) (hj : j ∈ d.support i.succ)
    (f : (I.projective j).obj ⟶ I.standardObject i) :
    f = 0 := by
  let D := I.termData i.succ
  let Pi := I.projective (d.removed i)
  let Pj := I.projective j
  letI : Projective Pj.obj := Pj.property.2
  let l : Pj.obj ⟶ (I.cover (d.removed i)).object :=
    Projective.factorThru f (I.standardProjection i)
  have hlf : l ≫ I.standardProjection i = f :=
    Projective.factorThru_comp f (I.standardProjection i)
  let lp : Pj.obj ⟶ Pi.obj :=
    l ≫ (I.coverIso (d.removed i)).hom
  let Xj : (I.term i.succ).FullSubcategory :=
    ⟨Pj, I.coordinate_mem i.succ j hj⟩
  let lpc : (I.term i.succ).ι.obj Xj ⟶ Pi :=
    ObjectProperty.homMk lp
  let g : Xj ⟶ D.coreflector.obj Pi :=
    D.adjunction.homEquiv Xj Pi lpc
  let gb : Pj.obj ⟶ I.kernel i :=
    ((I.term i.succ).ι.map g).hom
  have hfac :
      (I.term i.succ).ι.map g ≫ D.adjunction.counit.app Pi = lpc := by
    calc
      (I.term i.succ).ι.map g ≫ D.adjunction.counit.app Pi =
          (D.adjunction.homEquiv Xj Pi).symm g :=
        (D.adjunction.homEquiv_counit Xj Pi g).symm
      _ = lpc := Equiv.symm_apply_apply (D.adjunction.homEquiv Xj Pi) lpc
  have hfacBase := congrArg (fun q : Pj ⟶ Pi ↦ q.hom) hfac
  change
    gb ≫ I.counit i = lp
    at hfacBase
  rw [← hlf]
  change l ≫ (I.coverIso (d.removed i)).hom ≫
      cokernel.π (I.counit i) = 0
  rw [← Category.assoc]
  change lp ≫ cokernel.π (I.counit i) = 0
  rw [← hfacBase]
  change (gb ≫ I.counit i) ≫ cokernel.π (I.counit i) = 0
  calc
    (gb ≫ I.counit i) ≫ cokernel.π (I.counit i) =
        gb ≫ (I.counit i ≫ cokernel.π (I.counit i)) :=
      Category.assoc _ _ _
    _ = 0 := by rw [cokernel.condition, comp_zero]

/-- Finite length plus right orthogonality to all later coordinate
projectives produces a filtration by the permitted simples. -/
theorem isFilteredBy_of_finiteLength_of_hom_later_eq_zero
    (i : Fin n) (X : ModuleCat.{uA} A)
    (hXfinite : IsFiniteLength A X)
    (horth : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (I.projective j).obj ⟶ X, f = 0) :
    IsFilteredBy
      (fun k : Fin n ↦ I.simple (d.removed k))
      (fun k ↦ k ≤ i) X := by
  let motive : ℕ∞ → Prop := fun m ↦
    ∀ (Y : ModuleCat.{uA} A),
      IsFiniteLength A Y →
      Module.length A Y = m →
      (∀ (j : κ), j ∈ d.support i.succ →
        ∀ f : (I.projective j).obj ⟶ Y, f = 0) →
      IsFilteredBy
        (fun k : Fin n ↦ I.simple (d.removed k))
        (fun k ↦ k ≤ i) Y
  refine
    (WellFoundedLT.induction (motive := motive)
      (Module.length A X) ?_)
      X hXfinite rfl horth
  intro m ih Y hYfinite hYm hYorth
  by_cases hsub : Subsingleton Y
  · exact IsFilteredBy.zero Y
      ((ModuleCat.isZero_iff_subsingleton).mpr hsub)
  letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hsub
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hYfinite
  letI : IsNoetherian A Y := hNA.1
  letI : IsArtinian A Y := hNA.2
  obtain ⟨N, hNatom, -⟩ :=
    (eq_bot_or_exists_atom_le (⊤ : Submodule A Y)).resolve_left top_ne_bot
  have hNsimpleModule : IsSimpleModule A N :=
    isSimpleModule_iff_isAtom.mpr hNatom
  let S : ModuleCat.{uA} A := ModuleCat.of A N
  have hSsimple : Simple S :=
    simple_iff_isSimpleModule.mpr hNsimpleModule
  obtain ⟨k, ⟨e⟩⟩ := I.simple_complete S hSsimple
  obtain ⟨l, rfl⟩ := (removed_bijective d).2 k
  let nι : S ⟶ Y := ModuleCat.ofHom N.subtype
  letI : Mono nι := by
    rw [ModuleCat.mono_iff_injective]
    exact N.subtype_injective
  let a : I.simple (d.removed l) ⟶ Y := e.inv ≫ nι
  letI : Mono a := by
    dsimp [a]
    infer_instance
  have hli : l ≤ i := by
    by_contra hnot
    have hil : i < l := lt_of_not_ge hnot
    have hlower : d.removed l ∈ d.support i.succ :=
      later_removed_mem_support d hil
    have ha : a ≠ 0 := by
      intro ha
      letI : Simple (I.simple (d.removed l)) :=
        I.simple_isSimple (d.removed l)
      exact Simple.not_isZero (I.simple (d.removed l))
        (IsZero.of_mono_eq_zero a ha)
    have hPa : I.coordinateCoverMap (d.removed l) ≫ a ≠ 0 := by
      intro hPa
      apply ha
      rw [← cancel_epi (I.coordinateCoverMap (d.removed l))]
      simpa using hPa
    exact hPa <|
      hYorth (d.removed l) hlower
        (I.coordinateCoverMap (d.removed l) ≫ a)
  let Q : ModuleCat.{uA} A := ModuleCat.of A (Y ⧸ N)
  let g : Y ⟶ Q := ModuleCat.ofHom N.mkQ
  letI : Epi g := by
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.Quotient.mk_surjective N
  have hzero : a ≫ g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change N.mkQ (N.subtype (e.inv.hom x)) = 0
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    exact (e.inv.hom x).property
  have hshort :
      (ShortComplex.mk a g hzero).ShortExact := by
    constructor
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (N.subtype.comp e.inv.hom) =
      LinearMap.ker N.mkQ
    rw [LinearMap.range_comp]
    have heSurj : Function.Surjective e.inv.hom :=
      (ModuleCat.epi_iff_surjective e.inv).mp inferInstance
    rw [LinearMap.range_eq_top.mpr heSurj,
      Submodule.map_top, Submodule.range_subtype,
      Submodule.ker_mkQ]
  have hQfinite : IsFiniteLength A Q :=
    hYfinite.of_surjective (f := N.mkQ)
      (Submodule.Quotient.mk_surjective N)
  have hQorth : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (I.projective j).obj ⟶ Q, f = 0 := by
    intro j hj f
    letI : Projective (I.projective j).obj := (I.projective j).property.2
    let lift : (I.projective j).obj ⟶ Y :=
      Projective.factorThru f g
    calc
      f = lift ≫ g := (Projective.factorThru_comp f g).symm
      _ = 0 ≫ g := congrArg (fun t ↦ t ≫ g) (hYorth j hj lift)
      _ = 0 := zero_comp
  have hNne : N ≠ ⊥ := hNatom.ne_bot
  have hQlt : Module.length A Q < m := by
    rw [← hYm]
    exact Submodule.length_quotient_lt N hNne
  have htail :
      IsFilteredBy
        (fun k : Fin n ↦ I.simple (d.removed k))
        (fun k ↦ k ≤ i) Q :=
    ih (Module.length A Q) hQlt Q hQfinite rfl hQorth
  exact IsFilteredBy.extension l hli a g hzero hshort htail

/-- The standard cokernel has finite length. -/
theorem standardObject_isFiniteLength (i : Fin n) :
    IsFiniteLength A (I.standardObject i) := by
  apply (I.finiteLength (d.removed i)).of_surjective
    (f := (cokernel.π (I.counit i)).hom)
  exact (ModuleCat.epi_iff_surjective
    (cokernel.π (I.counit i))).mp inferInstance

/-- The coreflector cokernel has the required permitted simple
filtration. -/
theorem standardObject_simpleFiltered (i : Fin n) :
    IsFilteredBy
      (fun k : Fin n ↦ I.simple (d.removed k))
      (fun k ↦ k ≤ i) (I.standardObject i) :=
  I.isFilteredBy_of_finiteLength_of_hom_later_eq_zero i
    (I.standardObject i) (I.standardObject_isFiniteLength i)
    (I.hom_standardObject_eq_zero i)

/-- Every permitted simple-filtered quotient of the coordinate projective
kills the lower coreflector, hence factors through the standard cokernel. -/
theorem standardProjection_maximal
    (i : Fin n) {Q : ModuleCat.{uA} A}
    (q : (I.cover (d.removed i)).object ⟶ Q)
    (_hq : Epi q)
    (hQ : IsFilteredBy
      (fun k : Fin n ↦ I.simple (d.removed k))
      (fun k ↦ k ≤ i) Q) :
    ∃ u : I.standardObject i ⟶ Q,
      I.standardProjection i ≫ u = q := by
  let qP : (I.projective (d.removed i)).obj ⟶ Q :=
    (I.coverIso (d.removed i)).inv ≫ q
  have hkill : I.counit i ≫ qP = 0 := by
    let P := I.kernelPresentation i
    rw [← cancel_epi P.iso.inv]
    apply biproduct.hom_ext'
    intro t
    have hz := I.hom_eq_zero_of_mem_later_support_to_filtered
      i (P.label t) (P.mem t) hQ
      (biproduct.ι
        (fun t : P.index ↦ (I.projective (P.label t)).obj) t ≫
        P.iso.inv ≫ I.counit i ≫ qP)
    simpa only [Category.assoc, zero_comp, comp_zero] using hz
  let u : I.standardObject i ⟶ Q :=
    cokernel.desc (I.counit i) qP hkill
  refine ⟨u, ?_⟩
  dsimp [standardProjection, u, qP]
  simp [Category.assoc]

/-- The coreflector-cokernel construction supplies the full standard module
at every deletion step. -/
def standardModule (i : Fin n) :
    StandardModule
      (fun k : Fin n ↦ I.simple (d.removed k))
      (fun k ↦ I.cover (d.removed k)) i where
  object := I.standardObject i
  projection := I.standardProjection i
  epi_projection := I.standardProjection_epi i
  simpleFiltered := I.standardObject_simpleFiltered i
  maximal := by
    intro Q q hq hQ
    exact I.standardProjection_maximal i q hq hQ

/-- The coreflector kernels are filtered by standards removed strictly
later.  Descending induction uses only their coordinate-biproduct
presentations and extension-closure of finite filtrations. -/
theorem kernel_standardFiltered :
    ∀ i : Fin n,
      IsFilteredBy
        (fun j : Fin n ↦ (I.standardModule j).object)
        (fun j ↦ i < j) (I.kernel i) := by
  let layer : Fin n → ModuleCat.{uA} A :=
    fun j ↦ (I.standardModule j).object
  let motive : Fin n → Prop := fun i ↦
    IsFilteredBy layer (fun j ↦ i < j) (I.kernel i)
  intro i
  exact Finite.to_wellFoundedGT.wf.induction i (fun i ih ↦ by
    let P := I.kernelPresentation i
    have hcomponent : ∀ t : P.index,
        IsFilteredBy layer (fun j ↦ i < j)
          (I.projective (P.label t)).obj := by
      intro t
      obtain ⟨k, hk⟩ := (removed_bijective d).2 (P.label t)
      have hik : i < k := by
        by_contra hnot
        have hki : k ≤ i := le_of_not_gt hnot
        exact (removed_not_mem_later_support d hki) (hk ▸ P.mem t)
      have hKraw := ih k hik
      change IsFilteredBy layer (fun j ↦ k < j) (I.kernel k) at hKraw
      have hK : IsFilteredBy layer (fun j ↦ i < j) (I.kernel k) :=
        hKraw.mono_allowed layer (fun j hkj ↦ lt_trans hik hkj)
      have hDelta :
          IsFilteredBy layer (fun j ↦ i < j) (layer k) :=
        IsFilteredBy.single layer (fun j ↦ i < j) k hik
      have hCover :
          IsFilteredBy layer (fun j ↦ i < j)
            (I.cover (d.removed k)).object :=
        IsFilteredBy.extensionClosed layer (fun j ↦ i < j)
          (I.kernelι k) (I.standardProjection k)
          (I.kernel_zero k) (I.kernel_shortExact k) hK hDelta
      have hPk :
          IsFilteredBy layer (fun j ↦ i < j)
            (I.projective (d.removed k)).obj :=
        hCover.of_iso layer (fun j ↦ i < j)
          (I.coverIso (d.removed k))
      simpa only [hk] using hPk
    have hBip :
        IsFilteredBy layer (fun j ↦ i < j)
          (⨁ fun t : P.index ↦ (I.projective (P.label t)).obj) :=
      IsFilteredBy.fintype_biproduct layer (fun j ↦ i < j)
        (fun t : P.index ↦ (I.projective (P.label t)).obj)
        hcomponent
    change motive i
    exact hBip.of_iso layer (fun j ↦ i < j) P.iso.symm)

/-- A coordinate right-rejective deletion chain therefore determines an
ordered highest-weight structure. -/
def orderedHighestWeightStructure :
    OrderedHighestWeightStructure
      (ModuleCat.{uA} A) (Fin n) where
  simple k := I.simple (d.removed k)
  simple_isSimple k := I.simple_isSimple (d.removed k)
  simple_complete S hS := by
    obtain ⟨j, hj⟩ := I.simple_complete S hS
    obtain ⟨k, hk⟩ := (removed_bijective d).2 j
    exact ⟨k, hk ▸ hj⟩
  simple_nodup := by
    rintro i j ⟨e⟩
    apply (removed_injective d)
    exact I.simple_nodup ⟨e⟩
  cover k := I.cover (d.removed k)
  standard k := I.standardModule k
  kernel := I.kernel
  kernelι := I.kernelι
  kernel_zero := I.kernel_zero
  kernel_shortExact := I.kernel_shortExact
  kernel_standardFiltered := I.kernel_standardFiltered

/-- The coreflector kernels are finite projective by construction, so the
ordered highest-weight structure is right strong. -/
def rightStronglyQuasiHereditaryStructure :
    RightStronglyQuasiHereditaryStructure
      (ModuleCat.{uA} A) (Fin n) where
  toOrderedHighestWeightStructure :=
    I.orderedHighestWeightStructure
  kernel_projective i :=
    (I.kernelProjective i).property.2

end Input

end QuotientSubmoduleEquidistribution.CPSLeftStandardLayers.Abstract
