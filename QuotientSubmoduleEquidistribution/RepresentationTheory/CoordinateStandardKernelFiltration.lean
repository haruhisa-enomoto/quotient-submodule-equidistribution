import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateStandardQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagAuslanderPackage

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w}

/-- A finite filtration is invariant under isomorphism of its filtered
object. -/
theorem IsFilteredBy.of_iso
    (layer : ι → C) (allowed : ι → Prop)
    {X Y : C} (hX : IsFilteredBy layer allowed X)
    (e : X ≅ Y) :
    IsFilteredBy layer allowed Y := by
  cases hX with
  | zero X hzero =>
      exact IsFilteredBy.zero Y (hzero.of_iso e.symm)
  | extension i hi f g zero exact tail =>
      let f' := f ≫ e.hom
      let g' := e.inv ≫ g
      have hzero : f' ≫ g' = 0 := by
        simp [f', g', Category.assoc, zero]
      have hshort :
          (ShortComplex.mk f' g' hzero).ShortExact := by
        let S := ShortComplex.mk f g zero
        let S' := ShortComplex.mk f' g' hzero
        let se : S ≅ S' :=
          ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
            (by dsimp [S, S', f']; simp)
            (by dsimp [S, S', g']; simp)
        exact ShortComplex.shortExact_of_iso se exact
      exact
        IsFilteredBy.extension i hi f' g' hzero hshort tail

/-- Enlarging the permitted set of layers preserves a filtration. -/
theorem IsFilteredBy.mono_allowed
    (layer : ι → C) {allowed allowed' : ι → Prop}
    (hallowed : ∀ i, allowed i → allowed' i)
    {X : C} (hX : IsFilteredBy layer allowed X) :
    IsFilteredBy layer allowed' X := by
  induction hX with
  | zero X hzero => exact IsFilteredBy.zero X hzero
  | extension i hi f g zero exact tail ih =>
      exact
        IsFilteredBy.extension i (hallowed i hi)
          f g zero exact ih

/-- Adjoining an identity summand to the middle and quotient terms of a
short exact sequence preserves short exactness. -/
theorem shortExact_biprod_right
    {L X Q Y : C} (f : L ⟶ X) (g : X ⟶ Q)
    (hzero : f ≫ g = 0)
    (hshort : (ShortComplex.mk f g hzero).ShortExact) :
    let f' : L ⟶ X ⊞ Y := f ≫ biprod.inl
    let g' : X ⊞ Y ⟶ Q ⊞ Y := biprod.map g (𝟙 Y)
    let hzero' : f' ≫ g' = 0 := by
      dsimp only [f', g']
      rw [Category.assoc, biprod.inl_map,
        ← Category.assoc, hzero, zero_comp]
    (ShortComplex.mk f' g' hzero').ShortExact := by
  dsimp
  let f' : L ⟶ X ⊞ Y := f ≫ biprod.inl
  let g' : X ⊞ Y ⟶ Q ⊞ Y := biprod.map g (𝟙 Y)
  have hzero' : f' ≫ g' = 0 := by
    dsimp only [f', g']
    rw [Category.assoc, biprod.inl_map,
      ← Category.assoc, hzero, zero_comp]
  let S' := ShortComplex.mk f' g' hzero'
  letI : Mono f := hshort.mono_f
  letI : Epi g := hshort.epi_g
  have hker :
      IsLimit (KernelFork.ofι f hzero) :=
    hshort.fIsKernel
  have hker' :
      IsLimit (KernelFork.ofι f' hzero') := by
    let fst_zero : ∀ {Z : C} (k : Z ⟶ X ⊞ Y),
        k ≫ g' = 0 → (k ≫ biprod.fst) ≫ g = 0 :=
      fun {Z} k hk ↦ by
        have h := congrArg
          (fun t : Z ⟶ Q ⊞ Y ↦ t ≫ biprod.fst) hk
        simpa [g', Category.assoc] using h
    let lifted : ∀ {Z : C} (k : Z ⟶ X ⊞ Y)
        (hk : k ≫ g' = 0),
        { l : Z ⟶ L // l ≫ f = k ≫ biprod.fst } :=
      fun {Z} k hk ↦ by
        let q :=
          KernelFork.IsLimit.lift' hker
            (k ≫ biprod.fst) (fst_zero k hk)
        exact ⟨q.1, by
          have hq := q.2
          change q.1 ≫ f = k ≫ biprod.fst at hq
          exact hq⟩
    let lift : {Z : C} → (k : Z ⟶ X ⊞ Y) →
        k ≫ g' = 0 → (Z ⟶ L) :=
      fun {Z} k hk ↦ (lifted k hk).1
    refine KernelFork.IsLimit.ofι f' hzero' lift ?_ ?_
    · intro Z k hk
      apply biprod.hom_ext
      · dsimp [lift, f']
        simpa only [Category.assoc, biprod.inl_fst,
          Category.comp_id] using (lifted k hk).2
      · have h := congrArg
          (fun t : Z ⟶ Q ⊞ Y ↦ t ≫ biprod.snd) hk
        simpa [f', g', Category.assoc] using h.symm
    · intro Z k hk m hm
      dsimp [lift]
      apply (cancel_mono f).1
      calc
        m ≫ f =
            (m ≫ f') ≫ biprod.fst := by
              simp [f', Category.assoc]
        _ = k ≫ biprod.fst := by rw [hm]
        _ = (lifted k hk).1 ≫ f := (lifted k hk).2.symm
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  exact ShortComplex.exact_of_f_is_kernel S' hker'

/-- Binary biproducts of objects filtered by a fixed family are again
filtered by that family. -/
theorem IsFilteredBy.biprod
    (layer : ι → C) (allowed : ι → Prop)
    {X Y : C} (hX : IsFilteredBy layer allowed X)
    (hY : IsFilteredBy layer allowed Y) :
    IsFilteredBy layer allowed (X ⊞ Y) := by
  induction hX with
  | zero X hzero =>
      let e : Y ≅ X ⊞ Y := {
        hom := biprod.inr
        inv := biprod.snd
        hom_inv_id := by simp
        inv_hom_id := by
          apply biprod.hom_ext
          · simpa only [Category.assoc, biprod.inr_fst,
              comp_zero, Category.id_comp] using
                (hzero.eq_of_tgt (biprod.fst : X ⊞ Y ⟶ X) 0).symm
          · simp }
      exact hY.of_iso layer allowed e
  | extension i hi f g zero exact tail ih =>
      let f' := f ≫ (biprod.inl (Y := Y))
      let g' := biprod.map g (𝟙 Y)
      have hzero : f' ≫ g' = 0 := by
        dsimp only [f', g']
        rw [Category.assoc, biprod.inl_map,
          ← Category.assoc, zero, zero_comp]
      exact
        IsFilteredBy.extension i hi f' g' hzero
          (shortExact_biprod_right f g zero exact) ih

/-- Split a biproduct indexed by `Fin (n+1)` into its first term and
the biproduct indexed by the successors. -/
def biproductFinSuccIso
    [HasFiniteBiproducts C]
    {n : ℕ} (F : Fin (n + 1) → C) :
    F 0 ⊞ (⨁ fun j : Fin n ↦ F j.succ) ≅ ⨁ F where
  hom :=
    biprod.desc
      (biproduct.ι F 0)
      (biproduct.desc fun j : Fin n ↦ biproduct.ι F j.succ)
  inv :=
    biproduct.desc <| Fin.cases biprod.inl
      (fun j : Fin n ↦
        biproduct.ι (fun j : Fin n ↦ F j.succ) j ≫ biprod.inr)
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp
    · apply biproduct.hom_ext'
      intro j
      simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp

/-- Finite biproducts of objects filtered by a fixed family are again
filtered by that family. -/
theorem IsFilteredBy.finite_biproduct
    [HasFiniteBiproducts C]
    (layer : ι → C) (allowed : ι → Prop)
    {n : ℕ} (F : Fin n → C)
    (hF : ∀ j, IsFilteredBy layer allowed (F j)) :
    IsFilteredBy layer allowed (⨁ F) := by
  induction n with
  | zero =>
      apply IsFilteredBy.zero
      exact IsZero.mk
        (fun Z ↦ ⟨{
          default := 0
          uniq := fun f ↦ by
            apply biproduct.hom_ext'
            exact fun j ↦ Fin.elim0 j }⟩)
        (fun Z ↦ ⟨{
          default := 0
          uniq := fun f ↦ by
            apply biproduct.hom_ext
            exact fun j ↦ Fin.elim0 j }⟩)
  | succ n ih =>
      let Ftail : Fin n → C := fun j ↦ F j.succ
      have hhead : IsFilteredBy layer allowed (F 0) := hF 0
      have htail :
          IsFilteredBy layer allowed (⨁ Ftail) :=
        ih Ftail (fun j ↦ hF j.succ)
      exact
        (hhead.biprod layer allowed htail).of_iso
          layer allowed (biproductFinSuccIso F)

/-- A single permitted layer has the evident one-step filtration. -/
theorem IsFilteredBy.single
    (layer : ι → C) (allowed : ι → Prop)
    (i : ι) (hi : allowed i) :
    IsFilteredBy layer allowed (layer i) := by
  let Z : C := 0
  let g : layer i ⟶ Z := 0
  have hzero : (𝟙 (layer i)) ≫ g = 0 := by simp [g]
  have hshort :
      (ShortComplex.mk (𝟙 (layer i)) g hzero).ShortExact := by
    apply ShortComplex.ShortExact.mk'
    · apply
        ((ShortComplex.mk (𝟙 (layer i)) g hzero).exact_iff_epi
          (by simp [g])).2
      infer_instance
    · infer_instance
    · infer_instance
  exact
    IsFilteredBy.extension i hi (𝟙 (layer i)) g hzero hshort
      (IsFilteredBy.zero Z (isZero_zero C))

/-- The finite-biproduct closure statement with an arbitrary finite index
type, obtained by reindexing along its equivalence with `Fin`. -/
theorem IsFilteredBy.fintype_biproduct
    [HasFiniteBiproducts C]
    (layer : ι → C) (allowed : ι → Prop)
    {J : Type*} [Fintype J] (F : J → C)
    (hF : ∀ j, IsFilteredBy layer allowed (F j)) :
    IsFilteredBy layer allowed (⨁ F) := by
  let e := Fintype.equivFin J
  let G : Fin (Fintype.card J) → C := fun k ↦ F (e.symm k)
  have hG : ∀ k, IsFilteredBy layer allowed (G k) :=
    fun k ↦ hF (e.symm k)
  have hBip : IsFilteredBy layer allowed (⨁ G) :=
    IsFilteredBy.finite_biproduct layer allowed G hG
  let reindex : (⨁ F) ≅ ⨁ G :=
    biproduct.whiskerEquiv e
      (fun j ↦ eqToIso (by simp [G, e]))
  exact hBip.of_iso layer allowed reindex.symm

/-- The exact closure property needed to concatenate two finite
filtrations across a short exact sequence. -/
def IsFilteredBy.ExtensionClosed
    (layer : ι → C) (allowed : ι → Prop) : Prop :=
  ∀ {L X Q : C} (f : L ⟶ X) (g : X ⟶ Q)
    (hzero : f ≫ g = 0),
    (ShortComplex.mk f g hzero).ShortExact →
      IsFilteredBy layer allowed L →
      IsFilteredBy layer allowed Q →
      IsFilteredBy layer allowed X

/-- Finite filtrations are closed under short-exact extensions.  The proof
splices the filtration on the subobject one layer at a time by a pushout. -/
theorem IsFilteredBy.extensionClosed
    (layer : ι → C) (allowed : ι → Prop) :
    IsFilteredBy.ExtensionClosed layer allowed := by
  intro L X Q f g hfg hshort hL hQ
  induction hL generalizing X with
  | zero L hLzero =>
      letI : Mono f := hshort.mono_f
      letI : Epi g := hshort.epi_g
      haveI : IsIso g :=
        (ShortComplex.ShortExact.isIso_g_iff hshort).2 hLzero
      exact hQ.of_iso layer allowed (asIso g).symm
  | extension i hi a b hab habshort tail ih =>
      letI : Mono a := habshort.mono_f
      letI : Epi b := habshort.epi_g
      letI : Mono f := hshort.mono_f
      letI : Epi g := hshort.epi_g
      let P : C := pushout b f
      let f' : _ ⟶ P := pushout.inl b f
      let q : X ⟶ P := pushout.inr b f
      have hafq : (a ≫ f) ≫ q = 0 := by
        rw [Category.assoc, ← pushout.condition]
        simp only [← Category.assoc, hab, zero_comp]
      have hqCokernel :
          IsColimit (CokernelCofork.ofπ q hafq) := by
        apply CokernelCofork.IsColimit.ofπ'
        intro Z h hah
        have ha_fh : a ≫ (f ≫ h) = 0 := by
          simpa only [Category.assoc] using hah
        let l : _ ⟶ Z := habshort.exact.desc (f ≫ h) ha_fh
        refine ⟨pushout.desc l h ?_, ?_⟩
        · exact habshort.exact.g_desc (f ≫ h) ha_fh
        · dsimp only [q]
          exact pushout.inr_desc l h _
      have hLayerShort :
          (ShortComplex.mk (a ≫ f) q hafq).ShortExact := by
        apply ShortComplex.ShortExact.mk'
        · exact
            (ShortComplex.mk (a ≫ f) q hafq).exact_of_g_is_cokernel
              hqCokernel
        · infer_instance
        · exact epi_of_isColimit_cofork hqCokernel
      let g' : P ⟶ Q :=
        pushout.desc 0 g
          (by simpa only [comp_zero] using hfg.symm)
      have hf'g' : f' ≫ g' = 0 := by
        dsimp only [f', g']
        rw [pushout.inl_desc]
      have hqg' : q ≫ g' = g := by
        dsimp only [q, g']
        rw [pushout.inr_desc]
      letI : Epi g' := epi_of_epi_fac hqg'
      have hg'Cokernel :
          IsColimit (CokernelCofork.ofπ g' hf'g') := by
        apply CokernelCofork.IsColimit.ofπ'
        intro Z h hf'h
        have hf_qh : f ≫ (q ≫ h) = 0 := by
          calc
            f ≫ (q ≫ h) = (f ≫ q) ≫ h :=
              Category.assoc _ _ _ |>.symm
            _ = (b ≫ f') ≫ h := by rw [pushout.condition]
            _ = b ≫ (f' ≫ h) := Category.assoc _ _ _
            _ = 0 := by rw [hf'h, comp_zero]
        let u : Q ⟶ Z := hshort.exact.desc (q ≫ h) hf_qh
        refine ⟨u, ?_⟩
        apply (cancel_epi q).1
        rw [← Category.assoc, hqg']
        exact hshort.exact.g_desc (q ≫ h) hf_qh
      have hTailShort :
          (ShortComplex.mk f' g' hf'g').ShortExact := by
        apply ShortComplex.ShortExact.mk'
        · exact
            (ShortComplex.mk f' g' hf'g').exact_of_g_is_cokernel
              hg'Cokernel
        · infer_instance
        · infer_instance
      have hP : IsFilteredBy layer allowed P :=
        ih f' g' hf'g' hTailShort
      exact
        IsFilteredBy.extension i hi (a ≫ f) q hafq
          hLayerShort hP

end QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent

open QuotientSubmoduleEquidistribution.IndecomposableSkeleton
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton.LegalQuotientDeletionChain
open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics

universe uR uκ wR

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Fintype κ]

local notation "Γ" => skeletonAuslanderAlgebra σ

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
  FintypeCat.fintype

local instance kernelFiltrationTarget_hasFiniteBiproducts :
    HasFiniteBiproducts (skeletonProjectiveTarget σ) :=
  CategoricalAdditiveSubcategory.hasFiniteBiproductsOfEquivalence
    (skeletonAuslanderEquivalence σ)

/-- A categorical monomorphism between finitely generated projective modules
is injective on the underlying modules.  Testing against the rank-one free
module suffices, even though the ambient full subcategory does not itself
preserve arbitrary monomorphisms. -/
theorem finiteProjective_mono_injective
    {S : Type wR} [Ring S]
    {X Y :
      (AuslanderEquivalence.finiteProjectiveModules S).FullSubcategory}
    (f : X ⟶ Y) [Mono f] :
    Function.Injective f.hom.hom := by
  let I := AuslanderEquivalence.finiteProjectiveModules S
  let Reg : I.FullSubcategory :=
    ⟨ModuleCat.of S S,
      Module.Finite.self S,
      ModuleCat.projective_of_free
        (Module.Basis.singleton Unit S)⟩
  intro x y hxy
  let fx : Reg ⟶ X :=
    ObjectProperty.homMk <|
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton S X.obj x)
  let fy : Reg ⟶ X :=
    ObjectProperty.homMk <|
      ModuleCat.ofHom
        (LinearMap.toSpanSingleton S X.obj y)
  have hfxfy : fx = fy := by
    apply (cancel_mono f).1
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    dsimp only [fx, fy]
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, ModuleCat.hom_comp]
    change
      f.hom.hom.comp (LinearMap.toSpanSingleton S X.obj x) =
        f.hom.hom.comp (LinearMap.toSpanSingleton S X.obj y)
    rw [LinearMap.comp_toSpanSingleton,
      LinearMap.comp_toSpanSingleton, hxy]
  have hfxfyModule : fx.hom = fy.hom :=
    congrArg (fun k ↦ k.hom) hfxfy
  have hfxfyLinear :
      LinearMap.toSpanSingleton S X.obj x =
        LinearMap.toSpanSingleton S X.obj y :=
    congrArg (fun k ↦ k.hom) hfxfyModule
  exact
    LinearMap.toSpanSingleton_injective S X.obj hfxfyLinear

/-- An explicit finite biproduct presentation by selected coordinate
projectives.  This is stronger than a finite-additive-closure witness by a
retract. -/
structure CoordinateAddPresentation
    (T : Set κ) (X : ModuleCat.{wR} Γᵐᵒᵖ) where
  index : FintypeCat.{0}
  label : index → κ
  mem : ∀ t, label t ∈ T
  iso :
    X ≅
      ⨁ fun t : index ↦ (coordinateProjective σ (label t)).obj

/-- Membership in a transported skeleton-generated term yields an actual
finite biproduct presentation by its selected coordinate projectives. -/
def coordinateAddPresentation_of_mem_transportedGenerated
    (T : Set κ) (X : skeletonProjectiveTarget σ)
    (hX :
      (σ.transportedGeneratedSubcategory
        (skeletonAuslanderEquivalence σ) T).carrier X) :
    CoordinateAddPresentation σ T X.obj := by
  let E := skeletonAuslanderEquivalence σ
  let I :=
    AuslanderEquivalence.finiteProjectiveModules Γᵐᵒᵖ
  change σ.InAdd T (E.inverse.obj X) at hX
  let P := hX.some
  let F : P.index → FGModuleCat.{wR} R :=
    fun t ↦ σ.obj (P.label t)
  let Ft : P.index → skeletonProjectiveTarget σ :=
    fun t ↦ E.functor.obj (F t)
  letI : PreservesBiproduct F E.functor :=
    preservesBiproduct_of_preservesProduct E.functor
  letI : PreservesBiproduct Ft I.ι :=
    preservesBiproduct_of_preservesProduct I.ι
  refine {
    index := P.index
    label := P.label
    mem := P.mem
    iso :=
      I.ι.mapIso (E.counitIso.app X).symm ≪≫
      I.ι.mapIso (E.functor.mapIso P.iso) ≪≫
      I.ι.mapIso (E.functor.mapBiproduct F) ≪≫
      I.ι.mapBiproduct Ft ≪≫
      biproduct.mapIso (fun t ↦
        I.ι.mapIso
          (auslanderImageIsoCoordinateProjective σ (P.label t))) }

/-- Every map out of an explicitly selected coordinate biproduct is
annihilated by the corresponding coordinate standard projection. -/
theorem comp_coordinateStandardProjection_eq_zero_of_presentation
    (T : Set κ) (i : κ)
    {X : ModuleCat.{wR} Γᵐᵒᵖ}
    (P : CoordinateAddPresentation σ T X)
    (f : X ⟶ (coordinateProjective σ i).obj) :
    f ≫ coordinateStandardProjection σ T i = 0 := by
  rw [← cancel_epi P.iso.inv]
  apply biproduct.hom_ext'
  intro t
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, zero_comp,
    comp_zero] using
    comp_coordinateStandardProjection_eq_zero
      σ T i (P.label t) (P.mem t)
      (biproduct.ι
        (fun t : P.index ↦
          (coordinateProjective σ (P.label t)).obj) t ≫
        P.iso.inv ≫ f)

/-- Consequently every map out of such a selected coordinate biproduct
has range contained in the selected coordinate trace. -/
theorem range_le_coordinateProjectiveTrace_of_presentation
    (T : Set κ) (i : κ)
    {X : ModuleCat.{wR} Γᵐᵒᵖ}
    (P : CoordinateAddPresentation σ T X)
    (f : X ⟶ (coordinateProjective σ i).obj) :
    LinearMap.range f.hom ≤ coordinateProjectiveTrace σ T i := by
  rw [← Submodule.ker_mkQ (coordinateProjectiveTrace σ T i)]
  rw [LinearMap.range_le_ker_iff]
  have h :=
    congrArg (fun q : X ⟶ coordinateStandardQuotient σ T i ↦ q.hom)
      (comp_coordinateStandardProjection_eq_zero_of_presentation
        σ T i P f)
  change
    (Submodule.mkQ (coordinateProjectiveTrace σ T i)).comp f.hom =
      0 at h
  exact h

/-- A chosen right-rejective structure on the lower target term at a
deletion step. -/
def deletionLowerRightRejectiveData
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    CategoricalRejective.RightRejectiveData
      (targetRightRejectiveTerm σ
        (skeletonAuslanderEquivalence σ) d i.succ).1.carrier :=
  (targetRightRejectiveTerm σ
    (skeletonAuslanderEquivalence σ) d i.succ).2.some

/-- The lower-term coreflector of the projective removed at step `i`,
viewed in the ambient finite-projective target. -/
def deletionCoordinateTraceCoreflectorTarget
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    skeletonProjectiveTarget σ :=
  let D := deletionLowerRightRejectiveData σ d i
  (D.coreflector.obj (coordinateProjective σ (d.removed i))).obj

/-- The underlying module map of the monic counit from the lower-term
coreflector into the removed coordinate projective. -/
def deletionCoordinateTraceCoreflectorCounit
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    (deletionCoordinateTraceCoreflectorTarget σ d i).obj ⟶
      (coordinateProjective σ (d.removed i)).obj :=
  let D := deletionLowerRightRejectiveData σ d i
  (D.adjunction.counit.app
    (coordinateProjective σ (d.removed i))).hom

/-- The chosen lower-term coreflector has an actual finite biproduct
presentation by the coordinate projectives surviving to the next support. -/
def deletionCoordinateTraceCoreflectorPresentation
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    CoordinateAddPresentation σ (d.support i.succ)
      (deletionCoordinateTraceCoreflectorTarget σ d i).obj := by
  let E := skeletonAuslanderEquivalence σ
  let C :=
    (targetRightRejectiveTerm σ E d i.succ).1
  let D := deletionLowerRightRejectiveData σ d i
  apply
    coordinateAddPresentation_of_mem_transportedGenerated
      σ (d.support i.succ) (C.carrier.ι.obj
        (D.coreflector.obj
          (coordinateProjective σ (d.removed i))))
  rw [← targetRightRejectiveTerm_subcategory σ E d i.succ]
  exact
    (D.coreflector.obj
      (coordinateProjective σ (d.removed i))).property

/-- A selected coordinate projective belongs to the transported generated
subcategory of its support. -/
theorem coordinateProjective_mem_transportedGenerated
    (T : Set κ) (j : κ) (hj : j ∈ T) :
    (σ.transportedGeneratedSubcategory
      (skeletonAuslanderEquivalence σ) T).carrier
        (coordinateProjective σ j) := by
  let E := skeletonAuslanderEquivalence σ
  change σ.InAdd T (E.inverse.obj (coordinateProjective σ j))
  let e :
      σ.obj j ≅ E.inverse.obj (coordinateProjective σ j) :=
    E.unitIso.app (σ.obj j) ≪≫
      E.inverse.mapIso
        (auslanderImageIsoCoordinateProjective σ j)
  exact
    (inAdd_iff_of_iso σ e).mp (inAdd_obj σ hj)

/-- The range of the lower right-rejective counit is exactly the trace of
the coordinate projectives surviving to the next support. -/
theorem deletionCoordinateTraceCoreflectorCounit_range_eq_trace
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    LinearMap.range
        (deletionCoordinateTraceCoreflectorCounit σ d i).hom =
      coordinateProjectiveTrace σ
        (d.support i.succ) (d.removed i) := by
  let E := skeletonAuslanderEquivalence σ
  let C :=
    (targetRightRejectiveTerm σ E d i.succ).1
  let D := deletionLowerRightRejectiveData σ d i
  let Pi := coordinateProjective σ (d.removed i)
  let c := D.adjunction.counit.app Pi
  apply le_antisymm
  · exact
      range_le_coordinateProjectiveTrace_of_presentation
        σ (d.support i.succ) (d.removed i)
        (deletionCoordinateTraceCoreflectorPresentation σ d i)
        (deletionCoordinateTraceCoreflectorCounit σ d i)
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    apply iSup_le
    intro f
    have hjC : C.carrier (coordinateProjective σ j) := by
      simpa only [C, E,
        targetRightRejectiveTerm_subcategory] using
          coordinateProjective_mem_transportedGenerated σ
            (d.support i.succ) j hj
    let Xj : C.carrier.FullSubcategory :=
      ⟨coordinateProjective σ j, hjC⟩
    let fc : C.carrier.ι.obj Xj ⟶ Pi :=
      ObjectProperty.homMk f
    let g : Xj ⟶ D.coreflector.obj Pi :=
      D.adjunction.homEquiv Xj Pi fc
    have hfac :
        C.carrier.ι.map g ≫ c = fc := by
      calc
        C.carrier.ι.map g ≫ c =
            (D.adjunction.homEquiv Xj Pi).symm g :=
          (D.adjunction.homEquiv_counit Xj Pi g).symm
        _ = fc := by
          dsimp only [g]
          exact
            Equiv.symm_apply_apply
              (D.adjunction.homEquiv Xj Pi) fc
    have hfacLinear :=
      congrArg
        (fun q : coordinateProjective σ j ⟶ Pi ↦ q.hom.hom)
        hfac
    change
      LinearMap.range f.hom ≤
        LinearMap.range c.hom.hom
    change
      c.hom.hom.comp (C.carrier.ι.map g).hom.hom = f.hom
      at hfacLinear
    rw [← hfacLinear]
    exact
      LinearMap.range_comp_le_range
        (C.carrier.ι.map g).hom.hom c.hom.hom

/-- The monic lower-term coreflector realizes the literal coordinate trace
kernel, not just an abstract isomorphic subobject. -/
def deletionCoordinateTraceCoreflectorIsoTrace
    (d : LegalQuotientDeletionChain.Chain σ)
    (i : Fin (Fintype.card κ)) :
    (deletionCoordinateTraceCoreflectorTarget σ d i).obj ≅
      ModuleCat.of Γᵐᵒᵖ
        (coordinateProjectiveTrace σ
          (d.support i.succ) (d.removed i)) := by
  let D := deletionLowerRightRejectiveData σ d i
  let Pi := coordinateProjective σ (d.removed i)
  let c := D.adjunction.counit.app Pi
  letI : Mono c := D.counit_mono Pi
  have hinj : Function.Injective c.hom.hom :=
    finiteProjective_mono_injective c
  let eRange :
      (deletionCoordinateTraceCoreflectorTarget σ d i).obj ≃ₗ[Γᵐᵒᵖ]
        LinearMap.range
          (deletionCoordinateTraceCoreflectorCounit σ d i).hom :=
    LinearEquiv.ofInjective
      (deletionCoordinateTraceCoreflectorCounit σ d i).hom hinj
  let eTrace :
      LinearMap.range
          (deletionCoordinateTraceCoreflectorCounit σ d i).hom ≃ₗ[Γᵐᵒᵖ]
        coordinateProjectiveTrace σ
          (d.support i.succ) (d.removed i) :=
    LinearEquiv.ofEq _ _
      (deletionCoordinateTraceCoreflectorCounit_range_eq_trace σ d i)
  exact (eRange.trans eTrace).toModuleIso

/-- Conditional reduction of the entire trace-kernel filtration problem to
the general fact that finite filtrations are closed under extensions.  All
chain-specific input—right rejectivity, trace identification, finite
biproduct presentation, and descending induction—is discharged here. -/
theorem deletionCoordinateStandardKernelFiltration_of_extensionClosed
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : LegalQuotientDeletionChain.Chain σ)
    (hExtension : ∀ i : Fin (Fintype.card κ),
      IsFilteredBy.ExtensionClosed
        (fun j : Fin (Fintype.card κ) ↦
          (deletionCoordinateStandardModule σ hfinite
            d.toSaturatedSupport j).object)
        (fun j ↦ i < j)) :
    DeletionCoordinateStandardKernelFiltration σ hfinite
      d.toSaturatedSupport := by
  let ds := d.toSaturatedSupport
  let layer : Fin (Fintype.card κ) → ModuleCat.{wR} Γᵐᵒᵖ :=
    fun j ↦
      (deletionCoordinateStandardModule σ hfinite ds j).object
  let motive : Fin (Fintype.card κ) → Prop := fun i ↦
    IsFilteredBy layer (fun j ↦ i < j)
      (deletionCoordinateStandardKernel σ ds i)
  have hmot : ∀ i, motive i := fun i ↦
    Finite.to_wellFoundedGT.wf.induction i (fun i ih ↦ by
      let P := deletionCoordinateTraceCoreflectorPresentation σ d i
      have hcomponent : ∀ t : P.index,
          IsFilteredBy layer (fun j ↦ i < j)
            (coordinateProjective σ (P.label t)).obj := by
        intro t
        obtain ⟨k, hk⟩ := (removed_bijective ds).2 (P.label t)
        have hik : i < k := by
          by_contra hnot
          have hki : k ≤ i := le_of_not_gt hnot
          exact
            (removed_not_mem_later_support ds hki)
              (hk ▸ P.mem t)
        have hKraw := ih k hik
        change
          IsFilteredBy layer (fun j ↦ k < j)
            (deletionCoordinateStandardKernel σ ds k)
          at hKraw
        have hK :
            IsFilteredBy layer (fun j ↦ i < j)
              (deletionCoordinateStandardKernel σ ds k) :=
          hKraw.mono_allowed layer
            (fun j hkj ↦ lt_trans hik hkj)
        have hDelta :
            IsFilteredBy layer (fun j ↦ i < j) (layer k) :=
          IsFilteredBy.single layer (fun j ↦ i < j) k hik
        have hPk :
            IsFilteredBy layer (fun j ↦ i < j)
              (coordinateProjective σ (ds.removed k)).obj :=
          hExtension i
            (deletionCoordinateStandardKernelι σ ds k)
            (deletionCoordinateStandardProjection σ ds k)
            (deletionCoordinateStandardKernel_zero σ ds k)
            (deletionCoordinateStandard_shortExact σ ds k)
            hK hDelta
        simpa only [hk] using hPk
      have hBip :
          IsFilteredBy layer (fun j ↦ i < j)
            (⨁ fun t : P.index ↦
              (coordinateProjective σ (P.label t)).obj) :=
        IsFilteredBy.fintype_biproduct layer (fun j ↦ i < j)
          (fun t : P.index ↦
            (coordinateProjective σ (P.label t)).obj)
          hcomponent
      have hCore :
          IsFilteredBy layer (fun j ↦ i < j)
            (deletionCoordinateTraceCoreflectorTarget σ d i).obj :=
        hBip.of_iso layer (fun j ↦ i < j) P.iso.symm
      have hTrace :=
        hCore.of_iso layer (fun j ↦ i < j)
          (deletionCoordinateTraceCoreflectorIsoTrace σ d i)
      change motive i
      change
        IsFilteredBy layer (fun j ↦ i < j)
          (ModuleCat.of Γᵐᵒᵖ
            (coordinateProjectiveTrace σ
              (d.support i.succ) (d.removed i)))
      exact hTrace)
  exact ⟨hmot⟩

/-- Every legal quotient-deletion chain has the required later-standard
filtrations of its coordinate trace kernels. -/
theorem legalDeletionCoordinateStandardKernelFiltration
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : LegalQuotientDeletionChain.Chain σ) :
    DeletionCoordinateStandardKernelFiltration σ hfinite
      d.toSaturatedSupport :=
  deletionCoordinateStandardKernelFiltration_of_extensionClosed
    σ hfinite d (fun _ ↦ IsFilteredBy.extensionClosed _ _)

/-- Consequently a legal quotient-deletion chain supplies the concrete
ordered highest-weight structure attached to its coordinate standards. -/
def legalDeletionCoordinateOrderedHighestWeightStructure
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : LegalQuotientDeletionChain.Chain σ) :
    OrderedHighestWeightStructure
      (ModuleCat.{wR} Γᵐᵒᵖ) (Fin (Fintype.card κ)) :=
  deletionCoordinateOrderedHighestWeightStructure σ hfinite
    d.toSaturatedSupport
    (legalDeletionCoordinateStandardKernelFiltration σ hfinite d)

/-- The trace kernels are isomorphic to objects of the finite-projective
target, so the concrete ordered highest-weight structure is right strong. -/
def legalDeletionCoordinateRightStronglyQuasiHereditaryStructure
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : LegalQuotientDeletionChain.Chain σ) :
    RightStronglyQuasiHereditaryStructure
      (ModuleCat.{wR} Γᵐᵒᵖ) (Fin (Fintype.card κ)) where
  toOrderedHighestWeightStructure :=
    legalDeletionCoordinateOrderedHighestWeightStructure σ hfinite d
  kernel_projective i :=
    Projective.of_iso
      (deletionCoordinateTraceCoreflectorIsoTrace σ d i)
      (deletionCoordinateTraceCoreflectorTarget σ d i).property.2

/-- Right Artinianity of the Auslander algebra discharges the coordinate
finite-length input in the right-strong construction. -/
def legalDeletionCoordinateRightStronglyQuasiHereditaryStructureOfIsArtinian
    [IsArtinianRing Γᵐᵒᵖ]
    (d : LegalQuotientDeletionChain.Chain σ) :
    RightStronglyQuasiHereditaryStructure
      (ModuleCat.{wR} Γᵐᵒᵖ) (Fin (Fintype.card κ)) :=
  legalDeletionCoordinateRightStronglyQuasiHereditaryStructure σ
    (coordinateProjective_isFiniteLength σ) d

end QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent
