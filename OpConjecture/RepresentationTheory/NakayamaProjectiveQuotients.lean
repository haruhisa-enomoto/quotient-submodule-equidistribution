import OpConjecture.RepresentationTheory.ProjectiveSimpleRecognition
import OpConjecture.RepresentationTheory.LengthThreeUniserial
import OpConjecture.RepresentationTheory.FamilyFourControl

/-!
# Projective quotients in a Nakayama skeleton

This file proves the general quotient-side structural input used by the
Nakayama theorem.  A uniserial indecomposable is a quotient of the unique
indecomposable projective with its simple top.  Consequently, when every
indecomposable is uniserial, epimorphisms are exactly reverse length
comparisons inside one fixed-top fiber.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.NakayamaProjectiveQuotients

universe u v

variable {R : Type u} [Ring R]

/-- A map onto a uniserial module is epic as soon as its composite with
the quotient by a proper submodule is epic. -/
theorem epi_of_comp_quotient_epi_of_isUniserial
    {X : FGModuleCat.{u} R} {Y : FGModuleCat.{u} R}
    (hY : IsUniserialModule R Y)
    (J : Submodule R Y) (hJ : J ≠ ⊤)
    (f : X ⟶ Y)
    [Epi (f ≫ FGModuleCat.ofHom J.mkQ)] :
    Epi f := by
  apply (IndecomposableSkeleton.fg_epi_iff_surjective f).mpr
  rw [← LinearMap.range_eq_top]
  let L : Submodule R Y := LinearMap.range f.hom.hom
  have hcompSurj :
      Function.Surjective (J.mkQ.comp f.hom.hom) := by
    exact
      (IndecomposableSkeleton.fg_epi_iff_surjective
        (f ≫ FGModuleCat.ofHom J.mkQ)).mp inferInstance
  have hmapTop : L.map J.mkQ = ⊤ := by
    rw [← LinearMap.range_comp, LinearMap.range_eq_top]
    exact hcompSurj
  have hsup : J ⊔ L = ⊤ :=
    (J.map_mkQ_eq_top L).mp hmapTop
  unfold IsUniserialModule at hY
  rcases hY.total J L with hJL | hLJ
  · simpa only [sup_eq_right.mpr hJL] using hsup
  · exfalso
    apply hJ
    simpa only [sup_eq_left.mpr hLJ] using hsup

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank

variable [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : IndecomposableSkeleton.{u, v, u} R iota)

omit [Finite iota] in
/-- Every uniserial indecomposable is an epimorphic image of the chosen
indecomposable projective with the same simple top. -/
theorem exists_epi_projectiveLabelOfSimple_of_top_iso
    (i : iota)
    (hi : IsUniserialModule R (sigma.obj i))
    (j : sigma.SimpleIndex)
    (eTop :
      FGModuleCat.of R (sigma.moduleTop i) ≅ sigma.obj j.1) :
    ∃ f : sigma.obj (projectiveLabelOfSimple sigma j) ⟶ sigma.obj i,
      Epi f := by
  let p : ProjectiveIndex sigma :=
    (projectiveIndexEquivSimpleIndex sigma).symm j
  have hpLabel : p.1 = projectiveLabelOfSimple sigma j := rfl
  have hpTop : projectiveTopIndex sigma p = j :=
    (projectiveIndexEquivSimpleIndex sigma).apply_symm_apply j
  let qRad : sigma.obj p.1 ⟶ projectiveTop sigma p :=
    FGModuleCat.ofHom (Module.jacobson R (sigma.obj p.1)).mkQ
  let qP : sigma.obj p.1 ⟶ sigma.obj j.1 :=
    qRad ≫ (projectiveTopIso sigma p).hom ≫
      (eqToIso (congrArg (fun s : sigma.SimpleIndex ↦ sigma.obj s.1) hpTop)).hom
  haveI : Epi qRad :=
    (IndecomposableSkeleton.fg_epi_iff_surjective qRad).mpr
      (Module.jacobson R (sigma.obj p.1)).mkQ_surjective
  haveI : Epi qP := by
    dsimp [qP]
    infer_instance
  let qM : sigma.obj i ⟶ FGModuleCat.of R (sigma.moduleTop i) :=
    FGModuleCat.ofHom (sigma.moduleRadical i).mkQ
  haveI : Epi qM :=
    (IndecomposableSkeleton.fg_epi_iff_surjective qM).mpr
      (sigma.moduleRadical i).mkQ_surjective
  let topMap : sigma.obj i ⟶ sigma.obj j.1 := qM ≫ eTop.hom
  haveI : Epi topMap := by
    dsimp [topMap]
    infer_instance
  letI : CategoryTheory.Projective (sigma.obj p.1) := p.2
  let f : sigma.obj p.1 ⟶ sigma.obj i :=
    CategoryTheory.Projective.factorThru qP topMap
  have hfTop : f ≫ topMap = qP :=
    CategoryTheory.Projective.factorThru_comp qP topMap
  haveI : Epi (f ≫ topMap) := hfTop ▸ inferInstance
  haveI : Epi ((f ≫ qM) ≫ eTop.hom) := by
    simpa only [topMap, Category.assoc] using
      (inferInstance : Epi (f ≫ topMap))
  haveI : Epi (f ≫ qM) :=
    (CategoryTheory.epi_comp_iff_of_isIso (f ≫ qM) eTop.hom).mp
      (inferInstance : Epi ((f ≫ qM) ≫ eTop.hom))
  haveI :
      Epi (f ≫ FGModuleCat.ofHom (sigma.moduleRadical i).mkQ) := by
    simpa only [qM] using (inferInstance : Epi (f ≫ qM))
  letI : Nontrivial (sigma.obj i) := (sigma.indecomposable i).nontrivial
  letI : IsArtinian R (sigma.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength i)).2
  letI : Epi f :=
    epi_of_comp_quotient_epi_of_isUniserial hi
      (sigma.moduleRadical i)
      (by
        simpa only [IndecomposableSkeleton.moduleRadical] using
          (Module.jacobson_lt_top R (sigma.obj i)).ne)
      f
  refine ⟨eqToHom (congrArg sigma.obj hpLabel).symm ≫ f, ?_⟩
  infer_instance

omit [IsNoetherianRing R] in
/-- Two epimorphic images of equal finite length from the same uniserial
source have the same kernel. -/
theorem ker_eq_of_epi_of_length_eq_of_isUniserial
    {P X Y : FGModuleCat.{u} R}
    (hP : IsUniserialModule R P)
    (hPfinite : IsFiniteLength R P)
    (hXfinite : IsFiniteLength R X)
    (f : P ⟶ X) [Epi f]
    (g : P ⟶ Y) [Epi g]
    (hlength : Module.length R X = Module.length R Y) :
    LinearMap.ker f.hom.hom = LinearMap.ker g.hom.hom := by
  have hfSurj : Function.Surjective f.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).mp inferInstance
  have hgSurj : Function.Surjective g.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective g).mp inferInstance
  have hfLength :
      Module.length R P =
        Module.length R (LinearMap.ker f.hom.hom) +
          Module.length R X :=
    Module.length_eq_add_of_exact
      (LinearMap.ker f.hom.hom).subtype f.hom.hom
      (Submodule.subtype_injective _)
      hfSurj
      (LinearMap.exact_subtype_ker_map f.hom.hom)
  have hgLength :
      Module.length R P =
        Module.length R (LinearMap.ker g.hom.hom) +
          Module.length R Y :=
    Module.length_eq_add_of_exact
      (LinearMap.ker g.hom.hom).subtype g.hom.hom
      (Submodule.subtype_injective _)
      hgSurj
      (LinearMap.exact_subtype_ker_map g.hom.hom)
  have hkerLength :
      Module.length R (LinearMap.ker f.hom.hom) =
        Module.length R (LinearMap.ker g.hom.hom) := by
    apply WithTop.add_right_cancel
      ((Module.length_ne_top_iff).2 hXfinite)
    calc
      Module.length R (LinearMap.ker f.hom.hom) +
            Module.length R X =
          Module.length R P := hfLength.symm
      _ = Module.length R (LinearMap.ker g.hom.hom) +
            Module.length R Y := hgLength
      _ = Module.length R (LinearMap.ker g.hom.hom) +
            Module.length R X := by rw [hlength]
  letI : IsArtinian R P :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinite).2
  letI : IsNoetherian R P :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinite).1
  exact hP.eq_of_length_eq hkerLength

omit [IsNoetherianRing R] in
/-- For epimorphic images of one finite-length uniserial source, reverse
target-length order gives inclusion of kernels. -/
theorem ker_le_of_epi_of_length_le_of_isUniserial
    {P X Y : FGModuleCat.{u} R}
    (hP : IsUniserialModule R P)
    (hPfinite : IsFiniteLength R P)
    (f : P ⟶ X) [Epi f]
    (g : P ⟶ Y) [Epi g]
    (hlength : Module.length R Y ≤ Module.length R X) :
    LinearMap.ker f.hom.hom ≤ LinearMap.ker g.hom.hom := by
  have hfSurj : Function.Surjective f.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).mp inferInstance
  have hgSurj : Function.Surjective g.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective g).mp inferInstance
  have hfLength :
      Order.coheight (LinearMap.ker f.hom.hom) = Module.length R X := by
    rw [← Module.length_quotient]
    exact (f.hom.hom.quotKerEquivOfSurjective hfSurj).length_eq
  have hgLength :
      Order.coheight (LinearMap.ker g.hom.hom) = Module.length R Y := by
    rw [← Module.length_quotient]
    exact (g.hom.hom.quotKerEquivOfSurjective hgSurj).length_eq
  letI : IsArtinian R P :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinite).2
  letI : IsNoetherian R P :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinite).1
  unfold IsUniserialModule at hP
  rcases hP.total (LinearMap.ker f.hom.hom)
      (LinearMap.ker g.hom.hom) with hfg | hgf
  · exact hfg
  · by_cases heq :
        LinearMap.ker g.hom.hom = LinearMap.ker f.hom.hom
    · exact heq.symm.le
    · have hlt :
          LinearMap.ker g.hom.hom < LinearMap.ker f.hom.hom :=
        lt_of_le_of_ne hgf heq
      have hcoheight :
          Order.coheight (LinearMap.ker f.hom.hom) <
            Order.coheight (LinearMap.ker g.hom.hom) :=
        Order.coheight_strictAnti hlt
          (Order.coheight_lt_top (LinearMap.ker f.hom.hom))
      rw [hfLength, hgLength] at hcoheight
      exact (not_lt_of_ge hlength hcoheight).elim

omit [IsNoetherianRing R] in
/-- The kernel inclusion above produces the corresponding epimorphism
between the two quotient targets. -/
theorem exists_epi_of_epi_from_uniserial_of_length_le
    {P X Y : FGModuleCat.{u} R}
    (hP : IsUniserialModule R P)
    (hPfinite : IsFiniteLength R P)
    (f : P ⟶ X) [Epi f]
    (g : P ⟶ Y) [Epi g]
    (hlength : Module.length R Y ≤ Module.length R X) :
    ∃ h : X ⟶ Y, Epi h := by
  have hfSurj : Function.Surjective f.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective f).mp inferInstance
  have hgSurj : Function.Surjective g.hom.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective g).mp inferInstance
  have hker :
      LinearMap.ker f.hom.hom ≤ LinearMap.ker g.hom.hom :=
    ker_le_of_epi_of_length_le_of_isUniserial
      hP hPfinite f g hlength
  let gQ : (P ⧸ LinearMap.ker f.hom.hom) →ₗ[R] Y :=
    (LinearMap.ker f.hom.hom).liftQ g.hom.hom hker
  let hLinear : X →ₗ[R] Y :=
    gQ.comp
      (f.hom.hom.quotKerEquivOfSurjective hfSurj).symm.toLinearMap
  let h : X ⟶ Y := FGModuleCat.ofHom hLinear
  have hhSurj : Function.Surjective h.hom.hom := by
    intro y
    obtain ⟨p, rfl⟩ := hgSurj y
    refine ⟨f.hom.hom p, ?_⟩
    change gQ ((f.hom.hom.quotKerEquivOfSurjective hfSurj).symm
      (f.hom.hom p)) = g.hom.hom p
    have hInv :
        (f.hom.hom.quotKerEquivOfSurjective hfSurj).symm
            (f.hom.hom p) =
          Submodule.Quotient.mk p := by
      apply (f.hom.hom.quotKerEquivOfSurjective hfSurj).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [hInv]
    change gQ (Submodule.Quotient.mk p) = g.hom.hom p
    have hLift := DFunLike.congr_fun
      ((LinearMap.ker f.hom.hom).liftQ_mkQ g.hom.hom hker) p
    exact hLift
  exact ⟨h,
    (IndecomposableSkeleton.fg_epi_iff_surjective h).mpr hhSurj⟩

omit [Finite iota] in
/-- With a uniserial chosen projective at a fixed simple top, the top and
composition length determine a uniserial indecomposable uniquely. -/
theorem eq_of_top_iso_of_compositionLength_eq_of_projective_uniserial
    (j : sigma.SimpleIndex)
    (hProjectiveUniserial :
      IsUniserialModule R
        (sigma.obj (projectiveLabelOfSimple sigma j)))
    (i k : iota)
    (hi : IsUniserialModule R (sigma.obj i))
    (hk : IsUniserialModule R (sigma.obj k))
    (eTopI :
      FGModuleCat.of R (sigma.moduleTop i) ≅ sigma.obj j.1)
    (eTopK :
      FGModuleCat.of R (sigma.moduleTop k) ≅ sigma.obj j.1)
    (hlength : sigma.compositionLength i = sigma.compositionLength k) :
    i = k := by
  obtain ⟨f, hf⟩ :=
    exists_epi_projectiveLabelOfSimple_of_top_iso sigma i hi j eTopI
  obtain ⟨g, hg⟩ :=
    exists_epi_projectiveLabelOfSimple_of_top_iso sigma k hk j eTopK
  letI : Epi f := hf
  letI : Epi g := hg
  have hlength' :
      Module.length R (sigma.obj i) = Module.length R (sigma.obj k) := by
    rw [← sigma.coe_compositionLength i,
      ← sigma.coe_compositionLength k, hlength]
  have hker :
      LinearMap.ker f.hom.hom = LinearMap.ker g.hom.hom :=
    ker_eq_of_epi_of_length_eq_of_isUniserial
      hProjectiveUniserial
      (sigma.finiteLength (projectiveLabelOfSimple sigma j))
      (sigma.finiteLength i) f g hlength'
  let e : sigma.obj i ≃ₗ[R] sigma.obj k :=
    (f.hom.hom.quotKerEquivOfSurjective
      ((IndecomposableSkeleton.fg_epi_iff_surjective f).mp inferInstance)).symm.trans
      ((Submodule.quotEquivOfEq
        (LinearMap.ker f.hom.hom)
        (LinearMap.ker g.hom.hom) hker).trans
          (g.hom.hom.quotKerEquivOfSurjective
            ((IndecomposableSkeleton.fg_epi_iff_surjective g).mp inferInstance)))
  exact sigma.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- A chosen simple skeleton representative of the top of a uniserial
indecomposable. -/
def uniserialTopChoice
    (i : iota) (hi : IsUniserialModule R (sigma.obj i)) :
    Σ j : sigma.SimpleIndex,
      FGModuleCat.of R (sigma.moduleTop i) ≅ sigma.obj j.1 := by
  let hsimple : Simple (FGModuleCat.of R (sigma.moduleTop i)) := by
    rw [IndecomposableSkeleton.simple_iff_isSimpleModule_fg]
    exact sigma.moduleTop_isSimple_of_isUniserial hi
  letI : IsSimpleModule R (sigma.moduleTop i) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp hsimple
  have hindec :
      OpConjecture.Foundation.IsIndecomposableModule R (sigma.moduleTop i) :=
    OpConjecture.Foundation.IsSimpleModule.isIndecomposableModule
  let hcomplete :=
    sigma.complete (FGModuleCat.of R (sigma.moduleTop i)) hindec
  let j := Classical.choose hcomplete
  let e := Classical.choice (Classical.choose_spec hcomplete)
  exact ⟨⟨j, (Simple.iff_of_iso e).mp hsimple⟩, e⟩

/-- The selected simple-top label of a uniserial indecomposable. -/
def uniserialTopIndex
    (i : iota) (hi : IsUniserialModule R (sigma.obj i)) :
    sigma.SimpleIndex :=
  (uniserialTopChoice sigma i hi).1

/-- The selected top isomorphism of a uniserial indecomposable. -/
def uniserialTopIso
    (i : iota) (hi : IsUniserialModule R (sigma.obj i)) :
    FGModuleCat.of R (sigma.moduleTop i) ≅
      sigma.obj (uniserialTopIndex sigma i hi).1 :=
  (uniserialTopChoice sigma i hi).2

omit [Finite iota] in
/-- An epimorphism between uniserial indecomposables preserves their
selected simple-top label. -/
theorem uniserialTopIndex_eq_of_epi
    (i k : iota)
    (hi : IsUniserialModule R (sigma.obj i))
    (hk : IsUniserialModule R (sigma.obj k))
    (f : sigma.obj i ⟶ sigma.obj k) [Epi f] :
    uniserialTopIndex sigma i hi = uniserialTopIndex sigma k hk := by
  let qK : sigma.obj k ⟶ FGModuleCat.of R (sigma.moduleTop k) :=
    FGModuleCat.ofHom (sigma.moduleRadical k).mkQ
  haveI : Epi qK :=
    (IndecomposableSkeleton.fg_epi_iff_surjective qK).mpr
      (sigma.moduleRadical k).mkQ_surjective
  let g : sigma.obj i ⟶
      sigma.obj (uniserialTopIndex sigma k hk).1 :=
    f ≫ qK ≫ (uniserialTopIso sigma k hk).hom
  haveI : Epi g := by
    dsimp [g]
    infer_instance
  let e : sigma.moduleTop i ≃ₗ[R]
      sigma.obj (uniserialTopIndex sigma k hk).1 :=
    OpConjecture.FamilyFourControl.moduleTopLinearEquivOfSurjectiveToSimple
      (sigma.moduleTop_isSimple_of_isUniserial hi)
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
        (uniserialTopIndex sigma k hk).2)
      g.hom.hom
      ((IndecomposableSkeleton.fg_epi_iff_surjective g).mp inferInstance)
  apply Subtype.ext
  apply sigma.eq_of_iso
  exact ⟨(uniserialTopIso sigma i hi).symm ≪≫ e.toFGModuleCatIso⟩

omit [Finite iota] in
/-- If every chosen indecomposable is uniserial, epimorphisms are exactly
reverse composition-length comparisons inside one simple-top fiber. -/
theorem exists_epi_iff_topIndex_eq_and_compositionLength_le
    (hNakayama : ∀ i : iota, IsUniserialModule R (sigma.obj i))
    (i k : iota) :
    (∃ f : sigma.obj i ⟶ sigma.obj k, Epi f) ↔
      uniserialTopIndex sigma i (hNakayama i) =
          uniserialTopIndex sigma k (hNakayama k) ∧
        sigma.compositionLength k ≤ sigma.compositionLength i := by
  constructor
  · rintro ⟨f, hf⟩
    letI : Epi f := hf
    exact ⟨uniserialTopIndex_eq_of_epi sigma i k
      (hNakayama i) (hNakayama k) f,
      sigma.compositionLength_le_of_epi f⟩
  · rintro ⟨htop, hlength⟩
    let j := uniserialTopIndex sigma i (hNakayama i)
    let eTopI : FGModuleCat.of R (sigma.moduleTop i) ≅ sigma.obj j.1 :=
      uniserialTopIso sigma i (hNakayama i)
    let eTopK : FGModuleCat.of R (sigma.moduleTop k) ≅ sigma.obj j.1 :=
      uniserialTopIso sigma k (hNakayama k) ≪≫
        eqToIso
          (congrArg
            (fun s : sigma.SimpleIndex ↦ sigma.obj s.1)
            htop.symm)
    obtain ⟨f, hf⟩ :=
      exists_epi_projectiveLabelOfSimple_of_top_iso
        sigma i (hNakayama i) j eTopI
    obtain ⟨g, hg⟩ :=
      exists_epi_projectiveLabelOfSimple_of_top_iso
        sigma k (hNakayama k) j eTopK
    letI : Epi f := hf
    letI : Epi g := hg
    have hlength' :
        Module.length R (sigma.obj k) ≤
          Module.length R (sigma.obj i) := by
      rw [← sigma.coe_compositionLength k,
        ← sigma.coe_compositionLength i]
      exact ENat.coe_le_coe.mpr hlength
    exact exists_epi_of_epi_from_uniserial_of_length_le
      (hNakayama (projectiveLabelOfSimple sigma j))
      (sigma.finiteLength (projectiveLabelOfSimple sigma j))
      f g hlength'

end OpConjecture.NakayamaProjectiveQuotients
