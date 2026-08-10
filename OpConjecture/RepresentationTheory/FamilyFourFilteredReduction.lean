import OpConjecture.RepresentationTheory.FamilyFourControl

/-!
# A filtered reduction for family four

This file isolates what quotient closedness says about every proper quotient
of the long member of a two-nonsimple closed triple.  It deliberately does not
assume that the long member has simple top.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.FamilyFourFilteredReduction

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v}
  (sigma :
    _root_.OpConjecture.IndecomposableSkeleton.{u, v, w} R iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Every quotient by a nonzero submodule of the long member decomposes
using only the other nonsimple member and the simple member.  This is the
literal finite-additive form of the fact that the long member itself cannot
occur as a summand of a proper quotient. -/
theorem quotient_inAdd_pair_of_nonzero_submodule
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (N : Submodule R (sigma.obj x)) (hN : N ≠ ⊥) :
    sigma.InAdd ({y, s} : Set iota)
      (FGModuleCat.of R ((sigma.obj x) ⧸ N)) := by
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((sigma.obj x) ⧸ N)
  obtain ⟨n, a, ⟨e⟩⟩ := sigma.decomposes Q
  refine ⟨{
    index := FintypeCat.of (Fin n)
    label := a
    mem := ?_
    iso := e }⟩
  intro t
  let q : sigma.obj x ⟶ Q := FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (_root_.OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      N.mkQ_surjective
  let f : sigma.obj x ⟶ sigma.obj (a t) :=
    q ≫ e.hom ≫ biproduct.π (fun z : Fin n ↦ sigma.obj (a z)) t
  letI : Epi f := by
    dsimp only [f]
    infer_instance
  have hxmem : x ∈ S := by
    rw [hS]
    simp
  have hat : a t ∈ S :=
    sigma.mem_of_epi_of_mem_of_qClosure_isClosed hclosed hxmem f
  rw [hS] at hat
  rcases (by simpa using hat) with hatx | haty | hats
  · exfalso
    have hlen :
        sigma.compositionLength x =
          sigma.compositionLength (a t) := by
      rw [hatx]
    letI : IsIso f :=
      sigma.isIso_of_epi_of_compositionLength_eq f hlen
    have hfinj : Function.Injective f.hom.hom :=
      (_root_.OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective f).mp
        inferInstance
    apply hN
    ext z
    constructor
    · intro hz
      have hqz : q.hom.hom z = 0 := by
        change N.mkQ z = 0
        exact (Submodule.Quotient.mk_eq_zero N).mpr hz
      have hfz : f.hom.hom z = 0 := by
        change
          (biproduct.π (fun z : Fin n ↦ sigma.obj (a z)) t).hom
            (e.hom.hom (q.hom.hom z)) = 0
        rw [hqz]
        simp
      have hz0 : z = 0 := by
        apply hfinj
        simpa using hfz
      subst z
      exact Submodule.zero_mem ⊥
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      exact N.zero_mem
  · exact Or.inl haty
  · exact Or.inr hats

/-- An additive combination of one length-two representative and one simple
representative has zero second module radical. -/
theorem secondRadical_eq_bot_of_inAdd_lengthTwo_simple
    {y s : iota}
    (hyLength : sigma.compositionLength y = 2)
    (hss : Simple (sigma.obj s))
    (Q : FGModuleCat.{w} R)
    (hQ : sigma.InAdd ({y, s} : Set iota) Q) :
    Module.jacobson R (Module.jacobson R Q) = ⊥ := by
  obtain ⟨P⟩ := hQ
  have hsourceSemisimple :
      IsSemisimpleModule R
        (Module.jacobson R (sigma.sumOver P.index P.label)) := by
    apply
      OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_sumOver_isSemisimple
        sigma P.index P.label
    intro t
    rcases (by simpa using P.mem t) with hty | hts
    · have htLength : sigma.compositionLength (P.label t) = 2 := by
        simpa [hty] using hyLength
      letI : IsSimpleModule R
          (Module.jacobson R (sigma.obj (P.label t))) :=
        OpConjecture.LengthTwoGabrielBridge.IndecomposableSkeleton.moduleRadical_isSimple_of_compositionLength_eq_two
          sigma htLength
      infer_instance
    · letI : IsSimpleModule R (sigma.obj (P.label t)) :=
        (_root_.OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
          (sigma.obj (P.label t))).mp (by simpa [hts] using hss)
      infer_instance
  let e :
      Module.jacobson R Q ≃ₗ[R]
        Module.jacobson R (sigma.sumOver P.index P.label) :=
    OpConjecture.radicalRestrictionEquiv
      (FGModuleCat.isoToLinearEquiv P.iso)
  have htargetSemisimple :
      IsSemisimpleModule R (Module.jacobson R Q) :=
    e.isSemisimpleModule_iff.mpr hsourceSemisimple
  letI : IsSemisimpleModule R (Module.jacobson R Q) :=
    htargetSemisimple
  exact IsSemisimpleModule.jacobson_eq_bot R _

/-- The second radical of the long member is contained in every nonzero
submodule.  Thus all proper quotients have Loewy length at most two, and the
entire deeper gluing is concentrated in a monolithic bottom layer. -/
theorem secondRadical_le_every_nonzero_submodule
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (hyLength : sigma.compositionLength y = 2)
    (hss : Simple (sigma.obj s))
    (N : Submodule R (sigma.obj x)) (hN : N ≠ ⊥) :
    Submodule.map (sigma.moduleRadical x).subtype
        (Module.jacobson R (sigma.moduleRadical x)) ≤ N := by
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((sigma.obj x) ⧸ N)
  have hQadd : sigma.InAdd ({y, s} : Set iota) Q :=
    quotient_inAdd_pair_of_nonzero_submodule sigma hclosed hS N hN
  have hQsecond :
      Module.jacobson R (Module.jacobson R Q) = ⊥ :=
    secondRadical_eq_bot_of_inAdd_lengthTwo_simple
      sigma hyLength hss Q hQadd
  let q : sigma.obj x →ₗ[R] Q := N.mkQ
  let q₂ :
      Module.jacobson R (Module.jacobson R (sigma.obj x)) →ₗ[R]
        Module.jacobson R (Module.jacobson R Q) :=
    OpConjecture.radicalRestriction
      (OpConjecture.radicalRestriction q)
  intro z hz
  obtain ⟨j, hj, hjz⟩ := hz
  let z₂ : Module.jacobson R
      (Module.jacobson R (sigma.obj x)) := ⟨j, hj⟩
  have htargetSubsingleton :
      Subsingleton
        (Module.jacobson R (Module.jacobson R Q)) := by
    rw [Submodule.subsingleton_iff_eq_bot]
    exact hQsecond
  have hzmap : q₂ z₂ = 0 :=
    @Subsingleton.elim _ htargetSubsingleton _ _
  have hqj : N.mkQ j.1 = 0 := by
    have hval₁ := congrArg Subtype.val hzmap
    have hval₂ := congrArg Subtype.val hval₁
    exact hval₂
  have hjN : j.1 ∈ N :=
    (Submodule.Quotient.mk_eq_zero N).mp hqj
  rw [← hjz]
  exact hjN

/-- If the second radical is nonzero, its image in the long member is the
unique minimal nonzero submodule.  In particular the filtered obstruction
has a simple essential bottom. -/
theorem secondRadical_image_isAtom_of_ne_bot
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (hyLength : sigma.compositionLength y = 2)
    (hss : Simple (sigma.obj s))
    (hsecond :
      Submodule.map (sigma.moduleRadical x).subtype
          (Module.jacobson R (sigma.moduleRadical x)) ≠ ⊥) :
    IsAtom
      (Submodule.map (sigma.moduleRadical x).subtype
        (Module.jacobson R (sigma.moduleRadical x))) := by
  apply isAtom_iff_le_of_ge.mpr
  refine ⟨hsecond, ?_⟩
  intro N hN _hNle
  exact
    secondRadical_le_every_nonzero_submodule
      sigma hclosed hS hyLength hss N hN

/-- Final monolithic reduction: when the second radical is nonzero, its
image is a simple module contained in every nonzero submodule of the long
member.  This is the precise simple essential-socle configuration left for
the filtered Ext/bypass argument. -/
theorem secondRadical_image_simple_and_le_every_nonzero_submodule
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (hyLength : sigma.compositionLength y = 2)
    (hss : Simple (sigma.obj s))
    (hsecond :
      Submodule.map (sigma.moduleRadical x).subtype
          (Module.jacobson R (sigma.moduleRadical x)) ≠ ⊥) :
    IsSimpleModule R
        (Submodule.map (sigma.moduleRadical x).subtype
          (Module.jacobson R (sigma.moduleRadical x))) ∧
      ∀ N : Submodule R (sigma.obj x), N ≠ ⊥ →
        Submodule.map (sigma.moduleRadical x).subtype
            (Module.jacobson R (sigma.moduleRadical x)) ≤ N := by
  have hatom :=
    secondRadical_image_isAtom_of_ne_bot
      sigma hclosed hS hyLength hss hsecond
  constructor
  · exact isSimpleModule_iff_isAtom.mpr hatom
  · intro N hN
    exact
      secondRadical_le_every_nonzero_submodule
        sigma hclosed hS hyLength hss N hN

end OpConjecture.FamilyFourFilteredReduction
