import OpConjecture.RepresentationTheory.HereditaryTwoSimpleCardThreeShape

/-!
# Ext-arrow endpoints at the hereditary two-simple cardinality-three boundary

The radical sequence of the unique length-two projective determines the
orientation of the unique Ext--Gabriel arrow.  This argument is intrinsic to
an arbitrary complete skeleton; no concrete algebra or module classification
occurs here.
-/

noncomputable section

open CategoryTheory

namespace OpConjecture.HereditaryTwoSimpleCardThreeShape

universe u v

open OpConjecture.IndecomposableSkeleton.ProjectiveSimpleRank
open OpConjecture.NakayamaFixedTopChains
open OpConjecture.GabrielArrowBridge

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {iota : Type v} [Finite iota]
  (sigma : OpConjecture.IndecomposableSkeleton.{u, v, u} R iota)

omit [Finite iota] in
/-- A chosen projective of fixed-top capacity one is literally the chosen
simple representative which labels its top. -/
theorem projectiveLabelOfSimple_eq_index_of_fixedTopCapacity_eq_one
    (short : sigma.SimpleIndex)
    (hshort : fixedTopCapacity sigma short = 1) :
    projectiveLabelOfSimple sigma short = short.1 := by
  let q : ProjectiveIndex sigma :=
    (projectiveIndexEquivSimpleIndex sigma).symm short
  have hqLength : sigma.compositionLength q.1 = 1 := by
    simpa [q, fixedTopCapacity, projectiveLabelOfSimple] using hshort
  have hqSimple : Simple (sigma.obj q.1) :=
    (sigma.compositionLength_eq_one_iff_simple q.1).mp hqLength
  letI : IsSimpleModule R (sigma.obj q.1) :=
    (OpConjecture.IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).mp
      hqSimple
  have htop : projectiveTopIndex sigma q = short :=
    (projectiveIndexEquivSimpleIndex sigma).apply_symm_apply short
  let eBot : projectiveTop sigma q ≅ sigma.obj q.1 :=
    (Submodule.quotEquivOfEqBot
      (Module.jacobson R (sigma.obj q.1))
      (IsSimpleModule.jacobson_eq_bot R (sigma.obj q.1))).toFGModuleCatIso
  let e : sigma.obj q.1 ≅ sigma.obj short.1 :=
    eBot.symm ≪≫ projectiveTopIso sigma q ≪≫
      eqToIso
        (congrArg (fun s : sigma.SimpleIndex => sigma.obj s.1) htop)
  change q.1 = short.1
  exact sigma.eq_of_iso ⟨e⟩

omit [Finite iota] in
/-- The length-two long projective has top/source `long` and
radical/target `short` under the maintained Gabriel-arrow conventions. -/
theorem lengthTwoProjective_endpoints
    (short long : sigma.SimpleIndex)
    (hshort : fixedTopCapacity sigma short = 1)
    (hlong : fixedTopCapacity sigma long = 2)
    (hRad : Nonempty
      (sigma.obj (projectiveLabelOfSimple sigma short) ≅
        FGModuleCat.of R
          (sigma.moduleRadical
            (projectiveLabelOfSimple sigma long)))) :
    let xLong : sigma.LengthTwoIndex :=
      ⟨projectiveLabelOfSimple sigma long, by
        simpa [fixedTopCapacity] using hlong⟩
    LengthTwo.source sigma xLong = long ∧
      LengthTwo.target sigma xLong = short := by
  let pLong : ProjectiveIndex sigma :=
    (projectiveIndexEquivSimpleIndex sigma).symm long
  have hpLong : pLong.1 = projectiveLabelOfSimple sigma long := rfl
  have hLongLength : sigma.compositionLength pLong.1 = 2 := by
    simpa [pLong, fixedTopCapacity, projectiveLabelOfSimple] using hlong
  let xLong : sigma.LengthTwoIndex := ⟨pLong.1, hLongLength⟩
  have htop : projectiveTopIndex sigma pLong = long :=
    (projectiveIndexEquivSimpleIndex sigma).apply_symm_apply long
  let eTop : projectiveTop sigma pLong ≅ sigma.obj long.1 :=
    projectiveTopIso sigma pLong ≪≫
      eqToIso
        (congrArg (fun s : sigma.SimpleIndex => sigma.obj s.1) htop)
  let qTop : sigma.obj pLong.1 ⟶ sigma.obj long.1 :=
    FGModuleCat.ofHom (sigma.moduleRadical pLong.1).mkQ ≫ eTop.hom
  haveI : Epi (FGModuleCat.ofHom (sigma.moduleRadical pLong.1).mkQ) :=
    (OpConjecture.IndecomposableSkeleton.fg_epi_iff_surjective _).mpr
      (sigma.moduleRadical pLong.1).mkQ_surjective
  haveI : Epi qTop := by
    dsimp [qTop]
    infer_instance
  let Q : sigma.SimpleQuotient pLong.1 :=
    { index := long.1
      simple := long.2
      map := qTop
      epi := inferInstance }
  have hsource : LengthTwo.source sigma xLong = long := by
    apply Subtype.ext
    exact
      OpConjecture.IndecomposableSkeleton.SimpleQuotient.index_eq_of_compositionLength_eq_two
        sigma hLongLength (LengthTwo.quotient sigma xLong) Q
  have hpShort : projectiveLabelOfSimple sigma short = short.1 :=
    projectiveLabelOfSimple_eq_index_of_fixedTopCapacity_eq_one
      sigma short hshort
  obtain ⟨eRad⟩ := hRad
  let eRad' : sigma.obj short.1 ≅
      FGModuleCat.of R (sigma.moduleRadical pLong.1) :=
    eqToIso (congrArg sigma.obj hpShort.symm) ≪≫ eRad ≪≫
      eqToIso
        (congrArg
          (fun i => FGModuleCat.of R (sigma.moduleRadical i)) hpLong.symm)
  let mRad : sigma.obj short.1 ⟶ sigma.obj pLong.1 :=
    eRad'.hom ≫
      FGModuleCat.ofHom (sigma.moduleRadical pLong.1).subtype
  haveI :
      Mono (FGModuleCat.ofHom (sigma.moduleRadical pLong.1).subtype) :=
    (OpConjecture.IndecomposableSkeleton.fg_mono_iff_injective _).mpr
      (sigma.moduleRadical pLong.1).subtype_injective
  haveI : Mono mRad := by
    dsimp [mRad]
    infer_instance
  let T : sigma.SimpleSubmodule pLong.1 :=
    { index := short.1
      simple := short.2
      map := mRad
      mono := inferInstance }
  have htarget : LengthTwo.target sigma xLong = short := by
    apply Subtype.ext
    exact
      OpConjecture.IndecomposableSkeleton.SimpleSubmodule.index_eq_of_compositionLength_eq_two
        sigma hLongLength (LengthTwo.submodule sigma xLong) T
  simpa only [xLong, pLong, projectiveLabelOfSimple] using
    ⟨hsource, htarget⟩

section ExtArrow

variable {K : Type u} [Field K]
  [Small.{u} R] [IsArtinianRing R] [Algebra K R]

/-- If the length-two object is unique, every multiplicity-bearing
Ext--Gabriel arrow has the endpoints dictated by the long-projective
radical sequence. -/
theorem extGabrielArrow_endpoints_of_projective_shape
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3)
    (hNoParallel : NoParallelExtSupport (K := K) sigma)
    (short long : sigma.SimpleIndex)
    (hshort : fixedTopCapacity sigma short = 1)
    (hlong : fixedTopCapacity sigma long = 2)
    (hRad : Nonempty
      (sigma.obj (projectiveLabelOfSimple sigma short) ≅
        FGModuleCat.of R
          (sigma.moduleRadical
            (projectiveLabelOfSimple sigma long))))
    (a : ExtGabrielArrowIndex (K := K) sigma) :
    ExtGabrielArrowIndex.source sigma a = long ∧
      ExtGabrielArrowIndex.target sigma a = short := by
  let xLong : sigma.LengthTwoIndex :=
    ⟨projectiveLabelOfSimple sigma long, by
      simpa [fixedTopCapacity] using hlong⟩
  have hxEndpoints :
      LengthTwo.source sigma xLong = long ∧
        LengthTwo.target sigma xLong = short :=
    lengthTwoProjective_endpoints sigma short long hshort hlong hRad
  have hcard : Nat.card sigma.LengthTwoIndex = 1 :=
    natCard_lengthTwoIndex_eq_one sigma hNakayama hTwo hThree
  have hUnique := Nat.card_eq_one_iff_unique.mp hcard
  letI : Subsingleton sigma.LengthTwoIndex := hUnique.1
  let e := LengthTwo.lengthTwoEquivExtGabrielArrow sigma hNoParallel
  have ha : e xLong = a := by
    calc
      e xLong = e (e.symm a) :=
        congrArg e (Subsingleton.elim xLong (e.symm a))
      _ = a := e.apply_symm_apply a
  rw [← ha]
  simpa [e, LengthTwo.lengthTwoEquivExtGabrielArrow,
    ExtGabrielArrowIndex.source, ExtGabrielArrowIndex.target,
    extGabrielArrowEquivSupport,
    LengthTwo.lengthTwoEquivGabrielArrow,
    LengthTwo.toGabrielArrow,
    GabrielArrowIndex.source, GabrielArrowIndex.target] using hxEndpoints

/-- The intrinsic projective-shape theorem strengthened by the orientation
of every Ext--Gabriel arrow. -/
theorem exists_projective_shape_with_extGabrielArrow_endpoints
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hHereditary :
      OpConjecture.IndecomposableSkeleton.FaithfulCore.ConnectedSmallCore.FinitelyGeneratedLeftHereditary
        R)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3)
    (hNoParallel : NoParallelExtSupport (K := K) sigma) :
    ∃ short long : sigma.SimpleIndex,
      short ≠ long ∧
        fixedTopCapacity sigma short = 1 ∧
        fixedTopCapacity sigma long = 2 ∧
        Nonempty
          (sigma.obj (projectiveLabelOfSimple sigma short) ≅
            FGModuleCat.of R
              (sigma.moduleRadical
                (projectiveLabelOfSimple sigma long))) ∧
        ∀ a : ExtGabrielArrowIndex (K := K) sigma,
          ExtGabrielArrowIndex.source sigma a = long ∧
            ExtGabrielArrowIndex.target sigma a = short := by
  obtain ⟨short, long, hne, hshort, hlong, hRad⟩ :=
    exists_projective_shape
      sigma hNakayama hHereditary hTwo hThree
  refine ⟨short, long, hne, hshort, hlong, hRad, ?_⟩
  intro a
  exact
    extGabrielArrow_endpoints_of_projective_shape
      sigma hNakayama hTwo hThree hNoParallel
      short long hshort hlong hRad a

/-- There is exactly one Ext--Gabriel arrow, and its ordered endpoints are
`long → short`. -/
theorem existsUnique_extGabrielArrow_with_projective_shape_endpoints
    (hNakayama :
      OpConjecture.LocalNakayamaBranch.IsNakayamaSkeleton sigma)
    (hTwo : Nat.card sigma.SimpleIndex = 2)
    (hThree : Nat.card iota = 3)
    (hNoParallel : NoParallelExtSupport (K := K) sigma)
    (short long : sigma.SimpleIndex)
    (hshort : fixedTopCapacity sigma short = 1)
    (hlong : fixedTopCapacity sigma long = 2)
    (hRad : Nonempty
      (sigma.obj (projectiveLabelOfSimple sigma short) ≅
        FGModuleCat.of R
          (sigma.moduleRadical
            (projectiveLabelOfSimple sigma long)))) :
    ∃! a : ExtGabrielArrowIndex (K := K) sigma,
      ExtGabrielArrowIndex.source sigma a = long ∧
        ExtGabrielArrowIndex.target sigma a = short := by
  let xLong : sigma.LengthTwoIndex :=
    ⟨projectiveLabelOfSimple sigma long, by
      simpa [fixedTopCapacity] using hlong⟩
  let e := LengthTwo.lengthTwoEquivExtGabrielArrow sigma hNoParallel
  let aLong : ExtGabrielArrowIndex (K := K) sigma := e xLong
  have haLong :=
    extGabrielArrow_endpoints_of_projective_shape
      sigma hNakayama hTwo hThree hNoParallel
      short long hshort hlong hRad aLong
  refine ⟨aLong, haLong, ?_⟩
  intro a ha
  apply ExtGabrielArrowIndex.source_target_injective sigma hNoParallel
  exact Prod.ext (ha.1.trans haLong.1.symm) (ha.2.trans haLong.2.symm)

end ExtArrow

end OpConjecture.HereditaryTwoSimpleCardThreeShape
