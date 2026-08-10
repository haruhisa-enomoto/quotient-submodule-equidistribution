import OpConjecture.RepresentationTheory.BottomTwoSimpleTop

/-!
# Collective closure for a length-two pair

This file isolates the genuinely collective input in the
bottom-level-two argument.  The objectwise quotient and submodule
dichotomies are already available in `BottomTwoModules`.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Unique simple boundary objects -/

/--
All simple quotients of an indecomposable representative of composition
length two have the same skeleton index.
-/
theorem SimpleQuotient.index_eq_of_compositionLength_eq_two
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q Q' : σ.SimpleQuotient x) :
    Q.index = Q'.index := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  have htop :
      IsSimpleModule R (σ.moduleTop x) :=
    OpConjecture.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
      σ hx
  have hJcoatom :
      IsCoatom (Module.jacobson R (σ.obj x)) := by
    exact isSimpleModule_iff_isCoatom.mp htop
  letI : IsSimpleModule R (σ.obj Q.index) :=
    (simple_iff_isSimpleModule_fg _).mp Q.simple
  letI : IsSimpleModule R (σ.obj Q'.index) :=
    (simple_iff_isSimpleModule_fg _).mp Q'.simple
  letI : Epi Q.map := Q.epi
  letI : Epi Q'.map := Q'.epi
  have hQsurj : Function.Surjective Q.map.hom.hom :=
    (fg_epi_iff_surjective Q.map).mp inferInstance
  have hQ'surj : Function.Surjective Q'.map.hom.hom :=
    (fg_epi_iff_surjective Q'.map).mp inferInstance
  have hQcoatom :
      IsCoatom (LinearMap.ker Q.map.hom.hom) :=
    LinearMap.isCoatom_ker_of_surjective hQsurj
  have hQ'coatom :
      IsCoatom (LinearMap.ker Q'.map.hom.hom) :=
    LinearMap.isCoatom_ker_of_surjective hQ'surj
  have hJQ :
      Module.jacobson R (σ.obj x) =
        LinearMap.ker Q.map.hom.hom :=
    le_antisymm (sInf_le hQcoatom) (by
      by_cases hEq :
          Module.jacobson R (σ.obj x) =
            LinearMap.ker Q.map.hom.hom
      · exact hEq.ge
      · have hlt :
            Module.jacobson R (σ.obj x) <
              LinearMap.ker Q.map.hom.hom :=
          lt_of_le_of_ne (sInf_le hQcoatom) hEq
        exact
          (hQcoatom.ne_top (hJcoatom.2 _ hlt)).elim)
  have hJQ' :
      Module.jacobson R (σ.obj x) =
        LinearMap.ker Q'.map.hom.hom :=
    le_antisymm (sInf_le hQ'coatom) (by
      by_cases hEq :
          Module.jacobson R (σ.obj x) =
            LinearMap.ker Q'.map.hom.hom
      · exact hEq.ge
      · have hlt :
            Module.jacobson R (σ.obj x) <
              LinearMap.ker Q'.map.hom.hom :=
          lt_of_le_of_ne (sInf_le hQ'coatom) hEq
        exact
          (hQ'coatom.ne_top (hJcoatom.2 _ hlt)).elim)
  have hker :
      LinearMap.ker Q.map.hom.hom =
        LinearMap.ker Q'.map.hom.hom :=
    hJQ.symm.trans hJQ'
  let e :
      σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    (Q.map.hom.hom.quotKerEquivOfSurjective hQsurj).symm.trans
      ((Submodule.quotEquivOfEq
        (LinearMap.ker Q.map.hom.hom)
        (LinearMap.ker Q'.map.hom.hom) hker).trans
          (Q'.map.hom.hom.quotKerEquivOfSurjective hQ'surj))
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/--
The preceding uniqueness theorem is stable when the two quotient
structures are written over propositionally equal skeleton indices.
-/
theorem SimpleQuotient.index_eq_of_compositionLength_eq_two_of_eq
    {x y : ι} (hxy : x = y)
    (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (Q' : σ.SimpleQuotient y) :
    Q.index = Q'.index := by
  subst y
  exact
    SimpleQuotient.index_eq_of_compositionLength_eq_two
      σ hx Q Q'

/--
A selected simple quotient of a length-two representative supplies its
unique simple quotient type.
-/
theorem hasUniqueSimpleQuotientType_of_compositionLength_eq_two
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x) :
    σ.HasUniqueSimpleQuotientType x Q.index :=
  ⟨Q.simple, fun Q' ↦
    SimpleQuotient.index_eq_of_compositionLength_eq_two σ hx Q' Q⟩

/--
All simple submodules of an indecomposable representative of composition
length two have the same skeleton index.
-/
theorem SimpleSubmodule.index_eq_of_compositionLength_eq_two
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q Q' : σ.SimpleSubmodule x) :
    Q.index = Q'.index := by
  letI : IsSimpleModule R (σ.obj Q.index) :=
    (simple_iff_isSimpleModule_fg _).mp Q.simple
  letI : IsSimpleModule R (σ.obj Q'.index) :=
    (simple_iff_isSimpleModule_fg _).mp Q'.simple
  letI : Mono Q.map := Q.mono
  letI : Mono Q'.map := Q'.mono
  have hQinj : Function.Injective Q.map.hom.hom :=
    (fg_mono_iff_injective Q.map).mp inferInstance
  have hQ'inj : Function.Injective Q'.map.hom.hom :=
    (fg_mono_iff_injective Q'.map).mp inferInstance
  let A : Submodule R (σ.obj x) :=
    LinearMap.range Q.map.hom.hom
  let B : Submodule R (σ.obj x) :=
    LinearMap.range Q'.map.hom.hom
  let eA : σ.obj Q.index ≃ₗ[R] A :=
    LinearEquiv.ofInjective Q.map.hom.hom hQinj
  let eB : σ.obj Q'.index ≃ₗ[R] B :=
    LinearEquiv.ofInjective Q'.map.hom.hom hQ'inj
  have hAsimple : IsSimpleModule R A :=
    IsSimpleModule.congr eA.symm
  have hBsimple : IsSimpleModule R B :=
    IsSimpleModule.congr eB.symm
  have hAatom : IsAtom A :=
    isSimpleModule_iff_isAtom.mp hAsimple
  have hBatom : IsAtom B :=
    isSimpleModule_iff_isAtom.mp hBsimple
  have htotal :
      Module.length R (σ.obj x) = 2 := by
    rw [← σ.coe_compositionLength x, hx]
    norm_num
  have hAlength : Module.length R A = 1 :=
    Module.length_eq_one_iff.mpr hAsimple
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
  have hAB : A = B := by
    by_contra hne
    have hBnotleA : ¬ B ≤ A := by
      intro hBA
      rcases hAatom.le_iff.mp hBA with hBbot | hBAeq
      · exact hBatom.ne_bot hBbot
      · exact hne hBAeq.symm
    have hAltSup : A < A ⊔ B := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro hEq
      apply hBnotleA
      calc
        B ≤ A ⊔ B := le_sup_right
        _ = A := hEq.symm
    have hsup : A ⊔ B = ⊤ :=
      hAcoatom.2 _ hAltSup
    have hinf : A ⊓ B = ⊥ := by
      rcases hAatom.le_iff.mp inf_le_left with hbot | hEq
      · exact hbot
      · exfalso
        have hAleB : A ≤ B := by
          calc
            A = A ⊓ B := hEq.symm
            _ ≤ B := inf_le_right
        rcases hBatom.le_iff.mp hAleB with hAbot | hAB
        · exact hAatom.ne_bot hAbot
        · exact hne hAB
    have hcompl : IsCompl A B :=
      IsCompl.of_eq hinf hsup
    rcases (σ.indecomposable x).eq_bot_or_eq_bot hcompl with
      hAbot | hBbot
    · exact hAatom.ne_bot hAbot
    · exact hBatom.ne_bot hBbot
  let e :
      σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    eA.trans
      ((LinearEquiv.ofEq A B hAB).trans eB.symm)
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/--
A selected simple submodule of a length-two representative supplies its
unique simple submodule type.
-/
theorem hasUniqueSimpleSubmoduleType_of_compositionLength_eq_two
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleSubmodule x) :
    σ.HasUniqueSimpleSubmoduleType x Q.index :=
  ⟨Q.simple, fun Q' ↦
    SimpleSubmodule.index_eq_of_compositionLength_eq_two σ hx Q' Q⟩

/-! ## Finite generation of a local module -/

/--
If the target of an epic map from a finite biproduct has simple top, one
component is already epic.

This is the finite-biproduct form of the familiar fact that a finitely
generated local module cannot be the sum of proper submodules.
-/
theorem exists_epi_biproduct_component_of_simple_top
    (J : FintypeCat.{0}) (a : J → ι)
    {x : ι}
    (htop : IsSimpleModule R (σ.moduleTop x))
    (f : σ.sumOver J a ⟶ σ.obj x)
    [Epi f] :
    ∃ t : J,
      Epi
        (biproduct.ι
            (fun b : J ↦ σ.obj (a b)) t ≫ f) := by
  classical
  letI : Fintype J := FintypeCat.fintype
  let M : Submodule R (σ.obj x) :=
    Module.jacobson R (σ.obj x)
  have hMcoatom : IsCoatom M := by
    exact isSimpleModule_iff_isCoatom.mp htop
  by_contra hcomponent
  push Not at hcomponent
  have hrange (t : J) :
      LinearMap.range
          (biproduct.ι
              (fun b : J ↦ σ.obj (a b)) t ≫ f).hom.hom ≤
        M := by
    let g :
        σ.obj (a t) ⟶ σ.obj x :=
      biproduct.ι
          (fun b : J ↦ σ.obj (a b)) t ≫ f
    have hrangeNe :
        LinearMap.range g.hom.hom ≠ ⊤ := by
      intro hrangeTop
      have hsurj : Function.Surjective g.hom.hom :=
        LinearMap.range_eq_top.mp hrangeTop
      exact hcomponent t
        ((fg_epi_iff_surjective g).mpr hsurj)
    obtain ⟨N, hNcoatom, hle⟩ :=
      (eq_top_or_exists_le_coatom
        (LinearMap.range g.hom.hom)).resolve_left
        hrangeNe
    have hMN : M ≤ N :=
      sInf_le hNcoatom
    have hMN' : M = N := by
      by_cases hEq : M = N
      · exact hEq
      · have hlt : M < N :=
          lt_of_le_of_ne hMN hEq
        exact
          (hNcoatom.ne_top (hMcoatom.2 _ hlt)).elim
    simpa only [g, hMN'] using hle
  let q :
      σ.obj x ⟶ FGModuleCat.of R (σ.moduleTop x) :=
    FGModuleCat.ofHom M.mkQ
  have hq : q ≠ 0 := by
    intro hzero
    have hlinear :
        q.hom.hom = 0 := by
      exact congrArg (fun g ↦ g.hom.hom) hzero
    apply hMcoatom.ne_top
    apply top_unique
    intro y hy
    apply (Submodule.Quotient.mk_eq_zero M).mp
    change M.mkQ y = 0
    rw [show M.mkQ y = q.hom.hom y by rfl, hlinear]
    rfl
  have hfq : f ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro t
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change M.mkQ
        ((biproduct.ι
            (fun b : J ↦ σ.obj (a b)) t ≫ f).hom.hom y) = 0
    apply (Submodule.Quotient.mk_eq_zero M).mpr
    exact hrange t ⟨y, rfl⟩
  apply hq
  rw [← cancel_epi f]
  simpa using hfq

/-! ## The exact collective input -/

/--
Every jointly epic presentation of an indecomposable from the pair
`{x,s}` has an epic component.

This is stronger than the objectwise length-two quotient dichotomy: the
presentation map is already epic, while the conclusion singles out one
biproduct component.
-/
def PairFacPresentationsHaveEpiComponent (x s : ι) : Prop :=
  ∀ {j : ι}
      (P : σ.FacPresentation ({x, s} : Set ι) (σ.obj j)),
    ∃ t : P.index,
      Epi
        (biproduct.ι
            (fun a : P.index ↦ σ.obj (P.label a)) t ≫
          P.map)

/--
Top-direction form of the collective input: every indecomposable generated
by the pair has simple top.

Generation already forces all top composition factors to come from the
chosen simple quotient.  The additional content here is that a collective
quotient cannot acquire two or more such top directions.
-/
def PairFacTargetsHaveSimpleTop (x s : ι) : Prop :=
  ∀ {j : ι}, σ.InFac ({x, s} : Set ι) (σ.obj j) →
    IsSimpleModule R (σ.moduleTop j)

/--
The unconditional top information: every simple quotient of every
indecomposable generated by `{x, top(x)}` has the chosen top index.

Thus the remaining top-direction input is only multiplicity one, not
identification of the simple top type.
-/
theorem simpleQuotient_index_eq_of_inFac_length_two_pair
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    {j : ι}
    (hj :
      σ.InFac ({x, Q.index} : Set ι) (σ.obj j))
    (L : σ.SimpleQuotient j) :
    L.index = Q.index := by
  classical
  obtain ⟨P⟩ := hj
  let g :
      σ.sumOver P.index P.label ⟶ σ.obj L.index :=
    P.map ≫ L.map
  letI : Epi P.map := P.epi
  letI : Epi L.map := L.epi
  letI : Epi g := by
    dsimp only [g]
    infer_instance
  letI : Simple (σ.obj L.index) := L.simple
  have hg : g ≠ 0 := by
    intro hzero
    exact
      (Simple.not_isZero (σ.obj L.index))
        (IsZero.of_epi_eq_zero g hzero)
  have hcomponent :
      ∃ t : P.index,
        biproduct.ι
            (fun a : P.index ↦ σ.obj (P.label a)) t ≫
          g ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext'
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hcomponent
  let f :
      σ.obj (P.label t) ⟶ σ.obj L.index :=
    biproduct.ι
        (fun a : P.index ↦ σ.obj (P.label a)) t ≫
      g
  have hf : f ≠ 0 := ht
  letI : Epi f := epi_of_nonzero_to_simple hf
  have hlabel := P.mem t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabel
  rcases hlabel with hlabel | hlabel
  · let Q' : σ.SimpleQuotient (P.label t) := {
      index := L.index
      simple := L.simple
      map := f
      epi := inferInstance }
    exact
      SimpleQuotient.index_eq_of_compositionLength_eq_two_of_eq
        σ hlabel (by simpa [hlabel] using hx) Q' Q
  · letI : Simple (σ.obj (P.label t)) := by
      simpa [hlabel] using Q.simple
    haveI : IsIso f := isIso_of_hom_simple hf
    have hindex :
        P.label t = L.index :=
      σ.eq_of_iso ⟨asIso f⟩
    exact hindex.symm.trans hlabel

/-- A simple representative has simple concrete top. -/
theorem moduleTop_isSimple_of_simple
    {i : ι} (hi : Simple (σ.obj i)) :
    IsSimpleModule R (σ.moduleTop i) := by
  letI : IsSimpleModule R (σ.obj i) :=
    (simple_iff_isSimpleModule_fg _).mp hi
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  have hjacobson :
      Module.jacobson R (σ.obj i) = ⊥ := by
    rw [← IsArtinian.isSemisimpleModule_iff_jacobson]
    infer_instance
  change
    IsSimpleModule R
      ((σ.obj i) ⧸ Module.jacobson R (σ.obj i))
  rw [hjacobson]
  exact
    IsSimpleModule.congr
      (Submodule.quotEquivOfEqBot
        (⊥ : Submodule R (σ.obj i)) rfl)

/--
The top-direction condition implies the epic-component condition, by
applying the local-module biproduct lemma to each generated target.
-/
theorem pairFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
    {x s : ι}
    (htop : PairFacTargetsHaveSimpleTop σ x s) :
    PairFacPresentationsHaveEpiComponent σ x s := by
  intro j P
  letI : Epi P.map := P.epi
  exact
    exists_epi_biproduct_component_of_simple_top
      σ P.index P.label (htop ⟨P⟩) P.map

/--
If every collective presentation from a length-two object and a chosen
simple quotient has an epic component, the two-object support is
quotient closed.
-/
theorem qClosure_isClosed_pair_of_epiComponent
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (hcollective :
      PairFacPresentationsHaveEpiComponent σ x Q.index) :
    σ.qClosure.IsClosed ({x, Q.index} : Set ι) := by
  rw [σ.qClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    obtain ⟨t, ht⟩ := hcollective P
    let f :
        σ.obj (P.label t) ⟶ σ.obj j :=
      biproduct.ι
          (fun a : P.index ↦ σ.obj (P.label a)) t ≫
        P.map
    letI : Epi f := ht
    have hlabel := P.mem t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabel
    rcases hlabel with hlabel | hlabel
    · have hxLabel :
          σ.compositionLength (P.label t) = 2 := by
        simpa [hlabel] using hx
      rcases
          σ.simple_or_isIso_of_epi_of_compositionLength_eq_two
            f hxLabel with hjSimple | hfIso
      · let Q' : σ.SimpleQuotient (P.label t) := {
          index := j
          simple := hjSimple
          map := f
          epi := inferInstance }
        have hjQ :
            j = Q.index :=
          SimpleQuotient.index_eq_of_compositionLength_eq_two_of_eq
            σ hlabel hxLabel Q' Q
        simp [hjQ]
      · have hindex :
            P.label t = j :=
          σ.eq_of_iso ⟨asIso f⟩
        have hjx : j = x :=
          hindex.symm.trans hlabel
        simp [hjx]
    · letI : Simple (σ.obj (P.label t)) := by
        simpa [hlabel] using Q.simple
      letI : IsSimpleModule R (σ.obj (P.label t)) :=
        (simple_iff_isSimpleModule_fg _).mp inferInstance
      have hsurj : Function.Surjective f.hom.hom :=
        (fg_epi_iff_surjective f).mp inferInstance
      letI : IsSemisimpleModule R (σ.obj j) :=
        IsSemisimpleModule.of_surjective f.hom.hom hsurj
      letI : IsSimpleModule R (σ.obj j) :=
        isSimpleModule_of_semisimple_of_indecomposable
          (σ.indecomposable j)
      letI : Simple (σ.obj j) :=
        (simple_iff_isSimpleModule_fg _).mpr inferInstance
      have hf : f ≠ 0 := by
        intro hzero
        exact
          (Simple.not_isZero (σ.obj j))
            (IsZero.of_epi_eq_zero f hzero)
      haveI : IsIso f := isIso_of_hom_simple hf
      have hindex :
          P.label t = j :=
        σ.eq_of_iso ⟨asIso f⟩
      have hjQ : j = Q.index :=
        hindex.symm.trans hlabel
      simp [hjQ]
  · exact σ.subset_qSet ({x, Q.index} : Set ι)

/--
Closure packaged directly from the top-direction input.
-/
theorem qClosure_isClosed_pair_of_targetsHaveSimpleTop
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x)
    (htop :
      PairFacTargetsHaveSimpleTop σ x Q.index) :
    σ.qClosure.IsClosed ({x, Q.index} : Set ι) :=
  qClosure_isClosed_pair_of_epiComponent σ hx Q
    (pairFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
      σ htop)

/--
Under the length-two hypotheses, collective pair closure is equivalent to
the remaining multiplicity-one assertion for the tops of generated
indecomposables.
-/
theorem qClosure_isClosed_pair_iff_targetsHaveSimpleTop
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x) :
    σ.qClosure.IsClosed ({x, Q.index} : Set ι) ↔
      PairFacTargetsHaveSimpleTop σ x Q.index := by
  constructor
  · intro hclosed j hj
    have hjMem : j ∈ ({x, Q.index} : Set ι) := by
      rw [← hclosed.closure_eq]
      exact hj
    rcases hjMem with hjx | hjQ
    · subst j
      exact
        OpConjecture.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
          σ hx
    · subst j
      exact moduleTop_isSimple_of_simple σ Q.simple
  · exact qClosure_isClosed_pair_of_targetsHaveSimpleTop σ hx Q

/--
Equivalent epic-component formulation of the same collective obstruction.
-/
theorem qClosure_isClosed_pair_iff_epiComponent
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleQuotient x) :
    σ.qClosure.IsClosed ({x, Q.index} : Set ι) ↔
      PairFacPresentationsHaveEpiComponent σ x Q.index := by
  constructor
  · intro hclosed
    apply
      pairFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
        σ
    exact
      (qClosure_isClosed_pair_iff_targetsHaveSimpleTop
        σ hx Q).mp hclosed
  · exact qClosure_isClosed_pair_of_epiComponent σ hx Q

/-! ## Submodule-side companion -/

/--
Every collective submodule presentation into a sum of copies of `x` and
`s` has a monic component.
-/
def PairSubPresentationsHaveMonoComponent (x s : ι) : Prop :=
  ∀ {j : ι}
      (P : σ.SubPresentation ({x, s} : Set ι) (σ.obj j)),
    ∃ t : P.index,
      Mono
        (P.map ≫
          biproduct.π
            (fun a : P.index ↦ σ.obj (P.label a)) t)

/-- Dual collective reduction. -/
theorem sClosure_isClosed_pair_of_monoComponent
    {x : ι} (hx : σ.compositionLength x = 2)
    (Q : σ.SimpleSubmodule x)
    (hcollective :
      PairSubPresentationsHaveMonoComponent σ x Q.index) :
    σ.sClosure.IsClosed ({x, Q.index} : Set ι) := by
  have hunique :
      σ.HasUniqueSimpleSubmoduleType x Q.index :=
    hasUniqueSimpleSubmoduleType_of_compositionLength_eq_two
      σ hx Q
  rw [σ.sClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    obtain ⟨t, ht⟩ := hcollective P
    let f :
        σ.obj j ⟶ σ.obj (P.label t) :=
      P.map ≫
        biproduct.π
          (fun a : P.index ↦ σ.obj (P.label a)) t
    letI : Mono f := ht
    have hlabel := P.mem t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabel
    rcases hlabel with hlabel | hlabel
    · have hxLabel :
          σ.compositionLength (P.label t) = 2 := by
        simpa [hlabel] using hx
      rcases
          σ.simple_or_isIso_of_mono_of_compositionLength_eq_two
            f hxLabel with hjSimple | hfIso
      · let g :
            σ.obj j ⟶ σ.obj x :=
          f ≫ eqToHom (congrArg σ.obj hlabel)
        letI : Mono g := by
          dsimp only [g]
          infer_instance
        let Q' : σ.SimpleSubmodule x := {
          index := j
          simple := hjSimple
          map := g
          mono := inferInstance }
        have hjQ : j = Q.index :=
          hunique.2 Q'
        simp [hjQ]
      · have hindex :
            j = P.label t :=
          σ.eq_of_iso ⟨asIso f⟩
        have hjx : j = x :=
          hindex.trans hlabel
        simp [hjx]
    · letI : Simple (σ.obj (P.label t)) := by
        simpa [hlabel] using Q.simple
      letI : IsSimpleModule R (σ.obj (P.label t)) :=
        (simple_iff_isSimpleModule_fg _).mp inferInstance
      have hinj : Function.Injective f.hom.hom :=
        (fg_mono_iff_injective f).mp inferInstance
      letI : IsSemisimpleModule R (σ.obj j) :=
        IsSemisimpleModule.of_injective f.hom.hom hinj
      letI : IsSimpleModule R (σ.obj j) :=
        isSimpleModule_of_semisimple_of_indecomposable
          (σ.indecomposable j)
      letI : Simple (σ.obj j) :=
        (simple_iff_isSimpleModule_fg _).mpr inferInstance
      have hf : f ≠ 0 := by
        intro hzero
        exact
          (Simple.not_isZero (σ.obj j))
            (IsZero.of_mono_eq_zero f hzero)
      haveI : IsIso f := isIso_of_hom_simple hf
      have hindex :
          j = P.label t :=
        σ.eq_of_iso ⟨asIso f⟩
      have hjQ : j = Q.index :=
        hindex.trans hlabel
      simp [hjQ]
  · exact σ.subset_sSet ({x, Q.index} : Set ι)

end OpConjecture.IndecomposableSkeleton
