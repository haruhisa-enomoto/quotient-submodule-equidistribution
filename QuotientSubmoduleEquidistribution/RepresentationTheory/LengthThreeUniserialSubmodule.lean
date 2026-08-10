import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserial

/-!
# Collective submodule reduction for length-three uniserial chains

This file proves the submodule-side counterpart of the collective quotient
reduction. A monomorphism from a uniserial source, or more generally from a
source with simple socle, to a finite biproduct has a monic component.
Consequently, a length-three uniserial submodule-chain support is
collectively closed exactly when all generated indecomposables have simple
socle. Their socles are unconditionally isotypic of the chain-bottom
simple, leaving only multiplicity one unresolved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe u v w

namespace IsUniserialModule

variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- A module which embeds in a uniserial module is uniserial. -/
theorem of_injective
    (hM : IsUniserialModule R M)
    (f : N →ₗ[R] M) (hf : Function.Injective f) :
    IsUniserialModule R N := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total (P.map f) (Q.map f) with hPQ | hQP
  · exact Or.inl
      ((Submodule.map_le_map_iff_of_injective hf P Q).mp hPQ)
  · exact Or.inr
      ((Submodule.map_le_map_iff_of_injective hf Q P).mp hQP)

end IsUniserialModule

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A monomorphism from a nonzero uniserial module to a finite biproduct
has a monic component. -/
theorem exists_mono_biproduct_component_of_isUniserial
    {x : ι} (hx : IsUniserialModule R (σ.obj x))
    (J : FintypeCat.{0}) (a : J → ι)
    (f : σ.obj x ⟶ σ.sumOver J a) [Mono f] :
    ∃ t : J,
      Mono
        (f ≫ biproduct.π
          (fun b : J ↦ σ.obj (a b)) t) := by
  classical
  letI : Fintype J := FintypeCat.fintype
  have hf : Function.Injective f.hom.hom :=
    (fg_mono_iff_injective f).mp inferInstance
  letI : Nontrivial (σ.obj x) :=
    (σ.indecomposable x).nontrivial
  have hJ : Nonempty J := by
    by_contra h
    haveI : IsEmpty J := not_nonempty_iff.mp h
    have hzero : f = 0 := by
      apply biproduct.hom_ext
      intro j
      exact isEmptyElim j
    have hz : IsZero (σ.obj x) :=
      IsZero.of_mono_eq_zero f hzero
    have hz' :
        IsZero
          ((forget₂ (FGModuleCat.{w} R)
            (ModuleCat.{w} R)).obj (σ.obj x)) :=
      (forget₂ (FGModuleCat.{w} R)
        (ModuleCat.{w} R)).map_isZero hz
    exact
      not_subsingleton (σ.obj x)
        ((ModuleCat.isZero_iff_subsingleton).mp hz')
  let K (t : J) : Submodule R (σ.obj x) :=
    LinearMap.ker
      (f ≫ biproduct.π
        (fun b : J ↦ σ.obj (a b)) t).hom.hom
  obtain ⟨t, ht⟩ :=
    Set.Finite.exists_minimalFor
      (f := K) (s := Set.univ)
      (Set.toFinite (Set.univ : Set J)) Set.univ_nonempty
  have htLeast (s : J) : K t ≤ K s := by
    unfold IsUniserialModule at hx
    rcases hx.total (K t) (K s) with h | h
    · exact h
    · exact ht.le_of_le (Set.mem_univ s) h
  have hKt : K t = ⊥ := by
    apply le_antisymm
    · intro m hm
      let T : FGModuleCat.{w} R :=
        FGModuleCat.of R (K t)
      let inc : T ⟶ σ.obj x :=
        FGModuleCat.ofHom (K t).subtype
      have hcomp (s : J) :
          inc ≫ f ≫
              biproduct.π
                (fun b : J ↦ σ.obj (a b)) s =
            0 := by
        apply FGModuleCat.hom_ext
        ext z
        have hz := htLeast s z.property
        change
          (f ≫ biproduct.π
              (fun b : J ↦ σ.obj (a b)) s).hom.hom z.1 = 0
          at hz
        change
          (f ≫ biproduct.π
              (fun b : J ↦ σ.obj (a b)) s).hom.hom z.1 = 0
        exact hz
      have hincComp : inc ≫ f = 0 := by
        apply biproduct.hom_ext
        intro s
        simpa [Category.assoc] using hcomp s
      have hinc : inc = 0 := by
        rw [← cancel_mono f]
        simpa using hincComp
      have hmzero :
          (⟨m, hm⟩ : K t) = 0 := by
        have hfun :
            inc.hom.hom (⟨m, hm⟩ : K t) =
              (0 : T ⟶ σ.obj x).hom.hom
                (⟨m, hm⟩ : K t) :=
          LinearMap.congr_fun
            (congrArg (fun g ↦ g.hom.hom) hinc)
            (⟨m, hm⟩ : K t)
        apply Subtype.ext
        change m = 0
        change m = 0 at hfun
        exact hfun
      change m = 0
      exact congrArg Subtype.val hmzero
    · exact bot_le
  refine ⟨t, (fg_mono_iff_injective _).mpr ?_⟩
  exact (LinearMap.ker_eq_bot.mp hKt)

/-- The socle of a nonzero finite-length uniserial skeleton
representative is simple. -/
theorem moduleSocle_isSimple_of_isUniserial
    {x : ι} (hx : IsUniserialModule R (σ.obj x)) :
    IsSimpleModule R (σ.moduleSocle x) := by
  letI : Nontrivial (σ.obj x) :=
    (σ.indecomposable x).nontrivial
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  obtain ⟨N, hNatom, -⟩ :=
    (eq_bot_or_exists_atom_le
      (⊤ : Submodule R (σ.obj x))).resolve_left top_ne_bot
  have hNsimple : IsSimpleModule R N :=
    isSimpleModule_iff_isAtom.mpr hNatom
  have hNle : N ≤ σ.moduleSocle x :=
    σ.le_moduleSocle_of_simple N hNsimple
  have hsocleLe : σ.moduleSocle x ≤ N := by
    apply sSup_le
    intro L hLsimple
    have hLatom : IsAtom L :=
      isSimpleModule_iff_isAtom.mp hLsimple
    unfold IsUniserialModule at hx
    rcases hx.total L N with hLN | hNL
    · exact hLN
    · have hLN : L = N :=
        ((hLatom.le_iff_eq hNatom.ne_bot).mp hNL).symm
      exact hLN.le
  rw [le_antisymm hsocleLe hNle]
  exact hNsimple

/-- If the source has simple socle, a monomorphism from it to a finite
biproduct has a monic component. -/
theorem exists_mono_biproduct_component_of_simple_socle
    {x : ι} (hsocle : IsSimpleModule R (σ.moduleSocle x))
    (J : FintypeCat.{0}) (a : J → ι)
    (f : σ.obj x ⟶ σ.sumOver J a) [Mono f] :
    ∃ t : J,
      Mono
        (f ≫ biproduct.π
          (fun b : J ↦ σ.obj (a b)) t) := by
  classical
  letI : Fintype J := FintypeCat.fintype
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  by_contra hcomponent
  push Not at hcomponent
  have hsocleKer (t : J) :
      σ.moduleSocle x ≤
        LinearMap.ker
          (f ≫ biproduct.π
            (fun b : J ↦ σ.obj (a b)) t).hom.hom := by
    let g : σ.obj x ⟶ σ.obj (a t) :=
      f ≫ biproduct.π
        (fun b : J ↦ σ.obj (a b)) t
    have hkerNe :
        LinearMap.ker g.hom.hom ≠ ⊥ := by
      intro hker
      exact hcomponent t
        ((fg_mono_iff_injective g).mpr
          (LinearMap.ker_eq_bot.mp hker))
    obtain ⟨L, hLatom, hLle⟩ :=
      (eq_bot_or_exists_atom_le
        (LinearMap.ker g.hom.hom)).resolve_left hkerNe
    have hLsimple : IsSimpleModule R L :=
      isSimpleModule_iff_isAtom.mpr hLatom
    have hLsocle : L ≤ σ.moduleSocle x :=
      σ.le_moduleSocle_of_simple L hLsimple
    have hsocleAtom : IsAtom (σ.moduleSocle x) :=
      isSimpleModule_iff_isAtom.mp hsocle
    have hL_eq :
        L = σ.moduleSocle x :=
      (hsocleAtom.le_iff_eq hLatom.ne_bot).mp hLsocle
    simpa [g, ← hL_eq] using hLle
  let S : FGModuleCat.{w} R :=
    FGModuleCat.of R (σ.moduleSocle x)
  let inc : S ⟶ σ.obj x :=
    FGModuleCat.ofHom (σ.moduleSocle x).subtype
  letI : Mono inc :=
    (fg_mono_iff_injective inc).mpr
      (σ.moduleSocle x).subtype_injective
  have hincComp : inc ≫ f = 0 := by
    apply biproduct.hom_ext
    intro t
    apply FGModuleCat.hom_ext
    ext z
    simp only [zero_comp]
    have hz := hsocleKer t z.property
    change
      (f ≫ biproduct.π
          (fun b : J ↦ σ.obj (a b)) t).hom.hom z.1 = 0
      at hz
    change
      (inc ≫ f ≫ biproduct.π
          (fun b : J ↦ σ.obj (a b)) t).hom.hom z = 0
    exact hz
  have hinc : inc = 0 := by
    rw [← cancel_mono f]
    simpa using hincComp
  letI : IsSimpleModule R S := hsocle
  letI : Simple S :=
    (simple_iff_isSimpleModule_fg _).mpr inferInstance
  exact
    (Simple.not_isZero S)
      (IsZero.of_mono_eq_zero inc hinc)

/-- Every member of a length-three submodule-chain support embeds in the
length-three target. -/
theorem LengthThreeSubmoduleChain.exists_mono_from_mem_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {i : ι} (hi : i ∈ C.support) :
    ∃ f : σ.obj i ⟶ σ.obj x.1, Mono f := by
  rcases (by
      simpa [LengthThreeSubmoduleChain.support] using hi) with
      rfl | rfl | rfl
  · exact ⟨𝟙 _, inferInstance⟩
  · exact ⟨C.middle.map, C.middle.mono⟩
  · exact ⟨C.simpleSubmodule.map, C.simpleSubmodule.mono⟩

/-- Every object in a length-three submodule-chain support is uniserial. -/
theorem isUniserial_of_mem_submoduleChain_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {i : ι} (hi : i ∈ C.support) :
    IsUniserialModule R (σ.obj i) := by
  obtain ⟨f, hf⟩ :=
    LengthThreeSubmoduleChain.exists_mono_from_mem_support
      σ C hi
  letI : Mono f := hf
  exact
    x.2.2.of_injective f.hom.hom
      ((fg_mono_iff_injective f).mp inferInstance)

/-- Collective monic-component condition for a length-three submodule
chain. -/
def SubmoduleChainSubPresentationsHaveMonoComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) : Prop :=
  ∀ {j : ι}
      (P : σ.SubPresentation C.support (σ.obj j)),
    ∃ t : P.index,
      Mono
        (P.map ≫
          biproduct.π
            (fun a : P.index ↦ σ.obj (P.label a)) t)

/-- Socle-multiplicity-one form of the collective obstruction: every
indecomposable generated inside a sum of chain objects has simple
socle. -/
def SubmoduleChainSubSourcesHaveSimpleSocle
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) : Prop :=
  ∀ {j : ι},
    σ.InSub C.support (σ.obj j) →
      IsSimpleModule R (σ.moduleSocle j)

/-- Simple socle for every generated source supplies a monic component in
every collective presentation. -/
theorem submoduleChainSubPresentationsHaveMonoComponent_of_sourcesHaveSimpleSocle
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    (hsocle : σ.SubmoduleChainSubSourcesHaveSimpleSocle C) :
    σ.SubmoduleChainSubPresentationsHaveMonoComponent C := by
  unfold SubmoduleChainSubPresentationsHaveMonoComponent
  unfold SubmoduleChainSubSourcesHaveSimpleSocle at hsocle
  intro j P
  letI : Mono P.map := P.mono
  exact
    σ.exists_mono_biproduct_component_of_simple_socle
      (hsocle ⟨P⟩) P.index P.label P.map

/-- The monic-component condition implies collective submodule
closedness. -/
theorem sClosure_isClosed_submoduleChain_of_monoComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    (hcollective :
      σ.SubmoduleChainSubPresentationsHaveMonoComponent C) :
    σ.sClosure.IsClosed C.support := by
  unfold SubmoduleChainSubPresentationsHaveMonoComponent at hcollective
  rw [σ.sClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    obtain ⟨t, ht⟩ := hcollective P
    let g : σ.obj j ⟶ σ.obj (P.label t) :=
      P.map ≫
        biproduct.π
          (fun a : P.index ↦ σ.obj (P.label a)) t
    letI : Mono g := ht
    obtain ⟨q, hq⟩ :=
      LengthThreeSubmoduleChain.exists_mono_from_mem_support
        σ C (P.mem t)
    letI : Mono q := hq
    let f : σ.obj j ⟶ σ.obj x.1 := g ≫ q
    letI : Mono f := by
      dsimp only [f]
      infer_instance
    exact σ.mem_submoduleChain_support C f
  · exact σ.subset_sSet C.support

/-- A closed length-three submodule-chain support forces a monic
component in every collective presentation. -/
theorem submoduleChainSubPresentationsHaveMonoComponent_of_sClosure_isClosed
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    (hclosed : σ.sClosure.IsClosed C.support) :
    σ.SubmoduleChainSubPresentationsHaveMonoComponent C := by
  unfold SubmoduleChainSubPresentationsHaveMonoComponent
  intro j P
  have hj : j ∈ C.support := by
    rw [← hclosed.closure_eq]
    exact ⟨P⟩
  letI : Mono P.map := P.mono
  exact
    σ.exists_mono_biproduct_component_of_isUniserial
      (σ.isUniserial_of_mem_submoduleChain_support C hj)
      P.index P.label P.map

/-- A closed submodule-chain support forces simple socle for every
generated indecomposable. -/
theorem submoduleChainSubSourcesHaveSimpleSocle_of_sClosure_isClosed
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    (hclosed : σ.sClosure.IsClosed C.support) :
    σ.SubmoduleChainSubSourcesHaveSimpleSocle C := by
  unfold SubmoduleChainSubSourcesHaveSimpleSocle
  intro j hj
  have hjMem : j ∈ C.support := by
    rw [← hclosed.closure_eq]
    exact hj
  exact
    σ.moduleSocle_isSimple_of_isUniserial
      (σ.isUniserial_of_mem_submoduleChain_support C hjMem)

/-- Collective submodule closedness is equivalent to the monic-component
condition. -/
theorem sClosure_isClosed_submoduleChain_iff_monoComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) :
    σ.sClosure.IsClosed C.support ↔
      σ.SubmoduleChainSubPresentationsHaveMonoComponent C := by
  constructor
  · exact
      σ.submoduleChainSubPresentationsHaveMonoComponent_of_sClosure_isClosed
        C
  · exact σ.sClosure_isClosed_submoduleChain_of_monoComponent C

/-- Collective submodule closedness is equivalent to the simple-socle
condition on all generated indecomposables. -/
theorem sClosure_isClosed_submoduleChain_iff_sourcesHaveSimpleSocle
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) :
    σ.sClosure.IsClosed C.support ↔
      σ.SubmoduleChainSubSourcesHaveSimpleSocle C := by
  constructor
  · exact
      σ.submoduleChainSubSourcesHaveSimpleSocle_of_sClosure_isClosed C
  · intro hsocle
    exact
      σ.sClosure_isClosed_submoduleChain_of_monoComponent C
        (σ.submoduleChainSubPresentationsHaveMonoComponent_of_sourcesHaveSimpleSocle
          C hsocle)

/-! ## The unconditional socle type -/

/-- Every simple submodule of an indecomposable generated by the submodule
chain has the bottom simple index of the chain. -/
theorem simpleSubmodule_index_eq_of_inSub_submoduleChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {j : ι} (hj : σ.InSub C.support (σ.obj j))
    (L : σ.SimpleSubmodule j) :
    L.index = C.bottom.index := by
  classical
  obtain ⟨P⟩ := hj
  let g : σ.obj L.index ⟶ σ.sumOver P.index P.label :=
    L.map ≫ P.map
  letI : Mono L.map := L.mono
  letI : Mono P.map := P.mono
  letI : Mono g := by
    dsimp only [g]
    infer_instance
  letI : Simple (σ.obj L.index) := L.simple
  have hg : g ≠ 0 := by
    intro hzero
    exact
      (Simple.not_isZero (σ.obj L.index))
        (IsZero.of_mono_eq_zero g hzero)
  have hcomponent :
      ∃ t : P.index,
        g ≫
            biproduct.π
              (fun a : P.index ↦ σ.obj (P.label a)) t ≠
          0 := by
    by_contra h
    push Not at h
    apply hg
    apply biproduct.hom_ext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hcomponent
  let f : σ.obj L.index ⟶ σ.obj (P.label t) :=
    g ≫
      biproduct.π
        (fun a : P.index ↦ σ.obj (P.label a)) t
  letI : Mono f := mono_of_nonzero_from_simple ht
  obtain ⟨q, hq⟩ :=
    LengthThreeSubmoduleChain.exists_mono_from_mem_support
      σ C (P.mem t)
  letI : Mono q := hq
  let h : σ.obj L.index ⟶ σ.obj x.1 := f ≫ q
  letI : Mono h := by
    dsimp only [h]
    infer_instance
  let Q : σ.SimpleSubmodule x.1 := {
    index := L.index
    simple := L.simple
    map := h
    mono := inferInstance }
  exact
    SimpleSubmodule.index_eq_of_isUniserial
      σ x.2.2 Q C.simpleSubmodule

/-- Thus submodule generation fixes the simple socle type
unconditionally; only its multiplicity remains uncontrolled. -/
theorem hasUniqueSimpleSubmoduleType_of_inSub_submoduleChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {j : ι} (hj : σ.InSub C.support (σ.obj j)) :
    σ.HasUniqueSimpleSubmoduleType j C.bottom.index :=
  ⟨C.bottom.simple,
    fun L ↦ σ.simpleSubmodule_index_eq_of_inSub_submoduleChain C hj L⟩

/-- A unique skeleton type for simple submodules makes the concrete socle
isotypic of that type. -/
theorem moduleSocle_isIsotypicOfType_of_hasUniqueSimpleSubmoduleType
    {j s : ι} (hunique : σ.HasUniqueSimpleSubmoduleType j s) :
    IsIsotypicOfType R (σ.moduleSocle j) (σ.obj s) := by
  intro L hL
  letI : IsSimpleModule R L := hL
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R L
  have hLindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R L :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨k, ⟨e⟩⟩ := σ.complete Q hLindec
  letI : IsSimpleModule R (σ.obj k) :=
    IsSimpleModule.congr
      (FGModuleCat.isoToLinearEquiv e).symm
  letI : Simple (σ.obj k) :=
    (simple_iff_isSimpleModule_fg _).mpr inferInstance
  let inc : Q ⟶ σ.obj j :=
    FGModuleCat.ofHom
      ((σ.moduleSocle j).subtype.comp L.subtype)
  let f : σ.obj k ⟶ σ.obj j :=
    e.inv ≫ inc
  letI : Mono inc := by
    apply (fg_mono_iff_injective inc).mpr
    exact
      (σ.moduleSocle j).subtype_injective.comp
        L.subtype_injective
  letI : Mono f := by
    dsimp only [f]
    infer_instance
  let S : σ.SimpleSubmodule j := {
    index := k
    simple := inferInstance
    map := f
    mono := inferInstance }
  have hks : k = s := hunique.2 S
  subst k
  exact ⟨FGModuleCat.isoToLinearEquiv e⟩

/-- Hence the socle of every indecomposable generated by a length-three
submodule chain is isotypic of the chain-bottom simple. -/
theorem moduleSocle_isIsotypicOfType_of_inSub_submoduleChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {j : ι} (hj : σ.InSub C.support (σ.obj j)) :
    IsIsotypicOfType R
      (σ.moduleSocle j) (σ.obj C.bottom.index) :=
  σ.moduleSocle_isIsotypicOfType_of_hasUniqueSimpleSubmoduleType
    (σ.hasUniqueSimpleSubmoduleType_of_inSub_submoduleChain C hj)

end IndecomposableSkeleton

end QuotientSubmoduleEquidistribution
