import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeModules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthTwoPairClosure
import QuotientSubmoduleEquidistribution.RepresentationTheory.LevelTwoUnconditional

/-!
# Length-three uniserial representatives

Mathlib currently has no named predicate for uniserial modules. This file
uses totality of the submodule lattice as the definition and packages the
length-three skeleton indices that form the manuscript's `u₃` family.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe u v w

/-- A module is uniserial when any two of its submodules are comparable. -/
def IsUniserialModule
    (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  Std.Total ((· ≤ ·) : Submodule R M → Submodule R M → Prop)

namespace IsUniserialModule

variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- Quotients of uniserial modules are uniserial. -/
theorem quotient (hM : IsUniserialModule R M)
    (N : Submodule R M) :
    IsUniserialModule R (M ⧸ N) := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total (P.comap N.mkQ) (Q.comap N.mkQ) with hPQ | hQP
  · exact Or.inl
      ((Submodule.comap_le_comap_iff_of_surjective
        N.mkQ_surjective).mp hPQ)
  · exact Or.inr
      ((Submodule.comap_le_comap_iff_of_surjective
        N.mkQ_surjective).mp hQP)

/-- Submodules of uniserial modules are uniserial. -/
theorem submodule (hM : IsUniserialModule R M)
    (N : Submodule R M) :
    IsUniserialModule R N := by
  unfold IsUniserialModule at hM ⊢
  constructor
  intro P Q
  rcases hM.total (P.map N.subtype) (Q.map N.subtype) with hPQ | hQP
  · exact Or.inl
      ((Submodule.map_le_map_iff_of_injective
        N.subtype_injective P Q).mp hPQ)
  · exact Or.inr
      ((Submodule.map_le_map_iff_of_injective
        N.subtype_injective Q P).mp hQP)

/-- A nonzero uniserial module is indecomposable. -/
theorem isIndecomposableModule
    (hM : IsUniserialModule R M) [Nontrivial M] :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  unfold IsUniserialModule at hM
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro N P hcompl
  rcases hM.total N P with hNP | hPN
  · left
    apply le_antisymm
    · calc
        N ≤ N ⊓ P := le_inf le_rfl hNP
        _ = ⊥ := hcompl.inf_eq_bot
    · exact bot_le
  · right
    apply le_antisymm
    · calc
        P ≤ N ⊓ P := le_inf hPN le_rfl
        _ = ⊥ := hcompl.inf_eq_bot
    · exact bot_le

/-- In a finite-length uniserial module, submodules of equal composition
length coincide. -/
theorem eq_of_length_eq
    [IsArtinian R M] [IsNoetherian R M]
    (hM : IsUniserialModule R M)
    {N P : Submodule R M}
    (hlength : Module.length R N = Module.length R P) :
    N = P := by
  unfold IsUniserialModule at hM
  rcases hM.total N P with hNP | hPN
  · by_contra hne
    have hlt : N < P := lt_of_le_of_ne hNP hne
    have hlengthLt :
        Module.length R N < Module.length R P := by
      simpa only [Module.length_submodule] using
        (Submodule.height_strictMono hlt)
    exact (ne_of_lt hlengthLt) hlength
  · by_contra hne
    have hlt : P < N := lt_of_le_of_ne hPN (Ne.symm hne)
    have hlengthLt :
        Module.length R P < Module.length R N := by
      simpa only [Module.length_submodule] using
        (Submodule.height_strictMono hlt)
    exact (ne_of_lt hlengthLt) hlength.symm

end IsUniserialModule

namespace IndecomposableSkeleton

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- The property defining the manuscript's length-three uniserial family. -/
def IsLengthThreeUniserial (i : ι) : Prop :=
  σ.compositionLength i = 3 ∧
    IsUniserialModule R (σ.obj i)

/-- Skeleton indices of uniserial indecomposables of composition length three. -/
def LengthThreeUniserialIndex :=
  {i : ι // σ.IsLengthThreeUniserial i}

/-- A chosen indecomposable quotient of composition length two. -/
structure LengthTwoQuotient (x : ι) where
  index : ι
  length_two : σ.compositionLength index = 2
  map : σ.obj x ⟶ σ.obj index
  epi : Epi map

/-- A chosen indecomposable submodule of composition length two. -/
structure LengthTwoSubmodule (x : ι) where
  index : ι
  length_two : σ.compositionLength index = 2
  map : σ.obj index ⟶ σ.obj x
  mono : Mono map

/-- All simple quotient types of a uniserial representative agree. -/
theorem SimpleQuotient.index_eq_of_isUniserial
    {x : ι} (hx : IsUniserialModule R (σ.obj x))
    (Q Q' : σ.SimpleQuotient x) :
    Q.index = Q'.index := by
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
  have hQcoatom : IsCoatom (LinearMap.ker Q.map.hom.hom) :=
    LinearMap.isCoatom_ker_of_surjective hQsurj
  have hQ'coatom : IsCoatom (LinearMap.ker Q'.map.hom.hom) :=
    LinearMap.isCoatom_ker_of_surjective hQ'surj
  have hker :
      LinearMap.ker Q.map.hom.hom =
        LinearMap.ker Q'.map.hom.hom := by
    unfold IsUniserialModule at hx
    rcases hx.total (LinearMap.ker Q.map.hom.hom)
        (LinearMap.ker Q'.map.hom.hom) with hle | hle
    · exact ((hQcoatom.le_iff_eq hQ'coatom.ne_top).mp hle).symm
    · exact (hQ'coatom.le_iff_eq hQcoatom.ne_top).mp hle
  let e : σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    (Q.map.hom.hom.quotKerEquivOfSurjective hQsurj).symm.trans
      ((Submodule.quotEquivOfEq
        (LinearMap.ker Q.map.hom.hom)
        (LinearMap.ker Q'.map.hom.hom) hker).trans
          (Q'.map.hom.hom.quotKerEquivOfSurjective hQ'surj))
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- All simple submodule types of a uniserial representative agree. -/
theorem SimpleSubmodule.index_eq_of_isUniserial
    {x : ι} (hx : IsUniserialModule R (σ.obj x))
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
  have hAB : A = B := by
    unfold IsUniserialModule at hx
    rcases hx.total A B with hle | hle
    · exact (hBatom.le_iff_eq hAatom.ne_bot).mp hle
    · exact ((hAatom.le_iff_eq hBatom.ne_bot).mp hle).symm
  let e : σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    eA.trans ((LinearEquiv.ofEq A B hAB).trans eB.symm)
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- The kernel of an epimorphism from a length-three representative onto a
length-two representative is simple. -/
theorem kernel_isSimple_of_epi_of_compositionLength_three_two
    {x y : ι} (f : σ.obj x ⟶ σ.obj y) [Epi f]
    (hx : σ.compositionLength x = 3)
    (hy : σ.compositionLength y = 2) :
    IsSimpleModule R (LinearMap.ker f.hom.hom) := by
  have hsurj : Function.Surjective f.hom.hom :=
    (fg_epi_iff_surjective f).mp inferInstance
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R (LinearMap.ker f.hom.hom) +
          Module.length R (σ.obj y) :=
    Module.length_eq_add_of_exact
      (LinearMap.ker f.hom.hom).subtype f.hom.hom
      (Submodule.subtype_injective _)
      hsurj
      (LinearMap.exact_subtype_ker_map f.hom.hom)
  have htotal : Module.length R (σ.obj x) = 3 := by
    rw [← σ.coe_compositionLength x, hx]
    norm_num
  have htarget : Module.length R (σ.obj y) = 2 := by
    rw [← σ.coe_compositionLength y, hy]
    norm_num
  have hker :
      Module.length R (LinearMap.ker f.hom.hom) = 1 := by
    rw [htotal, htarget] at hlength
    apply WithTop.add_right_cancel (by norm_num : (2 : ℕ∞) ≠ ⊤)
    calc
      Module.length R (LinearMap.ker f.hom.hom) + 2 = 3 :=
        hlength.symm
      _ = 1 + 2 := by norm_num
  exact Module.length_eq_one_iff.mp hker

/-- A uniserial length-three representative has only one length-two
indecomposable quotient type, up to its skeleton index. -/
theorem LengthTwoQuotient.index_eq_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (Q Q' : σ.LengthTwoQuotient x) :
    Q.index = Q'.index := by
  letI : Epi Q.map := Q.epi
  letI : Epi Q'.map := Q'.epi
  have hQsurj : Function.Surjective Q.map.hom.hom :=
    (fg_epi_iff_surjective Q.map).mp inferInstance
  have hQ'surj : Function.Surjective Q'.map.hom.hom :=
    (fg_epi_iff_surjective Q'.map).mp inferInstance
  have hQsimple :
      IsSimpleModule R (LinearMap.ker Q.map.hom.hom) :=
    σ.kernel_isSimple_of_epi_of_compositionLength_three_two
      Q.map hx.1 Q.length_two
  have hQ'simple :
      IsSimpleModule R (LinearMap.ker Q'.map.hom.hom) :=
    σ.kernel_isSimple_of_epi_of_compositionLength_three_two
      Q'.map hx.1 Q'.length_two
  have hQatom : IsAtom (LinearMap.ker Q.map.hom.hom) :=
    isSimpleModule_iff_isAtom.mp hQsimple
  have hQ'atom : IsAtom (LinearMap.ker Q'.map.hom.hom) :=
    isSimpleModule_iff_isAtom.mp hQ'simple
  have hker :
      LinearMap.ker Q.map.hom.hom =
        LinearMap.ker Q'.map.hom.hom := by
    have htotal := hx.2
    unfold IsUniserialModule at htotal
    rcases htotal.total (LinearMap.ker Q.map.hom.hom)
        (LinearMap.ker Q'.map.hom.hom) with hle | hle
    · exact (hQ'atom.le_iff_eq hQatom.ne_bot).mp hle
    · exact ((hQatom.le_iff_eq hQ'atom.ne_bot).mp hle).symm
  let e : σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    (Q.map.hom.hom.quotKerEquivOfSurjective hQsurj).symm.trans
      ((Submodule.quotEquivOfEq
        (LinearMap.ker Q.map.hom.hom)
        (LinearMap.ker Q'.map.hom.hom) hker).trans
          (Q'.map.hom.hom.quotKerEquivOfSurjective hQ'surj))
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- A uniserial length-three representative has only one length-two
indecomposable submodule type, up to its skeleton index. -/
theorem LengthTwoSubmodule.index_eq_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x)
    (Q Q' : σ.LengthTwoSubmodule x) :
    Q.index = Q'.index := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  letI : IsNoetherian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).1
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
  have hAlength : Module.length R A = 2 := by
    calc
      Module.length R A = Module.length R (σ.obj Q.index) :=
        (LinearEquiv.length_eq eA).symm
      _ = 2 := by
        rw [← σ.coe_compositionLength Q.index, Q.length_two]
        norm_num
  have hBlength : Module.length R B = 2 := by
    calc
      Module.length R B = Module.length R (σ.obj Q'.index) :=
        (LinearEquiv.length_eq eB).symm
      _ = 2 := by
        rw [← σ.coe_compositionLength Q'.index, Q'.length_two]
        norm_num
  have hAB : A = B :=
    hx.2.eq_of_length_eq (hAlength.trans hBlength.symm)
  let e : σ.obj Q.index ≃ₗ[R] σ.obj Q'.index :=
    eA.trans ((LinearEquiv.ofEq A B hAB).trans eB.symm)
  exact σ.eq_of_iso ⟨e.toFGModuleCatIso⟩

/-- Every length-three uniserial representative has an indecomposable
quotient of composition length two. -/
theorem exists_lengthTwoQuotient_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x) :
    Nonempty (σ.LengthTwoQuotient x) := by
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
  have hNlength : Module.length R N = 1 :=
    Module.length_eq_one_iff.mpr hNsimple
  have htotal : Module.length R (σ.obj x) = 3 := by
    rw [← σ.coe_compositionLength x, hx.1]
    norm_num
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R N +
          Module.length R ((σ.obj x) ⧸ N) :=
    Module.length_eq_add_of_exact
      N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hquotLength :
      Module.length R ((σ.obj x) ⧸ N) = 2 := by
    rw [htotal, hNlength] at hlength
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R ((σ.obj x) ⧸ N) = 3 := hlength.symm
      _ = 1 + 2 := by norm_num
  letI : Nontrivial ((σ.obj x) ⧸ N) :=
    Module.length_pos_iff.mp (by rw [hquotLength]; norm_num)
  have hQuniserial :
      IsUniserialModule R ((σ.obj x) ⧸ N) :=
    hx.2.quotient N
  have hQindecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R ((σ.obj x) ⧸ N) :=
    hQuniserial.isIndecomposableModule
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((σ.obj x) ⧸ N)
  obtain ⟨j, ⟨e⟩⟩ :=
    σ.complete Q hQindecomposable
  let q : σ.obj x ⟶ Q :=
    FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (fg_epi_iff_surjective q).mpr N.mkQ_surjective
  let f : σ.obj x ⟶ σ.obj j :=
    q ≫ e.hom
  letI : Epi f := by
    dsimp only [f]
    infer_instance
  have hjLength : σ.compositionLength j = 2 := by
    rw [← ENat.coe_inj, σ.coe_compositionLength]
    calc
      Module.length R (σ.obj j) = Module.length R Q :=
        (LinearEquiv.length_eq
          (FGModuleCat.isoToLinearEquiv e)).symm
      _ = 2 := hquotLength
      _ = (2 : ℕ∞) := rfl
  exact ⟨{
    index := j
    length_two := hjLength
    map := f
    epi := inferInstance }⟩

/-- Every length-three uniserial representative has an indecomposable
submodule of composition length two. -/
theorem exists_lengthTwoSubmodule_of_isLengthThreeUniserial
    {x : ι} (hx : σ.IsLengthThreeUniserial x) :
    Nonempty (σ.LengthTwoSubmodule x) := by
  letI : Nontrivial (σ.obj x) :=
    (σ.indecomposable x).nontrivial
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  obtain ⟨N, hNcoatom, -⟩ :=
    (eq_top_or_exists_le_coatom
      (⊥ : Submodule R (σ.obj x))).resolve_left bot_ne_top
  have hquotSimple : IsSimpleModule R ((σ.obj x) ⧸ N) :=
    isSimpleModule_iff_isCoatom.mpr hNcoatom
  have hquotLength : Module.length R ((σ.obj x) ⧸ N) = 1 :=
    Module.length_eq_one_iff.mpr hquotSimple
  have htotal : Module.length R (σ.obj x) = 3 := by
    rw [← σ.coe_compositionLength x, hx.1]
    norm_num
  have hlength :
      Module.length R (σ.obj x) =
        Module.length R N +
          Module.length R ((σ.obj x) ⧸ N) :=
    Module.length_eq_add_of_exact
      N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hNlength : Module.length R N = 2 := by
    rw [htotal, hquotLength] at hlength
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R N + 1 = 3 := hlength.symm
      _ = 2 + 1 := by norm_num
  letI : Nontrivial N :=
    Module.length_pos_iff.mp (by rw [hNlength]; norm_num)
  have hNuniserial : IsUniserialModule R N :=
    hx.2.submodule N
  have hNindecomposable : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R N :=
    hNuniserial.isIndecomposableModule
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R N
  obtain ⟨j, ⟨e⟩⟩ :=
    σ.complete Q hNindecomposable
  let m : Q ⟶ σ.obj x :=
    FGModuleCat.ofHom N.subtype
  letI : Mono m :=
    (fg_mono_iff_injective m).mpr N.subtype_injective
  let f : σ.obj j ⟶ σ.obj x :=
    e.inv ≫ m
  letI : Mono f := by
    dsimp only [f]
    infer_instance
  have hjLength : σ.compositionLength j = 2 := by
    rw [← ENat.coe_inj, σ.coe_compositionLength]
    calc
      Module.length R (σ.obj j) = Module.length R Q :=
        (LinearEquiv.length_eq
          (FGModuleCat.isoToLinearEquiv e)).symm
      _ = 2 := hNlength
      _ = (2 : ℕ∞) := rfl
  exact ⟨{
    index := j
    length_two := hjLength
    map := f
    mono := inferInstance }⟩

/-! ## Canonical three-object quotient and submodule chains -/

/-- A representative of the two proper nonzero quotient steps of a
length-three uniserial object. -/
structure LengthThreeQuotientChain
    (x : σ.LengthThreeUniserialIndex) where
  middle : σ.LengthTwoQuotient x.1
  bottom : σ.SimpleQuotient middle.index

/-- A representative of the two proper nonzero submodule steps of a
length-three uniserial object. -/
structure LengthThreeSubmoduleChain
    (x : σ.LengthThreeUniserialIndex) where
  middle : σ.LengthTwoSubmodule x.1
  bottom : σ.SimpleSubmodule middle.index

/-- The simple quotient at the bottom of a quotient chain, viewed directly
as a simple quotient of the length-three source. -/
def LengthThreeQuotientChain.simpleQuotient
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.SimpleQuotient x.1 where
  index := C.bottom.index
  simple := C.bottom.simple
  map := C.middle.map ≫ C.bottom.map
  epi := by
    letI : Epi C.middle.map := C.middle.epi
    letI : Epi C.bottom.map := C.bottom.epi
    infer_instance

/-- The simple submodule at the bottom of a submodule chain, viewed directly
as a simple submodule of the length-three target. -/
def LengthThreeSubmoduleChain.simpleSubmodule
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) :
    σ.SimpleSubmodule x.1 where
  index := C.bottom.index
  simple := C.bottom.simple
  map := C.bottom.map ≫ C.middle.map
  mono := by
    letI : Mono C.middle.map := C.middle.mono
    letI : Mono C.bottom.map := C.bottom.mono
    infer_instance

/-- A length-three uniserial object has a quotient chain. -/
noncomputable def lengthThreeQuotientChain
    (x : σ.LengthThreeUniserialIndex) :
    σ.LengthThreeQuotientChain x := by
  let middle := Classical.choice
    (σ.exists_lengthTwoQuotient_of_isLengthThreeUniserial x.2)
  exact {
    middle := middle
    bottom := Classical.choice
      (σ.exists_simpleQuotient middle.index) }

/-- A length-three uniserial object has a submodule chain. -/
noncomputable def lengthThreeSubmoduleChain
    (x : σ.LengthThreeUniserialIndex) :
    σ.LengthThreeSubmoduleChain x := by
  let middle := Classical.choice
    (σ.exists_lengthTwoSubmodule_of_isLengthThreeUniserial x.2)
  exact {
    middle := middle
    bottom := Classical.choice
      (σ.exists_simpleSubmodule middle.index) }

/-- The three skeleton indices in a quotient chain. -/
def LengthThreeQuotientChain.support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) : Set ι :=
  {x.1, C.middle.index, C.bottom.index}

/-- The three skeleton indices in a submodule chain. -/
def LengthThreeSubmoduleChain.support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) : Set ι :=
  {x.1, C.middle.index, C.bottom.index}

@[simp]
theorem LengthThreeQuotientChain.ncard_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    C.support.ncard = 3 := by
  have hbottom : σ.compositionLength C.bottom.index = 1 :=
    (σ.compositionLength_eq_one_iff_simple C.bottom.index).2
      C.bottom.simple
  have hxm : x.1 ≠ C.middle.index := by
    intro h
    have hxlength := x.2.1
    rw [h, C.middle.length_two] at hxlength
    omega
  have hxb : x.1 ≠ C.bottom.index := by
    intro h
    have hxlength := x.2.1
    rw [h, hbottom] at hxlength
    omega
  have hmb : C.middle.index ≠ C.bottom.index := by
    intro h
    have hmiddle := C.middle.length_two
    rw [h, hbottom] at hmiddle
    omega
  simp [LengthThreeQuotientChain.support, hxm, hxb, hmb]

@[simp]
theorem LengthThreeSubmoduleChain.ncard_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x) :
    C.support.ncard = 3 := by
  have hbottom : σ.compositionLength C.bottom.index = 1 :=
    (σ.compositionLength_eq_one_iff_simple C.bottom.index).2
      C.bottom.simple
  have hxm : x.1 ≠ C.middle.index := by
    intro h
    have hxlength := x.2.1
    rw [h, C.middle.length_two] at hxlength
    omega
  have hxb : x.1 ≠ C.bottom.index := by
    intro h
    have hxlength := x.2.1
    rw [h, hbottom] at hxlength
    omega
  have hmb : C.middle.index ≠ C.bottom.index := by
    intro h
    have hmiddle := C.middle.length_two
    rw [h, hbottom] at hmiddle
    omega
  simp [LengthThreeSubmoduleChain.support, hxm, hxb, hmb]

/-- The support of a quotient chain determines its length-three source. -/
theorem LengthThreeQuotientChain.source_eq_of_support_eq
    {x y : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    (D : σ.LengthThreeQuotientChain y)
    (hCD : C.support = D.support) :
    x = y := by
  apply Subtype.ext
  have hxmem : x.1 ∈ D.support := by
    rw [← hCD]
    simp [LengthThreeQuotientChain.support]
  rcases (by
      simpa [LengthThreeQuotientChain.support] using hxmem) with
      hxy | hxm | hxb
  · exact hxy
  · exfalso
    have hxlength := x.2.1
    rw [hxm, D.middle.length_two] at hxlength
    omega
  · exfalso
    have hxlength := x.2.1
    have hbottom : σ.compositionLength D.bottom.index = 1 :=
      (σ.compositionLength_eq_one_iff_simple D.bottom.index).2
        D.bottom.simple
    rw [hxb, hbottom] at hxlength
    omega

/-- The support of a submodule chain determines its length-three target. -/
theorem LengthThreeSubmoduleChain.target_eq_of_support_eq
    {x y : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    (D : σ.LengthThreeSubmoduleChain y)
    (hCD : C.support = D.support) :
    x = y := by
  apply Subtype.ext
  have hxmem : x.1 ∈ D.support := by
    rw [← hCD]
    simp [LengthThreeSubmoduleChain.support]
  rcases (by
      simpa [LengthThreeSubmoduleChain.support] using hxmem) with
      hxy | hxm | hxb
  · exact hxy
  · exfalso
    have hxlength := x.2.1
    rw [hxm, D.middle.length_two] at hxlength
    omega
  · exfalso
    have hxlength := x.2.1
    have hbottom : σ.compositionLength D.bottom.index = 1 :=
      (σ.compositionLength_eq_one_iff_simple D.bottom.index).2
        D.bottom.simple
    rw [hxb, hbottom] at hxlength
    omega

theorem lengthThreeQuotientChain_support_injective :
    Function.Injective
      (fun x : σ.LengthThreeUniserialIndex ↦
        (σ.lengthThreeQuotientChain x).support) := by
  intro x y hxy
  exact
    LengthThreeQuotientChain.source_eq_of_support_eq
      σ (σ.lengthThreeQuotientChain x)
        (σ.lengthThreeQuotientChain y) hxy

theorem lengthThreeSubmoduleChain_support_injective :
    Function.Injective
      (fun x : σ.LengthThreeUniserialIndex ↦
        (σ.lengthThreeSubmoduleChain x).support) := by
  intro x y hxy
  exact
    LengthThreeSubmoduleChain.target_eq_of_support_eq
      σ (σ.lengthThreeSubmoduleChain x)
        (σ.lengthThreeSubmoduleChain y) hxy

/-- Quotient chains of a fixed length-three uniserial representative have
the same two proper quotient indices. -/
theorem LengthThreeQuotientChain.indices_eq
    {x : σ.LengthThreeUniserialIndex}
    (C D : σ.LengthThreeQuotientChain x) :
    C.middle.index = D.middle.index ∧
      C.bottom.index = D.bottom.index := by
  constructor
  · exact
      LengthTwoQuotient.index_eq_of_isLengthThreeUniserial
        σ x.2 C.middle D.middle
  · exact
      SimpleQuotient.index_eq_of_isUniserial
        σ x.2.2 C.simpleQuotient D.simpleQuotient

/-- Submodule chains of a fixed length-three uniserial representative have
the same two proper submodule indices. -/
theorem LengthThreeSubmoduleChain.indices_eq
    {x : σ.LengthThreeUniserialIndex}
    (C D : σ.LengthThreeSubmoduleChain x) :
    C.middle.index = D.middle.index ∧
      C.bottom.index = D.bottom.index := by
  constructor
  · exact
      LengthTwoSubmodule.index_eq_of_isLengthThreeUniserial
        σ x.2 C.middle D.middle
  · exact
      SimpleSubmodule.index_eq_of_isUniserial
        σ x.2.2 C.simpleSubmodule D.simpleSubmodule

/-- Every indecomposable quotient of a length-three uniserial representative
is the source or one of the two indices in any chosen quotient chain. -/
theorem quotient_index_eq_source_or_chain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (f : σ.obj x.1 ⟶ σ.obj j) [Epi f] :
    j = x.1 ∨
      j = C.middle.index ∨
        j = C.bottom.index := by
  rcases
      σ.simple_or_lengthTwo_or_isIso_of_epi_of_compositionLength_eq_three
        f x.2.1 with hsimple | hlength | hiso
  · right
    right
    let Q : σ.SimpleQuotient x.1 := {
      index := j
      simple := hsimple
      map := f
      epi := inferInstance }
    exact
      SimpleQuotient.index_eq_of_isUniserial
        σ x.2.2 Q C.simpleQuotient
  · right
    left
    let Q : σ.LengthTwoQuotient x.1 := {
      index := j
      length_two := hlength
      map := f
      epi := inferInstance }
    exact
      LengthTwoQuotient.index_eq_of_isLengthThreeUniserial
        σ x.2 Q C.middle
  · left
    exact (σ.eq_of_iso ⟨@asIso _ _ _ _ _ hiso⟩).symm

/-- Objectwise, every indecomposable quotient belongs to the three-index
support of a chosen quotient chain. -/
theorem mem_quotientChain_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (f : σ.obj x.1 ⟶ σ.obj j) [Epi f] :
    j ∈ C.support := by
  rcases σ.quotient_index_eq_source_or_chain C f with h | h | h
  · simp [LengthThreeQuotientChain.support, h]
  · simp [LengthThreeQuotientChain.support, h]
  · simp [LengthThreeQuotientChain.support, h]

/-- Every indecomposable submodule of a length-three uniserial representative
is the target or one of the two indices in any chosen submodule chain. -/
theorem submodule_index_eq_source_or_chain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {j : ι} (f : σ.obj j ⟶ σ.obj x.1) [Mono f] :
    j = x.1 ∨
      j = C.middle.index ∨
        j = C.bottom.index := by
  rcases
      σ.simple_or_lengthTwo_or_isIso_of_mono_of_compositionLength_eq_three
        f x.2.1 with hsimple | hlength | hiso
  · right
    right
    let Q : σ.SimpleSubmodule x.1 := {
      index := j
      simple := hsimple
      map := f
      mono := inferInstance }
    exact
      SimpleSubmodule.index_eq_of_isUniserial
        σ x.2.2 Q C.simpleSubmodule
  · right
    left
    let Q : σ.LengthTwoSubmodule x.1 := {
      index := j
      length_two := hlength
      map := f
      mono := inferInstance }
    exact
      LengthTwoSubmodule.index_eq_of_isLengthThreeUniserial
        σ x.2 Q C.middle
  · left
    exact σ.eq_of_iso ⟨@asIso _ _ _ _ _ hiso⟩

/-- Objectwise, every indecomposable submodule belongs to the three-index
support of a chosen submodule chain. -/
theorem mem_submoduleChain_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeSubmoduleChain x)
    {j : ι} (f : σ.obj j ⟶ σ.obj x.1) [Mono f] :
    j ∈ C.support := by
  rcases σ.submodule_index_eq_source_or_chain C f with h | h | h
  · simp [LengthThreeSubmoduleChain.support, h]
  · simp [LengthThreeSubmoduleChain.support, h]
  · simp [LengthThreeSubmoduleChain.support, h]

/-! ## Collective quotient closure: exact reduction -/

/-- Every member of the three-index quotient-chain support is itself an
indecomposable quotient of the length-three source. -/
theorem LengthThreeQuotientChain.exists_epi_to_mem_support
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {i : ι} (hi : i ∈ C.support) :
    ∃ f : σ.obj x.1 ⟶ σ.obj i, Epi f := by
  rcases (by
      simpa [LengthThreeQuotientChain.support] using hi) with
      rfl | rfl | rfl
  · exact ⟨𝟙 _, inferInstance⟩
  · exact ⟨C.middle.map, C.middle.epi⟩
  · exact ⟨C.simpleQuotient.map, C.simpleQuotient.epi⟩

/-- Collective epic-component condition for the three-object quotient
chain. -/
def QuotientChainFacPresentationsHaveEpiComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) : Prop :=
  ∀ {j : ι}
      (P : σ.FacPresentation C.support (σ.obj j)),
    ∃ t : P.index,
      Epi
        (biproduct.ι
            (fun a : P.index ↦ σ.obj (P.label a)) t ≫
          P.map)

/-- Top-multiplicity-one form of the collective obstruction: every
indecomposable generated by the chain has simple top. -/
def QuotientChainFacTargetsHaveSimpleTop
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) : Prop :=
  ∀ {j : ι},
    σ.InFac C.support (σ.obj j) →
      IsSimpleModule R (σ.moduleTop j)

/-- The top of a nonzero finite-length uniserial representative is simple. -/
theorem moduleTop_isSimple_of_isUniserial
    {i : ι} (hi : IsUniserialModule R (σ.obj i)) :
    IsSimpleModule R (σ.moduleTop i) := by
  letI : Nontrivial (σ.obj i) :=
    (σ.indecomposable i).nontrivial
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  have hradicalNeTop : σ.moduleRadical i ≠ ⊤ :=
    (Module.jacobson_lt_top R (σ.obj i)).ne
  letI : Nontrivial (σ.moduleTop i) :=
    Submodule.Quotient.nontrivial_iff.mpr hradicalNeTop
  have htopUniserial :
      IsUniserialModule R (σ.moduleTop i) :=
    hi.quotient (σ.moduleRadical i)
  have htopIndecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (σ.moduleTop i) :=
    htopUniserial.isIndecomposableModule
  letI : IsSemisimpleModule R (σ.moduleTop i) :=
    σ.moduleTop_isSemisimple i
  exact
    isSimpleModule_of_semisimple_of_indecomposable
      htopIndecomposable

/-- Simple top of every generated target supplies an epic component in
every collective presentation. -/
theorem quotientChainFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    (htop : σ.QuotientChainFacTargetsHaveSimpleTop C) :
    σ.QuotientChainFacPresentationsHaveEpiComponent C := by
  unfold QuotientChainFacPresentationsHaveEpiComponent
  unfold QuotientChainFacTargetsHaveSimpleTop at htop
  intro j P
  letI : Epi P.map := P.epi
  exact
    σ.exists_epi_biproduct_component_of_simple_top
      P.index P.label (htop ⟨P⟩) P.map

/-- The epic-component condition is sufficient for collective quotient
closedness of the uniserial chain support. -/
theorem qClosure_isClosed_quotientChain_of_epiComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    (hcollective :
      σ.QuotientChainFacPresentationsHaveEpiComponent C) :
    σ.qClosure.IsClosed C.support := by
  unfold QuotientChainFacPresentationsHaveEpiComponent at hcollective
  rw [σ.qClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    obtain ⟨t, ht⟩ := hcollective P
    let g : σ.obj (P.label t) ⟶ σ.obj j :=
      biproduct.ι
          (fun a : P.index ↦ σ.obj (P.label a)) t ≫
        P.map
    letI : Epi g := ht
    obtain ⟨q, hq⟩ :=
      LengthThreeQuotientChain.exists_epi_to_mem_support
        σ C (P.mem t)
    letI : Epi q := hq
    let f : σ.obj x.1 ⟶ σ.obj j := q ≫ g
    letI : Epi f := by
      dsimp only [f]
      infer_instance
    exact σ.mem_quotientChain_support C f
  · exact σ.subset_qSet C.support

/-- A closed quotient-chain support forces simple top for every generated
indecomposable. -/
theorem quotientChainFacTargetsHaveSimpleTop_of_qClosure_isClosed
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    (hclosed : σ.qClosure.IsClosed C.support) :
    σ.QuotientChainFacTargetsHaveSimpleTop C := by
  unfold QuotientChainFacTargetsHaveSimpleTop
  intro j hj
  have hjMem : j ∈ C.support := by
    rw [← hclosed.closure_eq]
    exact hj
  rcases (by
      simpa [LengthThreeQuotientChain.support] using hjMem) with
      hjx | hjm | hjb
  · subst j
    exact σ.moduleTop_isSimple_of_isUniserial x.2.2
  · subst j
    exact
      QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.IndecomposableSkeleton.moduleTop_isSimple_of_compositionLength_eq_two
        σ C.middle.length_two
  · subst j
    exact σ.moduleTop_isSimple_of_simple C.bottom.simple

/-- Collective quotient closedness is equivalent to the simple-top
condition on all generated indecomposables. -/
theorem qClosure_isClosed_quotientChain_iff_targetsHaveSimpleTop
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.qClosure.IsClosed C.support ↔
      σ.QuotientChainFacTargetsHaveSimpleTop C := by
  constructor
  · exact
      σ.quotientChainFacTargetsHaveSimpleTop_of_qClosure_isClosed C
  · intro htop
    exact
      σ.qClosure_isClosed_quotientChain_of_epiComponent C
        (σ.quotientChainFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
          C htop)

/-- Equivalent epic-component formulation of the collective obstruction. -/
theorem qClosure_isClosed_quotientChain_iff_epiComponent
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x) :
    σ.qClosure.IsClosed C.support ↔
      σ.QuotientChainFacPresentationsHaveEpiComponent C := by
  constructor
  · intro hclosed
    exact
      σ.quotientChainFacPresentationsHaveEpiComponent_of_targetsHaveSimpleTop
        C
        (σ.quotientChainFacTargetsHaveSimpleTop_of_qClosure_isClosed
          C hclosed)
  · exact σ.qClosure_isClosed_quotientChain_of_epiComponent C

/-! ## The unconditional top type and remaining multiplicity -/

/-- Every simple quotient of an indecomposable generated by the chain has
the bottom simple index of the chain. -/
theorem simpleQuotient_index_eq_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j))
    (L : σ.SimpleQuotient j) :
    L.index = C.bottom.index := by
  classical
  obtain ⟨P⟩ := hj
  let g : σ.sumOver P.index P.label ⟶ σ.obj L.index :=
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
  let f : σ.obj (P.label t) ⟶ σ.obj L.index :=
    biproduct.ι
        (fun a : P.index ↦ σ.obj (P.label a)) t ≫
      g
  letI : Epi f := epi_of_nonzero_to_simple ht
  obtain ⟨q, hq⟩ :=
    LengthThreeQuotientChain.exists_epi_to_mem_support
      σ C (P.mem t)
  letI : Epi q := hq
  let h : σ.obj x.1 ⟶ σ.obj L.index := q ≫ f
  letI : Epi h := by
    dsimp only [h]
    infer_instance
  let Q : σ.SimpleQuotient x.1 := {
    index := L.index
    simple := L.simple
    map := h
    epi := inferInstance }
  exact
    SimpleQuotient.index_eq_of_isUniserial
      σ x.2.2 Q C.simpleQuotient

/-- Thus generation fixes the simple top type unconditionally; only its
multiplicity remains uncontrolled. -/
theorem hasUniqueSimpleQuotientType_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    σ.HasUniqueSimpleQuotientType j C.bottom.index :=
  ⟨C.bottom.simple,
    fun L ↦ σ.simpleQuotient_index_eq_of_inFac_quotientChain C hj L⟩

/-- The full semisimple top of a generated indecomposable is isotypic of
the chain's bottom simple.  Consequently, collective closedness is reduced
exactly to proving that this isotypic top has multiplicity one. -/
theorem moduleTop_isIsotypicOfType_of_inFac_quotientChain
    {x : σ.LengthThreeUniserialIndex}
    (C : σ.LengthThreeQuotientChain x)
    {j : ι} (hj : σ.InFac C.support (σ.obj j)) :
    IsIsotypicOfType R
      (σ.moduleTop j) (σ.obj C.bottom.index) :=
  QuotientSubmoduleEquidistribution.LevelTwoUnconditional.moduleTop_isIsotypicOfType_of_hasUniqueSimpleQuotientType
    σ (σ.hasUniqueSimpleQuotientType_of_inFac_quotientChain C hj)

end IndecomposableSkeleton

end QuotientSubmoduleEquidistribution
