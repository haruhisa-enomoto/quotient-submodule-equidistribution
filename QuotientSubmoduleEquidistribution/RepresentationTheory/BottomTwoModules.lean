import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Length
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleLevels

/-!
# Length two and the second closure level

This file develops the unconditional part of the manuscript's level-two argument
which follows from the existing finite-length and collective `Fac`/`Sub`
definitions.

The main unconditional results are:

* concrete composition length on the chosen indecomposable skeleton;
* explicit simple quotient and simple submodule witnesses;
* collective closure of every support consisting only of simple objects;
* a necessary normal form for every quotient- or submodule-closed
  two-element support;
* length-two control of individual indecomposable quotients and submodules;
* concrete radical, top, socle, and length-two composition-series data.

These results deliberately stop before the Gabriel-quiver classification.
In particular, an objectwise quotient/submodule dichotomy does not replace
the collective finite-sum closure condition.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.IndecomposableSkeleton

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} (σ : IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-! ## Composition length -/

/-- The finite composition length of a chosen indecomposable
representative. -/
def compositionLength (i : ι) : ℕ :=
  (Module.length R (σ.obj i)).toNat

/-- The natural-valued composition length recovers Mathlib's `ℕ∞`-valued
module length. -/
theorem coe_compositionLength (i : ι) :
    (σ.compositionLength i : ℕ∞) =
      Module.length R (σ.obj i) := by
  exact ENat.coe_toNat
    ((Module.length_ne_top_iff).2 (σ.finiteLength i))

/-- Every chosen indecomposable representative has positive composition
length. -/
theorem compositionLength_pos (i : ι) :
    0 < σ.compositionLength i := by
  letI : Nontrivial (σ.obj i) :=
    (σ.indecomposable i).nontrivial
  have h :
      (0 : ℕ∞) < (σ.compositionLength i : ℕ∞) := by
    rw [coe_compositionLength]
    exact Module.length_pos
  exact_mod_cast h

/-- Composition length one is exactly simplicity. -/
theorem compositionLength_eq_one_iff_simple (i : ι) :
    σ.compositionLength i = 1 ↔ Simple (σ.obj i) := by
  rw [compositionLength, ENat.toNat_eq_iff one_ne_zero,
    Nat.cast_one, Module.length_eq_one_iff,
    simple_iff_isSimpleModule_fg]

/-- A nonsimple chosen indecomposable has composition length at least two. -/
theorem two_le_compositionLength_of_not_simple
    {i : ι} (hi : ¬ Simple (σ.obj i)) :
    2 ≤ σ.compositionLength i := by
  have hpos := σ.compositionLength_pos i
  have hne : σ.compositionLength i ≠ 1 := by
    simpa [σ.compositionLength_eq_one_iff_simple i] using hi
  omega

/-! ## Simple quotient and submodule witnesses -/

/-- A concrete simple quotient of one chosen representative. -/
structure SimpleQuotient (i : ι) where
  index : ι
  simple : Simple (σ.obj index)
  map : σ.obj i ⟶ σ.obj index
  epi : Epi map

/-- A concrete simple submodule of one chosen representative. -/
structure SimpleSubmodule (i : ι) where
  index : ι
  simple : Simple (σ.obj index)
  map : σ.obj index ⟶ σ.obj i
  mono : Mono map

/-- Every chosen indecomposable has a simple quotient. -/
theorem exists_simpleQuotient (i : ι) :
    Nonempty (σ.SimpleQuotient i) := by
  letI : Nontrivial (σ.obj i) :=
    (σ.indecomposable i).nontrivial
  obtain ⟨N, hNcoatom, -⟩ :=
    (eq_top_or_exists_le_coatom
      (⊥ : Submodule R (σ.obj i))).resolve_left bot_ne_top
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((σ.obj i) ⧸ N)
  have hQsimpleModule : IsSimpleModule R Q := by
    change IsSimpleModule R ((σ.obj i) ⧸ N)
    exact isSimpleModule_iff_isCoatom.mpr hNcoatom
  letI : IsSimpleModule R Q := hQsimpleModule
  have hQindecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Q :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨j, ⟨e⟩⟩ :=
    σ.complete Q hQindecomposable
  let q : σ.obj i ⟶ Q :=
    FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (fg_epi_iff_surjective q).mpr N.mkQ_surjective
  let f : σ.obj i ⟶ σ.obj j :=
    q ≫ e.hom
  have hQsimple : Simple Q :=
    (simple_iff_isSimpleModule_fg Q).mpr hQsimpleModule
  have hjSimple : Simple (σ.obj j) :=
    (Simple.iff_of_iso e).mp hQsimple
  exact ⟨{
    index := j
    simple := hjSimple
    map := f
    epi := by
      dsimp only [f]
      infer_instance }⟩

/-- Every chosen indecomposable has a simple submodule. -/
theorem exists_simpleSubmodule (i : ι) :
    Nonempty (σ.SimpleSubmodule i) := by
  letI : Nontrivial (σ.obj i) :=
    (σ.indecomposable i).nontrivial
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  obtain ⟨N, hNatom, -⟩ :=
    (eq_bot_or_exists_atom_le
      (⊤ : Submodule R (σ.obj i))).resolve_left top_ne_bot
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R N
  have hQsimpleModule : IsSimpleModule R Q := by
    change IsSimpleModule R N
    exact isSimpleModule_iff_isAtom.mpr hNatom
  letI : IsSimpleModule R Q := hQsimpleModule
  have hQindecomposable :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Q :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨j, ⟨e⟩⟩ :=
    σ.complete Q hQindecomposable
  let m : Q ⟶ σ.obj i :=
    FGModuleCat.ofHom N.subtype
  letI : Mono m :=
    ConcreteCategory.mono_of_injective m
      N.subtype_injective
  let f : σ.obj j ⟶ σ.obj i :=
    e.inv ≫ m
  have hQsimple : Simple Q :=
    (simple_iff_isSimpleModule_fg Q).mpr hQsimpleModule
  have hjSimple : Simple (σ.obj j) :=
    (Simple.iff_of_iso e).mp hQsimple
  exact ⟨{
    index := j
    simple := hjSimple
    map := f
    mono := by
      dsimp only [f]
      infer_instance }⟩

/-- A selected source places each of its simple quotients in the collective
quotient closure. -/
theorem SimpleQuotient.mem_qClosure
    {i : ι} (Q : σ.SimpleQuotient i)
    {S : Set ι} (hi : i ∈ S) :
    Q.index ∈ σ.qClosure S := by
  let a : Fin 1 → ι := fun _ ↦ i
  let f :
      σ.sumOver (FintypeCat.of (Fin 1)) a ⟶
        σ.obj Q.index :=
    (biproductUniqueIso fun t : Fin 1 ↦
      σ.obj (a t)).hom ≫ Q.map
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hi
    map := f
    epi := ?_ }⟩
  dsimp only [f]
  letI : Epi Q.map := Q.epi
  infer_instance

/-- A selected target places each of its simple submodules in the collective
submodule closure. -/
theorem SimpleSubmodule.mem_sClosure
    {i : ι} (Q : σ.SimpleSubmodule i)
    {S : Set ι} (hi : i ∈ S) :
    Q.index ∈ σ.sClosure S := by
  let a : Fin 1 → ι := fun _ ↦ i
  let f :
      σ.obj Q.index ⟶
        σ.sumOver (FintypeCat.of (Fin 1)) a :=
    Q.map ≫
      (biproductUniqueIso fun t : Fin 1 ↦
        σ.obj (a t)).inv
  refine ⟨{
    index := FintypeCat.of (Fin 1)
    label := a
    mem := fun _ ↦ hi
    map := f
    mono := ?_ }⟩
  dsimp only [f]
  letI : Mono Q.map := Q.mono
  infer_instance

/-- In a quotient-closed support, every simple quotient of a selected
representative is again selected. -/
theorem SimpleQuotient.mem_of_isClosed
    {i : ι} (Q : σ.SimpleQuotient i)
    {S : Set ι} (hS : σ.qClosure.IsClosed S)
    (hi : i ∈ S) :
    Q.index ∈ S := by
  rw [← hS.closure_eq]
  exact Q.mem_qClosure σ hi

/-- In a submodule-closed support, every simple submodule of a selected
representative is again selected. -/
theorem SimpleSubmodule.mem_of_isClosed
    {i : ι} (Q : σ.SimpleSubmodule i)
    {S : Set ι} (hS : σ.sClosure.IsClosed S)
    (hi : i ∈ S) :
    Q.index ∈ S := by
  rw [← hS.closure_eq]
  exact Q.mem_sClosure σ hi

/-! ## Supports consisting only of simples are collectively closed -/

/-- Any support consisting only of simple representatives is closed under
quotients of arbitrary finite direct sums. -/
theorem qClosure_isClosed_of_forall_simple
    {S : Set ι} (hS : ∀ i ∈ S, Simple (σ.obj i)) :
    σ.qClosure.IsClosed S := by
  rw [σ.qClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    letI (t : P.index) : Simple (σ.obj (P.label t)) :=
      hS (P.label t) (P.mem t)
    letI (t : P.index) :
        IsSimpleModule R (σ.obj (P.label t)) :=
      (simple_iff_isSimpleModule_fg _).mp inferInstance
    letI : IsSemisimpleModule R
        (∀ t : P.index, σ.obj (P.label t)) :=
      inferInstance
    let e :
        σ.sumOver P.index P.label ≅
          FGModuleCat.of R
            (∀ t : P.index, σ.obj (P.label t)) :=
      biproductIsoPiFG _
    letI : IsSemisimpleModule R
        (σ.sumOver P.index P.label) :=
      (LinearEquiv.isSemisimpleModule_iff
        (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
    letI : Epi P.map := P.epi
    have hsurj : Function.Surjective P.map.hom.hom :=
      (fg_epi_iff_surjective P.map).mp inferInstance
    letI : IsSemisimpleModule R (σ.obj j) :=
      IsSemisimpleModule.of_surjective P.map.hom.hom hsurj
    letI : IsSimpleModule R (σ.obj j) :=
      isSimpleModule_of_semisimple_of_indecomposable
        (σ.indecomposable j)
    letI : Simple (σ.obj j) :=
      (simple_iff_isSimpleModule_fg _).mpr inferInstance
    have hmap : P.map ≠ 0 := by
      intro hzero
      exact
        (Simple.not_isZero (σ.obj j))
          (IsZero.of_epi_eq_zero P.map hzero)
    have hcomponent :
        ∃ t : P.index,
          biproduct.ι
              (fun t : P.index ↦ σ.obj (P.label t)) t ≫
            P.map ≠ 0 := by
      by_contra h
      push Not at h
      apply hmap
      apply biproduct.hom_ext'
      intro t
      simpa using h t
    obtain ⟨t, ht⟩ := hcomponent
    let g :
        σ.obj (P.label t) ⟶ σ.obj j :=
      biproduct.ι
          (fun s : P.index ↦ σ.obj (P.label s)) t ≫
        P.map
    haveI : IsIso g := isIso_of_hom_simple ht
    have hindex : P.label t = j :=
      σ.eq_of_iso ⟨asIso g⟩
    simpa [← hindex] using P.mem t
  · exact σ.subset_qSet S

/-- Any support consisting only of simple representatives is closed under
submodules of arbitrary finite direct sums. -/
theorem sClosure_isClosed_of_forall_simple
    {S : Set ι} (hS : ∀ i ∈ S, Simple (σ.obj i)) :
    σ.sClosure.IsClosed S := by
  rw [σ.sClosure.isClosed_iff]
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨P⟩ := hj
    letI (t : P.index) : Simple (σ.obj (P.label t)) :=
      hS (P.label t) (P.mem t)
    letI (t : P.index) :
        IsSimpleModule R (σ.obj (P.label t)) :=
      (simple_iff_isSimpleModule_fg _).mp inferInstance
    letI : IsSemisimpleModule R
        (∀ t : P.index, σ.obj (P.label t)) :=
      inferInstance
    let e :
        σ.sumOver P.index P.label ≅
          FGModuleCat.of R
            (∀ t : P.index, σ.obj (P.label t)) :=
      biproductIsoPiFG _
    letI : IsSemisimpleModule R
        (σ.sumOver P.index P.label) :=
      (LinearEquiv.isSemisimpleModule_iff
        (FGModuleCat.isoToLinearEquiv e)).mpr inferInstance
    letI : Mono P.map := P.mono
    have hinj : Function.Injective P.map.hom.hom :=
      (fg_mono_iff_injective P.map).mp inferInstance
    letI : IsSemisimpleModule R (σ.obj j) :=
      IsSemisimpleModule.of_injective P.map.hom.hom hinj
    letI : IsSimpleModule R (σ.obj j) :=
      isSimpleModule_of_semisimple_of_indecomposable
        (σ.indecomposable j)
    letI : Simple (σ.obj j) :=
      (simple_iff_isSimpleModule_fg _).mpr inferInstance
    have hmap : P.map ≠ 0 := by
      intro hzero
      exact
        (Simple.not_isZero (σ.obj j))
          (IsZero.of_mono_eq_zero P.map hzero)
    have hcomponent :
        ∃ t : P.index,
          P.map ≫
            biproduct.π
              (fun t : P.index ↦ σ.obj (P.label t)) t ≠ 0 := by
      by_contra h
      push Not at h
      apply hmap
      apply biproduct.hom_ext
      intro t
      simpa using h t
    obtain ⟨t, ht⟩ := hcomponent
    let g :
        σ.obj j ⟶ σ.obj (P.label t) :=
      P.map ≫
        biproduct.π
          (fun s : P.index ↦ σ.obj (P.label s)) t
    haveI : IsIso g := isIso_of_hom_simple ht
    have hindex : j = P.label t :=
      σ.eq_of_iso ⟨asIso g⟩
    simpa [hindex] using P.mem t
  · exact σ.subset_sSet S

/-! ## The unconditional normal form of a closed pair -/

/-- All simple quotients of `x` have the same skeleton type `s`. -/
def HasUniqueSimpleQuotientType (x s : ι) : Prop :=
  Simple (σ.obj s) ∧
    ∀ Q : σ.SimpleQuotient x, Q.index = s

/-- All simple submodules of `x` have the same skeleton type `s`. -/
def HasUniqueSimpleSubmoduleType (x s : ι) : Prop :=
  Simple (σ.obj s) ∧
    ∀ Q : σ.SimpleSubmodule x, Q.index = s

/--
Every quotient-closed two-element support is either a pair of simples, or
has a unique nonsimple member all of whose simple quotients are the other
member.

This is a necessary normal form.  It does not assert that the nonsimple
member already has length two.
-/
theorem qClosed_pair_classification
    {S : Set ι} (hcard : S.ncard = 2)
    (hclosed : σ.qClosure.IsClosed S) :
    (∀ i ∈ S, Simple (σ.obj i)) ∨
      ∃ x s : ι,
        x ≠ s ∧ S = {x, s} ∧
          ¬ Simple (σ.obj x) ∧
            σ.HasUniqueSimpleQuotientType x s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp hcard
  by_cases ha : Simple (σ.obj a)
  · by_cases hb : Simple (σ.obj b)
    · left
      intro i hi
      rcases hi with (rfl | rfl)
      · exact ha
      · exact hb
    · right
      obtain ⟨Q⟩ := σ.exists_simpleQuotient b
      have hQmem : Q.index ∈ ({a, b} : Set ι) :=
        Q.mem_of_isClosed σ hclosed (by simp)
      have hQne : Q.index ≠ b := by
        intro h
        apply hb
        simpa [h] using Q.simple
      refine ⟨b, a, hab.symm, by ext i; simp [or_comm],
        hb, ha, ?_⟩
      intro Q'
      have hmem : Q'.index ∈ ({a, b} : Set ι) :=
        Q'.mem_of_isClosed σ hclosed (by simp)
      rcases hmem with h | h
      · exact h
      · exfalso
        apply hb
        exact h ▸ Q'.simple
  · right
    obtain ⟨Q⟩ := σ.exists_simpleQuotient a
    have hQmem : Q.index ∈ ({a, b} : Set ι) :=
      Q.mem_of_isClosed σ hclosed (by simp)
    have hQne : Q.index ≠ a := by
      intro h
      apply ha
      simpa [h] using Q.simple
    have hQb : Q.index = b := by
      simpa [hQne] using hQmem
    have hb : Simple (σ.obj b) := by
      simpa [hQb] using Q.simple
    refine ⟨a, b, hab, rfl, ha, hb, ?_⟩
    intro Q'
    have hmem : Q'.index ∈ ({a, b} : Set ι) :=
      Q'.mem_of_isClosed σ hclosed (by simp)
    rcases hmem with h | h
    · exfalso
      apply ha
      simpa [h] using Q'.simple
    · exact h

/--
Every submodule-closed two-element support is either a pair of simples, or
has a unique nonsimple member all of whose simple submodules are the other
member.
-/
theorem sClosed_pair_classification
    {S : Set ι} (hcard : S.ncard = 2)
    (hclosed : σ.sClosure.IsClosed S) :
    (∀ i ∈ S, Simple (σ.obj i)) ∨
      ∃ x s : ι,
        x ≠ s ∧ S = {x, s} ∧
          ¬ Simple (σ.obj x) ∧
            σ.HasUniqueSimpleSubmoduleType x s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.mp hcard
  by_cases ha : Simple (σ.obj a)
  · by_cases hb : Simple (σ.obj b)
    · left
      intro i hi
      rcases hi with (rfl | rfl)
      · exact ha
      · exact hb
    · right
      obtain ⟨Q⟩ := σ.exists_simpleSubmodule b
      have hQmem : Q.index ∈ ({a, b} : Set ι) :=
        Q.mem_of_isClosed σ hclosed (by simp)
      have hQne : Q.index ≠ b := by
        intro h
        apply hb
        simpa [h] using Q.simple
      have hQa : Q.index = a := by
        simpa [hQne] using hQmem
      refine ⟨b, a, hab.symm, by ext i; simp [or_comm],
        hb, ha, ?_⟩
      intro Q'
      have hmem : Q'.index ∈ ({a, b} : Set ι) :=
        Q'.mem_of_isClosed σ hclosed (by simp)
      rcases hmem with h | h
      · exact h
      · exfalso
        apply hb
        exact h ▸ Q'.simple
  · right
    obtain ⟨Q⟩ := σ.exists_simpleSubmodule a
    have hQmem : Q.index ∈ ({a, b} : Set ι) :=
      Q.mem_of_isClosed σ hclosed (by simp)
    have hQne : Q.index ≠ a := by
      intro h
      apply ha
      simpa [h] using Q.simple
    have hQb : Q.index = b := by
      simpa [hQne] using hQmem
    have hb : Simple (σ.obj b) := by
      simpa [hQb] using Q.simple
    refine ⟨a, b, hab, rfl, ha, hb, ?_⟩
    intro Q'
    have hmem : Q'.index ∈ ({a, b} : Set ι) :=
      Q'.mem_of_isClosed σ hclosed (by simp)
    rcases hmem with h | h
    · exfalso
      apply ha
      simpa [h] using Q'.simple
    · exact h

/-! ## Length-two quotients and submodules -/

/-- An epimorphism between chosen representatives of equal finite
composition length is an isomorphism. -/
theorem isIso_of_epi_of_compositionLength_eq
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Epi f]
    (hij :
      σ.compositionLength i =
        σ.compositionLength j) :
    IsIso f := by
  have hsurj : Function.Surjective f.hom.hom :=
    (fg_epi_iff_surjective f).mp inferInstance
  have hlength :
      Module.length R (σ.obj i) =
        Module.length R (LinearMap.ker f.hom.hom) +
          Module.length R (σ.obj j) :=
    Module.length_eq_add_of_exact
      (LinearMap.ker f.hom.hom).subtype f.hom.hom
      (Submodule.subtype_injective _)
      hsurj
      (LinearMap.exact_subtype_ker_map f.hom.hom)
  have hjfinite :
      Module.length R (σ.obj j) ≠ ⊤ :=
    (Module.length_ne_top_iff).2 (σ.finiteLength j)
  have hker :
      Module.length R (LinearMap.ker f.hom.hom) = 0 := by
    apply WithTop.add_right_cancel hjfinite
    calc
      Module.length R (LinearMap.ker f.hom.hom) +
            Module.length R (σ.obj j) =
          Module.length R (σ.obj i) :=
        hlength.symm
      _ = Module.length R (σ.obj j) := by
        rw [← σ.coe_compositionLength i,
          ← σ.coe_compositionLength j, hij]
      _ = 0 + Module.length R (σ.obj j) := by simp
  have hkerSubsingleton :
      Subsingleton (LinearMap.ker f.hom.hom) :=
    Module.length_eq_zero_iff.mp hker
  have hinj : Function.Injective f.hom.hom := by
    intro x y hxy
    have hmem :
        x - y ∈ LinearMap.ker f.hom.hom := by
      change f.hom.hom (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have heq :
        (⟨x - y, hmem⟩ :
          LinearMap.ker f.hom.hom) = 0 :=
      Subsingleton.elim _ _
    exact sub_eq_zero.mp (congrArg Subtype.val heq)
  letI : Mono f :=
    (fg_mono_iff_injective f).mpr hinj
  exact isIso_of_mono_of_epi f

/-- A monomorphism between chosen representatives of equal finite
composition length is an isomorphism. -/
theorem isIso_of_mono_of_compositionLength_eq
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Mono f]
    (hij :
      σ.compositionLength i =
        σ.compositionLength j) :
    IsIso f := by
  have hinj : Function.Injective f.hom.hom :=
    (fg_mono_iff_injective f).mp inferInstance
  let Q := LinearMap.range f.hom.hom
  have hlength :
      Module.length R (σ.obj j) =
        Module.length R (σ.obj i) +
          Module.length R ((σ.obj j) ⧸ Q) :=
    Module.length_eq_add_of_exact
      f.hom.hom Q.mkQ hinj Q.mkQ_surjective
      (LinearMap.exact_map_mkQ_range f.hom.hom)
  have hifinite :
      Module.length R (σ.obj i) ≠ ⊤ :=
    (Module.length_ne_top_iff).2 (σ.finiteLength i)
  have hquot :
      Module.length R ((σ.obj j) ⧸ Q) = 0 := by
    apply WithTop.add_left_cancel hifinite
    calc
      Module.length R (σ.obj i) +
            Module.length R ((σ.obj j) ⧸ Q) =
          Module.length R (σ.obj j) :=
        hlength.symm
      _ = Module.length R (σ.obj i) := by
        rw [← σ.coe_compositionLength i,
          ← σ.coe_compositionLength j, ← hij]
      _ = Module.length R (σ.obj i) + 0 := by simp
  have hquotSubsingleton :
      Subsingleton ((σ.obj j) ⧸ Q) :=
    Module.length_eq_zero_iff.mp hquot
  have hrange : Q = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp
      hquotSubsingleton
  have hsurj : Function.Surjective f.hom.hom :=
    LinearMap.range_eq_top.mp hrange
  letI : Epi f :=
    (fg_epi_iff_surjective f).mpr hsurj
  exact isIso_of_mono_of_epi f

/--
An indecomposable quotient of a length-two chosen representative is either
simple or isomorphic to the original representative.

This theorem concerns one source object.  It is not a replacement for
collective closure under quotients of arbitrary finite direct sums.
-/
theorem simple_or_isIso_of_epi_of_compositionLength_eq_two
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Epi f]
    (hi : σ.compositionLength i = 2) :
    Simple (σ.obj j) ∨ IsIso f := by
  have hsurj : Function.Surjective f.hom.hom :=
    (fg_epi_iff_surjective f).mp inferInstance
  have hleLength :
      Module.length R (σ.obj j) ≤
        Module.length R (σ.obj i) :=
    Module.length_le_of_surjective f.hom.hom hsurj
  have hle :
      σ.compositionLength j ≤
        σ.compositionLength i := by
    apply ENat.coe_le_coe.mp
    rw [σ.coe_compositionLength j,
      σ.coe_compositionLength i]
    exact hleLength
  have hjpos := σ.compositionLength_pos j
  have hj : σ.compositionLength j = 1 ∨
      σ.compositionLength j = 2 := by
    omega
  rcases hj with hj | hj
  · left
    exact
      (σ.compositionLength_eq_one_iff_simple j).mp hj
  · right
    exact σ.isIso_of_epi_of_compositionLength_eq f
      (hi.trans hj.symm)

/--
An indecomposable submodule of a length-two chosen representative is either
simple or isomorphic to the original representative.
-/
theorem simple_or_isIso_of_mono_of_compositionLength_eq_two
    {i j : ι} (f : σ.obj i ⟶ σ.obj j) [Mono f]
    (hj : σ.compositionLength j = 2) :
    Simple (σ.obj i) ∨ IsIso f := by
  have hinj : Function.Injective f.hom.hom :=
    (fg_mono_iff_injective f).mp inferInstance
  have hleLength :
      Module.length R (σ.obj i) ≤
        Module.length R (σ.obj j) :=
    Module.length_le_of_injective f.hom.hom hinj
  have hle :
      σ.compositionLength i ≤
        σ.compositionLength j := by
    apply ENat.coe_le_coe.mp
    rw [σ.coe_compositionLength i,
      σ.coe_compositionLength j]
    exact hleLength
  have hipos := σ.compositionLength_pos i
  have hi : σ.compositionLength i = 1 ∨
      σ.compositionLength i = 2 := by
    omega
  rcases hi with hi | hi
  · left
    exact
      (σ.compositionLength_eq_one_iff_simple i).mp hi
  · right
    exact σ.isIso_of_mono_of_compositionLength_eq f
      (hi.trans hj.symm)

/-! ## Concrete radical, top, and socle -/

/-- The module radical of a chosen representative. -/
def moduleRadical (i : ι) : Submodule R (σ.obj i) :=
  Module.jacobson R (σ.obj i)

/-- The semisimple top of a chosen representative, as an actual quotient
module. -/
abbrev moduleTop (i : ι) :=
  (σ.obj i) ⧸ σ.moduleRadical i

/-- The socle of a chosen representative: the sum of all of its simple
submodules. -/
def moduleSocle (i : ι) : Submodule R (σ.obj i) :=
  sSup {N : Submodule R (σ.obj i) |
    IsSimpleModule R N}

/-- The top of every finite-length representative is semisimple. -/
theorem moduleTop_isSemisimple (i : ι) :
    IsSemisimpleModule R (σ.moduleTop i) := by
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  rw [IsArtinian.isSemisimpleModule_iff_jacobson]
  exact Module.jacobson_quotient_jacobson
    R (σ.obj i)

/-- Every simple submodule is contained in the concrete socle. -/
theorem le_moduleSocle_of_simple
    {i : ι} (N : Submodule R (σ.obj i))
    (hN : IsSimpleModule R N) :
    N ≤ σ.moduleSocle i := by
  exact le_sSup hN

/-- A length-two representative admits a concrete composition series with
simple submodule and simple quotient. -/
structure LengthTwoSeries (i : ι) where
  submodule : Submodule R (σ.obj i)
  ne_bot : submodule ≠ ⊥
  ne_top : submodule ≠ ⊤
  simple_submodule : IsSimpleModule R submodule
  simple_quotient :
    IsSimpleModule R ((σ.obj i) ⧸ submodule)

/-- Construct a simple--simple composition series for a length-two chosen
representative. -/
theorem exists_lengthTwoSeries
    {i : ι} (hi : σ.compositionLength i = 2) :
    Nonempty (σ.LengthTwoSeries i) := by
  letI : Nontrivial (σ.obj i) :=
    (σ.indecomposable i).nontrivial
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  obtain ⟨N, hNatom, -⟩ :=
    (eq_bot_or_exists_atom_le
      (⊤ : Submodule R (σ.obj i))).resolve_left top_ne_bot
  have hNsimple : IsSimpleModule R N :=
    isSimpleModule_iff_isAtom.mpr hNatom
  have hNlength : Module.length R N = 1 :=
    Module.length_eq_one_iff.mpr hNsimple
  have hlength :
      Module.length R (σ.obj i) =
        Module.length R N +
          Module.length R ((σ.obj i) ⧸ N) :=
    Module.length_eq_add_of_exact
      N.subtype N.mkQ N.subtype_injective
      N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hquotLength :
      Module.length R ((σ.obj i) ⧸ N) = 1 := by
    have htotal :
        Module.length R (σ.obj i) = 2 := by
      rw [← σ.coe_compositionLength i, hi]
      norm_num
    rw [htotal, hNlength] at hlength
    apply WithTop.add_left_cancel ENat.one_ne_top
    have htwo : (2 : ℕ∞) = 1 + 1 := by
      change ((2 : ℕ) : ℕ∞) =
        ((1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞)
      rw [← ENat.coe_add]
    exact hlength.symm.trans htwo
  have hquotSimple :
      IsSimpleModule R ((σ.obj i) ⧸ N) :=
    Module.length_eq_one_iff.mp hquotLength
  have hNneTop : N ≠ ⊤ := by
    intro htop
    have hcontra :
        Module.length R N =
          Module.length R (σ.obj i) := by
      rw [htop, Module.length_top]
    rw [hNlength] at hcontra
    have htotal :
        Module.length R (σ.obj i) = 2 := by
      rw [← σ.coe_compositionLength i, hi]
      norm_num
    rw [htotal] at hcontra
    norm_num at hcontra
  exact ⟨{
    submodule := N
    ne_bot := hNatom.ne_bot
    ne_top := hNneTop
    simple_submodule := hNsimple
    simple_quotient := hquotSimple }⟩

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
