import QuotientSubmoduleEquidistribution.RepresentationTheory.BottomTwoModules

/-!
# The simple-top part of the bottom-two-level argument

This file isolates a theorem that does not need Gabriel-quiver
machinery: a finite-length nonsimple module with simple top has an
indecomposable quotient of composition length two.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.BottomTwoSimpleTop

universe u v w

variable {R : Type u} [Ring R]

/--
A length-two module with nonzero module radical is indecomposable.

The proof is elementary: a nontrivial direct-sum decomposition would have two
simple summands, so both summands would be maximal submodules; their
intersection would force the module radical to vanish.
-/
theorem isIndecomposableModule_of_length_eq_two_of_jacobson_ne_bot
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlen : Module.length R M = 2)
    (hrad : Module.jacobson R M ≠ ⊥) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  have hMnontrivial : Nontrivial M := by
    apply (Module.length_pos_iff (R := R) (M := M)).mp
    rw [hlen]
    norm_num
  letI : Nontrivial M := hMnontrivial
  refine QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
    (A := R) (M := M) fun P Q hPQ ↦ ?_
  by_contra h
  push Not at h
  obtain ⟨hP, hQ⟩ := h
  have hPnontrivial : Nontrivial P := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hP
  have hQnontrivial : Nontrivial Q := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hQ
  have hlenExact :
      Module.length R M =
        Module.length R P +
          Module.length R (M ⧸ P) :=
    Module.length_eq_add_of_exact
      P.subtype P.mkQ P.subtype_injective
      P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
  have hquotLength :
      Module.length R (M ⧸ P) =
        Module.length R Q :=
    LinearEquiv.length_eq
      (P.quotientEquivOfIsCompl Q hPQ)
  have hsum :
      Module.length R P + Module.length R Q = 2 := by
    rw [← hquotLength, ← hlenExact, hlen]
  have hPpos : 0 < Module.length R P :=
    Module.length_pos_iff.mpr hPnontrivial
  have hQpos : 0 < Module.length R Q :=
    Module.length_pos_iff.mpr hQnontrivial
  have hPone : Module.length R P = 1 := by
    apply le_antisymm
    · apply ENat.lt_two_iff.mp
      apply (ENat.add_one_le_coe_iff
        (m := Module.length R P) (n := 2)).mp
      calc
        Module.length R P + 1 ≤
            Module.length R P + Module.length R Q :=
          add_le_add_right
            (Order.one_le_iff_ne_zero.mpr hQpos.ne')
            (Module.length R P)
        _ = 2 := hsum
    · exact Order.one_le_iff_ne_zero.mpr hPpos.ne'
  have hQone : Module.length R Q = 1 := by
    apply le_antisymm
    · apply ENat.lt_two_iff.mp
      apply (ENat.add_one_le_coe_iff
        (m := Module.length R Q) (n := 2)).mp
      calc
        Module.length R Q + 1 ≤
            Module.length R Q + Module.length R P :=
          add_le_add_right
            (Order.one_le_iff_ne_zero.mpr hPpos.ne')
            (Module.length R Q)
        _ = 2 := by simpa [add_comm] using hsum
    · exact Order.one_le_iff_ne_zero.mpr hQpos.ne'
  have hPsimple : IsSimpleModule R P :=
    Module.length_eq_one_iff.mp hPone
  have hQsimple : IsSimpleModule R Q :=
    Module.length_eq_one_iff.mp hQone
  letI : IsSimpleModule R P := hPsimple
  letI : IsSimpleModule R Q := hQsimple
  have hPquotSimple : IsSimpleModule R (M ⧸ P) :=
    IsSimpleModule.congr
      (P.quotientEquivOfIsCompl Q hPQ)
  have hQquotSimple : IsSimpleModule R (M ⧸ Q) :=
    IsSimpleModule.congr
      (Q.quotientEquivOfIsCompl P hPQ.symm)
  have hPcoatom : IsCoatom P :=
    isSimpleModule_iff_isCoatom.mp hPquotSimple
  have hQcoatom : IsCoatom Q :=
    isSimpleModule_iff_isCoatom.mp hQquotSimple
  have hradP : Module.jacobson R M ≤ P := by
    exact sInf_le hPcoatom
  have hradQ : Module.jacobson R M ≤ Q := by
    exact sInf_le hQcoatom
  apply hrad
  apply le_antisymm
  · calc
      Module.jacobson R M ≤ P ⊓ Q := le_inf hradP hradQ
      _ = ⊥ := hPQ.disjoint.eq_bot
  · exact bot_le

/--
Conversely, an indecomposable length-two module has nonzero module radical.
-/
theorem jacobson_ne_bot_of_isIndecomposableModule_of_length_eq_two
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsArtinian R M]
    (hindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    (hlen : Module.length R M = 2) :
    Module.jacobson R M ≠ ⊥ := by
  intro hjacobson
  letI : IsSemisimpleModule R M := by
    rw [IsArtinian.isSemisimpleModule_iff_jacobson]
    exact hjacobson
  have hsimple : IsSimpleModule R M :=
    _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
      hindec
  have hlenOne : Module.length R M = 1 :=
    Module.length_eq_one_iff.mpr hsimple
  rw [hlen] at hlenOne
  norm_num at hlenOne

/--
The top of an indecomposable length-two module is simple.
-/
theorem simple_top_of_isIndecomposableModule_of_length_eq_two
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (hindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    (hlen : Module.length R M = 2) :
    IsSimpleModule R
      (M ⧸ Module.jacobson R M) := by
  let J : Submodule R M := Module.jacobson R M
  have hJneBot : J ≠ ⊥ :=
    jacobson_ne_bot_of_isIndecomposableModule_of_length_eq_two
      hindec hlen
  letI : Nontrivial M := hindec.nontrivial
  have hJneTop : J ≠ ⊤ :=
    (Module.jacobson_lt_top R M).ne
  have hquotNontrivial : Nontrivial (M ⧸ J) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    exact hJneTop
      (Submodule.Quotient.subsingleton_iff.mp hsub)
  have hquotPos : 0 < Module.length R (M ⧸ J) :=
    Module.length_pos_iff.mpr hquotNontrivial
  have hquotLt :
      Module.length R (M ⧸ J) < 2 := by
    simpa [J, hlen] using
      (Submodule.length_quotient_lt
        (R := R) (M := M) J hJneBot)
  have hquotOne :
      Module.length R (M ⧸ J) = 1 := by
    apply le_antisymm
    · exact ENat.lt_two_iff.mp hquotLt
    · exact Order.one_le_iff_ne_zero.mpr hquotPos.ne'
  exact Module.length_eq_one_iff.mp hquotOne

/--
A finite-length nonsimple module with simple top has an indecomposable
length-two quotient.  Its kernel can be chosen inside the module radical.
-/
theorem exists_indec_length_two_quotient_of_simple_top
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (htop :
      IsSimpleModule R
        (M ⧸ Module.jacobson R M))
    (hnonsimple : ¬ IsSimpleModule R M) :
    ∃ N : Submodule R M,
      N ≤ Module.jacobson R M ∧
        Module.length R (M ⧸ N) = 2 ∧
          QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (M ⧸ N) := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J := by
    exact isSimpleModule_iff_isCoatom.mp htop
  have hJne : J ≠ ⊥ := by
    intro hJbot
    apply hnonsimple
    rw [isSimpleModule_iff]
    rw [isSimpleOrder_iff_isCoatom_bot]
    simpa [J, hJbot] using hJcoatom
  obtain ⟨N, -, hNJ⟩ :=
    exists_le_covBy_of_lt
      (bot_lt_iff_ne_bot.mpr hJne)
  let Jbar : Submodule R (M ⧸ N) :=
    Submodule.map N.mkQ J
  let e :
      Submodule R (M ⧸ N) ≃o Set.Ici N :=
    Submodule.comapMkQRelIso N
  have hJintervalAtom :
      IsAtom (⟨J, hNJ.le⟩ : Set.Ici N) :=
    (covBy_iff_atom_Ici hNJ.le).mp hNJ
  have hJbarAtom : IsAtom Jbar := by
    change IsAtom (e.symm ⟨J, hNJ.le⟩)
    exact (e.symm.isAtom_iff _).mpr hJintervalAtom
  have hJintervalCoatom :
      IsCoatom (⟨J, hNJ.le⟩ : Set.Ici N) := by
    constructor
    · intro htopEq
      apply hJcoatom.ne_top
      exact congrArg Subtype.val htopEq
    · intro X hJX
      apply Subtype.ext
      exact hJcoatom.2 X hJX
  have hJbarCoatom : IsCoatom Jbar := by
    change IsCoatom (e.symm ⟨J, hNJ.le⟩)
    exact (e.symm.isCoatom_iff _).mpr
      hJintervalCoatom
  have hJbarSimple : IsSimpleModule R Jbar :=
    isSimpleModule_iff_isAtom.mpr hJbarAtom
  have htopBarSimple :
      IsSimpleModule R ((M ⧸ N) ⧸ Jbar) :=
    isSimpleModule_iff_isCoatom.mpr hJbarCoatom
  letI : IsSimpleModule R Jbar := hJbarSimple
  letI : IsSimpleModule R ((M ⧸ N) ⧸ Jbar) :=
    htopBarSimple
  have hlength :
      Module.length R (M ⧸ N) =
        Module.length R Jbar +
          Module.length R ((M ⧸ N) ⧸ Jbar) :=
    Module.length_eq_add_of_exact
      Jbar.subtype Jbar.mkQ Jbar.subtype_injective
      Jbar.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Jbar)
  have hlengthTwo :
      Module.length R (M ⧸ N) = 2 := by
    rw [hlength, Module.length_eq_one R Jbar,
      Module.length_eq_one R ((M ⧸ N) ⧸ Jbar)]
    norm_num
  have hjacobson :
      Module.jacobson R (M ⧸ N) = Jbar := by
    exact Module.jacobson_quotient_of_le hNJ.le
  have hjacobsonNe :
      Module.jacobson R (M ⧸ N) ≠ ⊥ := by
    rw [hjacobson]
    exact hJbarAtom.ne_bot
  exact ⟨N, hNJ.le, hlengthTwo,
    isIndecomposableModule_of_length_eq_two_of_jacobson_ne_bot
      hlengthTwo hjacobsonNe⟩

namespace IndecomposableSkeleton

variable [IsNoetherianRing R]
  {ι : Type v}
  (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, w} R ι)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/--
In a quotient-closed pair whose other member is simple, any
indecomposable length-two quotient of `x` forces `x` itself to have
composition length two.

This separates the collective-closure argument from the remaining
representation-theoretic task of constructing the quotient.
-/
theorem compositionLength_eq_two_of_qClosed_pair_of_epi
    {x s j : ι}
    (hclosed : σ.qClosure.IsClosed ({x, s} : Set ι))
    (hs : Simple (σ.obj s))
    (f : σ.obj x ⟶ σ.obj j) [Epi f]
    (hjLength : σ.compositionLength j = 2) :
    σ.compositionLength x = 2 := by
  have hjClosure :
      j ∈ σ.qClosure ({x, s} : Set ι) := by
    let a : Fin 1 → ι := fun _ ↦ x
    let g :
        σ.sumOver (FintypeCat.of (Fin 1)) a ⟶
          σ.obj j :=
      (biproductUniqueIso fun t : Fin 1 ↦
        σ.obj (a t)).hom ≫ f
    refine ⟨{
      index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ by simp [a]
      map := g
      epi := ?_ }⟩
    dsimp only [g]
    infer_instance
  have hjMem : j ∈ ({x, s} : Set ι) := by
    rw [← hclosed.closure_eq]
    exact hjClosure
  rcases hjMem with hjx | hjs
  · simpa [hjx] using hjLength
  · have hsLength : σ.compositionLength s = 1 :=
      (σ.compositionLength_eq_one_iff_simple s).mpr hs
    rw [hjs, hsLength] at hjLength
    omega

/--
Dual closure reduction: in a submodule-closed pair whose other member is
simple, any indecomposable length-two submodule of `x` forces `x` itself
to have composition length two.
-/
theorem compositionLength_eq_two_of_sClosed_pair_of_mono
    {x s j : ι}
    (hclosed : σ.sClosure.IsClosed ({x, s} : Set ι))
    (hs : Simple (σ.obj s))
    (f : σ.obj j ⟶ σ.obj x) [Mono f]
    (hjLength : σ.compositionLength j = 2) :
    σ.compositionLength x = 2 := by
  have hjClosure :
      j ∈ σ.sClosure ({x, s} : Set ι) := by
    let a : Fin 1 → ι := fun _ ↦ x
    let g :
        σ.obj j ⟶
          σ.sumOver (FintypeCat.of (Fin 1)) a :=
      f ≫
        (biproductUniqueIso fun t : Fin 1 ↦
          σ.obj (a t)).inv
    refine ⟨{
      index := FintypeCat.of (Fin 1)
      label := a
      mem := fun _ ↦ by simp [a]
      map := g
      mono := ?_ }⟩
    dsimp only [g]
    infer_instance
  have hjMem : j ∈ ({x, s} : Set ι) := by
    rw [← hclosed.closure_eq]
    exact hjClosure
  rcases hjMem with hjx | hjs
  · simpa [hjx] using hjLength
  · have hsLength : σ.compositionLength s = 1 :=
      (σ.compositionLength_eq_one_iff_simple s).mpr hs
    rw [hjs, hsLength] at hjLength
    omega

/--
An unconditional reduction for the simple-top branch of a quotient-closed
mixed pair: if the nonsimple member has simple top, then it has composition
length two.

The general mixed-pair argument still needs a way to extract a nonsplit
length-two quotient when the top has higher multiplicity.
-/
theorem compositionLength_eq_two_of_qClosed_pair_of_simple_top
    {x s : ι}
    (hclosed : σ.qClosure.IsClosed ({x, s} : Set ι))
    (hx : ¬ Simple (σ.obj x))
    (hs : Simple (σ.obj s))
    (htop : IsSimpleModule R (σ.moduleTop x)) :
    σ.compositionLength x = 2 := by
  letI : IsArtinian R (σ.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength x)).2
  have hxModule : ¬ IsSimpleModule R (σ.obj x) := by
    simpa only [
      _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg]
      using hx
  obtain ⟨N, -, hlength, hindec⟩ :=
    exists_indec_length_two_quotient_of_simple_top
      (R := R) htop hxModule
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((σ.obj x) ⧸ N)
  obtain ⟨j, ⟨e⟩⟩ :=
    σ.complete Q hindec
  let q : σ.obj x ⟶ Q :=
    FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      N.mkQ_surjective
  let f : σ.obj x ⟶ σ.obj j :=
    q ≫ e.hom
  letI : Epi f := by
    dsimp only [f]
    infer_instance
  have hjLength : σ.compositionLength j = 2 := by
    rw [← ENat.coe_inj]
    rw [σ.coe_compositionLength j]
    calc
      Module.length R (σ.obj j) =
          Module.length R Q :=
        (LinearEquiv.length_eq
          (FGModuleCat.isoToLinearEquiv e)).symm
      _ = 2 := hlength
      _ = (2 : ℕ∞) := rfl
  exact
    compositionLength_eq_two_of_qClosed_pair_of_epi
      σ hclosed hs f hjLength

/--
Every chosen indecomposable representative of composition length two has
simple concrete top.
-/
theorem moduleTop_isSimple_of_compositionLength_eq_two
    {i : ι} (hi : σ.compositionLength i = 2) :
    IsSimpleModule R (σ.moduleTop i) := by
  letI : IsArtinian R (σ.obj i) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (σ.finiteLength i)).2
  have hlength : Module.length R (σ.obj i) = 2 := by
    rw [← σ.coe_compositionLength i, hi]
    norm_num
  exact simple_top_of_isIndecomposableModule_of_length_eq_two
    (σ.indecomposable i) hlength

end IndecomposableSkeleton

end QuotientSubmoduleEquidistribution.BottomTwoSimpleTop
