import QuotientSubmoduleEquidistribution.RepresentationTheory.LengthThreeUniserialCollective
import QuotientSubmoduleEquidistribution.RepresentationTheory.LevelThreeExhaustive
import QuotientSubmoduleEquidistribution.RepresentationTheory.LoewyTwoOneArrowReduction

/-!
# The two-nonsimple long-uniserial reduction

This file reduces the remaining family-four classification problem to simple
top for the long member.  Once simple top is known, quotient closedness and
the no-parallel `Ext¹` theorem force the radical to be indecomposable; the
resulting length-three module is uniserial.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace QuotientSubmoduleEquidistribution.FamilyFourControl

universe u v w

variable {R : Type u} [Ring R]

/-- If the top of a finite-length module is simple, every proper submodule
lies in the module radical. -/
theorem le_jacobson_of_ne_top_of_simple_top
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    {N : Submodule R M} (hN : N ≠ ⊤) :
    N ≤ Module.jacobson R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  obtain ⟨C, hCcoatom, hNC⟩ :=
    (eq_top_or_exists_le_coatom N).resolve_left hN
  have hJC : J ≤ C := sInf_le hCcoatom
  have hJCeq : J = C := by
    by_cases hEq : J = C
    · exact hEq
    have hlt : J < C := lt_of_le_of_ne hJC hEq
    exact (hCcoatom.ne_top (hJcoatom.2 _ hlt)).elim
  change N ≤ J
  rw [hJCeq]
  exact hNC

/-- A finite-length module with simple top is indecomposable. -/
theorem isIndecomposableModule_of_simple_top
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  have hMnontrivial : Nontrivial M := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hJtop : J = ⊤ := by
      apply top_unique
      intro x _
      exact Subsingleton.elim x 0 ▸ J.zero_mem
    exact hJcoatom.ne_top hJtop
  letI : Nontrivial M := hMnontrivial
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isCompl
  intro P Q hPQ
  by_cases hPtop : P = ⊤
  · right
    have hinf := hPQ.inf_eq_bot
    simpa [hPtop] using hinf
  by_cases hQtop : Q = ⊤
  · left
    have hinf := hPQ.inf_eq_bot
    simpa [hQtop] using hinf
  exfalso
  have hPJ : P ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hPtop
  have hQJ : Q ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hQtop
  have htopLe : (⊤ : Submodule R M) ≤ J := by
    rw [← hPQ.sup_eq_top]
    exact sup_le hPJ hQJ
  exact hJcoatom.ne_top (top_unique htopLe)

/-- A surjection from a simple-top module to a simple module identifies the
canonical module top with that simple target. -/
noncomputable def moduleTopLinearEquivOfSurjectiveToSimple
    {M : Type v} [AddCommGroup M] [Module R M]
    {T : Type w} [AddCommGroup T] [Module R T]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hT : IsSimpleModule R T)
    (f : M →ₗ[R] T) (hf : Function.Surjective f) :
    (M ⧸ Module.jacobson R M) ≃ₗ[R] T := by
  let J : Submodule R M := Module.jacobson R M
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  have hkerCoatom : IsCoatom (LinearMap.ker f) := by
    letI : IsSimpleModule R T := hT
    exact LinearMap.isCoatom_ker_of_surjective hf
  have hJker : J ≤ LinearMap.ker f := sInf_le hkerCoatom
  have hkerEq : LinearMap.ker f = J :=
    (hJcoatom.le_iff_eq hkerCoatom.ne_top).mp hJker
  exact
    (Submodule.quotEquivOfEq J (LinearMap.ker f) hkerEq.symm).trans
      (f.quotKerEquivOfSurjective hf)

/-- If a finite-length module with simple top has length greater than three,
it has an indecomposable quotient of length exactly three.  The kernel is
chosen two cover steps below the radical. -/
theorem exists_indec_length_three_quotient_of_simple_top
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hlong : 3 < Module.length R M) :
    ∃ N : Submodule R M,
      N ≤ Module.jacobson R M ∧
        Module.length R (M ⧸ N) = 3 ∧
          QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (M ⧸ N) := by
  let J : Submodule R M := Module.jacobson R M
  have htopLength : Module.length R (M ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hlengthM :
      Module.length R M =
        Module.length R J + Module.length R (M ⧸ J) :=
    Module.length_eq_add_of_exact
      J.subtype J.mkQ J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  have hJne : J ≠ ⊥ := by
    intro hJbot
    have hMone : Module.length R M = 1 := by
      rw [hlengthM, htopLength, hJbot]
      simp
    rw [hMone] at hlong
    norm_num at hlong
  obtain ⟨P, -, hPJ⟩ :=
    exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr hJne)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hJatom : IsAtom J := by
      subst P
      exact hPJ.is_atom
    have hJsimple : IsSimpleModule R J :=
      isSimpleModule_iff_isAtom.mpr hJatom
    have hJlength : Module.length R J = 1 :=
      Module.length_eq_one_iff.mpr hJsimple
    have hMtwo : Module.length R M = 2 := by
      rw [hlengthM, hJlength, htopLength]
      norm_num
    rw [hMtwo] at hlong
    norm_num at hlong
  obtain ⟨N, -, hNP⟩ :=
    exists_le_covBy_of_lt (bot_lt_iff_ne_bot.mpr hPne)
  have hNJ : N ≤ J := hNP.le.trans hPJ.le
  let intervalEquiv :
      Submodule R (M ⧸ N) ≃o Set.Ici N :=
    Submodule.comapMkQRelIso N
  let Pbar : Submodule R (M ⧸ N) :=
    Submodule.map N.mkQ P
  let Jbar : Submodule R (M ⧸ N) :=
    Submodule.map N.mkQ J
  have hPintervalAtom :
      IsAtom (⟨P, hNP.le⟩ : Set.Ici N) :=
    (covBy_iff_atom_Ici hNP.le).mp hNP
  have hPbarAtom : IsAtom Pbar := by
    change IsAtom (intervalEquiv.symm ⟨P, hNP.le⟩)
    exact
      (intervalEquiv.symm.isAtom_iff _).mpr hPintervalAtom
  have hPbarSimple : IsSimpleModule R Pbar :=
    isSimpleModule_iff_isAtom.mpr hPbarAtom
  have hPbarJbar : Pbar ⋖ Jbar := by
    change
      intervalEquiv.symm ⟨P, hNP.le⟩ ⋖
        intervalEquiv.symm ⟨J, hNJ⟩
    rw [apply_covBy_apply_iff]
    constructor
    · exact hPJ.lt
    · intro C hPC hCJ
      exact hPJ.2 hPC hCJ
  let Pinside : Submodule R Jbar :=
    Submodule.comap Jbar.subtype Pbar
  have hPinsideSimple : IsSimpleModule R Pinside := by
    exact IsSimpleModule.congr
      (Submodule.comapSubtypeEquivOfLe hPbarJbar.le)
  have hJbarQuotSimple :
      IsSimpleModule R (Jbar ⧸ Pinside) :=
    (covBy_iff_quot_is_simple hPbarJbar.le).mp hPbarJbar
  have hJbarLength : Module.length R Jbar = 2 := by
    have hlength := Module.length_eq_add_of_exact
      (R := R) (M := Jbar) (N := Pinside)
      (P := Jbar ⧸ Pinside)
      (Pinside.subtype : Pinside →ₗ[R] Jbar) Pinside.mkQ
      Pinside.subtype_injective Pinside.mkQ_surjective
      (LinearMap.exact_subtype_mkQ Pinside)
    rw [hlength,
      Module.length_eq_one_iff.mpr hPinsideSimple,
      Module.length_eq_one_iff.mpr hJbarQuotSimple]
    norm_num
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  have hJintervalCoatom :
      IsCoatom (⟨J, hNJ⟩ : Set.Ici N) := by
    constructor
    · intro htopEq
      apply hJcoatom.ne_top
      exact congrArg Subtype.val htopEq
    · intro X hJX
      apply Subtype.ext
      exact hJcoatom.2 X hJX
  have hJbarCoatom : IsCoatom Jbar := by
    change IsCoatom (intervalEquiv.symm ⟨J, hNJ⟩)
    exact
      (intervalEquiv.symm.isCoatom_iff _).mpr hJintervalCoatom
  have hquotTopSimple :
      IsSimpleModule R ((M ⧸ N) ⧸ Jbar) :=
    isSimpleModule_iff_isCoatom.mpr hJbarCoatom
  have hquotLength : Module.length R (M ⧸ N) = 3 := by
    rw [Module.length_eq_add_of_exact
      Jbar.subtype Jbar.mkQ Jbar.subtype_injective
      Jbar.mkQ_surjective (LinearMap.exact_subtype_mkQ Jbar),
      hJbarLength,
      Module.length_eq_one_iff.mpr hquotTopSimple]
    norm_num
  have hjacobson : Module.jacobson R (M ⧸ N) = Jbar :=
    Module.jacobson_quotient_of_le hNJ
  have hactualTop :
      IsSimpleModule R
        ((M ⧸ N) ⧸ Module.jacobson R (M ⧸ N)) := by
    rw [hjacobson]
    exact hquotTopSimple
  exact ⟨N, hNJ, hquotLength,
    isIndecomposableModule_of_simple_top hactualTop⟩

/-- A length-three module with simple top has a radical of length two. -/
theorem jacobson_length_eq_two_of_length_eq_three_of_simple_top
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlength : Module.length R M = 3)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M)) :
    Module.length R (Module.jacobson R M) = 2 := by
  let J : Submodule R M := Module.jacobson R M
  have htopLength : Module.length R (M ⧸ J) = 1 :=
    Module.length_eq_one_iff.mpr htop
  have hlengthExact :
      Module.length R M =
        Module.length R J + Module.length R (M ⧸ J) :=
    Module.length_eq_add_of_exact
      J.subtype J.mkQ J.subtype_injective J.mkQ_surjective
      (LinearMap.exact_subtype_mkQ J)
  rw [hlength, htopLength] at hlengthExact
  apply WithTop.add_right_cancel ENat.one_ne_top
  calc
    Module.length R J + 1 = 3 := hlengthExact.symm
    _ = 2 + 1 := by norm_num

/-- A length-two indecomposable module is uniserial. -/
theorem isUniserialModule_of_isIndecomposable_of_length_eq_two
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (hindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R M)
    (hlength : Module.length R M = 2) :
    IsUniserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have htop : IsSimpleModule R (M ⧸ J) :=
    QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.simple_top_of_isIndecomposableModule_of_length_eq_two
      hindec hlength
  have hJne : J ≠ ⊥ :=
    QuotientSubmoduleEquidistribution.BottomTwoSimpleTop.jacobson_ne_bot_of_isIndecomposableModule_of_length_eq_two
      hindec hlength
  have hJlength : Module.length R J = 1 := by
    have htopLength : Module.length R (M ⧸ J) = 1 :=
      Module.length_eq_one_iff.mpr htop
    have hlengthExact :
        Module.length R M =
          Module.length R J + Module.length R (M ⧸ J) :=
      Module.length_eq_add_of_exact
        J.subtype J.mkQ J.subtype_injective J.mkQ_surjective
        (LinearMap.exact_subtype_mkQ J)
    rw [hlength, htopLength] at hlengthExact
    apply WithTop.add_right_cancel ENat.one_ne_top
    calc
      Module.length R J + 1 = 2 := hlengthExact.symm
      _ = 1 + 1 := by norm_num
  have hJsimple : IsSimpleModule R J :=
    Module.length_eq_one_iff.mp hJlength
  have hJatom : IsAtom J :=
    isSimpleModule_iff_isAtom.mp hJsimple
  unfold IsUniserialModule
  constructor
  intro P Q
  by_cases hPtop : P = ⊤
  · right
    simp [hPtop]
  by_cases hQtop : Q = ⊤
  · left
    simp [hQtop]
  have hPJ : P ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hPtop
  have hQJ : Q ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hQtop
  rcases hJatom.le_iff.mp hPJ with hPbot | hPeq
  · left
    simp [hPbot]
  rcases hJatom.le_iff.mp hQJ with hQbot | hQeq
  · right
    simp [hQbot]
  · left
    simp [hPeq, hQeq]

/-- A length-three module is uniserial once both its top and its radical
have the expected indecomposability. -/
theorem isUniserialModule_of_length_eq_three_of_simple_top_of_radical_indec
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (hlength : Module.length R M = 3)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (hradIndec :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (Module.jacobson R M)) :
    IsUniserialModule R M := by
  let J : Submodule R M := Module.jacobson R M
  have hJlength : Module.length R J = 2 :=
    jacobson_length_eq_two_of_length_eq_three_of_simple_top
      hlength htop
  have hJuniserial : IsUniserialModule R J :=
    isUniserialModule_of_isIndecomposable_of_length_eq_two
      hradIndec hJlength
  unfold IsUniserialModule at hJuniserial ⊢
  constructor
  intro P Q
  by_cases hPtop : P = ⊤
  · right
    simp [hPtop]
  by_cases hQtop : Q = ⊤
  · left
    simp [hQtop]
  have hPJ : P ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hPtop
  have hQJ : Q ≤ J :=
    le_jacobson_of_ne_top_of_simple_top htop hQtop
  let P' : Submodule R J := Submodule.comap J.subtype P
  let Q' : Submodule R J := Submodule.comap J.subtype Q
  have hPmap : Submodule.map J.subtype P' = P := by
    dsimp only [P']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPJ]
  have hQmap : Submodule.map J.subtype Q' = Q := by
    dsimp only [Q']
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hQJ]
  rcases hJuniserial.total P' Q' with hPQ | hQP
  · left
    rw [← hPmap, ← hQmap]
    exact Submodule.map_mono hPQ
  · right
    rw [← hPmap, ← hQmap]
    exact Submodule.map_mono hQP

/-- In a length-two module, both nonzero summands in a direct-sum
decomposition are simple. -/
theorem simple_summands_of_isCompl_of_length_eq_two
    {M : Type v} [AddCommGroup M] [Module R M]
    (hlength : Module.length R M = 2)
    {P Q : Submodule R M} (hPQ : IsCompl P Q)
    (hPne : P ≠ ⊥) (hQne : Q ≠ ⊥) :
    IsSimpleModule R P ∧ IsSimpleModule R Q := by
  have hPnontrivial : Nontrivial P := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hPne
  have hQnontrivial : Nontrivial Q := by
    rw [Submodule.nontrivial_iff_ne_bot]
    exact hQne
  have hlengthExact :
      Module.length R M =
        Module.length R P + Module.length R (M ⧸ P) :=
    Module.length_eq_add_of_exact
      P.subtype P.mkQ P.subtype_injective P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
  have hquotLength :
      Module.length R (M ⧸ P) = Module.length R Q :=
    LinearEquiv.length_eq (P.quotientEquivOfIsCompl Q hPQ)
  have hsum : Module.length R P + Module.length R Q = 2 := by
    rw [← hquotLength, ← hlengthExact, hlength]
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
            (Order.one_le_iff_ne_zero.mpr hQpos.ne') _
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
            (Order.one_le_iff_ne_zero.mpr hPpos.ne') _
        _ = 2 := by simpa [add_comm] using hsum
    · exact Order.one_le_iff_ne_zero.mpr hQpos.ne'
  exact ⟨Module.length_eq_one_iff.mp hPone,
    Module.length_eq_one_iff.mp hQone⟩

/-- Quotienting a length-three simple-top module by a simple submodule of
its radical gives an indecomposable length-two module. -/
theorem simple_radical_submodule_quotient
    {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherian R M] [IsArtinian R M]
    (hlength : Module.length R M = 3)
    (htop : IsSimpleModule R (M ⧸ Module.jacobson R M))
    (P : Submodule R M) (hP : IsSimpleModule R P)
    (hPJ : P ≤ Module.jacobson R M) :
    Module.length R (M ⧸ P) = 2 ∧
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (M ⧸ P) := by
  let J : Submodule R M := Module.jacobson R M
  have hPlength : Module.length R P = 1 :=
    Module.length_eq_one_iff.mpr hP
  have hlengthExact :
      Module.length R M =
        Module.length R P + Module.length R (M ⧸ P) :=
    Module.length_eq_add_of_exact
      P.subtype P.mkQ P.subtype_injective P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)
  have hquotLength : Module.length R (M ⧸ P) = 2 := by
    rw [hlength, hPlength] at hlengthExact
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R (M ⧸ P) = 3 := hlengthExact.symm
      _ = 1 + 2 := by norm_num
  let intervalEquiv :
      Submodule R (M ⧸ P) ≃o Set.Ici P :=
    Submodule.comapMkQRelIso P
  let Jbar : Submodule R (M ⧸ P) :=
    Submodule.map P.mkQ J
  have hJcoatom : IsCoatom J :=
    isSimpleModule_iff_isCoatom.mp htop
  have hJintervalCoatom :
      IsCoatom (⟨J, hPJ⟩ : Set.Ici P) := by
    constructor
    · intro htopEq
      apply hJcoatom.ne_top
      exact congrArg Subtype.val htopEq
    · intro X hJX
      apply Subtype.ext
      exact hJcoatom.2 X hJX
  have hJbarCoatom : IsCoatom Jbar := by
    change IsCoatom (intervalEquiv.symm ⟨J, hPJ⟩)
    exact
      (intervalEquiv.symm.isCoatom_iff _).mpr hJintervalCoatom
  have hquotTopAtJ :
      IsSimpleModule R ((M ⧸ P) ⧸ Jbar) :=
    isSimpleModule_iff_isCoatom.mpr hJbarCoatom
  have hjacobson : Module.jacobson R (M ⧸ P) = Jbar :=
    Module.jacobson_quotient_of_le hPJ
  have hquotTop :
      IsSimpleModule R
        ((M ⧸ P) ⧸ Module.jacobson R (M ⧸ P)) := by
    rw [hjacobson]
    exact hquotTopAtJ
  exact ⟨hquotLength,
    isIndecomposableModule_of_simple_top hquotTop⟩

/-- Any two simple submodules of an indecomposable length-two module are
linearly equivalent. -/
noncomputable def simpleSubmodulesLinearEquiv_of_indec_length_two
    {Y : Type v} [AddCommGroup Y] [Module R Y]
    {P : Type w} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hYindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R Y)
    (hYlength : Module.length R Y = 2)
    (hPsimple : IsSimpleModule R P)
    (hQsimple : IsSimpleModule R Q)
    (f : P →ₗ[R] Y) (hf : Function.Injective f)
    (g : Q →ₗ[R] Y) (hg : Function.Injective g) :
    P ≃ₗ[R] Q := by
  let A : Submodule R Y := LinearMap.range f
  let B : Submodule R Y := LinearMap.range g
  let eA : P ≃ₗ[R] A := LinearEquiv.ofInjective f hf
  let eB : Q ≃ₗ[R] B := LinearEquiv.ofInjective g hg
  have hAsimple : IsSimpleModule R A := by
    letI : IsSimpleModule R P := hPsimple
    exact IsSimpleModule.congr eA.symm
  have hBsimple : IsSimpleModule R B := by
    letI : IsSimpleModule R Q := hQsimple
    exact IsSimpleModule.congr eB.symm
  have hAatom : IsAtom A := isSimpleModule_iff_isAtom.mp hAsimple
  have hBatom : IsAtom B := isSimpleModule_iff_isAtom.mp hBsimple
  have hAlength : Module.length R A = 1 :=
    Module.length_eq_one_iff.mpr hAsimple
  have hlengthExact :
      Module.length R Y =
        Module.length R A + Module.length R (Y ⧸ A) :=
    Module.length_eq_add_of_exact
      A.subtype A.mkQ A.subtype_injective A.mkQ_surjective
      (LinearMap.exact_subtype_mkQ A)
  have hquotLength : Module.length R (Y ⧸ A) = 1 := by
    rw [hYlength, hAlength] at hlengthExact
    apply WithTop.add_left_cancel ENat.one_ne_top
    calc
      1 + Module.length R (Y ⧸ A) = 2 := hlengthExact.symm
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
    have hsup : A ⊔ B = ⊤ := hAcoatom.2 _ hAltSup
    have hinf : A ⊓ B = ⊥ := by
      rcases hAatom.le_iff.mp inf_le_left with hbot | hEq
      · exact hbot
      · exfalso
        have hAleB : A ≤ B := by
          calc
            A = A ⊓ B := hEq.symm
            _ ≤ B := inf_le_right
        rcases hBatom.le_iff.mp hAleB with hAbot | hAB'
        · exact hAatom.ne_bot hAbot
        · exact hne hAB'
    have hcompl : IsCompl A B := IsCompl.of_eq hinf hsup
    rcases hYindec.eq_bot_or_eq_bot hcompl with hAbot | hBbot
    · exact hAatom.ne_bot hAbot
    · exact hBatom.ne_bot hBbot
  exact eA.trans ((LinearEquiv.ofEq A B hAB).trans eB.symm)

namespace IndecomposableSkeleton

variable [IsNoetherianRing R]
  {iota : Type v}
  (sigma :
    _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, w} R iota)

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- A concrete repeated-target fork extracted from a decomposable radical:
two quotient maps onto the same length-two representative have complementary
simple kernels inside the source radical. -/
structure RepeatedRadicalFork (x y : iota) where
  leftKernel : Submodule R (sigma.moduleRadical x)
  rightKernel : Submodule R (sigma.moduleRadical x)
  complementary : IsCompl leftKernel rightKernel
  leftKernel_ne : leftKernel ≠ ⊥
  rightKernel_ne : rightKernel ≠ ⊥
  leftKernel_simple : IsSimpleModule R leftKernel
  rightKernel_simple : IsSimpleModule R rightKernel
  kernels_equiv : leftKernel ≃ₗ[R] rightKernel
  leftMap : sigma.obj x ⟶ sigma.obj y
  rightMap : sigma.obj x ⟶ sigma.obj y
  left_epi : Epi leftMap
  right_epi : Epi rightMap
  ker_leftMap :
    LinearMap.ker leftMap.hom.hom =
      Submodule.map (sigma.moduleRadical x).subtype leftKernel
  ker_rightMap :
    LinearMap.ker rightMap.hom.hom =
      Submodule.map (sigma.moduleRadical x).subtype rightKernel

/-- If the radical in a simple-top length-three member of the closed triple
is decomposable, closedness turns the split radical into a repeated-target
fork over the unique length-two member.  This is the precise configuration
that a filtered no-parallel-Ext argument still has to exclude. -/
theorem exists_repeatedRadicalFork_of_not_radical_indec
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (hxLength : sigma.compositionLength x = 3)
    (hyLength : sigma.compositionLength y = 2)
    (hss : Simple (sigma.obj s))
    (htop : IsSimpleModule R (sigma.moduleTop x))
    (hradNotIndec :
      ¬ QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (sigma.moduleRadical x)) :
    Nonempty (RepeatedRadicalFork sigma x y) := by
  let J : Submodule R (sigma.obj x) := sigma.moduleRadical x
  letI : IsNoetherian R (sigma.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength x)).1
  letI : IsArtinian R (sigma.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength x)).2
  have hxModuleLength : Module.length R (sigma.obj x) = 3 := by
    rw [← sigma.coe_compositionLength x, hxLength]
    norm_num
  have hJlength : Module.length R J = 2 :=
    jacobson_length_eq_two_of_length_eq_three_of_simple_top
      hxModuleLength htop
  have hJnontrivial : Nontrivial J :=
    Module.length_pos_iff.mp (by rw [hJlength]; norm_num)
  have hnotAll :
      ¬ ∀ P Q : Submodule R J,
        IsCompl P Q → P = ⊥ ∨ Q = ⊥ := by
    intro hall
    exact hradNotIndec ⟨hJnontrivial, hall⟩
  push Not at hnotAll
  obtain ⟨P, Q, hPQ, hPne, hQne⟩ := hnotAll
  have hsummands :=
    simple_summands_of_isCompl_of_length_eq_two
      hJlength hPQ hPne hQne
  let P0 : Submodule R (sigma.obj x) :=
    Submodule.map J.subtype P
  let Q0 : Submodule R (sigma.obj x) :=
    Submodule.map J.subtype Q
  have hP0simple : IsSimpleModule R P0 := by
    letI : IsSimpleModule R P := hsummands.1
    exact IsSimpleModule.congr (J.equivSubtypeMap P).symm
  have hQ0simple : IsSimpleModule R Q0 := by
    letI : IsSimpleModule R Q := hsummands.2
    exact IsSimpleModule.congr (J.equivSubtypeMap Q).symm
  have hP0J : P0 ≤ J := Submodule.map_subtype_le J P
  have hQ0J : Q0 ≤ J := Submodule.map_subtype_le J Q
  have hxmem : x ∈ S := by
    rw [hS]
    simp
  have quotient_to_y
      (K : Submodule R (sigma.obj x))
      (hKsimple : IsSimpleModule R K)
      (hKJ : K ≤ J) :
      ∃ f : sigma.obj x ⟶ sigma.obj y,
        Epi f ∧ LinearMap.ker f.hom.hom = K := by
    obtain ⟨hquotLength, hquotIndec⟩ :=
      simple_radical_submodule_quotient
        hxModuleLength htop K hKsimple hKJ
    let T : FGModuleCat.{w} R :=
      FGModuleCat.of R ((sigma.obj x) ⧸ K)
    obtain ⟨j, ⟨e⟩⟩ := sigma.complete T hquotIndec
    let q : sigma.obj x ⟶ T := FGModuleCat.ofHom K.mkQ
    letI : Epi q :=
      (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
        K.mkQ_surjective
    let f : sigma.obj x ⟶ sigma.obj j := q ≫ e.hom
    letI : Epi f := by
      dsimp only [f]
      infer_instance
    have hjLength : sigma.compositionLength j = 2 := by
      rw [← ENat.coe_inj, sigma.coe_compositionLength]
      calc
        Module.length R (sigma.obj j) = Module.length R T :=
          (LinearEquiv.length_eq
            (FGModuleCat.isoToLinearEquiv e)).symm
        _ = 2 := hquotLength
        _ = (2 : ℕ∞) := rfl
    have hjmem : j ∈ S :=
      sigma.mem_of_epi_of_mem_of_qClosure_isClosed hclosed hxmem f
    have hjy : j = y := by
      rw [hS] at hjmem
      rcases (by simpa using hjmem) with hjx | hjy | hjs
      · subst j
        omega
      · exact hjy
      · subst j
        have hsLength : sigma.compositionLength s = 1 :=
          (sigma.compositionLength_eq_one_iff_simple s).mpr hss
        omega
    subst j
    refine ⟨f, inferInstance, ?_⟩
    ext z
    constructor
    · intro hz
      have hfz : f.hom.hom z = 0 := LinearMap.mem_ker.mp hz
      have hqz' : q.hom.hom z = 0 := by
        apply (FGModuleCat.isoToLinearEquiv e).injective
        change e.hom.hom.hom (q.hom.hom z) = e.hom.hom.hom 0
        simpa [f] using hfz
      have hqz : K.mkQ z = 0 := by
        exact hqz'
      exact (Submodule.Quotient.mk_eq_zero K).mp hqz
    · intro hz
      apply LinearMap.mem_ker.mpr
      have hqz : K.mkQ z = 0 :=
        (Submodule.Quotient.mk_eq_zero K).mpr hz
      change e.hom.hom.hom (K.mkQ z) = 0
      rw [hqz]
      simp
  obtain ⟨fP, hfPEpi, hfPKer⟩ :=
    quotient_to_y P0 hP0simple hP0J
  obtain ⟨fQ, hfQEpi, hfQKer⟩ :=
    quotient_to_y Q0 hQ0simple hQ0J
  let gP : P →ₗ[R] sigma.obj y :=
    (fQ.hom.hom.comp J.subtype).comp P.subtype
  let gQ : Q →ₗ[R] sigma.obj y :=
    (fP.hom.hom.comp J.subtype).comp Q.subtype
  have hgP : Function.Injective gP := by
    intro a b hab
    have hdker :
        J.subtype (P.subtype (a - b)) ∈
          LinearMap.ker fQ.hom.hom := by
      apply LinearMap.mem_ker.mpr
      have hab' : gP (a - b) = 0 := by
        simp [map_sub, hab]
      exact hab'
    rw [hfQKer] at hdker
    change
      J.subtype (P.subtype (a - b)) ∈
        Submodule.map J.subtype Q at hdker
    obtain ⟨q, hq, hqeq⟩ := hdker
    have hinsideEq : (P.subtype (a - b) : J) = q :=
      J.subtype_injective hqeq.symm
    have hdiffQ : (P.subtype (a - b) : J) ∈ Q := by
      rw [hinsideEq]
      exact hq
    have hdiffInf :
        (P.subtype (a - b) : J) ∈ P ⊓ Q :=
      ⟨(a - b).2, hdiffQ⟩
    rw [hPQ.inf_eq_bot] at hdiffInf
    have hdiffZero : a - b = 0 := by
      apply Subtype.ext
      exact hdiffInf
    exact sub_eq_zero.mp hdiffZero
  have hgQ : Function.Injective gQ := by
    intro a b hab
    have hdker :
        J.subtype (Q.subtype (a - b)) ∈
          LinearMap.ker fP.hom.hom := by
      apply LinearMap.mem_ker.mpr
      have hab' : gQ (a - b) = 0 := by
        simp [map_sub, hab]
      exact hab'
    rw [hfPKer] at hdker
    change
      J.subtype (Q.subtype (a - b)) ∈
        Submodule.map J.subtype P at hdker
    obtain ⟨p, hp, hpeq⟩ := hdker
    have hinsideEq : (Q.subtype (a - b) : J) = p :=
      J.subtype_injective hpeq.symm
    have hdiffP : (Q.subtype (a - b) : J) ∈ P := by
      rw [hinsideEq]
      exact hp
    have hdiffInf :
        (Q.subtype (a - b) : J) ∈ P ⊓ Q :=
      ⟨hdiffP, (a - b).2⟩
    rw [hPQ.inf_eq_bot] at hdiffInf
    have hdiffZero : a - b = 0 := by
      apply Subtype.ext
      exact hdiffInf
    exact sub_eq_zero.mp hdiffZero
  have hyModuleLength : Module.length R (sigma.obj y) = 2 := by
    rw [← sigma.coe_compositionLength y, hyLength]
    norm_num
  let ePQ : P ≃ₗ[R] Q :=
    simpleSubmodulesLinearEquiv_of_indec_length_two
      (sigma.indecomposable y) hyModuleLength
      hsummands.1 hsummands.2 gP hgP gQ hgQ
  exact ⟨{
    leftKernel := P
    rightKernel := Q
    complementary := hPQ
    leftKernel_ne := hPne
    rightKernel_ne := hQne
    leftKernel_simple := hsummands.1
    rightKernel_simple := hsummands.2
    kernels_equiv := ePQ
    leftMap := fP
    rightMap := fQ
    left_epi := hfPEpi
    right_epi := hfQEpi
    ker_leftMap := hfPKer
    ker_rightMap := hfQKer }⟩

/-- In the two-nonsimple closed triple, simple top already forces every
member not of length two to have length exactly three.  The proof constructs
a genuine indecomposable length-three quotient if the source were longer. -/
theorem compositionLength_eq_three_of_simple_top_of_twoNonsimple
    (hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        sigma)
    {S : Set iota} (hclosed : sigma.qClosure.IsClosed S)
    {x y s : iota} (hS : S = {x, y, s})
    (hxn : ¬ Simple (sigma.obj x))
    (hyn : ¬ Simple (sigma.obj y))
    (hss : Simple (sigma.obj s))
    (hxNotTwo : sigma.compositionLength x ≠ 2)
    (htop : IsSimpleModule R (sigma.moduleTop x)) :
    sigma.compositionLength x = 3 := by
  have hyLength : sigma.compositionLength y = 2 :=
    (sigma.length_two_left_or_right_of_twoNonsimple
      hclassification hclosed hS hxn hyn hss).resolve_left hxNotTwo
  by_contra hxNotThree
  have hxNotOne : sigma.compositionLength x ≠ 1 := by
    intro hxOne
    exact hxn ((sigma.compositionLength_eq_one_iff_simple x).mp hxOne)
  have hxLongNat : 4 ≤ sigma.compositionLength x := by
    have hxPos := sigma.compositionLength_pos x
    omega
  have hxLong : 3 < Module.length R (sigma.obj x) := by
    rw [← sigma.coe_compositionLength x]
    exact_mod_cast hxLongNat
  letI : IsNoetherian R (sigma.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength x)).1
  letI : IsArtinian R (sigma.obj x) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength x)).2
  obtain ⟨N, -, hquotLength, hquotIndec⟩ :=
    exists_indec_length_three_quotient_of_simple_top htop hxLong
  let Q : FGModuleCat.{w} R :=
    FGModuleCat.of R ((sigma.obj x) ⧸ N)
  obtain ⟨j, ⟨e⟩⟩ := sigma.complete Q hquotIndec
  let q : sigma.obj x ⟶ Q := FGModuleCat.ofHom N.mkQ
  letI : Epi q :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective q).mpr
      N.mkQ_surjective
  let f : sigma.obj x ⟶ sigma.obj j := q ≫ e.hom
  letI : Epi f := by
    dsimp only [f]
    infer_instance
  have hjLength : sigma.compositionLength j = 3 := by
    rw [← ENat.coe_inj, sigma.coe_compositionLength]
    calc
      Module.length R (sigma.obj j) = Module.length R Q :=
        (LinearEquiv.length_eq
          (FGModuleCat.isoToLinearEquiv e)).symm
      _ = 3 := hquotLength
      _ = (3 : ℕ∞) := rfl
  have hxmem : x ∈ S := by
    rw [hS]
    simp
  have hjmem : j ∈ S :=
    sigma.mem_of_epi_of_mem_of_qClosure_isClosed hclosed hxmem f
  rw [hS] at hjmem
  rcases (by simpa using hjmem) with hjx | hjy | hjs
  · exact hxNotThree (by simpa [hjx] using hjLength)
  · have : sigma.compositionLength y = 3 := by
      simpa [hjy] using hjLength
    omega
  · have hsLength : sigma.compositionLength s = 1 :=
      (sigma.compositionLength_eq_one_iff_simple s).mpr hss
    have : sigma.compositionLength s = 3 := by
      simpa [hjs] using hjLength
    omega

/-- The sole remaining filtered structure after the length and radical
reductions: every long member has simple top. -/
def TwoNonsimpleLongSimpleTopControl : Prop :=
  ∀ {S : Set iota}, S.ncard = 3 → sigma.qClosure.IsClosed S →
    ∀ {x y s : iota},
      x ≠ y → x ≠ s → y ≠ s →
      S = {x, y, s} →
      ¬ Simple (sigma.obj x) → ¬ Simple (sigma.obj y) →
      Simple (sigma.obj s) →
      (sigma.compositionLength x ≠ 2 →
        IsSimpleModule R (sigma.moduleTop x)) ∧
      (sigma.compositionLength y ≠ 2 →
        IsSimpleModule R (sigma.moduleTop y))

/-- The remaining filtered structure, separated from the already-proved
length and lattice argument: a long member has simple top and indecomposable
radical. -/
def TwoNonsimpleLongTopRadicalControl : Prop :=
  ∀ {S : Set iota}, S.ncard = 3 → sigma.qClosure.IsClosed S →
    ∀ {x y s : iota},
      x ≠ y → x ≠ s → y ≠ s →
      S = {x, y, s} →
      ¬ Simple (sigma.obj x) → ¬ Simple (sigma.obj y) →
      Simple (sigma.obj s) →
      (sigma.compositionLength x ≠ 2 →
        IsSimpleModule R (sigma.moduleTop x) ∧
          QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (sigma.moduleRadical x)) ∧
      (sigma.compositionLength y ≠ 2 →
        IsSimpleModule R (sigma.moduleTop y) ∧
          QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule R (sigma.moduleRadical y))

/-- The top/radical filtered control implies the manuscript's long-uniserial
control.  In particular, neither the length-three conclusion nor the final
uniserial lattice argument remains an assumption. -/
theorem twoNonsimpleLongUniserialControl_of_topRadicalControl
    (hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        sigma)
    (hcontrol : TwoNonsimpleLongTopRadicalControl sigma) :
    sigma.TwoNonsimpleLongUniserialControl := by
  intro S hcard hclosed x y s hxy hxs hys hS hxn hyn hss
  have hlocal :=
    hcontrol hcard hclosed hxy hxs hys hS hxn hyn hss
  constructor
  · intro hxNotTwo
    have hxData := hlocal.1 hxNotTwo
    have hxLength :=
      compositionLength_eq_three_of_simple_top_of_twoNonsimple sigma
        hclassification hclosed hS hxn hyn hss hxNotTwo hxData.1
    have hxModuleLength : Module.length R (sigma.obj x) = 3 := by
      rw [← sigma.coe_compositionLength x, hxLength]
      norm_num
    letI : IsNoetherian R (sigma.obj x) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (sigma.finiteLength x)).1
    letI : IsArtinian R (sigma.obj x) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (sigma.finiteLength x)).2
    exact ⟨hxLength,
      isUniserialModule_of_length_eq_three_of_simple_top_of_radical_indec
        hxModuleLength hxData.1 hxData.2⟩
  · intro hyNotTwo
    have hyData := hlocal.2 hyNotTwo
    have hyLength :=
      compositionLength_eq_three_of_simple_top_of_twoNonsimple sigma
        hclassification hclosed
          (by
            rw [hS]
            ext i
            simp [or_left_comm])
          hyn hxn hss hyNotTwo hyData.1
    have hyModuleLength : Module.length R (sigma.obj y) = 3 := by
      rw [← sigma.coe_compositionLength y, hyLength]
      norm_num
    letI : IsNoetherian R (sigma.obj y) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (sigma.finiteLength y)).1
    letI : IsArtinian R (sigma.obj y) :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (sigma.finiteLength y)).2
    exact ⟨hyLength,
      isUniserialModule_of_length_eq_three_of_simple_top_of_radical_indec
        hyModuleLength hyData.1 hyData.2⟩

end IndecomposableSkeleton

namespace NoParallelRepeatedRadical

universe x

variable {A : Type x} [Ring A]
  {iota : Type x} [IsNoetherianRing Aᵐᵒᵖ]
  (sigma :
    _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
      Aᵐᵒᵖ iota)
  (K : Type x) [Field K]
  [Algebra K A] [FiniteDimensional K A]

/-- No-parallel `Ext¹` rules out an indecomposable extension with one
simple top and two copies of one simple radical type. -/
theorem impossible_two_copy_isotypic_radical
    (hnoParallel :
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.NoParallelExtOne sigma K)
    {j s t : iota}
    (hs : Simple (sigma.obj s))
    (ht : Simple (sigma.obj t))
    (eTop : sigma.obj s ≃ₗ[Aᵐᵒᵖ] sigma.moduleTop j)
    (eRadical :
      (Fin 2 → sigma.obj t) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleRadical j) :
    False := by
  let topIso :
      ((⨁ fun _ : Unit ↦ (sigma.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (sigma.moduleTop j) :=
    ModuleCat.biproductIsoPi
        (fun _ : Unit ↦ (sigma.obj s).obj) ≪≫
      (LinearEquiv.funUnique Unit Aᵐᵒᵖ
        (sigma.obj s)).toModuleIso ≪≫
      eTop.toModuleIso
  let radicalIso :
      ((⨁ fun _ : Fin 2 ↦ (sigma.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≅
        ModuleCat.of Aᵐᵒᵖ (sigma.moduleRadical j) :=
    ModuleCat.biproductIsoPi
        (fun _ : Fin 2 ↦ (sigma.obj t).obj) ≪≫
      eRadical.toModuleIso
  let eRadical' :
      ((⨁ fun _ : Fin 2 ↦ (sigma.obj t).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleRadical j :=
    radicalIso.toLinearEquiv
  let eMiddle :
      sigma.obj j ≃ₗ[Aᵐᵒᵖ] sigma.obj j :=
    LinearEquiv.refl Aᵐᵒᵖ (sigma.obj j)
  let eTop' :
      ((⨁ fun _ : Unit ↦ (sigma.obj s).obj) :
          ModuleCat.{x} Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleTop j :=
    topIso.toLinearEquiv
  let radicalInclusion :
      sigma.moduleRadical j →ₗ[Aᵐᵒᵖ] sigma.obj j :=
    (sigma.moduleRadical j).subtype
  let topProjection :
      sigma.obj j →ₗ[Aᵐᵒᵖ] sigma.moduleTop j :=
    (sigma.moduleRadical j).mkQ
  have hexact : Function.Exact radicalInclusion topProjection :=
    LinearMap.exact_subtype_mkQ (sigma.moduleRadical j)
  let SC : ShortComplex (ModuleCat.{x} Aᵐᵒᵖ) :=
    ModuleCat.shortComplexOfConj
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact.linearMap_comp_eq_zero
  have hSC : SC.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact
      eRadical' eMiddle eTop' radicalInclusion topProjection
      hexact (sigma.moduleRadical j).subtype_injective
      (sigma.moduleRadical j).mkQ_surjective
  have hSC' :
      (ShortComplex.mk SC.f SC.g SC.zero).ShortExact := by
    simpa only [SC] using hSC
  letI : IsNoetherian Aᵐᵒᵖ (sigma.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength j)).1
  letI : IsArtinian Aᵐᵒᵖ (sigma.obj j) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (sigma.finiteLength j)).2
  have hExt := hnoParallel hs ht
  letI : FiniteDimensional K
      (Ext (sigma.obj s).obj (sigma.obj t).obj 1) :=
    hExt.1
  obtain ⟨ell, hell⟩ :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.exists_injective_linearMap_to_field_of_finrank_le_one
      hExt.2
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj s) :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj s)).mp hs
  letI : IsSimpleModule Aᵐᵒᵖ (sigma.obj t) :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj t)).mp ht
  letI : Simple (sigma.obj s).obj :=
    (simple_iff_isSimpleModule' (sigma.obj s).obj).mpr inferInstance
  letI : Simple (sigma.obj t).obj :=
    (simple_iff_isSimpleModule' (sigma.obj t).obj).mpr inferInstance
  have hsNonzero : 𝟙 (sigma.obj s).obj ≠ 0 :=
    CategoryTheory.id_nonzero (sigma.obj s).obj
  have htNonzero : 𝟙 (sigma.obj t).obj ≠ 0 :=
    CategoryTheory.id_nonzero (sigma.obj t).obj
  let arrow : (Unit → K) →ₗ[K] (Fin 2 → K) :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.scalarizedExtLinearMap
      (sigma.obj s).obj (sigma.obj t).obj ell hSC'.extClass
  have harrow :
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.IsIdempotentIndecomposable arrow :=
    QuotientSubmoduleEquidistribution.YonedaExtReflection.shortExact_scalarizedExtLinearMap_isIdempotentIndecomposable
      (sigma.obj s).obj (sigma.obj t).obj (sigma.obj j).obj
      hsNonzero htNonzero SC.f SC.g SC.zero hSC'
      (sigma.indecomposable j) ell hell
  have hbound : Module.finrank K (Fin 2 → K) ≤ 1 :=
    QuotientSubmoduleEquidistribution.LoewyTwoRankCore.target_finrank_le_one harrow
  have hdim : Module.finrank K (Fin 2 → K) = 2 := by simp
  rw [hdim] at hbound
  omega

end NoParallelRepeatedRadical

namespace PaperSpecialization

universe x

/-- In paper scope, once a long member of the two-nonsimple triple has
simple top and length three, its radical is automatically indecomposable.
Closedness makes a split radical into two copies of one simple type, while
the no-parallel one-arrow matrix forbids multiplicity two. -/
theorem radical_isIndecomposable_of_simple_top_of_twoNonsimple
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {iota : Type x} [Finite iota]
      (sigma :
        _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
          Aᵐᵒᵖ iota)
      {S : Set iota}, sigma.qClosure.IsClosed S →
      ∀ {j y s : iota},
        S = {j, y, s} →
        ¬ Simple (sigma.obj j) →
        ¬ Simple (sigma.obj y) →
        Simple (sigma.obj s) →
        sigma.compositionLength j = 3 →
        sigma.compositionLength y = 2 →
        IsSimpleModule Aᵐᵒᵖ (sigma.moduleTop j) →
        QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Aᵐᵒᵖ
          (sigma.moduleRadical j) := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro iota _ sigma S hclosed j y s hS hjn hyn hss
    hjLength hyLength htop
  by_contra hradNotIndec
  obtain ⟨F⟩ :=
    IndecomposableSkeleton.exists_repeatedRadicalFork_of_not_radical_indec
      sigma hclosed hS hjLength hyLength hss htop hradNotIndec
  have hjmem : j ∈ S := by
    rw [hS]
    simp
  have hymem : y ∈ S := by
    rw [hS]
    simp
  have hunique :=
    sigma.hasUniqueSimpleQuotientType_of_twoNonsimple
      hclosed hS hjmem hymem hjn hyn hss
  let Qj : sigma.SimpleQuotient j :=
    Classical.choice (sigma.exists_simpleQuotient j)
  have hQjIndex : Qj.index = s := hunique.1.2 Qj
  subst s
  letI : Epi Qj.map := Qj.epi
  have hQjSurjective : Function.Surjective Qj.map.hom.hom :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      Qj.map).mp inferInstance
  have hQjSimpleModule : IsSimpleModule Aᵐᵒᵖ (sigma.obj Qj.index) :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      (sigma.obj Qj.index)).mp Qj.simple
  let eTop0 :
      sigma.moduleTop j ≃ₗ[Aᵐᵒᵖ] sigma.obj Qj.index :=
    moduleTopLinearEquivOfSurjectiveToSimple
      htop hQjSimpleModule Qj.map.hom.hom hQjSurjective
  let Pfg : FGModuleCat.{x} Aᵐᵒᵖ :=
    FGModuleCat.of Aᵐᵒᵖ F.leftKernel
  letI : IsSimpleModule Aᵐᵒᵖ F.leftKernel :=
    F.leftKernel_simple
  have hPindec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule Aᵐᵒᵖ Pfg :=
    QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  obtain ⟨t, ⟨ePcat⟩⟩ := sigma.complete Pfg hPindec
  have hPfgSimple : Simple Pfg :=
    (_root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.simple_iff_isSimpleModule_fg
      Pfg).2 inferInstance
  have ht : Simple (sigma.obj t) :=
    (Simple.iff_of_iso ePcat).mp hPfgSimple
  let eP : F.leftKernel ≃ₗ[Aᵐᵒᵖ] sigma.obj t :=
    FGModuleCat.isoToLinearEquiv ePcat
  let eProduct :
      (sigma.obj t × sigma.obj t) ≃ₗ[Aᵐᵒᵖ]
        (F.leftKernel × F.rightKernel) :=
    LinearEquiv.prodCongr
      eP.symm (eP.symm.trans F.kernels_equiv)
  let eSplit :
      (F.leftKernel × F.rightKernel) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleRadical j :=
    Submodule.prodEquivOfIsCompl
      F.leftKernel F.rightKernel F.complementary
  let eRadical :
      (Fin 2 → sigma.obj t) ≃ₗ[Aᵐᵒᵖ]
        sigma.moduleRadical j :=
    (LinearEquiv.finTwoArrow Aᵐᵒᵖ (sigma.obj t)).trans
      (eProduct.trans eSplit)
  have hnoParallel :
      QuotientSubmoduleEquidistribution.LoewyTwoRankCore.NoParallelExtOne sigma K :=
    QuotientSubmoduleEquidistribution.NoParallelExtOne.noParallelExtOne_of_finiteDimensional_of_finiteSkeleton
      K A sigma
  exact
    NoParallelRepeatedRadical.impossible_two_copy_isotypic_radical
      sigma K hnoParallel hss ht eTop0.symm eRadical

/-- Under the paper hypotheses, the sole remaining filtered datum is simple
top: it automatically implies the stronger top-and-indecomposable-radical
control. -/
theorem topRadicalControl_of_simpleTopControl
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {iota : Type x} [Finite iota]
      (sigma :
        _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
          Aᵐᵒᵖ iota),
      IndecomposableSkeleton.TwoNonsimpleLongSimpleTopControl sigma →
        IndecomposableSkeleton.TwoNonsimpleLongTopRadicalControl sigma := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro iota _ sigma htopControl S hcard hclosed x y s hxy hxs hys hS hxn hyn hss
  have htopLocal :=
    htopControl hcard hclosed hxy hxs hys hS hxn hyn hss
  have hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        sigma :=
    QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.isotypicLoewyTwoIndecomposablesHaveSimpleTop
      K A sigma
  have honeLength :=
    sigma.length_two_left_or_right_of_twoNonsimple
      hclassification hclosed hS hxn hyn hss
  constructor
  · intro hxNotTwo
    have htopX := htopLocal.1 hxNotTwo
    have hyLength : sigma.compositionLength y = 2 :=
      honeLength.resolve_left hxNotTwo
    have hxLength :=
      IndecomposableSkeleton.compositionLength_eq_three_of_simple_top_of_twoNonsimple
        sigma hclassification hclosed hS hxn hyn hss hxNotTwo htopX
    have hradX :=
      radical_isIndecomposable_of_simple_top_of_twoNonsimple
        K A sigma hclosed hS hxn hyn hss hxLength hyLength htopX
    exact ⟨htopX, hradX⟩
  · intro hyNotTwo
    have htopY := htopLocal.2 hyNotTwo
    have hxLength : sigma.compositionLength x = 2 :=
      honeLength.resolve_right hyNotTwo
    have hSswap : S = {y, x, s} := by
      rw [hS]
      ext i
      simp [or_left_comm]
    have hyLength :=
      IndecomposableSkeleton.compositionLength_eq_three_of_simple_top_of_twoNonsimple
        sigma hclassification hclosed hSswap hyn hxn hss hyNotTwo htopY
    have hradY :=
      radical_isIndecomposable_of_simple_top_of_twoNonsimple
        K A sigma hclosed hSswap hyn hxn hss hyLength hxLength htopY
    exact ⟨htopY, hradY⟩

/-- Paper-scope final reduction: the manuscript's entire long-uniserial
control follows from simple-top control alone. -/
theorem twoNonsimpleLongUniserialControl_of_simpleTopControl
    (K A : Type x)
    [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : IsNoetherianRing Aᵐᵒᵖ :=
      QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
    ∀ {iota : Type x} [Finite iota]
      (sigma :
        _root_.QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{x, x, x}
          Aᵐᵒᵖ iota),
      IndecomposableSkeleton.TwoNonsimpleLongSimpleTopControl sigma →
        sigma.TwoNonsimpleLongUniserialControl := by
  letI : IsNoetherianRing Aᵐᵒᵖ :=
    QuotientSubmoduleEquidistribution.isNoetherianRing_op_of_finiteDimensional K A
  intro iota _ sigma htopControl
  have hclassification :
      QuotientSubmoduleEquidistribution.LengthTwoGabrielBridge.IndecomposableSkeleton.IsotypicLoewyTwoIndecomposablesHaveSimpleTop
        sigma :=
    QuotientSubmoduleEquidistribution.LoewyTwoGabrielClassification.isotypicLoewyTwoIndecomposablesHaveSimpleTop
      K A sigma
  intro S hcard hclosed x y s hxy hxs hys hS hxn hyn hss
  exact
    (IndecomposableSkeleton.twoNonsimpleLongUniserialControl_of_topRadicalControl
      sigma hclassification
      (topRadicalControl_of_simpleTopControl K A sigma htopControl))
      hcard hclosed hxy hxs hys hS hxn hyn hss

end PaperSpecialization

end QuotientSubmoduleEquidistribution.FamilyFourControl
