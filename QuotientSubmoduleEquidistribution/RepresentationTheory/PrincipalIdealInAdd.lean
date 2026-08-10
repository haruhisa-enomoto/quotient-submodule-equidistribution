import QuotientSubmoduleEquidistribution.RepresentationTheory.TsukamotoRejectiveBridge

/-!
# Principal ideals in additive closures

A two-sided principal ideal `AeA` which is finite projective as a right
module is a retract of a finite biproduct of copies of `eA`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open MulOpposite

namespace QuotientSubmoduleEquidistribution.Tsukamoto

universe u

variable {A : Type u} [Ring A]

private abbrev principalIdealOpposite (e : A) : Ideal Aᵐᵒᵖ :=
  (principalTwoSidedIdeal e).asIdealOpposite

private abbrev principalIdealOppositeModule (e : A) :
    ModuleCat.{u} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (principalIdealOpposite e)

private theorem principalRightIdeal_le_principalIdealOpposite
    (e : A) :
    principalRightIdeal e ≤ principalIdealOpposite e := by
  apply Ideal.span_le.mpr
  rw [Set.singleton_subset_iff]
  exact
    TwoSidedIdeal.mem_asIdealOpposite.mpr
      (TwoSidedIdeal.subset_span (Set.mem_singleton e))

/-- Multiplication by a left coefficient, viewed as a right-module map
`eA → AeA`.  In the opposite-ring convention this is right
multiplication by `op a`. -/
private def leftCoefficientMap (e a : A) :
    principalRightIdeal e →ₗ[Aᵐᵒᵖ] principalIdealOpposite e :=
  ((LinearMap.mulRight Aᵐᵒᵖ (op a)).comp
      (Submodule.subtype (principalRightIdeal e))).codRestrict
    (principalIdealOpposite e)
    (fun x ↦ by
      rw [TwoSidedIdeal.mem_asIdealOpposite]
      change a * unop x ∈ principalTwoSidedIdeal e
      exact
        (principalTwoSidedIdeal e).mul_mem_left
          a (unop x)
          (TwoSidedIdeal.mem_asIdealOpposite.mp
            (principalRightIdeal_le_principalIdealOpposite e
              x.property)))

/-- The maps `eA → AeA` obtained from all left coefficients jointly
generate the whole right module `AeA`. -/
private theorem iSup_range_leftCoefficientMap_eq_top (e : A) :
    (⨆ a : A, LinearMap.range (leftCoefficientMap e a)) = ⊤ := by
  let K : Submodule Aᵐᵒᵖ (principalIdealOpposite e) :=
    ⨆ a : A, LinearMap.range (leftCoefficientMap e a)
  apply top_unique
  intro z hz
  change z ∈ K
  have hspan :
      ∀ (x : A) (hx : x ∈ principalTwoSidedIdeal e),
        ∀ a : A,
          (⟨op (a * x),
              TwoSidedIdeal.mem_asIdealOpposite.mpr
                ((principalTwoSidedIdeal e).mul_mem_left a x hx)⟩ :
            principalIdealOpposite e) ∈ K := by
    intro x hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx =>
        have hxe : x = e := Set.mem_singleton_iff.mp hx
        subst x
        intro a
        apply
          (le_iSup
            (fun a : A ↦
              LinearMap.range (leftCoefficientMap e a)) a)
        refine ⟨
          (⟨op e,
              Ideal.subset_span
                (Set.mem_singleton (op e))⟩ :
            principalRightIdeal e), ?_⟩
        apply Subtype.ext
        simp [leftCoefficientMap]
    | zero =>
        intro a
        convert K.zero_mem using 1
        apply Subtype.ext
        simp
    | add x y hx hy ihx ihy =>
        intro a
        have hxK := ihx a
        have hyK := ihy a
        convert K.add_mem hxK hyK using 1
        apply Subtype.ext
        simp [mul_add]
    | neg x hx ih =>
        intro a
        have hxK := ih a
        convert K.neg_mem hxK using 1
        apply Subtype.ext
        simp
    | left_absorb b x hx ih =>
        intro a
        have hxK := ih (a * b)
        convert hxK using 1
        apply Subtype.ext
        simp [mul_assoc]
    | right_absorb b x hx ih =>
        intro a
        have hxK := ih a
        have hsmul := K.smul_mem (op b) hxK
        convert hsmul using 1
        apply Subtype.ext
        simp [mul_assoc]
  have hzH :
      unop z ∈ principalTwoSidedIdeal e :=
    TwoSidedIdeal.mem_asIdealOpposite.mp z.property
  have h := hspan (unop z) hzH 1
  convert h using 1
  apply Subtype.ext
  simp

/-- If `AeA` is finitely generated and projective as a right module,
then it is a retract of a finite biproduct of copies of `eA`.  This
version states the hypotheses on the literal opposite ideal carrying
that right module. -/
theorem principalIdealOpposite_mem_add_of_finite_projective
    (e : A)
    (hfinite :
      Module.Finite Aᵐᵒᵖ (principalIdealOpposite e))
    (hprojective :
      Module.Projective Aᵐᵒᵖ (principalIdealOpposite e)) :
    AuslanderEquivalence.finiteAddClosure
      (principalRightModule e)
      (principalIdealOppositeModule e) := by
  classical
  letI :
      Module.Finite Aᵐᵒᵖ (principalIdealOpposite e) :=
    hfinite
  have hcompact :
      IsCompactElement
        (⊤ : Submodule Aᵐᵒᵖ (principalIdealOpposite e)) := by
    obtain ⟨G, hG⟩ :=
      Module.Finite.fg_top
        (R := Aᵐᵒᵖ)
        (M := principalIdealOpposite e)
    rw [← hG]
    exact Submodule.finset_span_isCompactElement G
  have hle :
      (⊤ : Submodule Aᵐᵒᵖ (principalIdealOpposite e)) ≤
        ⨆ a : A,
          LinearMap.range (leftCoefficientMap e a) := by
    rw [iSup_range_leftCoefficientMap_eq_top e]
  obtain ⟨F, hF⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
      (Submodule Aᵐᵒᵖ (principalIdealOpposite e))
      hcompact
      (fun a : A ↦
        LinearMap.range (leftCoefficientMap e a))
      hle
  let enum : Fin F.card ≃ F :=
    F.equivFin.symm
  let E : Fin F.card → ModuleCat.{u} Aᵐᵒᵖ :=
    fun _ ↦ principalRightModule e
  let q :
      (⨁ E) ⟶ principalIdealOppositeModule e :=
    biproduct.desc
      (fun j : Fin F.card ↦
        ModuleCat.ofHom
          (leftCoefficientMap e (enum j).1))
  have hq_range :
      LinearMap.range q.hom = ⊤ := by
    apply top_unique
    refine hF.trans ?_
    refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
    let j : Fin F.card :=
      F.equivFin ⟨a, ha⟩
    have hcomp :
        biproduct.ι E j ≫ q =
          ModuleCat.ofHom
            (leftCoefficientMap e a) := by
      dsimp only [q]
      rw [biproduct.ι_desc]
      congr 1
      simp [enum, j]
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    refine ⟨(biproduct.ι E j).hom x, ?_⟩
    exact ConcreteCategory.congr_hom hcomp x
  haveI : Epi q :=
    (ModuleCat.epi_iff_range_eq_top q).mpr hq_range
  have htargetProjective :
      Projective (principalIdealOppositeModule e) :=
    (IsProjective.iff_projective
      (principalIdealOpposite e)).mp hprojective
  letI :
      Projective (principalIdealOppositeModule e) :=
    htargetProjective
  obtain ⟨i, hi⟩ :=
    Projective.factors
      (𝟙 (principalIdealOppositeModule e)) q
  exact
    ⟨{
      n := F.card
      retract :=
        { i := i
          r := q
          retract := hi } }⟩

/-- The right module carried by a two-sided ideal is linearly
equivalent to its realization as an ideal of the opposite ring. -/
private def asIdealOppositeLinearEquiv
    (H : TwoSidedIdeal A) :
    H.asIdealOpposite ≃ₗ[Aᵐᵒᵖ] H where
  toFun x :=
    ⟨unop x,
      TwoSidedIdeal.mem_asIdealOpposite.mp x.property⟩
  invFun x :=
    ⟨op x,
      TwoSidedIdeal.mem_asIdealOpposite.mpr x.property⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by rfl)

/-- Literal right-module form of the finite-additive-closure result.
No idempotence hypothesis on `e` is needed: finite generation extracts
finitely many left coefficients in `AeA`, and projectivity splits the
resulting epimorphism from a finite sum of copies of `eA`. -/
theorem principalTwoSidedIdeal_mem_add_of_finite_projective
    (e : A)
    (hfinite :
      Module.Finite Aᵐᵒᵖ (principalTwoSidedIdeal e))
    (hprojective :
      IsRightProjectiveIdeal (principalTwoSidedIdeal e)) :
    AuslanderEquivalence.finiteAddClosure
      (principalRightModule e)
      (ModuleCat.of Aᵐᵒᵖ (principalTwoSidedIdeal e)) := by
  let equiv :=
    asIdealOppositeLinearEquiv
      (principalTwoSidedIdeal e)
  have hfiniteOpp :
      Module.Finite Aᵐᵒᵖ (principalIdealOpposite e) :=
    (Module.Finite.equiv_iff equiv).mpr hfinite
  letI :
      Module.Projective Aᵐᵒᵖ
        (principalTwoSidedIdeal e) :=
    hprojective
  have hprojectiveOpp :
      Module.Projective Aᵐᵒᵖ
        (principalIdealOpposite e) :=
    Module.Projective.of_equiv equiv.symm
  obtain ⟨P⟩ :=
    principalIdealOpposite_mem_add_of_finite_projective
      e hfiniteOpp hprojectiveOpp
  let iso :
      principalIdealOppositeModule e ≅
        ModuleCat.of Aᵐᵒᵖ (principalTwoSidedIdeal e) :=
    equiv.toModuleIso
  exact
    ⟨{
      n := P.n
      retract :=
        (Retract.ofIso iso.symm).trans P.retract }⟩

end QuotientSubmoduleEquidistribution.Tsukamoto

