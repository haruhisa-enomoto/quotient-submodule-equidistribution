import QuotientSubmoduleEquidistribution.RadicalSquareZero.OriginalNonsimpleClosure
import QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedTriangularIndecomposable
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedFinite
import QuotientSubmoduleEquidistribution.RepresentationTheory.TrivSqZeroExtSeparatedSimple
import QuotientSubmoduleEquidistribution.RepresentationTheory.SimpleNonsimpleRelabeling

/-!
# Constructing the separated indecomposable labels

This file builds the three canonical families of indecomposable modules over
the triangular separated algebra: separated realizations of the original
nonsimples, covered copies of the original simples, and their free
radical-side copies.  It then prepares their placement in an arbitrary
complete duplicate-free indecomposable skeleton.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.RadicalSquareZero

open SeparatedTriangularAlgebra
open TrivSqZeroExtSeparatedCorrespondence
open TrivSqZeroExtSeparatedData
open TrivSqZeroExtSeparatedFinite
open TrivSqZeroExtSeparatedIndecomposable
open TrivSqZeroExtSeparatedSimple

universe u v w x y z

variable {S : Type u} {J : Type v}
variable [CommRing S] [AddCommGroup J]
variable [Module S J] [Module Sᵐᵒᵖ J]
variable [SMulCommClass S Sᵐᵒᵖ J]
variable [IsSemisimpleRing S] [Module.Finite S J]
variable [IsNoetherianRing (TrivSqZeroExt S J)]
variable [IsNoetherianRing (Algebra S J)]
variable {Nonsimple : Type x} {Vertex : Type y} {kappa : Type z}
variable
  {sigma : IndecomposableSkeleton.{max u v, max x y, w}
    (TrivSqZeroExt S J) (Nonsimple ⊕ Vertex)}

/-- The canonical separated datum attached to each of the three prospective
label families. -/
abbrev separatedCandidateData
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    SeparatedData.{u, v, w} (S := S) (J := J) :=
  match i with
  | Sum.inl n =>
      moduleSeparatedData (S := S) (J := J)
        (sigma.obj (Sum.inl n)).obj
  | Sum.inr (Sum.inl a) =>
      moduleSeparatedData (S := S) (J := J)
        (sigma.obj (Sum.inr a)).obj
  | Sum.inr (Sum.inr a) =>
      freeData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj

omit [IsNoetherianRing (Algebra S J)] in
/-- Each canonical separated candidate is finitely generated over the
triangular algebra. -/
theorem separatedCandidateData_moduleFinite
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    let D := separatedCandidateData (sigma := sigma) i
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    Module.Finite (Algebra S J) (Realized D) := by
  rcases i with n | (a | a)
  · exact moduleSeparatedData_realized_moduleFinite
      (sigma.obj (Sum.inl n))
  · exact moduleSeparatedData_realized_moduleFinite
      (sigma.obj (Sum.inr a))
  · exact freeData_realized_moduleFinite (sigma.obj (Sum.inr a))

/-- The finitely generated triangular module represented by a canonical
separated candidate. -/
abbrev separatedCandidateFG
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    FGModuleCat.{w} (Algebra S J) := by
  let D := separatedCandidateData (sigma := sigma) i
  letI : Module.Finite (Algebra S J) (Realized D) :=
    separatedCandidateData_moduleFinite i
  exact FGModuleCat.of (Algebra S J) (Realized D)

omit [IsNoetherianRing (Algebra S J)] in
@[simp]
theorem separatedCandidateFG_obj
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    (separatedCandidateFG (sigma := sigma) i).obj =
      realizedModuleCat (separatedCandidateData (sigma := sigma) i) :=
  rfl

omit [IsNoetherianRing (Algebra S J)] in
/-- Under the original label hypotheses, every canonical candidate is
indecomposable over the triangular algebra. -/
theorem separatedCandidateFG_indecomposable
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J)
      (separatedCandidateFG (sigma := sigma) i) := by
  rcases i with n | (a | a)
  · let X := sigma.obj (Sum.inl n)
    let D := moduleSeparatedData (S := S) (J := J) X.obj
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    change QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J) (Realized D)
    letI : Nontrivial (Module.jacobson (TrivSqZeroExt S J) X) :=
      L.nonsimple_radical_nontrivial n
    exact (realized_isIndecomposable_iff D).2
      ((module_isIndecomposable_iff_separatedData X.obj).1
        (sigma.indecomposable (Sum.inl n)))
  · let D := moduleSeparatedData (S := S) (J := J)
      (sigma.obj (Sum.inr a)).obj
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    change QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J) (Realized D)
    have hs := covered_realized_simple
      (S := S) (J := J) (sigma.obj (Sum.inr a)).obj
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
        (L.simple_simple a))
    letI : IsSimpleModule (Algebra S J) (Realized D) :=
      (simple_iff_isSimpleModule' _).1 hs
    exact QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
  · let D := freeData (S := S) (J := J)
      (sigma.obj (Sum.inr a)).obj
    letI : Module (Algebra S J) (Realized D) := realizedModule D
    change QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (Algebra S J) (Realized D)
    have hs := free_realized_simple
      (S := S) (J := J) (sigma.obj (Sum.inr a)).obj
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
        (L.simple_simple a))
    letI : IsSimpleModule (Algebra S J) (Realized D) :=
      (simple_iff_isSimpleModule' _).1 hs
    exact QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule

/-- Exactly the covered and free families among the canonical candidates are
simple. -/
theorem separatedCandidateFG_simple_iff
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    Simple (separatedCandidateFG (sigma := sigma) i) ↔
      ∃ a : Vertex, i = Sum.inr (Sum.inl a) ∨
        i = Sum.inr (Sum.inr a) := by
  rcases i with n | (a | a)
  · constructor
    · intro hsimple
      exfalso
      let X := sigma.obj (Sum.inl n)
      let D := moduleSeparatedData (S := S) (J := J) X.obj
      letI : Module (Algebra S J) (Realized D) := realizedModule D
      letI : Module.Finite (Algebra S J) (Realized D) :=
        moduleSeparatedData_realized_moduleFinite X
      have hsimpleModule : IsSimpleModule (Algebra S J) (Realized D) :=
        (IndecomposableSkeleton.simple_iff_isSimpleModule_fg
          (FGModuleCat.of (Algebra S J) (Realized D))).1 hsimple
      letI : Nontrivial X := (sigma.indecomposable (Sum.inl n)).nontrivial
      letI : Nontrivial D.top := moduleSeparatedData_top_nontrivial X
      letI : Nontrivial D.radical :=
        L.nonsimple_radical_nontrivial n
      apply realized_not_simple_of_top_radical_nontrivial D
      exact (simple_iff_isSimpleModule' (realizedModuleCat D)).2
        hsimpleModule
    · rintro ⟨a, h | h⟩ <;> cases h
  · constructor
    · intro _
      exact ⟨a, Or.inl rfl⟩
    · intro _
      apply (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).2
      exact (simple_iff_isSimpleModule' _).1
        (covered_realized_simple
          (S := S) (J := J) (sigma.obj (Sum.inr a)).obj
          ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
            (L.simple_simple a)))
  · constructor
    · intro _
      exact ⟨a, Or.inr rfl⟩
    · intro _
      apply (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).2
      exact (simple_iff_isSimpleModule' _).1
        (free_realized_simple
          (S := S) (J := J) (sigma.obj (Sum.inr a)).obj
          ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
            (L.simple_simple a)))

variable
  (tau : IndecomposableSkeleton.{max u v, z, w}
    (Algebra S J) kappa)

/-- The reconstruction of the separated data extracted from a finite
triangular module, packaged as a finite original module. -/
abbrev separatedReconstructionFG
    (X : FGModuleCat.{w} (Algebra S J)) :
    FGModuleCat.{w} (TrivSqZeroExt S J) := by
  let D := ofModule (S := S) (J := J) X.obj
  letI : Module (TrivSqZeroExt S J) (Reconstructed D) :=
    reconstructedModule D
  letI : Module.Finite (TrivSqZeroExt S J) (Reconstructed D) :=
    ofModule_reconstructed_moduleFinite X
  exact FGModuleCat.of (TrivSqZeroExt S J) (Reconstructed D)

omit [IsNoetherianRing (TrivSqZeroExt S J)]
    [IsNoetherianRing (Algebra S J)] in
@[simp]
theorem separatedReconstructionFG_obj
    (X : FGModuleCat.{w} (Algebra S J)) :
    (separatedReconstructionFG (S := S) (J := J) X).obj =
      reconstructedModuleCat (ofModule (S := S) (J := J) X.obj) :=
  rfl

omit [IsSemisimpleRing S] [Module.Finite S J]
    [IsNoetherianRing (Algebra S J)] in
/-- Original nonsimple labels cannot represent simple modules. -/
theorem OriginalNonsimpleLabelData.nonsimple_not_simple
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (n : Nonsimple) : ¬ Simple (sigma.obj (Sum.inl n)) := by
  intro hsimple
  letI : IsSimpleModule (TrivSqZeroExt S J) (sigma.obj (Sum.inl n)) :=
    (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1 hsimple
  have hbot := IsSimpleModule.jacobson_eq_bot
    (TrivSqZeroExt S J) (sigma.obj (Sum.inl n))
  letI : Subsingleton
      (Module.jacobson (TrivSqZeroExt S J) (sigma.obj (Sum.inl n))) := by
    rw [hbot]
    infer_instance
  exact not_subsingleton_iff_nontrivial.mpr
    (L.nonsimple_radical_nontrivial n) inferInstance

/-- The label in the separated skeleton corresponding to an original
nonsimple or to its covered simple copy. -/
def generatedCandidateLabel :
    Nonsimple ⊕ Vertex → Nonsimple ⊕ (Vertex ⊕ Vertex)
  | Sum.inl n => Sum.inl n
  | Sum.inr a => Sum.inr (Sum.inl a)

/-- If a generated extracted datum reconstructs to a chosen original
skeleton object, its nonsimple/covered candidate realizes back to the given
triangular module. -/
def generatedCandidateIso
    (X : FGModuleCat.{w} (Algebra S J))
    (i : Nonsimple ⊕ Vertex)
    (e : separatedReconstructionFG (S := S) (J := J) X ≅ sigma.obj i)
    (hgen : IsGenerated (ofModule (S := S) (J := J) X.obj)) :
    separatedCandidateFG (sigma := sigma) (generatedCandidateLabel i) ≅ X := by
  let U := forget₂ (FGModuleCat.{w} (TrivSqZeroExt S J))
    (ModuleCat.{w} (TrivSqZeroExt S J))
  let V := forget₂ (FGModuleCat.{w} (Algebra S J))
    (ModuleCat.{w} (Algebra S J))
  let F := TrivSqZeroExtSeparatedModuleFunctor.moduleSeparatedDataFunctor
    (S := S) (J := J)
  let D := ofModule (S := S) (J := J) X.obj
  let eModule : reconstructedModuleCat D ≅ (sigma.obj i).obj :=
    U.mapIso e
  let eData :
      moduleSeparatedData (S := S) (J := J) (sigma.obj i).obj ≅ D :=
    (F.mapIso eModule).symm ≪≫
      reconstructedSeparatedDataIso D hgen
  let eRealized :
      realizedModuleCat
          (moduleSeparatedData (S := S) (J := J) (sigma.obj i).obj) ≅
        X.obj :=
    (realizationFunctor (S := S) (J := J)).mapIso eData ≪≫
      realizedOfModuleIso (S := S) (J := J) X.obj
  rcases i with n | a
  · exact V.preimageIso eRealized
  · exact V.preimageIso eRealized

/-- In the pure radical case, an original simple reconstruction gives the
free candidate realizing back to the triangular module. -/
def freeCandidateIso
    (X : FGModuleCat.{w} (Algebra S J))
    (a : Vertex)
    (e : separatedReconstructionFG (S := S) (J := J) X ≅
      sigma.obj (Sum.inr a))
    [Subsingleton (ofModule (S := S) (J := J) X.obj).top]
    (hRadical : IsSimpleModule S
      (ofModule (S := S) (J := J) X.obj).radical) :
    separatedCandidateFG (sigma := sigma) (Sum.inr (Sum.inr a)) ≅ X := by
  let U := forget₂ (FGModuleCat.{w} (TrivSqZeroExt S J))
    (ModuleCat.{w} (TrivSqZeroExt S J))
  let V := forget₂ (FGModuleCat.{w} (Algebra S J))
    (ModuleCat.{w} (Algebra S J))
  let D := ofModule (S := S) (J := J) X.obj
  let eModule : reconstructedModuleCat D ≅ (sigma.obj (Sum.inr a)).obj :=
    U.mapIso e
  let eFree :
      realizedModuleCat
          (freeData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj) ≅
        realizedModuleCat (freeData (S := S) (J := J)
          (reconstructedModuleCat D)) :=
    freeDataIsoOfModuleIso (S := S) (J := J) eModule.symm
  let eRealized :
      realizedModuleCat
          (freeData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj) ≅
        X.obj :=
    eFree ≪≫ freeDataReconstructedIso D hRadical ≪≫
      realizedOfModuleIso (S := S) (J := J) X.obj
  exact V.preimageIso eRealized

/-- Every indecomposable in the target triangular skeleton is isomorphic to
one of the three canonical candidates. -/
theorem exists_separatedCandidateFG_iso
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (k : kappa) :
    ∃ i : Nonsimple ⊕ (Vertex ⊕ Vertex),
      Nonempty (separatedCandidateFG (sigma := sigma) i ≅ tau.obj k) := by
  let X := tau.obj k
  let D := ofModule (S := S) (J := J) X.obj
  letI : Module (TrivSqZeroExt S J) (Reconstructed D) :=
    reconstructedModule D
  letI : Module.Finite (TrivSqZeroExt S J) (Reconstructed D) :=
    ofModule_reconstructed_moduleFinite X
  have hD : IsIndecomposableSeparatedData D :=
    ofModule_isIndecomposableSeparatedData X.obj (tau.indecomposable k)
  rcases subsingleton_or_nontrivial D.top with htop | htop
  · letI : Subsingleton D.top := htop
    have hRadIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S D.radical :=
      radical_isIndecomposable_of_top_subsingleton D hD
    have hRadSimple : IsSimpleModule S D.radical :=
      IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
        hRadIndec
    have hRecSimpleCat : Simple (reconstructedModuleCat D) :=
      reconstructed_simple_of_radical D hRadSimple
    have hRecSimpleModule :
        IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
      (simple_iff_isSimpleModule' (reconstructedModuleCat D)).1
        hRecSimpleCat
    have hRecIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (TrivSqZeroExt S J)
        (separatedReconstructionFG (S := S) (J := J) X) := by
      letI : IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
        hRecSimpleModule
      exact QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
    obtain ⟨i, ⟨e⟩⟩ :=
      sigma.complete (separatedReconstructionFG (S := S) (J := J) X)
        hRecIndec
    rcases i with n | a
    · exfalso
      apply L.nonsimple_not_simple n
      apply (Simple.iff_of_iso e).1
      exact (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).2
        hRecSimpleModule
    · exact ⟨Sum.inr (Sum.inr a),
        ⟨freeCandidateIso (sigma := sigma) X a e hRadSimple⟩⟩
  · letI : Nontrivial D.top := htop
    rcases subsingleton_or_nontrivial D.radical with hrad | hrad
    · letI : Subsingleton D.radical := hrad
      have hTopIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S D.top :=
        top_isIndecomposable_of_radical_subsingleton D hD
      have hTopSimple : IsSimpleModule S D.top :=
        IndecomposableSkeleton.isSimpleModule_of_semisimple_of_indecomposable
          hTopIndec
      have hRecSimpleCat : Simple (reconstructedModuleCat D) :=
        reconstructed_simple_of_top D hTopSimple
      have hRecSimpleModule :
          IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
        (simple_iff_isSimpleModule' (reconstructedModuleCat D)).1
          hRecSimpleCat
      have hRecIndec : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (TrivSqZeroExt S J)
          (separatedReconstructionFG (S := S) (J := J) X) := by
        letI : IsSimpleModule (TrivSqZeroExt S J) (Reconstructed D) :=
          hRecSimpleModule
        exact QuotientSubmoduleEquidistribution.Foundation.IsSimpleModule.isIndecomposableModule
      obtain ⟨i, ⟨e⟩⟩ :=
        sigma.complete (separatedReconstructionFG (S := S) (J := J) X)
          hRecIndec
      have hgen : IsGenerated D :=
        isGenerated_of_indecomposable_of_top_nontrivial D hD
      rcases i with n | a
      · exfalso
        apply L.nonsimple_not_simple n
        apply (Simple.iff_of_iso e).1
        exact (IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).2
          hRecSimpleModule
      · exact ⟨Sum.inr (Sum.inl a),
          ⟨generatedCandidateIso (sigma := sigma) X (Sum.inr a) e hgen⟩⟩
    · letI : Nontrivial D.radical := hrad
      obtain ⟨hgen, -, hRecIndec, -⟩ :=
        reconstructedModule_of_bisupported_indecomposable D hD
      have hRecIndecFG : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
          (TrivSqZeroExt S J)
          (separatedReconstructionFG (S := S) (J := J) X) :=
        hRecIndec
      obtain ⟨i, ⟨e⟩⟩ :=
        sigma.complete (separatedReconstructionFG (S := S) (J := J) X)
          hRecIndecFG
      rcases i with n | a
      · exact ⟨Sum.inl n,
          ⟨generatedCandidateIso (sigma := sigma) X (Sum.inl n) e hgen⟩⟩
      · exfalso
        have hRecSimpleFG : Simple
            (separatedReconstructionFG (S := S) (J := J) X) :=
          (Simple.iff_of_iso e).2 (L.simple_simple a)
        apply reconstructed_not_simple_of_top_radical_nontrivial D
        exact (simple_iff_isSimpleModule' (reconstructedModuleCat D)).2
          ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
            hRecSimpleFG)

/-- An isomorphism between two candidate modules lifts uniquely to an
isomorphism of their separated data. -/
def separatedCandidateDataIsoOfFGIso
    {i j : Nonsimple ⊕ (Vertex ⊕ Vertex)}
    (e : separatedCandidateFG (sigma := sigma) i ≅
      separatedCandidateFG (sigma := sigma) j) :
    separatedCandidateData (sigma := sigma) i ≅
      separatedCandidateData (sigma := sigma) j := by
  let V := forget₂ (FGModuleCat.{w} (Algebra S J))
    (ModuleCat.{w} (Algebra S J))
  exact (realizationFunctor (S := S) (J := J)).preimageIso (V.mapIso e)

omit [Module.Finite S J]
    [IsNoetherianRing (SeparatedTriangularAlgebra.Algebra S J)] in
/-- Isomorphic separated data extracted from two original skeleton objects
force equality of their original labels. -/
theorem originalIndex_eq_of_moduleSeparatedData_iso
    {i j : Nonsimple ⊕ Vertex}
    (e : moduleSeparatedData (S := S) (J := J) (sigma.obj i).obj ≅
      moduleSeparatedData (S := S) (J := J) (sigma.obj j).obj) :
    i = j := by
  let U := forget₂ (FGModuleCat.{w} (TrivSqZeroExt S J))
    (ModuleCat.{w} (TrivSqZeroExt S J))
  let eModule : (sigma.obj i).obj ≅ (sigma.obj j).obj :=
    (reconstructedModuleIso (S := S) (J := J) (sigma.obj i).obj).symm ≪≫
      (reconstructionFunctor (S := S) (J := J)).mapIso e ≪≫
      reconstructedModuleIso (S := S) (J := J) (sigma.obj j).obj
  exact sigma.eq_of_iso ⟨U.preimageIso eModule⟩

/-- An isomorphism between free copies of two original simples induces an
isomorphism between their full original separated data. -/
def moduleSeparatedDataIsoOfFreeDataIso
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (a b : Vertex)
    (e : freeData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj ≅
      freeData (S := S) (J := J) (sigma.obj (Sum.inr b)).obj) :
    moduleSeparatedData (S := S) (J := J) (sigma.obj (Sum.inr a)).obj ≅
      moduleSeparatedData (S := S) (J := J)
        (sigma.obj (Sum.inr b)).obj := by
  let DA := moduleSeparatedData (S := S) (J := J)
    (sigma.obj (Sum.inr a)).obj
  let DB := moduleSeparatedData (S := S) (J := J)
    (sigma.obj (Sum.inr b)).obj
  letI : Subsingleton DA.radical :=
    moduleSeparatedData_radical_subsingleton _
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
        (L.simple_simple a))
  letI : Subsingleton DB.radical :=
    moduleSeparatedData_radical_subsingleton _
      ((IndecomposableSkeleton.simple_iff_isSimpleModule_fg _).1
        (L.simple_simple b))
  let eTop : DA.top ≃ₗ[S] DB.top := isoRadicalLinearEquiv e
  exact
    { hom := ⟨(eTop.toLinearMap, 0), by
          intro j t
          exact Subsingleton.elim _ _⟩
      inv := ⟨(eTop.symm.toLinearMap, 0), by
          intro j t
          exact Subsingleton.elim _ _⟩
      hom_inv_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact eTop.symm_apply_apply t
        · ext d
          exact Subsingleton.elim _ _
      inv_hom_id := by
        apply Subtype.ext
        apply Prod.ext
        · ext t
          exact eTop.apply_symm_apply t
        · ext d
          exact Subsingleton.elim _ _ }

/-- The three canonical candidate families contain no isomorphic duplicates. -/
theorem separatedCandidate_eq_of_iso
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    {i j : Nonsimple ⊕ (Vertex ⊕ Vertex)}
    (e : separatedCandidateFG (sigma := sigma) i ≅
      separatedCandidateFG (sigma := sigma) j) :
    i = j := by
  let eData := separatedCandidateDataIsoOfFGIso (sigma := sigma) e
  rcases i with n | (a | a) <;> rcases j with m | (b | b)
  · have h : (Sum.inl n : Nonsimple ⊕ Vertex) = Sum.inl m :=
      originalIndex_eq_of_moduleSeparatedData_iso (sigma := sigma) eData
    have hnm : n = m := Sum.inl.inj h
    subst m
    rfl
  · exfalso
    have hsTarget : Simple
        (separatedCandidateFG (sigma := sigma)
          (Sum.inr (Sum.inl b))) :=
      (separatedCandidateFG_simple_iff L _).2 ⟨b, Or.inl rfl⟩
    have hsSource := (Simple.iff_of_iso e).2 hsTarget
    obtain ⟨c, h | h⟩ := (separatedCandidateFG_simple_iff L _).1 hsSource
    · cases h
    · cases h
  · exfalso
    have hsTarget : Simple
        (separatedCandidateFG (sigma := sigma)
          (Sum.inr (Sum.inr b))) :=
      (separatedCandidateFG_simple_iff L _).2 ⟨b, Or.inr rfl⟩
    have hsSource := (Simple.iff_of_iso e).2 hsTarget
    obtain ⟨c, h | h⟩ := (separatedCandidateFG_simple_iff L _).1 hsSource
    · cases h
    · cases h
  · exfalso
    have hsSource : Simple
        (separatedCandidateFG (sigma := sigma)
          (Sum.inr (Sum.inl a))) :=
      (separatedCandidateFG_simple_iff L _).2 ⟨a, Or.inl rfl⟩
    have hsTarget := (Simple.iff_of_iso e).1 hsSource
    obtain ⟨c, h | h⟩ := (separatedCandidateFG_simple_iff L _).1 hsTarget
    · cases h
    · cases h
  · have h : (Sum.inr a : Nonsimple ⊕ Vertex) = Sum.inr b :=
      originalIndex_eq_of_moduleSeparatedData_iso (sigma := sigma) eData
    exact congrArg (fun q : Vertex ↦ Sum.inr (Sum.inl q)) (Sum.inr.inj h)
  · exfalso
    let DA := moduleSeparatedData (S := S) (J := J)
      (sigma.obj (Sum.inr a)).obj
    letI : Nontrivial (sigma.obj (Sum.inr a)) :=
      (sigma.indecomposable (Sum.inr a)).nontrivial
    letI : Nontrivial DA.top :=
      moduleSeparatedData_top_nontrivial (sigma.obj (Sum.inr a))
    let eTop : DA.top ≃ₗ[S]
        (freeData (S := S) (J := J)
          (sigma.obj (Sum.inr b)).obj).top :=
      isoTopLinearEquiv eData
    obtain ⟨t, ht⟩ := exists_ne (0 : DA.top)
    apply ht
    apply eTop.injective
    exact Subsingleton.elim _ _
  · exfalso
    have hsSource : Simple
        (separatedCandidateFG (sigma := sigma)
          (Sum.inr (Sum.inr a))) :=
      (separatedCandidateFG_simple_iff L _).2 ⟨a, Or.inr rfl⟩
    have hsTarget := (Simple.iff_of_iso e).1 hsSource
    obtain ⟨c, h | h⟩ := (separatedCandidateFG_simple_iff L _).1 hsTarget
    · cases h
    · cases h
  · exfalso
    let DB := moduleSeparatedData (S := S) (J := J)
      (sigma.obj (Sum.inr b)).obj
    letI : Nontrivial (sigma.obj (Sum.inr b)) :=
      (sigma.indecomposable (Sum.inr b)).nontrivial
    letI : Nontrivial DB.top :=
      moduleSeparatedData_top_nontrivial (sigma.obj (Sum.inr b))
    let eTop : DB.top ≃ₗ[S]
        (freeData (S := S) (J := J)
          (sigma.obj (Sum.inr a)).obj).top :=
      isoTopLinearEquiv eData.symm
    obtain ⟨t, ht⟩ := exists_ne (0 : DB.top)
    apply ht
    apply eTop.injective
    exact Subsingleton.elim _ _
  · let eOriginalData := moduleSeparatedDataIsoOfFreeDataIso L a b eData
    have h : (Sum.inr a : Nonsimple ⊕ Vertex) = Sum.inr b :=
      originalIndex_eq_of_moduleSeparatedData_iso
        (sigma := sigma) eOriginalData
    exact congrArg (fun q : Vertex ↦ Sum.inr (Sum.inr q)) (Sum.inr.inj h)

/-- The index chosen by completeness of the target skeleton for a canonical
candidate. -/
def separatedCandidateIndex
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) : kappa :=
  Classical.choose
    (tau.complete (separatedCandidateFG (sigma := sigma) i)
      (separatedCandidateFG_indecomposable L i))

/-- The chosen candidate isomorphism into the target skeleton. -/
def separatedCandidateIso
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    separatedCandidateFG (sigma := sigma) i ≅
      tau.obj (separatedCandidateIndex tau L i) :=
  Classical.choice
    (Classical.choose_spec
      (tau.complete (separatedCandidateFG (sigma := sigma) i)
        (separatedCandidateFG_indecomposable L i)))

/-- Distinct canonical candidates are sent to distinct labels in the target
skeleton. -/
theorem separatedCandidateIndex_injective
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    Function.Injective (separatedCandidateIndex tau L) := by
  intro i j hij
  apply separatedCandidate_eq_of_iso L
  exact separatedCandidateIso tau L i ≪≫
    eqToIso (congrArg tau.obj hij) ≪≫
    (separatedCandidateIso tau L j).symm

/-- Every label in the target skeleton is represented by a canonical
candidate. -/
theorem separatedCandidateIndex_surjective
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    Function.Surjective (separatedCandidateIndex tau L) := by
  intro k
  obtain ⟨i, ⟨e⟩⟩ := exists_separatedCandidateFG_iso tau L k
  refine ⟨i, ?_⟩
  exact tau.eq_of_iso
    ⟨(separatedCandidateIso tau L i).symm ≪≫ e⟩

/-- The three canonical families give exactly the labels of any complete
duplicate-free target skeleton. -/
noncomputable def separatedCandidateEquiv
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma) :
    Nonsimple ⊕ (Vertex ⊕ Vertex) ≃ kappa :=
  Equiv.ofBijective (separatedCandidateIndex tau L)
    ⟨separatedCandidateIndex_injective tau L,
      separatedCandidateIndex_surjective tau L⟩

@[simp]
theorem separatedCandidateEquiv_apply
    (L : OriginalNonsimpleLabelData Nonsimple Vertex sigma)
    (i : Nonsimple ⊕ (Vertex ⊕ Vertex)) :
    separatedCandidateEquiv tau L i = separatedCandidateIndex tau L i :=
  rfl

end QuotientSubmoduleEquidistribution.RadicalSquareZero
