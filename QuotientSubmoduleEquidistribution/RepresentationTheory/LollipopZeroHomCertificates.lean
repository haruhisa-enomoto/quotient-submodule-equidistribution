import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopTableCertificates

/-!
# Turning Hom-vanishing rows into lollipop omission certificates

The concrete quiver calculation naturally proves that every Hom from a
selected named indecomposable to an omitted target is zero (or dually that
every Hom from the target to a selected object is zero).  The maintained
lollipop interface asks instead for a trace bound or a reject witness.

These helper lemmas close that small API gap.  They are independent of the
lollipop algebra and can be used as soon as a concrete bound-quiver/module
bridge supplies the relevant Hom-vanishing rows.
-/

noncomputable section

open Set
open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates

universe u v w

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {ι : Type v} [Finite ι]
  (σ : IndecomposableSkeleton.{u, v, w} R ι)

namespace Quotient

/-- A zero Hom row gives an omission certificate with bound `⊥`. -/
def omissionCertificateOfHomEqZero
    {S : Set ι} {j : ι}
    (hnot : j ∉ S)
    (hzero : ∀ i : ι, i ∈ S → ∀ f : σ.obj i ⟶ σ.obj j, f = 0) :
    OmissionCertificate σ S j where
  not_mem := hnot
  bound := ⊥
  bound_ne_top := by
    letI := (σ.indecomposable j).nontrivial
    exact bot_ne_top
  trace_le_bound := by
    rw [σ.trace_eq_bot_of_forall_hom_eq_zero hzero]

end Quotient

namespace Submodule

/-- A zero dual Hom row gives an omission certificate with witness `⊤`. -/
def omissionCertificateOfHomEqZero
    {S : Set ι} {j : ι}
    (hnot : j ∉ S)
    (hzero : ∀ i : ι, i ∈ S → ∀ f : σ.obj j ⟶ σ.obj i, f = 0) :
    OmissionCertificate σ S j where
  not_mem := hnot
  witness := ⊤
  witness_ne_bot := by
    letI := (σ.indecomposable j).nontrivial
    exact top_ne_bot
  witness_le_reject := by
    rw [σ.reject_eq_top_of_forall_hom_eq_zero hzero]

end Submodule

end QuotientSubmoduleEquidistribution.BottomLevels.LollipopTableCertificates
