import QuotientSubmoduleEquidistribution.RepresentationTheory.ConormalModules

/-!
# Intrinsic basic normal and conormal modules

This file upgrades the canonical-support classifications to
isomorphism-invariant predicates on arbitrary finitely generated modules.
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

/-- A multiplicity-free decomposition of an arbitrary module into the
chosen indecomposable representatives.  It is the intrinsic witness that
the module is basic. -/
structure BasicDecomposition (M : FGModuleCat.{w} R) where
  index : ℕ
  label : Fin index → ι
  label_injective : Function.Injective label
  iso : M ≅ σ.sum index label

namespace BasicDecomposition

/-- The finite support underlying a multiplicity-free decomposition. -/
def support {M : FGModuleCat.{w} R}
    (d : BasicDecomposition σ M) :
    FiniteSupport (ι := ι) :=
  ⟨Set.range d.label, Set.finite_range d.label⟩

/-- Reindex the decomposition by the canonical enumeration of its finite
support. -/
noncomputable def reindexEquiv {M : FGModuleCat.{w} R}
    (d : BasicDecomposition σ M) :
    Fin d.index ≃ d.support.index :=
  (Equiv.ofInjective d.label d.label_injective).trans
    d.support.equivFin

theorem support_label_reindexEquiv {M : FGModuleCat.{w} R}
    (d : BasicDecomposition σ M) (t : Fin d.index) :
    d.support.label (reindexEquiv σ d t) = d.label t := by
  change
    d.support.label
      (d.support.equivFin
        ((Equiv.ofInjective d.label d.label_injective) t)) =
      d.label t
  rw [FiniteSupport.label_equivFin]
  rfl

/-- A multiplicity-free decomposition canonically identifies the module
with the duplicate-free basic module on its support. -/
noncomputable def canonicalIso {M : FGModuleCat.{w} R}
    (d : BasicDecomposition σ M) :
    M ≅ σ.basicModule d.support :=
  d.iso ≪≫
    biproduct.whiskerEquiv (reindexEquiv σ d)
      (fun t ↦
        eqToIso
          (congrArg σ.obj
            (support_label_reindexEquiv σ d t)))

/-- Transport a basic decomposition across an isomorphism. -/
def transport {M N : FGModuleCat.{w} R}
    (e : M ≅ N) (d : BasicDecomposition σ M) :
    BasicDecomposition σ N where
  index := d.index
  label := d.label
  label_injective := d.label_injective
  iso := e.symm ≪≫ d.iso

@[simp]
theorem transport_support {M N : FGModuleCat.{w} R}
    (e : M ≅ N) (d : BasicDecomposition σ M) :
    (transport σ e d).support = d.support :=
  rfl

end BasicDecomposition

/-- An arbitrary module is intrinsically basic normal if it has a
multiplicity-free indecomposable decomposition whose finite support is
paper-normal. -/
def IsIntrinsicBasicNormal (M : FGModuleCat.{w} R) : Prop :=
  ∃ d : BasicDecomposition σ M, IsPaperNormal σ d.support

/-- Intrinsic basic normality is invariant under module isomorphism. -/
theorem isIntrinsicBasicNormal_iff_of_iso
    {M N : FGModuleCat.{w} R} (e : M ≅ N) :
    IsIntrinsicBasicNormal σ M ↔ IsIntrinsicBasicNormal σ N := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨BasicDecomposition.transport σ e d, by simpa using hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨BasicDecomposition.transport σ e.symm d, by simpa using hd⟩

/-- The range of the canonical enumeration is the original support. -/
theorem FiniteSupport.range_label
    (B : FiniteSupport (ι := ι)) :
    Set.range B.label = B.1 := by
  ext i
  constructor
  · rintro ⟨t, rfl⟩
    exact B.label_mem t
  · intro hi
    obtain ⟨t, ht⟩ := B.exists_label_eq hi
    exact ⟨t, ht⟩

/-- Every canonical basic normal module is intrinsically basic normal. -/
theorem BasicNormalModule.isIntrinsic
    (B : BasicNormalModule σ) :
    IsIntrinsicBasicNormal σ (BasicNormalModule.object σ B) := by
  let d : BasicDecomposition σ (BasicNormalModule.object σ B) :=
    { index := Nat.card B.1.1
      label := B.1.label
      label_injective := B.1.label_injective
      iso := Iso.refl _ }
  refine ⟨d, ?_⟩
  have hs : d.support = B.1 := by
    apply Subtype.ext
    exact B.1.range_label
  rw [hs]
  exact B.2

/-- An intrinsically basic normal object is isomorphic to a unique
canonical basic normal module. -/
theorem existsUnique_basicNormalModule
    (M : FGModuleCat.{w} R) (hM : IsIntrinsicBasicNormal σ M) :
    ∃! B : BasicNormalModule σ,
      Nonempty (M ≅ BasicNormalModule.object σ B) := by
  obtain ⟨d, hd⟩ := hM
  let B : BasicNormalModule σ := ⟨d.support, hd⟩
  refine ⟨B, ⟨BasicDecomposition.canonicalIso σ d⟩, ?_⟩
  intro C hC
  apply Subtype.ext
  apply finiteSupport_eq_of_basicModule_iso σ
  obtain ⟨eC⟩ := hC
  exact
    ⟨eC.symm ≪≫ BasicDecomposition.canonicalIso σ d⟩

/-- The intrinsic basic-normal isomorphism classes, defined as an actual
isomorphism-invariant subtype of the module skeleton. -/
def IntrinsicBasicNormalIsoClass :=
  {X : Skeleton (FGModuleCat.{w} R) //
    IsIntrinsicBasicNormal σ
      ((fromSkeleton (FGModuleCat.{w} R)).obj X)}

/-- Intrinsic membership in the skeleton is equivalent to belonging to
the existing image of canonical basic normal modules. -/
theorem intrinsicBasicNormal_iff_canonicalImage
    (X : Skeleton (FGModuleCat.{w} R)) :
    IsIntrinsicBasicNormal σ
        ((fromSkeleton (FGModuleCat.{w} R)).obj X) ↔
      ∃ B : BasicNormalModule σ,
        X = toSkeleton (BasicNormalModule.object σ B) := by
  constructor
  · intro hX
    obtain ⟨B, hB, -⟩ :=
      existsUnique_basicNormalModule σ
        ((fromSkeleton (FGModuleCat.{w} R)).obj X) hX
    have heq :
        toSkeleton
            ((fromSkeleton (FGModuleCat.{w} R)).obj X) =
          toSkeleton (BasicNormalModule.object σ B) :=
      toSkeleton_eq_toSkeleton_iff.mpr hB
    rw [toSkeleton_fromSkeleton_obj] at heq
    exact ⟨B, heq⟩
  · rintro ⟨B, rfl⟩
    exact
      (isIntrinsicBasicNormal_iff_of_iso σ
        (fromSkeletonToSkeletonIso
          (BasicNormalModule.object σ B))).2
        (BasicNormalModule.isIntrinsic σ B)

/-- The intrinsic skeleton subtype is exactly the previously constructed
canonical-image subtype. -/
def intrinsicBasicNormalIsoClassEquiv :
    IntrinsicBasicNormalIsoClass σ ≃
      BasicNormalModule.IsoClass σ where
  toFun X :=
    ⟨X.1,
      (intrinsicBasicNormal_iff_canonicalImage σ X.1).1 X.2⟩
  invFun X :=
    ⟨X.1,
      (intrinsicBasicNormal_iff_canonicalImage σ X.1).2 X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Consequently, intrinsic basic-normal isomorphism classes are
classified by compact quotient-closed supports. -/
noncomputable def intrinsicBasicNormalIsoClassEquivCompactClosed
    (hfin : σ.qClosure.IsFinitary)
    (hae : σ.qClosure.IsAntiExchange) :
    IntrinsicBasicNormalIsoClass σ ≃
      σ.qClosure.CompactClosed :=
  (intrinsicBasicNormalIsoClassEquiv σ).trans
    (BasicNormalModule.isoClassEquivCompactClosed σ hfin hae)

/-- An arbitrary module is intrinsically basic conormal if it has a
multiplicity-free indecomposable decomposition whose support is
paper-conormal. -/
def IsIntrinsicBasicConormal (M : FGModuleCat.{w} R) : Prop :=
  ∃ d : BasicDecomposition σ M, IsPaperConormal σ d.support

/-- Intrinsic basic conormality is invariant under module isomorphism. -/
theorem isIntrinsicBasicConormal_iff_of_iso
    {M N : FGModuleCat.{w} R} (e : M ≅ N) :
    IsIntrinsicBasicConormal σ M ↔
      IsIntrinsicBasicConormal σ N := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨BasicDecomposition.transport σ e d, by simpa using hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨BasicDecomposition.transport σ e.symm d, by simpa using hd⟩

/-- Every canonical basic conormal module is intrinsically basic
conormal. -/
theorem BasicConormalModule.isIntrinsic
    (B : BasicConormalModule σ) :
    IsIntrinsicBasicConormal σ
      (BasicConormalModule.object σ B) := by
  let d : BasicDecomposition σ
      (BasicConormalModule.object σ B) :=
    { index := Nat.card B.1.1
      label := B.1.label
      label_injective := B.1.label_injective
      iso := Iso.refl _ }
  refine ⟨d, ?_⟩
  have hs : d.support = B.1 := by
    apply Subtype.ext
    exact B.1.range_label
  rw [hs]
  exact B.2

/-- An intrinsically basic conormal object is isomorphic to a unique
canonical basic conormal module. -/
theorem existsUnique_basicConormalModule
    (M : FGModuleCat.{w} R)
    (hM : IsIntrinsicBasicConormal σ M) :
    ∃! B : BasicConormalModule σ,
      Nonempty (M ≅ BasicConormalModule.object σ B) := by
  obtain ⟨d, hd⟩ := hM
  let B : BasicConormalModule σ := ⟨d.support, hd⟩
  refine
    ⟨B, ⟨BasicDecomposition.canonicalIso σ d⟩, ?_⟩
  intro C hC
  apply Subtype.ext
  apply finiteSupport_eq_of_basicModule_iso σ
  obtain ⟨eC⟩ := hC
  exact
    ⟨eC.symm ≪≫ BasicDecomposition.canonicalIso σ d⟩

/-- The intrinsic basic-conormal isomorphism classes as an
isomorphism-invariant subtype of the module skeleton. -/
def IntrinsicBasicConormalIsoClass :=
  {X : Skeleton (FGModuleCat.{w} R) //
    IsIntrinsicBasicConormal σ
      ((fromSkeleton (FGModuleCat.{w} R)).obj X)}

/-- Intrinsic conormal membership in the skeleton is equivalent to the
existing canonical-image condition. -/
theorem intrinsicBasicConormal_iff_canonicalImage
    (X : Skeleton (FGModuleCat.{w} R)) :
    IsIntrinsicBasicConormal σ
        ((fromSkeleton (FGModuleCat.{w} R)).obj X) ↔
      ∃ B : BasicConormalModule σ,
        X = toSkeleton
          (BasicConormalModule.object σ B) := by
  constructor
  · intro hX
    obtain ⟨B, hB, -⟩ :=
      existsUnique_basicConormalModule σ
        ((fromSkeleton (FGModuleCat.{w} R)).obj X) hX
    have heq :
        toSkeleton
            ((fromSkeleton (FGModuleCat.{w} R)).obj X) =
          toSkeleton
            (BasicConormalModule.object σ B) :=
      toSkeleton_eq_toSkeleton_iff.mpr hB
    rw [toSkeleton_fromSkeleton_obj] at heq
    exact ⟨B, heq⟩
  · rintro ⟨B, rfl⟩
    exact
      (isIntrinsicBasicConormal_iff_of_iso σ
        (fromSkeletonToSkeletonIso
          (BasicConormalModule.object σ B))).2
        (BasicConormalModule.isIntrinsic σ B)

/-- The intrinsic basic-conormal skeleton subtype is exactly the existing
canonical-image subtype. -/
def intrinsicBasicConormalIsoClassEquiv :
    IntrinsicBasicConormalIsoClass σ ≃
      BasicConormalModule.IsoClass σ where
  toFun X :=
    ⟨X.1,
      (intrinsicBasicConormal_iff_canonicalImage σ X.1).1 X.2⟩
  invFun X :=
    ⟨X.1,
      (intrinsicBasicConormal_iff_canonicalImage σ X.1).2 X.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Consequently, intrinsic basic-conormal isomorphism classes are
classified by compact submodule-closed supports. -/
noncomputable def intrinsicBasicConormalIsoClassEquivCompactClosed
    (hfin : σ.sClosure.IsFinitary)
    (hae : σ.sClosure.IsAntiExchange) :
    IntrinsicBasicConormalIsoClass σ ≃
      σ.sClosure.CompactClosed :=
  (intrinsicBasicConormalIsoClassEquiv σ).trans
    (BasicConormalModule.isoClassEquivCompactClosed σ hfin hae)

end QuotientSubmoduleEquidistribution.IndecomposableSkeleton
