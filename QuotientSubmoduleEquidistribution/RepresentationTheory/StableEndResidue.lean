import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleRadicalQuotient
import QuotientSubmoduleEquidistribution.RepresentationTheory.StableQuotients

/-!
# Residue functionals on projective-stable endomorphisms

For a nonprojective indecomposable finite-length module `X`, every
endomorphism factoring through a projective is a nonretraction.  Consequently
the additive quotient of `End(X)` by its nonretractions receives a canonical
map from the projective-stable endomorphism group.  This map detects the
identity and kills every nonretraction.

The construction isolates the local functional used by the classical
Auslander--Reiten socle argument.  It is classification-free and does not
construct a Hom--Ext duality or an almost-split sequence.

The skeleton specialization currently places module carriers in the ring's
universe, as required by the existing projective-stable quotient API; this is
an implementation restriction rather than a mathematical hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution

universe uC vC uQ vQ uOmega

/-- An additive functional on stable endomorphisms which detects the identity
and kills the image of every ambient nonretraction. -/
structure StableEndIdentityFunctional
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    (Q : C ⥤ QCat) (X : C) (Omega : Type uOmega) [AddCommGroup Omega] where
  functional : (Q.obj X ⟶ Q.obj X) →+ Omega
  identity_ne_zero : functional (𝟙 (Q.obj X)) ≠ 0
  nonretraction_eq_zero :
    ∀ (r : X ⟶ X), ¬ IsSplitEpi r → functional (Q.map r) = 0

namespace StableEndIdentityFunctional

variable
    {C : Type uC} [Category.{vC} C]
    {QCat : Type uQ} [Category.{vQ} QCat] [Preadditive QCat]
    {Q : C ⥤ QCat} {X : C}
    {Omega : Type uOmega} [AddCommGroup Omega]

/-- Postcompose an identity-detecting stable functional with any additive map
which does not kill its value on the identity.  No injectivity hypothesis is
needed. -/
def postcomp (F : StableEndIdentityFunctional Q X Omega)
    {Omega' : Type*} [AddCommGroup Omega']
    (phi : Omega →+ Omega')
    (hphi : phi (F.functional (𝟙 (Q.obj X))) ≠ 0) :
    StableEndIdentityFunctional Q X Omega' where
  functional := phi.comp F.functional
  identity_ne_zero := hphi
  nonretraction_eq_zero := by
    intro r hr
    rw [AddMonoidHom.comp_apply, F.nonretraction_eq_zero r hr, map_zero]

end StableEndIdentityFunctional

namespace IndecomposableSkeleton

open QuotientSubmoduleEquidistribution.RingelStable

universe uR uIota

variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{uR, uIota, uR} R Iota)

omit [IsNoetherianRing R] in
/-- A split-epimorphic endomorphism which factors through a projective makes
its source projective. -/
theorem projective_of_factorsThroughProjective_of_isSplitEpi
    {X : FGModuleCat.{uR} R} {f : X ⟶ X}
    (hf : FactorsThroughProjective f) (hsplit : IsSplitEpi f) :
    Projective X := by
  letI : Projective hf.middle := hf.projective
  letI : IsSplitEpi f := hsplit
  let r : Retract X hf.middle :=
    { i := section_ f ≫ hf.left
      r := hf.right
      retract := by rw [Category.assoc, hf.fac, IsSplitEpi.id] }
  exact r.projective

omit [IsNoetherianRing R] in
/-- A map through a projective cannot be a retraction when its source is
nonprojective. -/
theorem not_isSplitEpi_of_factorsThroughProjective_of_not_projective
    {X : FGModuleCat.{uR} R} (hX : ¬ Projective X) {f : X ⟶ X}
    (hf : FactorsThroughProjective f) : ¬ IsSplitEpi f := by
  intro hsplit
  exact hX
    (projective_of_factorsThroughProjective_of_isSplitEpi hf hsplit)

/-- The additive residue group of an indecomposable skeleton object: its
endomorphism group modulo the subgroup of nonretractions. -/
abbrev endResidue (x : Iota) :=
  (sigma.obj x ⟶ sigma.obj x) ⧸ sigma.radicalHomAddSubgroup x x

/-- The quotient map from endomorphisms to the additive residue group. -/
abbrev endResidueMap (x : Iota) :
    (sigma.obj x ⟶ sigma.obj x) →+ sigma.endResidue x :=
  QuotientAddGroup.mk' (sigma.radicalHomAddSubgroup x x)

/-- The residue class of the identity endomorphism. -/
abbrev endResidueIdentityClass (x : Iota) :
    sigma.endResidue x :=
  sigma.endResidueMap x (𝟙 (sigma.obj x))

@[simp]
theorem endResidueMap_eq_zero_iff (x : Iota)
    (r : sigma.obj x ⟶ sigma.obj x) :
    sigma.endResidueMap x r = 0 ↔ ¬ IsSplitEpi r := by
  change QuotientAddGroup.mk' (sigma.radicalHomAddSubgroup x x) r = 0 ↔
    ¬ IsSplitEpi r
  constructor
  · intro hzero
    exact (sigma.mem_radicalHomAddSubgroup_iff_not_isSplitEpi r).mp
      ((QuotientAddGroup.eq_zero_iff r).mp hzero)
  · intro hr
    exact (QuotientAddGroup.eq_zero_iff r).mpr
      ((sigma.mem_radicalHomAddSubgroup_iff_not_isSplitEpi r).mpr hr)

/-- The identity has a nonzero class in the additive endomorphism residue. -/
theorem endResidueIdentityClass_ne_zero (x : Iota) :
    sigma.endResidueIdentityClass x ≠ 0 := by
  rw [ne_eq, endResidueMap_eq_zero_iff, not_not]
  infer_instance

instance endResidue_nontrivial (x : Iota) :
    Nontrivial (sigma.endResidue x) :=
  ⟨⟨sigma.endResidueIdentityClass x, 0,
    sigma.endResidueIdentityClass_ne_zero x⟩⟩

/-- The residue map descends from concrete endomorphisms to the
projective-stable endomorphism group of a nonprojective representative. -/
def projectiveStableResidueMap (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) :
    ((projectiveStableFunctor (R := R)).obj (sigma.obj x) ⟶
        (projectiveStableFunctor (R := R)).obj (sigma.obj x)) →+
      sigma.endResidue x where
  toFun a := Quot.liftOn a
    (fun f ↦ sigma.endResidueMap x f)
    (by
      intro f g hfg
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      have hrel : projectiveStableRel (R := R) f g :=
        (HomRel.compClosure_iff_self
          (projectiveStableRel (R := R)) f g).mp hfg
      obtain ⟨hfactor⟩ := hrel
      exact (sigma.mem_radicalHomAddSubgroup_iff_not_isSplitEpi
        (f - g)).mpr
          (not_isSplitEpi_of_factorsThroughProjective_of_not_projective
            hx hfactor))
  map_zero' := rfl
  map_add' := by
    rintro ⟨f⟩ ⟨g⟩
    exact (QuotientAddGroup.mk'
      (sigma.radicalHomAddSubgroup x x)).map_add f g

@[simp]
theorem projectiveStableResidueMap_map (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) (f : sigma.obj x ⟶ sigma.obj x) :
    projectiveStableResidueMap sigma x hx
        ((projectiveStableFunctor (R := R)).map f) =
      sigma.endResidueMap x f := by
  rfl

@[simp]
theorem projectiveStableResidueMap_map_eq_zero_iff (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) (f : sigma.obj x ⟶ sigma.obj x) :
    projectiveStableResidueMap sigma x hx
        ((projectiveStableFunctor (R := R)).map f) = 0 ↔
      ¬ IsSplitEpi f := by
  rw [projectiveStableResidueMap_map, endResidueMap_eq_zero_iff]

/-- Every endomorphism residue class is represented by a projective-stable
endomorphism. -/
theorem projectiveStableResidueMap_surjective (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) :
    Function.Surjective (projectiveStableResidueMap sigma x hx) := by
  rintro ⟨f⟩
  exact ⟨(projectiveStableFunctor (R := R)).map f, rfl⟩

/-- The stable residue functional does not kill the identity. -/
theorem projectiveStableResidueMap_identity_ne_zero (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) :
    projectiveStableResidueMap sigma x hx
        (𝟙 ((projectiveStableFunctor (R := R)).obj (sigma.obj x))) ≠ 0 := by
  rw [← (projectiveStableFunctor (R := R)).map_id,
    projectiveStableResidueMap_map]
  exact sigma.endResidueIdentityClass_ne_zero x

/-- The stable residue functional kills every nonretraction endomorphism. -/
theorem projectiveStableResidueMap_nonretraction_eq_zero (x : Iota)
    (hx : ¬ Projective (sigma.obj x))
    (r : sigma.obj x ⟶ sigma.obj x) (hr : ¬ IsSplitEpi r) :
    projectiveStableResidueMap sigma x hx
        ((projectiveStableFunctor (R := R)).map r) = 0 := by
  exact (projectiveStableResidueMap_map_eq_zero_iff sigma x hx r).mpr hr

/-- The canonical identity-detecting functional with the endomorphism residue
group itself as coefficients. -/
def projectiveStableEndIdentityFunctional (x : Iota)
    (hx : ¬ Projective (sigma.obj x)) :
    StableEndIdentityFunctional
      (projectiveStableFunctor (R := R)) (sigma.obj x)
      (sigma.endResidue x) where
  functional := projectiveStableResidueMap sigma x hx
  identity_ne_zero :=
    projectiveStableResidueMap_identity_ne_zero sigma x hx
  nonretraction_eq_zero :=
    projectiveStableResidueMap_nonretraction_eq_zero sigma x hx

/-- For a prescribed coefficient group, it suffices to give an additive map
from the endomorphism residue which does not kill the identity class. -/
def projectiveStableEndIdentityFunctionalOfResidueMap
    (x : Iota) (hx : ¬ Projective (sigma.obj x))
    {Omega : Type uOmega} [AddCommGroup Omega]
    (phi : sigma.endResidue x →+ Omega)
    (hphi : phi (sigma.endResidueIdentityClass x) ≠ 0) :
    StableEndIdentityFunctional
      (projectiveStableFunctor (R := R)) (sigma.obj x) Omega :=
  (projectiveStableEndIdentityFunctional sigma x hx).postcomp phi (by
    change phi (projectiveStableResidueMap sigma x hx
      (𝟙 ((projectiveStableFunctor (R := R)).obj (sigma.obj x)))) ≠ 0
    rw [← (projectiveStableFunctor (R := R)).map_id,
      projectiveStableResidueMap_map]
    exact hphi)

end IndecomposableSkeleton

end QuotientSubmoduleEquidistribution
