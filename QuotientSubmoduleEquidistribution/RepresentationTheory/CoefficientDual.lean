import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Duals with coefficients in an injective module

For a commutative ring `k` and a `k`-module `E`, this file develops the
annihilator calculus for the coefficient dual `Hom_k(-, E)`.  It first
identifies the dual of a quotient with the functionals that vanish on its
denominator; this part requires no injectivity hypothesis.

If `E` is injective, restriction of functionals is surjective.  Consequently,
for `N ⊆ H ⊆ M`, the quotient of the ambient annihilator of `N` by the
ambient annihilator of `H` is canonically the `E`-valued dual of `H / N`.
This is the linear-algebra step needed to pass from a presentation quotient
to the dual of projective-stable Hom.

The coefficient module is abstract.  No Matlis module, Artin duality, concrete
algebra, or module classification is constructed here.
-/

noncomputable section

open LinearMap

namespace QuotientSubmoduleEquidistribution.CoefficientDual

universe uk uM uN uE

variable {k : Type uk} {M : Type uM} {E : Type uE} [CommRing k]
  [AddCommGroup M] [Module k M]
  [AddCommGroup E] [Module k E]

/-- The submodule of `E`-valued linear functionals that vanish on `N`. -/
def annihilator (N : Submodule k M) : Submodule k (M →ₗ[k] E) :=
  LinearMap.ker (LinearMap.lcomp k E N.subtype)

@[simp]
theorem mem_annihilator_iff (N : Submodule k M) (phi : M →ₗ[k] E) :
    phi ∈ annihilator (E := E) N ↔ ∀ n ∈ N, phi n = 0 := by
  rw [annihilator, LinearMap.mem_ker]
  change phi.comp N.subtype = 0 ↔ _
  constructor
  · intro h n hn
    have hn' := LinearMap.congr_fun h ⟨n, hn⟩
    exact hn'
  · intro h
    ext n
    exact h n.1 n.2

/-- The coefficient dual of `M / N` is canonically the annihilator of `N`
inside the coefficient dual of `M`.  This does not require `E` to be
injective. -/
def quotientDualEquivAnnihilator (N : Submodule k M) :
    ((M ⧸ N) →ₗ[k] E) ≃ₗ[k] annihilator (E := E) N where
  toFun phi := ⟨phi.comp N.mkQ, by
    rw [mem_annihilator_iff]
    intro n hn
    change phi (Submodule.Quotient.mk n) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hn, map_zero]⟩
  invFun phi := N.liftQ phi.1 (by
    intro n hn
    exact (mem_annihilator_iff N phi.1).mp phi.2 n hn)
  left_inv phi := by
    ext x
    rfl
  right_inv phi := by
    ext x
    rfl
  map_add' phi psi := by
    ext x
    rfl
  map_smul' a phi := by
    ext x
    rfl

@[simp]
theorem quotientDualEquivAnnihilator_apply
    (N : Submodule k M) (phi : (M ⧸ N) →ₗ[k] E) (m : M) :
    (quotientDualEquivAnnihilator (E := E) N phi).1 m =
      phi (Submodule.Quotient.mk m) :=
  rfl

/-- For an injective coefficient module, precomposition by `t` has exactly
the functionals annihilating `ker t` as its range. -/
theorem range_lcomp_eq_annihilator_ker
    {N : Type uN} [AddCommGroup N] [Module k N]
    [Small.{uE} k] [Module.Injective k E]
    (t : M →ₗ[k] N) :
    LinearMap.range (LinearMap.lcomp k E t) =
      annihilator (E := E) (LinearMap.ker t) := by
  apply le_antisymm
  · rintro phi ⟨psi, rfl⟩
    rw [mem_annihilator_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    simp [LinearMap.lcomp_apply, hm]
  · intro phi hphi
    have hker : LinearMap.ker t ≤ LinearMap.ker phi := by
      intro m hm
      rw [LinearMap.mem_ker]
      exact (mem_annihilator_iff (LinearMap.ker t) phi).mp hphi m hm
    let psi : LinearMap.range t →ₗ[k] E :=
      (LinearMap.ker t).liftQ phi hker ∘ₗ
        t.quotKerEquivRange.symm.toLinearMap
    obtain ⟨extension, hextension⟩ :=
      Module.Injective.extension_property k E (LinearMap.range t) N
        (LinearMap.range t).subtype Subtype.val_injective psi
    refine ⟨extension, ?_⟩
    ext m
    change extension (t m) = phi m
    have hvalue := LinearMap.congr_fun hextension
      ⟨t m, LinearMap.mem_range_self t m⟩
    calc
      extension (t m) =
          psi ⟨t m, LinearMap.mem_range_self t m⟩ := by
        simpa using hvalue
      _ = phi m := by
        simp [psi, LinearMap.quotKerEquivRange_symm_apply_image,
          Submodule.liftQ_apply]

/-- Functionals on the ambient module that vanish on a submodule of `H`. -/
def ambientAnnihilator (H : Submodule k M) (N : Submodule k H) :
    Submodule k (M →ₗ[k] E) :=
  annihilator (E := E) (N.map H.subtype)

/-- Inside the functionals vanishing on `N`, those that vanish on all of
`H`. -/
def wholeAnnihilatorIn (H : Submodule k M) (N : Submodule k H) :
    Submodule k (ambientAnnihilator (E := E) H N) :=
  (annihilator (E := E) H).comap
    (ambientAnnihilator (E := E) H N).subtype

/-- Restrict an ambient functional vanishing on `N` to the quotient
`H / N`. -/
def restrictToSubquotient (H : Submodule k M) (N : Submodule k H) :
    ambientAnnihilator (E := E) H N →ₗ[k] ((H ⧸ N) →ₗ[k] E) where
  toFun phi := N.liftQ (phi.1.comp H.subtype) (by
    intro n hn
    apply (mem_annihilator_iff (E := E) (N.map H.subtype) phi.1).mp phi.2
    exact ⟨n, hn, rfl⟩)
  map_add' phi psi := by
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := N.mkQ_surjective q
    rfl
  map_smul' a phi := by
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := N.mkQ_surjective q
    rfl

/-- The kernel of restriction to `H / N` consists precisely of the
functionals that vanish on all of `H`. -/
theorem ker_restrictToSubquotient
    (H : Submodule k M) (N : Submodule k H) :
    LinearMap.ker (restrictToSubquotient (E := E) H N) =
      wholeAnnihilatorIn (E := E) H N := by
  ext phi
  constructor
  · intro hphi
    change phi.1 ∈ annihilator (E := E) H
    rw [mem_annihilator_iff]
    intro h hh
    have hz := LinearMap.congr_fun hphi (Submodule.Quotient.mk ⟨h, hh⟩)
    exact hz
  · intro hphi
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro q
    obtain ⟨h, rfl⟩ := N.mkQ_surjective q
    exact (mem_annihilator_iff (E := E) H phi.1).mp hphi h.1 h.2

/-- If `E` is injective, every functional on `H / N` extends to an ambient
functional on `M` that vanishes on `N`. -/
theorem restrictToSubquotient_surjective
    [Small.{uE} k] [Module.Injective k E]
    (H : Submodule k M) (N : Submodule k H) :
    Function.Surjective (restrictToSubquotient (E := E) H N) := by
  intro psi
  let g : H →ₗ[k] E := psi.comp N.mkQ
  obtain ⟨extension, hextension⟩ :=
    Module.Injective.extension_property k E H M H.subtype
      Subtype.val_injective g
  let phi : ambientAnnihilator (E := E) H N := ⟨extension, by
    change extension ∈ annihilator (E := E) (N.map H.subtype)
    rw [mem_annihilator_iff]
    intro m hm
    obtain ⟨n, hn, rfl⟩ := hm
    have hvalue := LinearMap.congr_fun hextension n
    change extension (H.subtype n) = g n at hvalue
    change extension (H.subtype n) = 0
    rw [hvalue]
    change psi (Submodule.Quotient.mk n) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).mpr hn, map_zero]⟩
  refine ⟨phi, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨h, rfl⟩ := N.mkQ_surjective q
  exact LinearMap.congr_fun hextension h

/-- Quotienting nested annihilators gives the coefficient dual of the
corresponding subquotient. -/
def nestedAnnihilatorQuotientEquiv
    [Small.{uE} k] [Module.Injective k E]
    (H : Submodule k M) (N : Submodule k H) :
    (ambientAnnihilator (E := E) H N ⧸
        wholeAnnihilatorIn (E := E) H N) ≃ₗ[k]
      ((H ⧸ N) →ₗ[k] E) :=
  (Submodule.quotEquivOfEq
      (wholeAnnihilatorIn (E := E) H N)
      (LinearMap.ker (restrictToSubquotient (E := E) H N))
      (ker_restrictToSubquotient (E := E) H N).symm).trans
    ((restrictToSubquotient (E := E) H N).quotKerEquivOfSurjective
      (restrictToSubquotient_surjective (E := E) H N))

@[simp]
theorem nestedAnnihilatorQuotientEquiv_mk_apply
    [Small.{uE} k] [Module.Injective k E]
    (H : Submodule k M) (N : Submodule k H)
    (phi : ambientAnnihilator (E := E) H N) (h : H) :
    nestedAnnihilatorQuotientEquiv (E := E) H N
        (Submodule.Quotient.mk phi) (Submodule.Quotient.mk h) =
      phi.1 h.1 := by
  rfl

end QuotientSubmoduleEquidistribution.CoefficientDual
