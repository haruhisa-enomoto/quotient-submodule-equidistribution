import OpConjecture.RepresentationDirected.FiniteDimensionalAlmostSplitExtBridge
import OpConjecture.RepresentationDirected.FiniteDimensionalMixedCoordinates
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finrank and complement assembly for effective lifting

This file contains the abstract linear-algebra and categorical
postcomposition arguments used in the directed effective-lifting proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OpConjecture.RepresentationDirected

universe uK uC vC

variable {K : Type uK} [Field K]
  {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear K C]

/-- Postcomposition by a categorical morphism as a linear map on Hom spaces. -/
def postcompLinearMap {X T Y : C} (f : T ⟶ Y) :
    (X ⟶ T) →ₗ[K] (X ⟶ Y) where
  toFun a := a ≫ f
  map_add' a b := by simp
  map_smul' r a := by simp

@[simp]
theorem postcompLinearMap_apply {X T Y : C} (f : T ⟶ Y) (a : X ⟶ T) :
    postcompLinearMap (K := K) f a = a ≫ f :=
  rfl

/-- Transporting the source of a morphism across an isomorphism preserves
bijectivity of postcomposition from every fixed test object. -/
theorem postcompLinearMap_bijective_comp_iso
    {X S T Y : C} (e : S ≅ T) (f : T ⟶ Y)
    (hf : Function.Bijective
      (postcompLinearMap (K := K) (X := X) f)) :
    Function.Bijective
      (postcompLinearMap (K := K) (X := X) (e.hom ≫ f)) := by
  constructor
  · intro a b hab
    change a ≫ (e.hom ≫ f) = b ≫ (e.hom ≫ f) at hab
    apply (cancel_mono e.hom).1
    apply hf.1
    change (a ≫ e.hom) ≫ f = (b ≫ e.hom) ≫ f
    simpa only [Category.assoc] using hab
  · intro y
    obtain ⟨t, ht⟩ := hf.2 y
    change t ≫ f = y at ht
    refine ⟨t ≫ e.inv, ?_⟩
    change (t ≫ e.inv) ≫ e.hom ≫ f = y
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ht

/-- Orthogonality to the categorical kernel makes postcomposition injective. -/
theorem postcompLinearMap_injective_of_kernel_orthogonal
    {X T Y : C} (f : T ⟶ Y) [HasKernel f]
    (hzero : ∀ a : X ⟶ kernel f, a = 0) :
    Function.Injective (postcompLinearMap (K := K) (X := X) f) := by
  intro a b hab
  apply sub_eq_zero.mp
  change a ≫ f = b ≫ f at hab
  have hab0 : (a - b) ≫ f = 0 := by
    simp only [Preadditive.sub_comp, hab, sub_self]
  let t : X ⟶ kernel f := kernel.lift f (a - b) hab0
  calc
    a - b = t ≫ kernel.ι f := (kernel.lift_ι f (a - b) hab0).symm
    _ = 0 := by rw [hzero t, zero_comp]

/-- A nonzero map to the kernel witnesses failure of injectivity. -/
theorem postcompLinearMap_not_injective_of_nonzero_kernel_hom
    {X T Y : C} (f : T ⟶ Y) [HasKernel f]
    (g : X ⟶ kernel f) (hg : g ≠ 0) :
    ¬ Function.Injective (postcompLinearMap (K := K) (X := X) f) := by
  intro hinj
  have hgi : g ≫ kernel.ι f ≠ 0 := by
    intro h
    apply hg
    exact (cancel_mono (kernel.ι f)).mp (by simpa using h)
  apply hgi
  apply hinj
  simp [postcompLinearMap, kernel.condition]

/-- Displayed-kernel form of the preceding witness. -/
theorem postcompLinearMap_not_injective_of_nonzero_left_hom
    {X Z T Y : C} (j : Z ⟶ T) (f : T ⟶ Y) [Mono j]
    (hjf : j ≫ f = 0) (g : X ⟶ Z) (hg : g ≠ 0) :
    ¬ Function.Injective (postcompLinearMap (K := K) (X := X) f) := by
  intro hinj
  have hgj : g ≫ j ≠ 0 := by
    intro h
    apply hg
    exact (cancel_mono j).mp (by simpa using h)
  apply hgj
  apply hinj
  simp [postcompLinearMap, Category.assoc, hjf]

/-- If the source finrank is at most the target finrank, a noninjective
linear map cannot be surjective. -/
theorem LinearMap.not_surjective_of_not_injective_of_finrank_le
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (L : V →ₗ[K] W)
    (hle : Module.finrank K V ≤ Module.finrank K W)
    (hni : ¬ Function.Injective L) :
    ¬ Function.Surjective L := by
  intro hsurj
  have hge : Module.finrank K W ≤ Module.finrank K V :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have heq : Module.finrank K V = Module.finrank K W :=
    Nat.le_antisymm hle hge
  exact hni
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hsurj)

/-- A projective source lifts through an epimorphism. -/
theorem postcompLinearMap_surjective_of_projective
    {X T Y : C} [Projective X] (f : T ⟶ Y) [Epi f] :
    Function.Surjective (postcompLinearMap (K := K) (X := X) f) := by
  intro a
  obtain ⟨b, hb⟩ := Projective.factors a f
  exact ⟨b, hb⟩

/-- Projectivity and the manuscript's finrank inequality rule out a
nonzero map into the kernel of an epimorphism. -/
theorem hom_kernel_eq_zero_of_projective_of_finrank_le
    {X T Y : C} [Projective X] (f : T ⟶ Y) [Epi f]
    [HasKernel f]
    [FiniteDimensional K (X ⟶ T)] [FiniteDimensional K (X ⟶ Y)]
    (hle : Module.finrank K (X ⟶ T) ≤ Module.finrank K (X ⟶ Y))
    (g : X ⟶ kernel f) : g = 0 := by
  by_contra hg
  exact (LinearMap.not_surjective_of_not_injective_of_finrank_le
      (postcompLinearMap (K := K) (X := X) f) hle
      (postcompLinearMap_not_injective_of_nonzero_kernel_hom
        (K := K) f g hg))
    (postcompLinearMap_surjective_of_projective (K := K) (X := X) f)

/-- Displayed-left-term version of the projective branch. -/
theorem hom_left_eq_zero_of_projective_of_finrank_le
    {X Z T Y : C} [Projective X]
    (j : Z ⟶ T) [Mono j] (f : T ⟶ Y) [Epi f]
    (hjf : j ≫ f = 0)
    [FiniteDimensional K (X ⟶ T)] [FiniteDimensional K (X ⟶ Y)]
    (hle : Module.finrank K (X ⟶ T) ≤ Module.finrank K (X ⟶ Y))
    (g : X ⟶ Z) : g = 0 := by
  by_contra hg
  have hni := postcompLinearMap_not_injective_of_nonzero_left_hom
    (K := K) j f hjf g hg
  exact (LinearMap.not_surjective_of_not_injective_of_finrank_le
      (postcompLinearMap (K := K) (X := X) f) hle hni)
    (postcompLinearMap_surjective_of_projective (K := K) (X := X) f)

section ComplementAssembly

variable [HasFiniteBiproducts C]

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- Right orthogonality to every summand implies right orthogonality to a
finite biproduct. -/
theorem hom_biproduct_eq_zero
    {J : Type} [Fintype J]
    {U : C} {X : J → C}
    (hzero : ∀ j, ∀ a : U ⟶ X j, a = 0)
    (a : U ⟶ ⨁ X) : a = 0 := by
  apply biproduct.hom_ext
  intro j
  rw [zero_comp]
  exact hzero j (a ≫ biproduct.π X j)

/-- Appending copies of an object invisible from `U` preserves an existing
Hom-isomorphism at `U`. -/
theorem postcompLinearMap_bijective_append_of_hom_zero
    {J : Type} [Fintype J]
    {U X T Y : C} (f : T ⟶ Y) (g : J → (X ⟶ Y))
    (hf : Function.Bijective
      (postcompLinearMap (K := K) (X := U) f))
    (hzero : ∀ a : U ⟶ X, a = 0) :
    Function.Bijective
      (postcompLinearMap (K := K) (X := U)
        (biprod.desc f (biproduct.desc g))) := by
  constructor
  · intro a b hab
    have haB : a ≫ biprod.snd = 0 :=
      hom_biproduct_eq_zero (fun _ e => hzero e) (a ≫ biprod.snd)
    have hbB : b ≫ biprod.snd = 0 :=
      hom_biproduct_eq_zero (fun _ e => hzero e) (b ≫ biprod.snd)
    have ha : a = biprod.lift (a ≫ biprod.fst) (a ≫ biprod.snd) := by
      apply biprod.hom_ext
      · simp
      · simp
    have hb : b = biprod.lift (b ≫ biprod.fst) (b ≫ biprod.snd) := by
      apply biprod.hom_ext
      · simp
      · simp
    change a ≫ biprod.desc f (biproduct.desc g) =
      b ≫ biprod.desc f (biproduct.desc g) at hab
    rw [ha, hb, biprod.lift_desc, biprod.lift_desc,
      haB, hbB, zero_comp] at hab
    have hab' : (a ≫ biprod.fst) ≫ f = (b ≫ biprod.fst) ≫ f := by
      simpa only [add_zero] using hab
    apply biprod.hom_ext
    · apply hf.1
      exact hab'
    · exact haB.trans hbB.symm
  · intro y
    obtain ⟨t, ht⟩ := hf.2 y
    change t ≫ f = y at ht
    refine ⟨biprod.lift t 0, ?_⟩
    change biprod.lift t 0 ≫ biprod.desc f (biproduct.desc g) = y
    rw [biprod.lift_desc, zero_comp, add_zero, ht]

/-- A basis of a complement to the old image can be realized by appending
copies of `X`. -/
theorem postcompLinearMap_surjective_append_complement
    {J : Type} [Fintype J]
    {X T Y : C} (f : T ⟶ Y)
    (Q : Submodule K (X ⟶ Y))
    (hQ : IsCompl (postcompLinearMap (K := K) (X := X) f).range Q)
    (b : Module.Basis J K Q) :
    Function.Surjective
      (postcompLinearMap (K := K) (X := X)
        (biprod.desc f (biproduct.desc fun j : J => (b j : Q).1))) := by
  intro y
  let L := postcompLinearMap (K := K) (X := X) f
  let e := L.range.prodEquivOfIsCompl Q hQ
  let rq : L.range × Q := e.symm y
  obtain ⟨a, ha⟩ := rq.1.property
  let coeff : J → K := fun j => b.repr rq.2 j
  let hcopies : X ⟶ ⨁ (fun _ : J => X) :=
    biproduct.lift (fun j => coeff j • 𝟙 X)
  refine ⟨biprod.lift a hcopies, ?_⟩
  have ha' : a ≫ f = (rq.1 : X ⟶ Y) := ha
  have hb : ∑ j, coeff j • ((b j : Q).1) = (rq.2 : X ⟶ Y) := by
    change ∑ j, coeff j • ((b j : Q).1) = Q.subtype rq.2
    rw [← b.sum_repr rq.2, map_sum]
    simp only [map_smul, coeff, Submodule.subtype_apply]
  have hy : (rq.1 : X ⟶ Y) + (rq.2 : X ⟶ Y) = y := by
    change e rq = y
    exact e.apply_symm_apply y
  change biprod.lift a hcopies ≫
      biprod.desc f (biproduct.desc fun j : J => (b j : Q).1) = y
  rw [biprod.lift_desc]
  dsimp only [hcopies]
  rw [biproduct.lift_desc]
  simp only [Linear.smul_comp, Category.id_comp]
  rw [ha', hb, hy]

/-- With an injective old Hom map and one-dimensional endomorphism space,
the complement construction is bijective after adjoining the basis-sized
block. -/
theorem postcompLinearMap_bijective_append_complement
    {J : Type} [Fintype J]
    {X T Y : C} (f : T ⟶ Y)
    [FiniteDimensional K (X ⟶ T)]
    [FiniteDimensional K (X ⟶ Y)]
    [FiniteDimensional K (X ⟶ X)]
    [FiniteDimensional K (X ⟶ ⨁ (fun _ : J => X))]
    [FiniteDimensional K (X ⟶ (T ⊞ ⨁ (fun _ : J => X)))]
    (hf : Function.Injective (postcompLinearMap (K := K) (X := X) f))
    (hend : Module.finrank K (X ⟶ X) = 1)
    (Q : Submodule K (X ⟶ Y))
    (hQ : IsCompl (postcompLinearMap (K := K) (X := X) f).range Q)
    (b : Module.Basis J K Q) :
    Function.Bijective
      (postcompLinearMap (K := K) (X := X)
        (biprod.desc f (biproduct.desc fun j : J => (b j : Q).1))) := by
  have hcopies :
      Module.finrank K (X ⟶ ⨁ (fun _ : J => X)) = Fintype.card J := by
    rw [finrank_hom_biproduct (K := K) X (fun _ : J => X)]
    simp [hend]
  have hcomplement :
      Module.finrank K (X ⟶ T) + Fintype.card J =
        Module.finrank K (X ⟶ Y) := by
    have h := Submodule.finrank_add_eq_of_isCompl hQ
    rw [LinearMap.finrank_range_of_inj hf,
      Module.finrank_eq_card_basis b] at h
    exact h
  have hdim :
      Module.finrank K (X ⟶ (T ⊞ ⨁ (fun _ : J => X))) =
        Module.finrank K (X ⟶ Y) := by
    rw [finrank_hom_biprod (K := K) X T (⨁ (fun _ : J => X)), hcopies]
    exact hcomplement
  have hsurj := postcompLinearMap_surjective_append_complement
    (K := K) f Q hQ b
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj,
    hsurj⟩

/-- An injective Hom map can be made bijective by adjoining exactly its
finrank deficit many copies of `X`. -/
theorem exists_fin_copies_postcomp_bijective
    {X T Y : C} (f : T ⟶ Y)
    [FiniteDimensional K (X ⟶ T)]
    [FiniteDimensional K (X ⟶ Y)]
    [FiniteDimensional K (X ⟶ X)]
    (hf : Function.Injective (postcompLinearMap (K := K) (X := X) f))
    (hend : Module.finrank K (X ⟶ X) = 1) :
    ∃ (m : ℕ) (g : Fin m → (X ⟶ Y)),
      m = Module.finrank K (X ⟶ Y) - Module.finrank K (X ⟶ T) ∧
      Function.Bijective
        (postcompLinearMap (K := K) (X := X)
          (biprod.desc f (biproduct.desc g))) := by
  let L := postcompLinearMap (K := K) (X := X) f
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl L.range
  let m := Module.finrank K Q
  let b : Module.Basis (Fin m) K Q := Module.finBasis K Q
  let g : Fin m → (X ⟶ Y) := fun j => (b j : Q).1
  have hcomplement :
      Module.finrank K (X ⟶ T) + Module.finrank K Q =
        Module.finrank K (X ⟶ Y) := by
    have h := Submodule.finrank_add_eq_of_isCompl hQ
    rw [LinearMap.finrank_range_of_inj hf] at h
    exact h
  have hm :
      m = Module.finrank K (X ⟶ Y) - Module.finrank K (X ⟶ T) := by
    dsimp only [m]
    omega
  letI : FiniteDimensional K (∀ _ : Fin m, X ⟶ X) := inferInstance
  letI : FiniteDimensional K (X ⟶ ⨁ (fun _ : Fin m => X)) :=
    LinearEquiv.finiteDimensional
      (homLinearEquivBiproduct (K := K) X (fun _ : Fin m => X)).symm
  letI : FiniteDimensional K
      ((X ⟶ T) × (X ⟶ ⨁ (fun _ : Fin m => X))) := inferInstance
  letI : FiniteDimensional K (X ⟶ (T ⊞ ⨁ (fun _ : Fin m => X))) :=
    LinearEquiv.finiteDimensional
      (homLinearEquivBiprod (K := K) X T (⨁ (fun _ : Fin m => X))).symm
  refine ⟨m, g, hm, ?_⟩
  simpa only [g, L] using
    postcompLinearMap_bijective_append_complement
      (K := K) f hf hend Q hQ b

/-- Exact-deficit form of complement assembly. -/
theorem exists_fin_copies_postcomp_bijective_of_finrank_eq_add
    {X T Y : C} (f : T ⟶ Y)
    [FiniteDimensional K (X ⟶ T)]
    [FiniteDimensional K (X ⟶ Y)]
    [FiniteDimensional K (X ⟶ X)]
    (hf : Function.Injective (postcompLinearMap (K := K) (X := X) f))
    (hend : Module.finrank K (X ⟶ X) = 1)
    (n : ℕ)
    (hdim : Module.finrank K (X ⟶ Y) =
      Module.finrank K (X ⟶ T) + n) :
    ∃ g : Fin n → (X ⟶ Y),
      Function.Bijective
        (postcompLinearMap (K := K) (X := X)
          (biprod.desc f (biproduct.desc g))) := by
  obtain ⟨m, g, hm, hg⟩ :=
    exists_fin_copies_postcomp_bijective (K := K) f hf hend
  have hmn : m = n := by omega
  subst n
  exact ⟨g, hg⟩

end ComplementAssembly

section FiniteDimensionalNonprojectiveBranch

universe u uIota

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing A]
  {Iota : Type uIota}
  (sigma : IndecomposableSkeleton.{u, uIota, u} A Iota)

/-- In the nonprojective branch, directed almost-split lifting contradicts
noninjectivity whenever the source Hom finrank is at most the target one. -/
theorem hom_left_eq_zero_of_nonprojective_of_finrank_le
    (H : HasAcyclicNonzeroNonisomorphisms sigma)
    (x : sigma.NonprojectiveLabel) (z : Iota)
    {V W : FGModuleCat.{u} A}
    {j : sigma.obj z ⟶ V} {p : V ⟶ W} {hjp : j ≫ p = 0}
    (hS : (ShortComplex.mk j p hjp).ShortExact)
    (hle : Module.finrank k (sigma.obj x.1 ⟶ V) ≤
      Module.finrank k (sigma.obj x.1 ⟶ W))
    (g : sigma.obj x.1 ⟶ sigma.obj z) : g = 0 := by
  letI : FiniteDimensional k (sigma.obj x.1 ⟶ V) :=
    finiteDimensional_hom_from_obj k A sigma x.1 V
  letI : FiniteDimensional k (sigma.obj x.1 ⟶ W) :=
    finiteDimensional_hom_from_obj k A sigma x.1 W
  letI : Mono j := hS.mono_f
  by_contra hg
  have hni : ¬ Function.Injective
      (postcompLinearMap (K := k) (X := sigma.obj x.1) p) :=
    postcompLinearMap_not_injective_of_nonzero_left_hom
      (K := k) j p hjp g hg
  have hnsurj : ¬ Function.Surjective
      (postcompLinearMap (K := k) (X := sigma.obj x.1) p) :=
    LinearMap.not_surjective_of_not_injective_of_finrank_le
      (postcompLinearMap (K := k) (X := sigma.obj x.1) p) hle hni
  apply hnsurj
  intro a
  obtain ⟨b, hb⟩ :=
    DirectedHomOrder.finiteDimensional_exists_lift_of_acyclicNonzeroNonisomorphisms
      k A sigma H x z g hg hS a
  exact ⟨b, hb⟩

end FiniteDimensionalNonprojectiveBranch

end OpConjecture.RepresentationDirected
