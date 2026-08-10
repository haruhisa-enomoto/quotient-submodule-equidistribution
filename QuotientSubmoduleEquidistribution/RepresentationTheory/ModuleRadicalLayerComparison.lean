import Mathlib.RingTheory.Jacobson.Radical

/-!
# The functorial top-and-radical comparison

Every module homomorphism preserves the module Jacobson radical, hence induces
maps on both the radical and the semisimple top.  This file packages those two
maps and proves the exact kernel description used by the separated-quiver
argument: a morphism is invisible on both layers precisely when it vanishes on
the source radical and has image in the target radical.  Consequently, the
composite of two invisible morphisms is zero.

The result is independent of any quiver presentation.  For a square-zero
algebra, the later separated-representation construction refines this layer
comparison by retaining the radical-action maps and proves fullness by choosing
linear splittings of the tops.
-/

set_option autoImplicit false

namespace QuotientSubmoduleEquidistribution.ModuleRadicalLayerComparison

universe u v w x

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- The restriction of a module map to the Jacobson radicals. -/
def radicalMap (f : M →ₗ[R] N) :
    Module.jacobson R M →ₗ[R] Module.jacobson R N where
  toFun m :=
    ⟨f m, Module.map_jacobson_le f ⟨m, m.property, rfl⟩⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem radicalMap_apply (f : M →ₗ[R] N)
    (m : Module.jacobson R M) :
    (radicalMap f m : N) = f m :=
  rfl

/-- The map induced by a module homomorphism on semisimple tops. -/
def topMap (f : M →ₗ[R] N) :
    (M ⧸ Module.jacobson R M) →ₗ[R]
      (N ⧸ Module.jacobson R N) :=
  (Module.jacobson R M).mapQ (Module.jacobson R N) f
    (Module.le_comap_jacobson f)

@[simp]
theorem topMap_mk (f : M →ₗ[R] N) (m : M) :
    topMap f ((Module.jacobson R M).mkQ m) =
      (Module.jacobson R N).mkQ (f m) :=
  Submodule.mapQ_apply _ _ _ _

/-- The two linear layers retained by the radical-layer comparison. -/
abbrev RadicalLayerHom (M : Type v) (N : Type w)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :=
  (Module.jacobson R M →ₗ[R] Module.jacobson R N) ×
    ((M ⧸ Module.jacobson R M) →ₗ[R]
      (N ⧸ Module.jacobson R N))

/-- Send a module homomorphism to its maps on radical and top. -/
def layerMap (f : M →ₗ[R] N) : RadicalLayerHom (R := R) M N :=
  (radicalMap f, topMap f)

@[simp]
theorem radicalMap_id : radicalMap (LinearMap.id (R := R) (M := M)) =
    LinearMap.id := by
  ext m
  rfl

@[simp]
theorem topMap_id : topMap (LinearMap.id (R := R) (M := M)) =
    LinearMap.id := by
  ext m
  rfl

@[simp]
theorem radicalMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    radicalMap (g.comp f) = (radicalMap g).comp (radicalMap f) := by
  ext m
  rfl

@[simp]
theorem topMap_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    topMap (g.comp f) = (topMap g).comp (topMap f) := by
  ext m
  rfl

/-- Vanishing on the radical layer means literal vanishing on every radical
element. -/
theorem radicalMap_eq_zero_iff (f : M →ₗ[R] N) :
    radicalMap f = 0 ↔
      ∀ m : M, m ∈ Module.jacobson R M → f m = 0 := by
  constructor
  · intro h m hm
    have h' := LinearMap.congr_fun h (⟨m, hm⟩ : Module.jacobson R M)
    simpa using congrArg Subtype.val h'
  · intro h
    ext m
    exact h m m.property

/-- Vanishing on the top layer means that the whole image lies in the target
radical. -/
theorem topMap_eq_zero_iff (f : M →ₗ[R] N) :
    topMap f = 0 ↔
      ∀ m : M, f m ∈ Module.jacobson R N := by
  constructor
  · intro h m
    have h' := LinearMap.congr_fun h ((Module.jacobson R M).mkQ m)
    rw [topMap_mk, LinearMap.zero_apply] at h'
    exact (Submodule.Quotient.mk_eq_zero _).mp h'
  · intro h
    ext q
    change topMap f ((Module.jacobson R M).mkQ q) = 0
    rw [topMap_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h q)

/-- Exact kernel description for the top-and-radical comparison. -/
theorem layerMap_eq_zero_iff (f : M →ₗ[R] N) :
    layerMap f = 0 ↔
      (∀ m : M, m ∈ Module.jacobson R M → f m = 0) ∧
      (∀ m : M, f m ∈ Module.jacobson R N) := by
  constructor
  · intro h
    have hr : radicalMap f = 0 := congrArg Prod.fst h
    have ht : topMap f = 0 := congrArg Prod.snd h
    exact ⟨(radicalMap_eq_zero_iff f).mp hr,
      (topMap_eq_zero_iff f).mp ht⟩
  · rintro ⟨hr, ht⟩
    apply Prod.ext
    · exact (radicalMap_eq_zero_iff f).mpr hr
    · exact (topMap_eq_zero_iff f).mpr ht

/-- The kernel of the radical-layer comparison is a square-zero ideal: the
first invisible map lands in the middle radical, while the second invisible
map vanishes there. -/
theorem comp_eq_zero_of_layerMap_eq_zero
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : layerMap f = 0) (hg : layerMap g = 0) :
    g.comp f = 0 := by
  rw [layerMap_eq_zero_iff] at hf hg
  ext m
  exact hg.1 (f m) (hf.2 m)

end QuotientSubmoduleEquidistribution.ModuleRadicalLayerComparison
