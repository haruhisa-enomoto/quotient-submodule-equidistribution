import QuotientSubmoduleEquidistribution.RepresentationTheory.SurjectiveQuotientRepresentationInfinite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The loop--two-cycle parameter family from six multiplication coordinates

This file deliberately assumes only the complete multiplication table of the
six-dimensional quotient.  It constructs the paper's one-parameter
family, proves indecomposability and parameter recovery, and feeds it into the
existing quotient-inflation obstruction.  It does not classify any modules.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LoopTwoCycleFamily

universe u v

/-- Coordinates in the ordered basis `e₁,e₂,x,a,b,ab`.  Multiplication is
read in the left-module convention: the paper path `ab` acts as `b * a`. -/
structure SixCoordinates (K : Type u) where
  e₁ : K
  e₂ : K
  x : K
  a : K
  b : K
  ab : K

/-- Coordinate equivalence used to transport the additive structure. -/
def SixCoordinates.equivProd (K : Type u) :
    SixCoordinates K ≃ K × K × K × K × K × K where
  toFun p := (p.e₁, p.e₂, p.x, p.a, p.b, p.ab)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
    p.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (K : Type u) [Field K] : AddCommGroup (SixCoordinates K) :=
  (SixCoordinates.equivProd K).addCommGroup

/-- The coordinate equivalence as an additive equivalence. -/
def SixCoordinates.addEquivProd (K : Type u) [Field K] :
    SixCoordinates K ≃+ K × K × K × K × K × K where
  __ := SixCoordinates.equivProd K
  map_add' _ _ := rfl

instance (K : Type u) [Field K] : Module K (SixCoordinates K) :=
  (SixCoordinates.addEquivProd K).module K

@[ext]
theorem SixCoordinates.ext {K : Type u} {p q : SixCoordinates K}
    (h₁ : p.e₁ = q.e₁) (h₂ : p.e₂ = q.e₂)
    (hx : p.x = q.x) (ha : p.a = q.a) (hb : p.b = q.b)
    (hab : p.ab = q.ab) : p = q := by
  cases p
  cases q
  simp_all

@[simp] theorem SixCoordinates.zero_e₁ {K : Type u} [Field K] :
    (0 : SixCoordinates K).e₁ = 0 := rfl
@[simp] theorem SixCoordinates.zero_e₂ {K : Type u} [Field K] :
    (0 : SixCoordinates K).e₂ = 0 := rfl
@[simp] theorem SixCoordinates.zero_x {K : Type u} [Field K] :
    (0 : SixCoordinates K).x = 0 := rfl
@[simp] theorem SixCoordinates.zero_a {K : Type u} [Field K] :
    (0 : SixCoordinates K).a = 0 := rfl
@[simp] theorem SixCoordinates.zero_b {K : Type u} [Field K] :
    (0 : SixCoordinates K).b = 0 := rfl
@[simp] theorem SixCoordinates.zero_ab {K : Type u} [Field K] :
    (0 : SixCoordinates K).ab = 0 := rfl

@[simp] theorem SixCoordinates.add_e₁ {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).e₁ = p.e₁ + q.e₁ := rfl
@[simp] theorem SixCoordinates.add_e₂ {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).e₂ = p.e₂ + q.e₂ := rfl
@[simp] theorem SixCoordinates.add_x {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).x = p.x + q.x := rfl
@[simp] theorem SixCoordinates.add_a {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).a = p.a + q.a := rfl
@[simp] theorem SixCoordinates.add_b {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).b = p.b + q.b := rfl
@[simp] theorem SixCoordinates.add_ab {K : Type u} [Field K]
    (p q : SixCoordinates K) : (p + q).ab = p.ab + q.ab := rfl

@[simp] theorem SixCoordinates.smul_e₁ {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).e₁ = c * p.e₁ := rfl
@[simp] theorem SixCoordinates.smul_e₂ {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).e₂ = c * p.e₂ := rfl
@[simp] theorem SixCoordinates.smul_x {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).x = c * p.x := rfl
@[simp] theorem SixCoordinates.smul_a {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).a = c * p.a := rfl
@[simp] theorem SixCoordinates.smul_b {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).b = c * p.b := rfl
@[simp] theorem SixCoordinates.smul_ab {K : Type u} [Field K]
    (c : K) (p : SixCoordinates K) : (c • p).ab = c * p.ab := rfl

/-- Multiplication table of the six-dimensional loop--two-cycle quotient.
The only nonzero product of radical basis vectors is `b * a = ab`. -/
def SixCoordinates.mul (K : Type u) [Field K]
    (p q : SixCoordinates K) : SixCoordinates K where
  e₁ := p.e₁ * q.e₁
  e₂ := p.e₂ * q.e₂
  x := p.e₁ * q.x + p.x * q.e₁
  a := p.e₂ * q.a + p.a * q.e₁
  b := p.e₁ * q.b + p.b * q.e₂
  ab := p.e₁ * q.ab + p.ab * q.e₁ + p.b * q.a

/-- The precise quotient-side input needed by the parameter-family proof:
linear coordinates and the complete unit and multiplication formulas. -/
structure SixDimensionalQuotientData (K S : Type u)
    [Field K]
    [Ring S] [Algebra K S] where
  coord : S ≃ₗ[K] SixCoordinates K
  coord_one : coord 1 = ⟨1, 1, 0, 0, 0, 0⟩
  coord_mul : ∀ r s, coord (r * s) = SixCoordinates.mul K (coord r) (coord s)

namespace SixDimensionalQuotientData

variable {K : Type u} [Field K]
variable {S : Type u} [Ring S] [Algebra K S]

/-- The underlying three-dimensional vector space, with a two-dimensional
vertex-`1` part and a one-dimensional vertex-`2` part. -/
abbrev Carrier := (K × K) × K

/-- A parameter-tagged three-dimensional carrier.  It is a structure, rather
than a reducible alias, so different parameters have definitionally distinct
module structures. -/
structure FamilyCarrier (_D : SixDimensionalQuotientData K S) (_t : K) where
  first : K
  second : K
  vertexTwo : K

def FamilyCarrier.equivProd
    (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t ≃ K × K × K where
  toFun z := (z.first, z.second, z.vertexTwo)
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance familyCarrierAddCommGroup
    (D : SixDimensionalQuotientData K S) (t : K) :
    AddCommGroup (FamilyCarrier D t) :=
  (FamilyCarrier.equivProd D t).addCommGroup

def FamilyCarrier.addEquivProd
    (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t ≃+ K × K × K where
  __ := FamilyCarrier.equivProd D t
  map_add' _ _ := rfl

instance familyCarrierModule
    (D : SixDimensionalQuotientData K S) (t : K) :
    Module K (FamilyCarrier D t) :=
  (FamilyCarrier.addEquivProd D t).module K

def FamilyCarrier.linearEquivProd
    (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t ≃ₗ[K] K × K × K where
  __ := FamilyCarrier.addEquivProd D t
  map_smul' _ _ := rfl

instance familyCarrierFinite
    (D : SixDimensionalQuotientData K S) (t : K) :
    FiniteDimensional K (FamilyCarrier D t) :=
  (FamilyCarrier.linearEquivProd D t).symm.finiteDimensional

@[ext] theorem familyCarrier_ext
    {D : SixDimensionalQuotientData K S} {t : K}
    {z w : FamilyCarrier D t}
    (h₁ : z.first = w.first) (h₂ : z.second = w.second)
    (h₃ : z.vertexTwo = w.vertexTwo) : z = w := by
  cases z
  cases w
  simp_all

@[simp] theorem familyCarrier_zero_first
    (D : SixDimensionalQuotientData K S) (t : K) :
    (0 : FamilyCarrier D t).first = 0 := rfl
@[simp] theorem familyCarrier_zero_second
    (D : SixDimensionalQuotientData K S) (t : K) :
    (0 : FamilyCarrier D t).second = 0 := rfl
@[simp] theorem familyCarrier_zero_vertexTwo
    (D : SixDimensionalQuotientData K S) (t : K) :
    (0 : FamilyCarrier D t).vertexTwo = 0 := rfl

@[simp] theorem familyCarrier_mk_zero
    (D : SixDimensionalQuotientData K S) (t : K) :
    (⟨0, 0, 0⟩ : FamilyCarrier D t) = 0 := by
  ext <;> simp

@[simp] theorem familyCarrier_add_first
    (D : SixDimensionalQuotientData K S) (t : K) (z w : FamilyCarrier D t) :
    (z + w).first = z.first + w.first := rfl
@[simp] theorem familyCarrier_add_second
    (D : SixDimensionalQuotientData K S) (t : K) (z w : FamilyCarrier D t) :
    (z + w).second = z.second + w.second := rfl
@[simp] theorem familyCarrier_add_vertexTwo
    (D : SixDimensionalQuotientData K S) (t : K) (z w : FamilyCarrier D t) :
    (z + w).vertexTwo = z.vertexTwo + w.vertexTwo := rfl

@[simp] theorem familyCarrier_smul_first
    (D : SixDimensionalQuotientData K S) (t c : K) (z : FamilyCarrier D t) :
    (c • z).first = c * z.first := rfl
@[simp] theorem familyCarrier_smul_second
    (D : SixDimensionalQuotientData K S) (t c : K) (z : FamilyCarrier D t) :
    (c • z).second = c * z.second := rfl
@[simp] theorem familyCarrier_smul_vertexTwo
    (D : SixDimensionalQuotientData K S) (t c : K) (z : FamilyCarrier D t) :
    (c • z).vertexTwo = c * z.vertexTwo := rfl

/-- Action of one coordinate vector on the member with parameter `λ`.
For `((u,v),w)`, the generators act by
`x(v)=u`, `a(v)=w`, `b(w)=λu`, and `(ab)(v)=λu`. -/
def coordinateAction (D : SixDimensionalQuotientData K S)
    (t : K) (p : SixCoordinates K) :
    Module.End K (FamilyCarrier D t) where
  toFun z :=
    ⟨p.e₁ * z.first + p.x * z.second + p.b * (t * z.vertexTwo) +
        p.ab * (t * z.second),
      p.e₁ * z.second,
      p.e₂ * z.vertexTwo + p.a * z.second⟩
  map_add' z w := by
    ext <;> simp <;> ring
  map_smul' c z := by
    ext <;> simp <;> ring

theorem coordinateAction_one (D : SixDimensionalQuotientData K S) (t : K) :
    coordinateAction D t
      (⟨1, 1, 0, 0, 0, 0⟩ : SixCoordinates K) = 1 := by
  apply LinearMap.ext
  intro z
  ext <;> simp [coordinateAction]

theorem coordinateAction_mul (D : SixDimensionalQuotientData K S)
    (t : K) (p q : SixCoordinates K) :
    coordinateAction D t (SixCoordinates.mul K p q) =
      coordinateAction D t p * coordinateAction D t q := by
  apply LinearMap.ext
  intro z
  ext <;> simp [coordinateAction, SixCoordinates.mul] <;> ring

/-- The algebra action of the quotient on the parameter member. -/
def actionHom (D : SixDimensionalQuotientData K S) (t : K) :
    S →ₐ[K] Module.End K (FamilyCarrier D t) where
  toFun s := coordinateAction D t (D.coord s)
  map_one' := by rw [D.coord_one, coordinateAction_one]
  map_mul' r s := by rw [D.coord_mul, coordinateAction_mul]
  map_zero' := by
    apply LinearMap.ext
    intro z
    ext <;> simp [coordinateAction]
  map_add' r s := by
    apply LinearMap.ext
    intro z
    ext <;> simp [coordinateAction] <;> ring
  commutes' c := by
    apply LinearMap.ext
    intro z
    have hc : D.coord (algebraMap K S c) = c • D.coord 1 := by
      simpa [Algebra.smul_def] using D.coord.map_smul c (1 : S)
    rw [hc, D.coord_one]
    ext <;> simp [coordinateAction]

instance familyModule (D : SixDimensionalQuotientData K S) (t : K) :
    Module S (FamilyCarrier D t) :=
  Module.compHom (FamilyCarrier D t) (actionHom D t).toRingHom

instance familyScalarTower (D : SixDimensionalQuotientData K S) (t : K) :
    IsScalarTower K S (FamilyCarrier D t) :=
  IsScalarTower.of_algebraMap_smul fun c z => by
    change actionHom D t (algebraMap K S c) z = c • z
    rw [(actionHom D t).commutes]
    rfl

instance familyModuleFinite (D : SixDimensionalQuotientData K S) (t : K) :
    Module.Finite S (FamilyCarrier D t) :=
  Module.Finite.of_restrictScalars_finite K S (FamilyCarrier D t)

/-- The genuine finitely generated quotient module with parameter `t`. -/
abbrev FamilyModule (D : SixDimensionalQuotientData K S) (t : K) :
    FGModuleCat S :=
  FGModuleCat.of S (FamilyCarrier D t)

/-! ### Named quotient generators and their action -/

def e₁ (D : SixDimensionalQuotientData K S) : S :=
  D.coord.symm ⟨1, 0, 0, 0, 0, 0⟩

def e₂ (D : SixDimensionalQuotientData K S) : S :=
  D.coord.symm ⟨0, 1, 0, 0, 0, 0⟩

def x (D : SixDimensionalQuotientData K S) : S :=
  D.coord.symm ⟨0, 0, 1, 0, 0, 0⟩

def a (D : SixDimensionalQuotientData K S) : S :=
  D.coord.symm ⟨0, 0, 0, 1, 0, 0⟩

def b (D : SixDimensionalQuotientData K S) : S :=
  D.coord.symm ⟨0, 0, 0, 0, 1, 0⟩

@[simp] theorem e₁_smul (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    e₁ D • z = ⟨z.first, z.second, 0⟩ := by
  change coordinateAction D t (D.coord (D.coord.symm _)) z = _
  rw [D.coord.apply_symm_apply]
  ext <;> simp [coordinateAction]

@[simp] theorem e₂_smul (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    e₂ D • z = ⟨0, 0, z.vertexTwo⟩ := by
  change coordinateAction D t (D.coord (D.coord.symm _)) z = _
  rw [D.coord.apply_symm_apply]
  ext <;> simp [coordinateAction]

@[simp] theorem x_smul (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    x D • z = ⟨z.second, 0, 0⟩ := by
  change coordinateAction D t (D.coord (D.coord.symm _)) z = _
  rw [D.coord.apply_symm_apply]
  ext <;> simp [coordinateAction]

@[simp] theorem a_smul (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    a D • z = ⟨0, 0, z.second⟩ := by
  change coordinateAction D t (D.coord (D.coord.symm _)) z = _
  rw [D.coord.apply_symm_apply]
  ext <;> simp [coordinateAction]

@[simp] theorem b_smul (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    b D • z = ⟨t * z.vertexTwo, 0, 0⟩ := by
  change coordinateAction D t (D.coord (D.coord.symm _)) z = _
  rw [D.coord.apply_symm_apply]
  ext <;> simp [coordinateAction]

def firstBasis (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t := ⟨1, 0, 0⟩

def secondBasis (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t := ⟨0, 1, 0⟩

def vertexTwoBasis (D : SixDimensionalQuotientData K S) (t : K) :
    FamilyCarrier D t := ⟨0, 0, 1⟩

theorem basis_decompose
    (D : SixDimensionalQuotientData K S) (t : K)
    (z : FamilyCarrier D t) :
    z = z.first • firstBasis D t +
      z.second • secondBasis D t +
      z.vertexTwo • vertexTwoBasis D t := by
  ext <;> simp [firstBasis, secondBasis, vertexTwoBasis]

@[simp] theorem x_smul_firstBasis
    (D : SixDimensionalQuotientData K S) (t : K) :
    x D • firstBasis D t = 0 := by
  ext <;> simp [firstBasis]

@[simp] theorem x_smul_secondBasis
    (D : SixDimensionalQuotientData K S) (t : K) :
    x D • secondBasis D t = firstBasis D t := by
  simp [firstBasis, secondBasis]

@[simp] theorem a_smul_secondBasis
    (D : SixDimensionalQuotientData K S) (t : K) :
    a D • secondBasis D t = vertexTwoBasis D t := by
  simp [secondBasis, vertexTwoBasis]

@[simp] theorem b_smul_vertexTwoBasis
    (D : SixDimensionalQuotientData K S) (t : K) :
    b D • vertexTwoBasis D t = t • firstBasis D t := by
  ext <;> simp [vertexTwoBasis, firstBasis]

/-! ### The three basis images of every module homomorphism -/

theorem hom_firstBasis
    (D : SixDimensionalQuotientData K S) {t s : K}
    (f : FamilyCarrier D t →ₗ[S] FamilyCarrier D s) :
    f (firstBasis D t) =
      ⟨(f (firstBasis D t)).first, 0, 0⟩ := by
  apply familyCarrier_ext
  · rfl
  · have hx := congrArg FamilyCarrier.first
      (f.map_smul (x D) (firstBasis D t))
    simpa [firstBasis] using hx.symm
  · have he₁ := congrArg FamilyCarrier.vertexTwo
      (f.map_smul (e₁ D) (firstBasis D t))
    simpa [firstBasis] using he₁

theorem hom_secondBasis
    (D : SixDimensionalQuotientData K S) {t s : K}
    (f : FamilyCarrier D t →ₗ[S] FamilyCarrier D s) :
    f (secondBasis D t) =
      ⟨(f (secondBasis D t)).first,
        (f (firstBasis D t)).first, 0⟩ := by
  apply familyCarrier_ext
  · rfl
  · have hx := congrArg FamilyCarrier.first
      (f.map_smul (x D) (secondBasis D t))
    simpa [firstBasis, secondBasis] using hx.symm
  · have he₁ := congrArg FamilyCarrier.vertexTwo
      (f.map_smul (e₁ D) (secondBasis D t))
    simpa [secondBasis] using he₁

theorem hom_vertexTwoBasis
    (D : SixDimensionalQuotientData K S) {t s : K}
    (f : FamilyCarrier D t →ₗ[S] FamilyCarrier D s) :
    f (vertexTwoBasis D t) =
      ⟨0, 0, (f (firstBasis D t)).first⟩ := by
  apply familyCarrier_ext
  · have he₂ := congrArg FamilyCarrier.first
      (f.map_smul (e₂ D) (vertexTwoBasis D t))
    simpa [vertexTwoBasis] using he₂
  · have he₂ := congrArg FamilyCarrier.second
      (f.map_smul (e₂ D) (vertexTwoBasis D t))
    simpa [vertexTwoBasis] using he₂
  · have ha := congrArg FamilyCarrier.vertexTwo
      (f.map_smul (a D) (secondBasis D t))
    have hv := congrArg FamilyCarrier.second (hom_secondBasis D f)
    have ha' :
        (f (vertexTwoBasis D t)).vertexTwo =
          (f (secondBasis D t)).second := by
      simpa [secondBasis, vertexTwoBasis] using ha
    have hv' :
        (f (secondBasis D t)).second =
          (f (firstBasis D t)).first := by
      simpa using hv
    exact ha'.trans hv'

/-- Every module homomorphism intertwines the two parameters after
multiplication by its common diagonal coefficient. -/
theorem parameter_mul_diagonal_eq
    (D : SixDimensionalQuotientData K S) {t s : K}
    (f : FamilyCarrier D t →ₗ[S] FamilyCarrier D s) :
    t * (f (firstBasis D t)).first =
      s * (f (firstBasis D t)).first := by
  let fK : FamilyCarrier D t →ₗ[K] FamilyCarrier D s :=
    f.restrictScalars K
  calc
    t * (f (firstBasis D t)).first =
        (f (t • firstBasis D t)).first := by
      have h := congrArg FamilyCarrier.first
        (fK.map_smul t (firstBasis D t))
      exact h.symm
    _ = (f (b D • vertexTwoBasis D t)).first := by
      rw [b_smul_vertexTwoBasis]
    _ = (b D • f (vertexTwoBasis D t)).first := by
      exact congrArg FamilyCarrier.first
        (f.map_smul (b D) (vertexTwoBasis D t))
    _ = s * (f (firstBasis D t)).first := by
      rw [hom_vertexTwoBasis D f, b_smul]

/-- Every module homomorphism has the upper-triangular matrix asserted in the
paper.  This is used only to test idempotents; it is not a module
classification. -/
theorem hom_apply
    (D : SixDimensionalQuotientData K S) {t s : K}
    (f : FamilyCarrier D t →ₗ[S] FamilyCarrier D s)
    (z : FamilyCarrier D t) :
    f z =
      ⟨(f (firstBasis D t)).first * z.first +
          (f (secondBasis D t)).first * z.second,
        (f (firstBasis D t)).first * z.second,
        (f (firstBasis D t)).first * z.vertexTwo⟩ := by
  let fK : FamilyCarrier D t →ₗ[K] FamilyCarrier D s :=
    f.restrictScalars K
  conv_lhs => rw [basis_decompose D t z]
  change fK (_ + _ + _) = _
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  change z.first • f (firstBasis D t) +
      z.second • f (secondBasis D t) +
      z.vertexTwo • f (vertexTwoBasis D t) = _
  rw [hom_firstBasis D f, hom_secondBasis D f,
    hom_vertexTwoBasis D f]
  ext <;> simp <;> ring

theorem firstBasis_ne_zero
    (D : SixDimensionalQuotientData K S) (t : K) :
    firstBasis D t ≠ 0 := by
  intro h
  have hfirst := congrArg FamilyCarrier.first h
  change (1 : K) = 0 at hfirst
  exact one_ne_zero hfirst

/-- An isomorphism between two family members preserves the scalar
parameter. -/
theorem parameter_eq_of_iso
    (D : SixDimensionalQuotientData K S) {t s : K}
    (e : FamilyModule D t ≅ FamilyModule D s) : t = s := by
  let f : FamilyCarrier D t ≃ₗ[S] FamilyCarrier D s :=
    FGModuleCat.isoToLinearEquiv e
  have hdiag : (f (firstBasis D t)).first ≠ 0 := by
    intro h
    have hfzero : f (firstBasis D t) = 0 := by
      change f.toLinearMap (firstBasis D t) = 0
      rw [hom_firstBasis D f.toLinearMap]
      ext <;> simp [h]
    apply firstBasis_ne_zero D t
    apply f.injective
    simpa using hfzero
  exact mul_right_cancel₀ hdiag
    (parameter_mul_diagonal_eq D f.toLinearMap)

/-- The computed endomorphism matrix has no nontrivial idempotents. -/
theorem eq_zero_or_eq_one_of_isIdempotentElem
    (D : SixDimensionalQuotientData K S) (t : K)
    (f : Module.End S (FamilyCarrier D t)) (hf : IsIdempotentElem f) :
    f = 0 ∨ f = 1 := by
  have hu0 := DFunLike.congr_fun hf (firstBasis D t)
  change f (f (firstBasis D t)) = f (firstBasis D t) at hu0
  have hu := congrArg FamilyCarrier.first hu0
  rw [hom_apply D f (f (firstBasis D t)),
    hom_apply D f (firstBasis D t)] at hu
  have hc :
      (f (firstBasis D t)).first * (f (firstBasis D t)).first =
        (f (firstBasis D t)).first := by
    simpa [firstBasis] using hu
  have hv0 := DFunLike.congr_fun hf (secondBasis D t)
  change f (f (secondBasis D t)) = f (secondBasis D t) at hv0
  have hv := congrArg FamilyCarrier.first hv0
  rw [hom_apply D f (f (secondBasis D t)),
    hom_apply D f (secondBasis D t)] at hv
  have hd :
      (f (firstBasis D t)).first * (f (secondBasis D t)).first +
          (f (secondBasis D t)).first * (f (firstBasis D t)).first =
        (f (secondBasis D t)).first := by
    simpa [firstBasis, secondBasis] using hv
  have hfactor :
      (f (firstBasis D t)).first *
          ((f (firstBasis D t)).first - 1) = 0 := by
    rw [mul_sub, mul_one, hc, sub_self]
  rcases mul_eq_zero.mp hfactor with hc0 | hc1
  · left
    have hd0 : (f (secondBasis D t)).first = 0 := by
      simpa [hc0] using hd.symm
    apply LinearMap.ext
    intro z
    rw [hom_apply D f z]
    ext <;> simp [hc0, hd0]
  · right
    have hcOne : (f (firstBasis D t)).first = 1 :=
      sub_eq_zero.mp hc1
    have hd0 : (f (secondBasis D t)).first = 0 := by
      simpa [hcOne] using hd
    apply LinearMap.ext
    intro z
    rw [hom_apply D f z]
    ext <;> simp [hcOne, hd0]

/-- Every member of the scalar family is indecomposable. -/
theorem familyModule_indecomposable
    (D : SixDimensionalQuotientData K S) (t : K) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule S (FamilyModule D t) := by
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · apply not_subsingleton_iff_nontrivial.mp
    intro h
    exact firstBasis_ne_zero D t (Subsingleton.elim _ _)
  · intro f hf
    exact eq_zero_or_eq_one_of_isIdempotentElem D t f hf

/-- The complete one-parameter certificate.  No assertion about any other
module over the quotient is made. -/
def infiniteIndecomposableFamily
    (D : SixDimensionalQuotientData K S) :
    RepresentationInfiniteCertificate.InfiniteIndecomposableFamily
      (R := S) K where
  obj := FamilyModule D
  indecomposable := familyModule_indecomposable D
  eq_of_iso e := parameter_eq_of_iso D e.some

/-- A surjective image with the six-coordinate multiplication table rules
out a finite complete indecomposable skeleton upstairs. -/
theorem false_of_surjection_to_sixDimensionalQuotient
    {R : Type u} [Ring R] [IsNoetherianRing R]
    [Infinite K]
    (q : R →+* S) (hq : Function.Surjective q)
    (D : SixDimensionalQuotientData K S)
    {ι : Type v} [Finite ι]
    (σ : QuotientSubmoduleEquidistribution.IndecomposableSkeleton.{u, v, u} R ι) :
    False :=
  RepresentationInfiniteCertificate.false_of_surjective_image_family
    q hq (infiniteIndecomposableFamily D) σ

end SixDimensionalQuotientData

end QuotientSubmoduleEquidistribution.LoopTwoCycleFamily
