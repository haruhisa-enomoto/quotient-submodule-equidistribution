import OpConjecture.RepresentationTheory.LoopTwoCycleOppositeAlignment
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Basis-level constructor for the six-coordinate quotient

This file is an abstract bridge only.  It packages a surjective quotient,
an ordered six-element basis, the unit formula, and the complete basis
multiplication table.  From those data it constructs exactly
`LoopTwoCycleFamily.SixDimensionalQuotientData`, without constructing a
concrete quiver algebra or classifying any of its modules.
-/

noncomputable section

namespace OpConjecture.LoopTwoCycleFamily

universe u v

/-- Names of the ordered basis `e₁,e₂,x,a,b,ab`. -/
inductive SixBasisIndex
  | e₁ | e₂ | x | a | b | ab
  deriving DecidableEq

instance : Fintype SixBasisIndex where
  elems := {.e₁, .e₂, .x, .a, .b, .ab}
  complete i := by cases i <;> simp

namespace SixBasisIndex

/-- The coordinate function corresponding to an ordered basis vector. -/
def coordinateVector {K : Type u} [Field K]
    (i : SixBasisIndex) : SixCoordinates K :=
  match i with
  | .e₁ => ⟨1, 0, 0, 0, 0, 0⟩
  | .e₂ => ⟨0, 1, 0, 0, 0, 0⟩
  | .x => ⟨0, 0, 1, 0, 0, 0⟩
  | .a => ⟨0, 0, 0, 1, 0, 0⟩
  | .b => ⟨0, 0, 0, 0, 1, 0⟩
  | .ab => ⟨0, 0, 0, 0, 0, 1⟩

/-- The ordered coordinate equivalence indexed by the six basis names. -/
def funLinearEquiv (K : Type u) [Field K] :
    (SixBasisIndex → K) ≃ₗ[K] SixCoordinates K where
  toFun f := ⟨f .e₁, f .e₂, f .x, f .a, f .b, f .ab⟩
  invFun p := fun i =>
    match i with
    | .e₁ => p.e₁
    | .e₂ => p.e₂
    | .x => p.x
    | .a => p.a
    | .b => p.b
    | .ab => p.ab
  left_inv f := by
    funext i
    cases i <;> rfl
  right_inv p := rfl
  map_add' f g := by
    apply SixCoordinates.ext <;> rfl
  map_smul' c f := by
    apply SixCoordinates.ext <;> rfl

@[simp]
theorem funLinearEquiv_apply_single
    {K : Type u} [Field K] (i : SixBasisIndex) :
    funLinearEquiv K (Pi.single i 1) = coordinateVector i := by
  cases i <;> apply SixCoordinates.ext <;> simp [funLinearEquiv, coordinateVector]

/-- The complete nonzero part of the paper's multiplication table.  `none`
means that the corresponding product is zero. -/
def productIndex : SixBasisIndex → SixBasisIndex → Option SixBasisIndex
  | .e₁, .e₁ => some .e₁
  | .e₂, .e₂ => some .e₂
  | .e₁, .x => some .x
  | .x, .e₁ => some .x
  | .e₂, .a => some .a
  | .a, .e₁ => some .a
  | .e₁, .b => some .b
  | .b, .e₂ => some .b
  | .e₁, .ab => some .ab
  | .ab, .e₁ => some .ab
  | .b, .a => some .ab
  | _, _ => none

/-- Multiplying coordinate basis vectors gives exactly `productIndex`.
In particular, the only nonzero radical--radical product is `b * a = ab`. -/
theorem coordinateVector_mul (K : Type u) [Field K]
    (i j : SixBasisIndex) :
    SixCoordinates.mul K (coordinateVector i) (coordinateVector j) =
      match productIndex i j with
      | none => 0
      | some k => coordinateVector k := by
  cases i <;> cases j <;>
    apply SixCoordinates.ext <;>
    simp [SixCoordinates.mul, coordinateVector, productIndex]

end SixBasisIndex

namespace SixCoordinates

/-- Multiplication by a fixed coordinate vector on the left is linear. -/
def mulLeftLinear {K : Type u} [Field K] (p : SixCoordinates K) :
    SixCoordinates K →ₗ[K] SixCoordinates K where
  toFun q := mul K p q
  map_add' q r := by
    apply SixCoordinates.ext <;> simp [mul] <;> ring
  map_smul' c q := by
    apply SixCoordinates.ext <;> simp [mul] <;> ring

/-- Multiplication by a fixed coordinate vector on the right is linear. -/
def mulRightLinear {K : Type u} [Field K] (q : SixCoordinates K) :
    SixCoordinates K →ₗ[K] SixCoordinates K where
  toFun p := mul K p q
  map_add' p r := by
    apply SixCoordinates.ext <;> simp [mul] <;> ring
  map_smul' c p := by
    apply SixCoordinates.ext <;> simp [mul] <;> ring

end SixCoordinates

/--
The strict basis-level predecessor of `SixDimensionalQuotientData`.

`basis_mul` is one finite premise (36 basis pairs), not an arbitrary-element
product identity.  Its right-hand side says precisely that the basis product
has the coordinate vector prescribed by the paper's multiplication table.
-/
structure SixCoordinateBasisQuotientData
    (K R S : Type u)
    [Field K]
    [Ring R]
    [Ring S] [Algebra K S] where
  quotient : R →+* S
  quotient_surjective : Function.Surjective quotient
  basis : Module.Basis SixBasisIndex K S
  one_eq : 1 = basis .e₁ + basis .e₂
  basis_mul : ∀ i j,
    basis i * basis j =
      basis.equivFun.symm
        ((SixBasisIndex.funLinearEquiv K).symm
          (SixCoordinates.mul K
            (SixBasisIndex.coordinateVector i)
            (SixBasisIndex.coordinateVector j)))

namespace SixCoordinateBasisQuotientData

variable {K R S : Type u}
  [Field K]
  [Ring R]
  [Ring S] [Algebra K S]

/-- The linear combination of a named six-tuple with a prescribed coordinate
vector.  This exposes the relation premise without mentioning a previously
constructed basis. -/
def linearCombination (v : SixBasisIndex → S) (p : SixCoordinates K) : S :=
  ∑ i, ((SixBasisIndex.funLinearEquiv K).symm p) i • v i

/-- The element prescribed by the finite basis multiplication table. -/
def basisProduct (v : SixBasisIndex → S)
    (i j : SixBasisIndex) : S :=
  match SixBasisIndex.productIndex i j with
  | none => 0
  | some k => v k

@[simp]
theorem linearCombination_coordinateVector
    (v : SixBasisIndex → S) (i : SixBasisIndex) :
    linearCombination v (SixBasisIndex.coordinateVector (K := K) i) = v i := by
  have hcoords :
      (SixBasisIndex.funLinearEquiv K).symm
          (SixBasisIndex.coordinateVector (K := K) i) = Pi.single i 1 := by
    rw [← SixBasisIndex.funLinearEquiv_apply_single,
      (SixBasisIndex.funLinearEquiv K).symm_apply_apply]
  rw [linearCombination, hcoords]
  simp

/-- The coordinate formula and the explicit zero/nonzero basis table agree. -/
theorem linearCombination_mul_coordinateVectors
    (v : SixBasisIndex → S) (i j : SixBasisIndex) :
    linearCombination v
        (SixCoordinates.mul K
          (SixBasisIndex.coordinateVector i)
          (SixBasisIndex.coordinateVector j)) =
      basisProduct v i j := by
  rw [SixBasisIndex.coordinateVector_mul]
  cases h : SixBasisIndex.productIndex i j with
  | none => simp [basisProduct, h, linearCombination]
  | some k =>
      simp [basisProduct, h]

/-- Build the basis-level quotient package directly from six named elements.
Linear independence and spanning are the exact basis hypotheses; `hMul` is
the finite table of products of those six elements. -/
def ofLinearIndependentSpanning
    (q : R →+* S) (hq : Function.Surjective q)
    (v : SixBasisIndex → S)
    (hIndependent : LinearIndependent K v)
    (hSpans : ⊤ ≤ Submodule.span K (Set.range v))
    (hOne : 1 = v .e₁ + v .e₂)
    (hMul : ∀ i j,
      v i * v j =
        linearCombination v
          (SixCoordinates.mul K
            (SixBasisIndex.coordinateVector i)
            (SixBasisIndex.coordinateVector j))) :
    SixCoordinateBasisQuotientData K R S where
  quotient := q
  quotient_surjective := hq
  basis := Module.Basis.mk hIndependent hSpans
  one_eq := by simpa using hOne
  basis_mul i j := by
    rw [Module.Basis.equivFun_symm_apply]
    simpa [linearCombination] using hMul i j

/-- User-facing constructor from the paper's explicit multiplication
relations.  The premise `hMul` reduces by cases to the eleven nonzero products
listed in `SixBasisIndex.productIndex` and zero for every other pair. -/
def ofLinearIndependentSpanningRelations
    (q : R →+* S) (hq : Function.Surjective q)
    (v : SixBasisIndex → S)
    (hIndependent : LinearIndependent K v)
    (hSpans : ⊤ ≤ Submodule.span K (Set.range v))
    (hOne : 1 = v .e₁ + v .e₂)
    (hMul : ∀ i j, v i * v j = basisProduct v i j) :
    SixCoordinateBasisQuotientData K R S :=
  ofLinearIndependentSpanning q hq v hIndependent hSpans hOne fun i j =>
    (hMul i j).trans (linearCombination_mul_coordinateVectors v i j).symm

/-- Coordinates of the ordered basis. -/
def coord (D : SixCoordinateBasisQuotientData K R S) :
    S ≃ₗ[K] SixCoordinates K :=
  D.basis.equivFun ≪≫ₗ SixBasisIndex.funLinearEquiv K

@[simp]
theorem coord_basis (D : SixCoordinateBasisQuotientData K R S)
    (i : SixBasisIndex) :
    D.coord (D.basis i) = SixBasisIndex.coordinateVector i := by
  change SixBasisIndex.funLinearEquiv K (D.basis.equivFun (D.basis i)) = _
  rw [show D.basis.equivFun (D.basis i) = Pi.single i 1 by
    funext j
    by_cases h : i = j
    · subst j
      simp [Module.Basis.equivFun_self]
    · simp [Module.Basis.equivFun_self, h, Ne.symm h]]
  exact SixBasisIndex.funLinearEquiv_apply_single i

@[simp]
theorem coord_symm_coordinateVector
    (D : SixCoordinateBasisQuotientData K R S)
    (i : SixBasisIndex) :
    D.coord.symm (SixBasisIndex.coordinateVector i) = D.basis i := by
  apply D.coord.injective
  rw [D.coord.apply_symm_apply, coord_basis]

/-- The basis multiplication table transported to coordinates. -/
theorem coord_basis_mul
    (D : SixCoordinateBasisQuotientData K R S)
    (i j : SixBasisIndex) :
    D.coord (D.basis i * D.basis j) =
      SixCoordinates.mul K
        (SixBasisIndex.coordinateVector i)
        (SixBasisIndex.coordinateVector j) := by
  rw [D.basis_mul]
  change
    SixBasisIndex.funLinearEquiv K
        (D.basis.equivFun
          (D.basis.equivFun.symm
            ((SixBasisIndex.funLinearEquiv K).symm _))) = _
  rw [D.basis.equivFun.apply_symm_apply,
    (SixBasisIndex.funLinearEquiv K).apply_symm_apply]

/-- For a fixed basis vector on the left, the table determines products with
every element on the right. -/
theorem coord_basis_mul_all
    (D : SixCoordinateBasisQuotientData K R S)
    (i : SixBasisIndex) (s : S) :
    D.coord (D.basis i * s) =
      SixCoordinates.mul K
        (SixBasisIndex.coordinateVector i) (D.coord s) := by
  let f : S →ₗ[K] SixCoordinates K :=
    D.coord.toLinearMap.comp (LinearMap.mulLeft K (D.basis i))
  let g : S →ₗ[K] SixCoordinates K :=
    (SixCoordinates.mulLeftLinear (SixBasisIndex.coordinateVector i)).comp
      D.coord.toLinearMap
  have hfg : f = g := by
    apply D.basis.ext
    intro j
    simpa [f, g, SixCoordinates.mulLeftLinear] using
      D.coord_basis_mul i j
  exact DFunLike.congr_fun hfg s

/-- Bilinearity upgrades the 36 basis products to the complete multiplication
formula for arbitrary quotient elements. -/
theorem coord_mul
    (D : SixCoordinateBasisQuotientData K R S)
    (r s : S) :
    D.coord (r * s) = SixCoordinates.mul K (D.coord r) (D.coord s) := by
  let f : S →ₗ[K] SixCoordinates K :=
    D.coord.toLinearMap.comp (LinearMap.mulRight K s)
  let g : S →ₗ[K] SixCoordinates K :=
    (SixCoordinates.mulRightLinear (D.coord s)).comp D.coord.toLinearMap
  have hfg : f = g := by
    apply D.basis.ext
    intro i
    simpa [f, g, SixCoordinates.mulRightLinear] using
      D.coord_basis_mul_all i s
  exact DFunLike.congr_fun hfg r

/-- The unit formula in the target coordinate convention. -/
theorem coord_one (D : SixCoordinateBasisQuotientData K R S) :
    D.coord 1 = (⟨1, 1, 0, 0, 0, 0⟩ : SixCoordinates K) := by
  rw [D.one_eq, map_add, coord_basis, coord_basis]
  apply SixCoordinates.ext <;> simp [SixBasisIndex.coordinateVector]

/-- The exact coordinate datum consumed by the parameter-family proof. -/
def toSixDimensionalQuotientData
    (D : SixCoordinateBasisQuotientData K R S) :
    SixDimensionalQuotientData K S where
  coord := D.coord
  coord_one := D.coord_one
  coord_mul := D.coord_mul

/-- The resulting representation-infinite contradiction, retaining the
surjective quotient map packaged by this basis-level predecessor. -/
theorem false_of_finite_skeleton
    [IsNoetherianRing R] [Infinite K]
    (D : SixCoordinateBasisQuotientData K R S)
    {ι : Type v} [Finite ι]
    (σ : OpConjecture.IndecomposableSkeleton.{u, v, u} R ι) : False :=
  SixDimensionalQuotientData.false_of_surjection_to_sixDimensionalQuotient
    D.quotient D.quotient_surjective
    D.toSixDimensionalQuotientData σ

/-- Paper-facing right-module endpoint: the same abstract basis and table
contradict a finite complete skeleton over the opposite of a
finite-dimensional source algebra. -/
theorem false_of_right_finite_skeleton
    [Algebra K R] [FiniteDimensional K R] [Infinite K]
    (D : SixCoordinateBasisQuotientData K R S) :
    letI : IsNoetherianRing Rᵐᵒᵖ :=
      IsNoetherianRing.of_finite K Rᵐᵒᵖ
    ∀ {ι : Type v} [Finite ι],
      OpConjecture.IndecomposableSkeleton.{u, v, u} Rᵐᵒᵖ ι →
        False := by
  letI : IsNoetherianRing Rᵐᵒᵖ :=
    IsNoetherianRing.of_finite K Rᵐᵒᵖ
  intro ι _ σ
  exact
    SixDimensionalQuotientData.false_of_right_finite_skeleton
      D.quotient D.quotient_surjective
      D.toSixDimensionalQuotientData σ

end SixCoordinateBasisQuotientData

end OpConjecture.LoopTwoCycleFamily
