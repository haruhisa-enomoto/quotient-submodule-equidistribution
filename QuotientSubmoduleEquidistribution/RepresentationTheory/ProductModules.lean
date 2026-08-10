import Mathlib.Algebra.Category.ModuleCat.Biproducts
import QuotientSubmoduleEquidistribution.RepresentationTheory.SkeletonAlignment
import QuotientSubmoduleEquidistribution.ConvexGeometry.ComponentwiseProduct

/-!
# Modules over a product ring

Maintained construction of the concrete equivalence between modules over
`A × B` and pairs of modules over `A` and `B`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.ProductModules

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

/-- Componentwise preadditive structure on a product category. -/
instance productCategoryPreadditive
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] : Preadditive (C × D) where
  homGroup := fun X Y ↦
    show AddCommGroup ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)) from inferInstance
  add_comp := by
    intros
    apply Prod.hom_ext <;> simp [Prod.fst_add, Prod.snd_add]
  comp_add := by
    intros
    apply Prod.hom_ext <;> simp [Prod.fst_add, Prod.snd_add]

/-- The first projection from a product of preadditive categories is
additive for the componentwise structure above. -/
instance productFstAdditive
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] :
    (CategoryTheory.Prod.fst C D).Additive where
  map_add := by
    intros
    rfl

/-- The second projection from a product of preadditive categories is
additive for the componentwise structure above. -/
instance productSndAdditive
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] :
    (CategoryTheory.Prod.snd C D).Additive where
  map_add := by
    intros
    rfl

universe u v w

variable {A : Type u} {B : Type u} [Ring A] [Ring B]

/-- Projection onto the summand cut out by `(1, 0)`. -/
def leftProjection (M : ModuleCat.{v} (A × B)) : M →ₗ[A × B] M where
  toFun x := ((1 : A), (0 : B)) • x
  map_add' x y := smul_add ((1 : A), (0 : B)) x y
  map_smul' r x := by
    change ((1 : A), (0 : B)) • (r • x) =
      r • (((1 : A), (0 : B)) • x)
    calc
      _ = (((1 : A), (0 : B)) * r) • x :=
        (mul_smul ((1 : A), (0 : B)) r x).symm
      _ = (r * ((1 : A), (0 : B))) • x := by
        congr 1
        ext <;> simp
      _ = _ := mul_smul r ((1 : A), (0 : B)) x

/-- Projection onto the summand cut out by `(0, 1)`. -/
def rightProjection (M : ModuleCat.{v} (A × B)) : M →ₗ[A × B] M where
  toFun x := ((0 : A), (1 : B)) • x
  map_add' x y := smul_add ((0 : A), (1 : B)) x y
  map_smul' r x := by
    change ((0 : A), (1 : B)) • (r • x) =
      r • (((0 : A), (1 : B)) • x)
    calc
      _ = (((0 : A), (1 : B)) * r) • x :=
        (mul_smul ((0 : A), (1 : B)) r x).symm
      _ = (r * ((0 : A), (1 : B))) • x := by
        congr 1
        ext <;> simp
      _ = _ := mul_smul r ((0 : A), (1 : B)) x

/-- The `(1,0)`-summand of a product-ring module. -/
abbrev leftPart (M : ModuleCat.{v} (A × B)) :=
  (leftProjection M).range

/-- The `(0,1)`-summand of a product-ring module. -/
abbrev rightPart (M : ModuleCat.{v} (A × B)) :=
  (rightProjection M).range

instance leftPartModule (M : ModuleCat.{v} (A × B)) :
    Module A (leftPart M) where
  smul a x := ⟨(a, 0) • (x : M),
    (leftProjection M).range.smul_mem (a, 0) x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((1 : A), (0 : B)) • (x : M) = (x : M)
    rcases x.2 with ⟨y, hy⟩
    calc
      _ = ((1 : A), (0 : B)) •
          (((1 : A), (0 : B)) • y) := by
        simpa [leftProjection] using
          (congrArg (fun z : M ↦ ((1 : A), (0 : B)) • z) hy).symm
      _ = ((1 : A), (0 : B)) • y := by
        rw [← mul_smul]
        simp
      _ = _ := hy
  mul_smul a b x := by
    apply Subtype.ext
    change (a * b, 0) • (x : M) = (a, 0) • ((b, 0) • (x : M))
    rw [← mul_smul]
    simp
  smul_zero a := by
    apply Subtype.ext
    exact smul_zero _
  smul_add a x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  add_smul a b x := by
    apply Subtype.ext
    change (a + b, 0) • (x : M) =
      (a, 0) • (x : M) + (b, 0) • (x : M)
    simpa using add_smul (a, (0 : B)) (b, (0 : B)) (x : M)
  zero_smul x := by
    apply Subtype.ext
    exact zero_smul _ _

instance rightPartModule (M : ModuleCat.{v} (A × B)) :
    Module B (rightPart M) where
  smul b x := ⟨(0, b) • (x : M),
    (rightProjection M).range.smul_mem (0, b) x.2⟩
  one_smul x := by
    apply Subtype.ext
    change ((0 : A), (1 : B)) • (x : M) = (x : M)
    rcases x.2 with ⟨y, hy⟩
    calc
      _ = ((0 : A), (1 : B)) •
          (((0 : A), (1 : B)) • y) := by
        simpa [rightProjection] using
          (congrArg (fun z : M ↦ ((0 : A), (1 : B)) • z) hy).symm
      _ = ((0 : A), (1 : B)) • y := by
        rw [← mul_smul]
        simp
      _ = _ := hy
  mul_smul a b x := by
    apply Subtype.ext
    change (0, a * b) • (x : M) = (0, a) • ((0, b) • (x : M))
    rw [← mul_smul]
    simp
  smul_zero a := by
    apply Subtype.ext
    exact smul_zero _
  smul_add a x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  add_smul a b x := by
    apply Subtype.ext
    change (0, a + b) • (x : M) =
      (0, a) • (x : M) + (0, b) • (x : M)
    simpa using add_smul ((0 : A), a) ((0 : A), b) (x : M)
  zero_smul x := by
    apply Subtype.ext
    exact zero_smul _ _

/-- The left summand bundled as an `A`-module. -/
def leftPartObj (M : ModuleCat.{v} (A × B)) : ModuleCat.{v} A :=
  ModuleCat.of A (leftPart M)

/-- The right summand bundled as a `B`-module. -/
def rightPartObj (M : ModuleCat.{v} (A × B)) : ModuleCat.{v} B :=
  ModuleCat.of B (rightPart M)

/-- A product-ring linear map restricts to the left idempotent summands. -/
def leftPartMap {M N : ModuleCat.{v} (A × B)} (f : M ⟶ N) :
    leftPart M →ₗ[A] leftPart N where
  toFun x := ⟨f x, by
    rcases x.2 with ⟨y, hy⟩
    refine ⟨f y, ?_⟩
    change ((1 : A), (0 : B)) • f y = f x
    rw [← hy]
    exact (f.hom.map_smul ((1 : A), (0 : B)) y).symm⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.hom.map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    exact f.hom.map_smul (a, 0) x

/-- A product-ring linear map restricts to the right idempotent summands. -/
def rightPartMap {M N : ModuleCat.{v} (A × B)} (f : M ⟶ N) :
    rightPart M →ₗ[B] rightPart N where
  toFun x := ⟨f x, by
    rcases x.2 with ⟨y, hy⟩
    refine ⟨f y, ?_⟩
    change ((0 : A), (1 : B)) • f y = f x
    rw [← hy]
    exact (f.hom.map_smul ((0 : A), (1 : B)) y).symm⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.hom.map_add _ _
  map_smul' b x := by
    apply Subtype.ext
    exact f.hom.map_smul (0, b) x

/-- Send a product-ring module to its two central-idempotent summands. -/
def splitFunctor :
    ModuleCat.{v} (A × B) ⥤ (ModuleCat.{v} A × ModuleCat.{v} B) where
  obj M := (ModuleCat.of A (leftPart M), ModuleCat.of B (rightPart M))
  map f := Prod.mkHom (ModuleCat.ofHom (leftPartMap f))
    (ModuleCat.ofHom (rightPartMap f))
  map_id M := by
    apply Prod.ext <;> apply ModuleCat.hom_ext <;> ext x <;> rfl
  map_comp f g := by
    apply Prod.ext <;> apply ModuleCat.hom_ext <;> ext x <;> rfl

/-- The componentwise product module structure on `X × Y`. -/
@[reducible] def productModule (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B) :
    Module (A × B) (X × Y) where
  smul r x := (r.1 • x.1, r.2 • x.2)
  one_smul x := by
    change ((1 : A) • x.1, (1 : B) • x.2) = x
    ext <;> simp
  mul_smul r s x := by
    change ((r.1 * s.1) • x.1, (r.2 * s.2) • x.2) =
      (r.1 • (s.1 • x.1), r.2 • (s.2 • x.2))
    ext <;> exact mul_smul _ _ _
  smul_zero r := by
    change (r.1 • (0 : X), r.2 • (0 : Y)) = 0
    ext <;> exact smul_zero _
  smul_add r x y := by
    change (r.1 • (x.1 + y.1), r.2 • (x.2 + y.2)) =
      (r.1 • x.1 + r.1 • y.1, r.2 • x.2 + r.2 • y.2)
    ext <;> exact smul_add _ _ _
  add_smul r s x := by
    change ((r.1 + s.1) • x.1, (r.2 + s.2) • x.2) =
      (r.1 • x.1 + s.1 • x.1, r.2 • x.2 + s.2 • x.2)
    ext <;> exact add_smul _ _ _
  zero_smul x := by
    change ((0 : A) • x.1, (0 : B) • x.2) = 0
    ext <;> exact zero_smul _ _

/-- The product of an `A`-linear and a `B`-linear map. -/
def productMap {X X' : ModuleCat.{v} A} {Y Y' : ModuleCat.{v} B}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := productModule X Y
    letI := productModule X' Y'
    (X × Y) →ₗ[A × B] (X' × Y') := by
  letI := productModule X Y
  letI := productModule X' Y'
  exact
    { toFun := fun x ↦ (f x.1, g x.2)
      map_add' := fun x y ↦ by ext <;> simp
      map_smul' := fun r x ↦ by
        change (f (r.1 • x.1), g (r.2 • x.2)) =
          (r.1 • f x.1, r.2 • g x.2)
        ext
        · exact f.hom.map_smul r.1 x.1
        · exact g.hom.map_smul r.2 x.2 }

/-- Assemble a pair of factor modules into a product-ring module. -/
def assembleFunctor :
    (ModuleCat.{v} A × ModuleCat.{v} B) ⥤ ModuleCat.{v} (A × B) where
  obj P := by
    letI := productModule P.1 P.2
    exact ModuleCat.of (A × B) (P.1 × P.2)
  map {X Y} f := by
    letI := productModule X.1 X.2
    letI := productModule Y.1 Y.2
    exact ModuleCat.ofHom (productMap f.1 f.2)
  map_id P := by
    letI := productModule P.1 P.2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp {X Y Z} f g := by
    letI := productModule X.1 X.2
    letI := productModule Y.1 Y.2
    letI := productModule Z.1 Z.2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp]
theorem leftPart_fixed (M : ModuleCat.{v} (A × B)) (x : leftPart M) :
    ((1 : A), (0 : B)) • (x : M) = x := by
  rcases x.2 with ⟨y, hy⟩
  calc
    _ = ((1 : A), (0 : B)) •
        (((1 : A), (0 : B)) • y) := by
      simpa [leftProjection] using
        (congrArg (fun z : M ↦ ((1 : A), (0 : B)) • z) hy).symm
    _ = ((1 : A), (0 : B)) • y := by
      rw [← mul_smul]
      simp
    _ = _ := hy

@[simp]
theorem rightPart_fixed (M : ModuleCat.{v} (A × B)) (x : rightPart M) :
    ((0 : A), (1 : B)) • (x : M) = x := by
  rcases x.2 with ⟨y, hy⟩
  calc
    _ = ((0 : A), (1 : B)) •
        (((0 : A), (1 : B)) • y) := by
      simpa [rightProjection] using
        (congrArg (fun z : M ↦ ((0 : A), (1 : B)) • z) hy).symm
    _ = ((0 : A), (1 : B)) • y := by
      rw [← mul_smul]
      simp
    _ = _ := hy

@[simp]
theorem right_smul_leftPart (M : ModuleCat.{v} (A × B))
    (x : leftPart M) :
    ((0 : A), (1 : B)) • (x : M) = 0 := by
  rcases x.2 with ⟨y, hy⟩
  rw [← hy]
  change ((0 : A), (1 : B)) •
    (((1 : A), (0 : B)) • y) = 0
  rw [← mul_smul]
  calc
    (((0 : A), (1 : B)) * ((1 : A), (0 : B))) • y =
        (0 : A × B) • y := by
      congr 1
      ext <;> simp
    _ = 0 := zero_smul (A × B) y

@[simp]
theorem left_smul_rightPart (M : ModuleCat.{v} (A × B))
    (x : rightPart M) :
    ((1 : A), (0 : B)) • (x : M) = 0 := by
  rcases x.2 with ⟨y, hy⟩
  rw [← hy]
  change ((1 : A), (0 : B)) •
    (((0 : A), (1 : B)) • y) = 0
  rw [← mul_smul]
  calc
    (((1 : A), (0 : B)) * ((0 : A), (1 : B))) • y =
        (0 : A × B) • y := by
      congr 1
      ext <;> simp
    _ = 0 := zero_smul (A × B) y

/-- Every product-ring module is linearly equivalent to the product of its
two central-idempotent summands. -/
def splitAssembleLinearEquiv (M : ModuleCat.{v} (A × B)) :
    letI := productModule
      (ModuleCat.of A (leftPart M)) (ModuleCat.of B (rightPart M))
    M ≃ₗ[A × B] (leftPart M × rightPart M) := by
  letI := productModule
    (ModuleCat.of A (leftPart M)) (ModuleCat.of B (rightPart M))
  exact
    { toFun := fun x ↦
        (⟨((1 : A), (0 : B)) • x, ⟨x, by simp [leftProjection]⟩⟩,
          ⟨((0 : A), (1 : B)) • x, ⟨x, by simp [rightProjection]⟩⟩)
      invFun := fun p ↦ (p.1 : M) + (p.2 : M)
      left_inv := fun x ↦ by
        change ((1 : A), (0 : B)) • x +
          ((0 : A), (1 : B)) • x = x
        rw [← add_smul]
        calc
          _ = (1 : A × B) • x := by
            congr 1
            apply Prod.ext <;> simp
          _ = x := one_smul (A × B) x
      right_inv := fun p ↦ by
        apply Prod.ext <;> apply Subtype.ext
        · change ((1 : A), (0 : B)) •
            ((p.1 : M) + (p.2 : M)) = p.1
          rw [smul_add, leftPart_fixed, left_smul_rightPart, add_zero]
        · change ((0 : A), (1 : B)) •
            ((p.1 : M) + (p.2 : M)) = p.2
          rw [smul_add, right_smul_leftPart, rightPart_fixed, zero_add]
      map_add' := fun x y ↦ by
        apply Prod.ext <;> apply Subtype.ext <;> exact smul_add _ _ _
      map_smul' := fun r x ↦ by
        apply Prod.ext <;> apply Subtype.ext
        · change ((1 : A), (0 : B)) • (r • x) =
            (r.1, (0 : B)) • (((1 : A), (0 : B)) • x)
          simp only [← mul_smul]
          congr 1
          ext <;> simp
        · change ((0 : A), (1 : B)) • (r • x) =
            ((0 : A), r.2) • (((0 : A), (1 : B)) • x)
          simp only [← mul_smul]
          congr 1
          ext <;> simp }

/-- The unit isomorphism for splitting and reassembling a product-ring
module. -/
def splitAssembleUnitIso :
    𝟭 (ModuleCat.{v} (A × B)) ≅ splitFunctor ⋙ assembleFunctor :=
  NatIso.ofComponents
    (fun M ↦ LinearEquiv.toModuleIso (splitAssembleLinearEquiv M))
    (fun {M N} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> apply Subtype.ext
      · simp only [Functor.id_map, Functor.comp_map,
          ModuleCat.hom_comp, LinearEquiv.toModuleIso_hom,
          LinearMap.comp_apply]
        dsimp [splitAssembleLinearEquiv, splitFunctor,
          assembleFunctor, productMap, leftPartMap]
        exact (f.hom.map_smul ((1 : A), (0 : B)) x).symm
      · simp only [Functor.id_map, Functor.comp_map,
          ModuleCat.hom_comp, LinearEquiv.toModuleIso_hom,
          LinearMap.comp_apply]
        dsimp [splitAssembleLinearEquiv, splitFunctor,
          assembleFunctor, productMap, rightPartMap]
        exact (f.hom.map_smul ((0 : A), (1 : B)) x).symm)

/-- The left summand of an assembled pair is its original left module. -/
def leftSplitAssembleLinearEquiv
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B) :
    letI := productModule X Y
    leftPartObj (ModuleCat.of (A × B) (X × Y)) ≃ₗ[A] X := by
  letI := productModule X Y
  letI : Module A
      (leftPart (ModuleCat.of (A × B) (X × Y))) :=
    leftPartModule (A := A) (B := B)
      (ModuleCat.of (A × B) (X × Y))
  unfold leftPartObj
  exact
    { toFun := fun z ↦ (z : X × Y).1
      invFun := fun x ↦ ⟨(x, 0), ⟨(x, 0), by
        change (((1 : A) • x, (0 : B) • (0 : Y))) = (x, 0)
        ext <;> simp⟩⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        rcases z.2 with ⟨p, hp⟩
        change ((z : X × Y).1, 0) = (z : X × Y)
        have hp' : (p.1, 0) = (z : X × Y) := by
          change ((1 : A) • p.1, (0 : B) • p.2) =
            (z : X × Y) at hp
          simpa using hp
        rw [← hp']
      right_inv := fun x ↦ rfl
      map_add' := fun x y ↦ rfl
      map_smul' := fun a x ↦ rfl }

/-- The right summand of an assembled pair is its original right module. -/
def rightSplitAssembleLinearEquiv
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B) :
    letI := productModule X Y
    rightPartObj (ModuleCat.of (A × B) (X × Y)) ≃ₗ[B] Y := by
  letI := productModule X Y
  letI : Module B
      (rightPart (ModuleCat.of (A × B) (X × Y))) :=
    rightPartModule (A := A) (B := B)
      (ModuleCat.of (A × B) (X × Y))
  unfold rightPartObj
  exact
    { toFun := fun z ↦ (z : X × Y).2
      invFun := fun y ↦ ⟨(0, y), ⟨(0, y), by
        change (((0 : A) • (0 : X), (1 : B) • y)) = (0, y)
        ext <;> simp⟩⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        rcases z.2 with ⟨p, hp⟩
        change (0, (z : X × Y).2) = (z : X × Y)
        have hp' : (0, p.2) = (z : X × Y) := by
          change ((0 : A) • p.1, (1 : B) • p.2) =
            (z : X × Y) at hp
          simpa using hp
        rw [← hp']
      right_inv := fun y ↦ rfl
      map_add' := fun x y ↦ rfl
      map_smul' := fun b x ↦ rfl }

/-- The counit isomorphism for reassembling and splitting a pair. -/
def splitAssembleCounitIso :
    assembleFunctor ⋙ splitFunctor ≅
      𝟭 (ModuleCat.{v} A × ModuleCat.{v} B) :=
  NatIso.ofComponents
    (fun P ↦ Iso.prod
      (LinearEquiv.toModuleIso
        (leftSplitAssembleLinearEquiv P.1 P.2))
      (LinearEquiv.toModuleIso
        (rightSplitAssembleLinearEquiv P.1 P.2)))
    (fun {P Q} f ↦ by
      letI := productModule P.1 P.2
      letI := productModule Q.1 Q.2
      apply Prod.hom_ext
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change leftPart
          (ModuleCat.of (A × B) (P.1 × P.2)) at x
        simp only [Functor.comp_map, Functor.id_map]
        dsimp [assembleFunctor, splitFunctor, productMap, leftPartMap,
          leftSplitAssembleLinearEquiv, Iso.prod, LinearEquiv.toModuleIso]
        change f.1 ((x : P.1 × P.2).1) =
          f.1 ((x : P.1 × P.2).1)
        rfl
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change rightPart
          (ModuleCat.of (A × B) (P.1 × P.2)) at x
        simp only [Functor.comp_map, Functor.id_map]
        dsimp [assembleFunctor, splitFunctor, productMap, rightPartMap,
          rightSplitAssembleLinearEquiv, Iso.prod, LinearEquiv.toModuleIso]
        change f.2 ((x : P.1 × P.2).2) =
          f.2 ((x : P.1 × P.2).2)
        rfl)

/-- Modules over a product ring are equivalent to pairs of modules over the
two factors. -/
def moduleEquivalence :
    ModuleCat.{v} (A × B) ≌
      (ModuleCat.{v} A × ModuleCat.{v} B) :=
  CategoryTheory.Equivalence.mk splitFunctor assembleFunctor
    splitAssembleUnitIso splitAssembleCounitIso

/-! ## Restriction to finitely generated modules -/

/-- The left projection as a semilinear map along the surjective ring
projection `A × B → A`. -/
def leftProjectionSemilinear (M : ModuleCat.{v} (A × B)) :
    M →ₛₗ[RingHom.fst A B] leftPart M where
  toFun x := ⟨((1 : A), (0 : B)) • x, ⟨x, by simp [leftProjection]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change ((1 : A), (0 : B)) • (r • x) =
      (r.1, (0 : B)) • (((1 : A), (0 : B)) • x)
    simp only [← mul_smul]
    congr 1
    ext <;> simp

/-- The right projection as a semilinear map along `A × B → B`. -/
def rightProjectionSemilinear (M : ModuleCat.{v} (A × B)) :
    M →ₛₗ[RingHom.snd A B] rightPart M where
  toFun x := ⟨((0 : A), (1 : B)) • x, ⟨x, by simp [rightProjection]⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    change ((0 : A), (1 : B)) • (r • x) =
      ((0 : A), r.2) • (((0 : A), (1 : B)) • x)
    simp only [← mul_smul]
    congr 1
    ext <;> simp

/-- The left central-idempotent summand of a finitely generated product-ring
module is finitely generated over the left factor. -/
theorem leftPart_finite (M : FGModuleCat.{v} (A × B)) :
    Module.Finite A (leftPart M.obj) := by
  apply Module.Finite.of_surjective (leftProjectionSemilinear M.obj)
  intro x
  rcases x.2 with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- The right central-idempotent summand is finitely generated over the right
factor. -/
theorem rightPart_finite (M : FGModuleCat.{v} (A × B)) :
    Module.Finite B (rightPart M.obj) := by
  apply Module.Finite.of_surjective (rightProjectionSemilinear M.obj)
  intro x
  rcases x.2 with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hy

/-- A finite `A`-module remains finite over `A × B` when the action is
pulled back along the first projection. -/
theorem finite_comp_fst (X : FGModuleCat.{v} A) :
    letI := Module.compHom X (RingHom.fst A B)
    Module.Finite (A × B) X := by
  letI := Module.compHom X (RingHom.fst A B)
  let identity : X →ₛₗ[RingHom.fst A B] X :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (identity.finite_iff_of_bijective ⟨Function.injective_id,
    Function.surjective_id⟩).mpr inferInstance

/-- The analogous finite-generation result for the second projection. -/
theorem finite_comp_snd (Y : FGModuleCat.{v} B) :
    letI := Module.compHom Y (RingHom.snd A B)
    Module.Finite (A × B) Y := by
  letI := Module.compHom Y (RingHom.snd A B)
  let identity : Y →ₛₗ[RingHom.snd A B] Y :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact (identity.finite_iff_of_bijective ⟨Function.injective_id,
    Function.surjective_id⟩).mpr inferInstance

/-- The componentwise product of two finitely generated factor modules is
finitely generated over the product ring. -/
theorem product_finite (X : FGModuleCat.{v} A) (Y : FGModuleCat.{v} B) :
    letI := productModule X.obj Y.obj
    Module.Finite (A × B) (X × Y) := by
  letI leftModule : Module (A × B) X :=
    Module.compHom X (RingHom.fst A B)
  letI rightModule : Module (A × B) Y :=
    Module.compHom Y (RingHom.snd A B)
  letI leftFinite : Module.Finite (A × B) X :=
    finite_comp_fst (B := B) X
  letI rightFinite : Module.Finite (A × B) Y :=
    finite_comp_snd (A := A) Y
  letI defaultProductModule : Module (A × B) (X × Y) :=
    inferInstance
  have defaultFinite : Module.Finite (A × B) (X × Y) :=
    inferInstance
  letI componentwiseModule : Module (A × B) (X × Y) :=
    productModule X.obj Y.obj
  have modules_eq : defaultProductModule = componentwiseModule := by
    rfl
  change @Module.Finite (A × B) (X × Y) _ _ componentwiseModule
  exact modules_eq ▸
    (show @Module.Finite (A × B) (X × Y) _ _ defaultProductModule
      from defaultFinite)

/-- Split a finitely generated product-ring module into two finitely
generated factor modules. -/
def fgSplitFunctor :
    FGModuleCat.{v} (A × B) ⥤
      (FGModuleCat.{v} A × FGModuleCat.{v} B) where
  obj M :=
    (⟨leftPartObj M.obj, leftPart_finite M⟩,
      ⟨rightPartObj M.obj, rightPart_finite M⟩)
  map {M N} f := by
    letI : Module.Finite A (leftPart M.obj) := leftPart_finite M
    letI : Module.Finite A (leftPart N.obj) := leftPart_finite N
    letI : Module.Finite B (rightPart M.obj) := rightPart_finite M
    letI : Module.Finite B (rightPart N.obj) := rightPart_finite N
    exact Prod.mkHom
      (FGModuleCat.ofHom (leftPartMap f.hom))
      (FGModuleCat.ofHom (rightPartMap f.hom))
  map_id M := by
    letI : Module.Finite A (leftPart M.obj) := leftPart_finite M
    letI : Module.Finite B (rightPart M.obj) := rightPart_finite M
    apply Prod.hom_ext
    · apply FGModuleCat.hom_ext
      ext x
      rfl
    · apply FGModuleCat.hom_ext
      ext x
      rfl
  map_comp {M N P} f g := by
    letI : Module.Finite A (leftPart M.obj) := leftPart_finite M
    letI : Module.Finite A (leftPart N.obj) := leftPart_finite N
    letI : Module.Finite A (leftPart P.obj) := leftPart_finite P
    letI : Module.Finite B (rightPart M.obj) := rightPart_finite M
    letI : Module.Finite B (rightPart N.obj) := rightPart_finite N
    letI : Module.Finite B (rightPart P.obj) := rightPart_finite P
    apply Prod.hom_ext
    · apply FGModuleCat.hom_ext
      ext x
      rfl
    · apply FGModuleCat.hom_ext
      ext x
      rfl

/-- Reassemble a pair of finitely generated factor modules. -/
def fgAssembleFunctor :
    (FGModuleCat.{v} A × FGModuleCat.{v} B) ⥤
      FGModuleCat.{v} (A × B) where
  obj P := by
    letI := productModule P.1.obj P.2.obj
    exact ⟨ModuleCat.of (A × B) (P.1 × P.2), product_finite P.1 P.2⟩
  map {X Y} f := by
    letI := productModule X.1.obj X.2.obj
    letI := productModule Y.1.obj Y.2.obj
    letI : Module.Finite (A × B) (X.1 × X.2) :=
      product_finite X.1 X.2
    letI : Module.Finite (A × B) (Y.1 × Y.2) :=
      product_finite Y.1 Y.2
    exact FGModuleCat.ofHom (productMap f.1.hom f.2.hom)
  map_id P := by
    letI := productModule P.1.obj P.2.obj
    letI : Module.Finite (A × B) (P.1 × P.2) :=
      product_finite P.1 P.2
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp {X Y Z} f g := by
    letI := productModule X.1.obj X.2.obj
    letI := productModule Y.1.obj Y.2.obj
    letI := productModule Z.1.obj Z.2.obj
    letI : Module.Finite (A × B) (X.1 × X.2) :=
      product_finite X.1 X.2
    letI : Module.Finite (A × B) (Y.1 × Y.2) :=
      product_finite Y.1 Y.2
    letI : Module.Finite (A × B) (Z.1 × Z.2) :=
      product_finite Z.1 Z.2
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The splitting/reassembly unit restricted to finitely generated modules. -/
def fgSplitAssembleUnitIso :
    𝟭 (FGModuleCat.{v} (A × B)) ≅
      fgSplitFunctor ⋙ fgAssembleFunctor :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _
      (splitAssembleUnitIso.app M.obj))
    (fun {M N} f ↦ by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext <;> apply Subtype.ext
      · simp only [Functor.id_map, Functor.comp_map,
          FGModuleCat.hom_hom_comp,
          LinearMap.comp_apply]
        dsimp [fgSplitFunctor, fgAssembleFunctor,
          splitAssembleLinearEquiv, productMap, leftPartMap]
        exact (f.hom.hom.map_smul ((1 : A), (0 : B)) x).symm
      · simp only [Functor.id_map, Functor.comp_map,
          FGModuleCat.hom_hom_comp,
          LinearMap.comp_apply]
        dsimp [fgSplitFunctor, fgAssembleFunctor,
          splitAssembleLinearEquiv, productMap, rightPartMap]
        exact (f.hom.hom.map_smul ((0 : A), (1 : B)) x).symm)

/-- The reassembly/splitting counit restricted to finitely generated modules. -/
def fgSplitAssembleCounitIso :
    fgAssembleFunctor ⋙ fgSplitFunctor ≅
      𝟭 (FGModuleCat.{v} A × FGModuleCat.{v} B) :=
  NatIso.ofComponents
    (fun P ↦ by
      letI := productModule P.1.obj P.2.obj
      exact Iso.prod
        (ObjectProperty.isoMk _ (LinearEquiv.toModuleIso
          (leftSplitAssembleLinearEquiv P.1.obj P.2.obj)))
        (ObjectProperty.isoMk _ (LinearEquiv.toModuleIso
          (rightSplitAssembleLinearEquiv P.1.obj P.2.obj))))
    (fun {P Q} f ↦ by
      letI := productModule P.1.obj P.2.obj
      letI := productModule Q.1.obj Q.2.obj
      apply Prod.hom_ext
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change leftPart
          (ModuleCat.of (A × B) (P.1 × P.2)) at x
        simp only [Functor.comp_map, Functor.id_map]
        dsimp [fgAssembleFunctor, fgSplitFunctor, productMap, leftPartMap,
          leftSplitAssembleLinearEquiv, Iso.prod,
          LinearEquiv.toFGModuleCatIso]
        change f.1.hom ((x : P.1 × P.2).1) =
          f.1.hom ((x : P.1 × P.2).1)
        rfl
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change rightPart
          (ModuleCat.of (A × B) (P.1 × P.2)) at x
        simp only [Functor.comp_map, Functor.id_map]
        dsimp [fgAssembleFunctor, fgSplitFunctor, productMap, rightPartMap,
          rightSplitAssembleLinearEquiv, Iso.prod,
          LinearEquiv.toFGModuleCatIso]
        change f.2.hom ((x : P.1 × P.2).2) =
          f.2.hom ((x : P.1 × P.2).2)
        rfl)

/-- Finitely generated modules over a product ring are equivalent to pairs
of finitely generated modules over the factors. -/
def fgModuleEquivalence :
    FGModuleCat.{v} (A × B) ≌
      (FGModuleCat.{v} A × FGModuleCat.{v} B) :=
  CategoryTheory.Equivalence.mk fgSplitFunctor fgAssembleFunctor
    fgSplitAssembleUnitIso fgSplitAssembleCounitIso

/-! ## Indecomposable modules have one-factor support -/

/-- The central projection cutting out the left factor is idempotent. -/
theorem leftProjection_isIdempotentElem (M : ModuleCat.{v} (A × B)) :
    IsIdempotentElem (leftProjection M) := by
  apply LinearMap.ext
  intro x
  change ((1 : A), (0 : B)) •
      (((1 : A), (0 : B)) • x) =
    ((1 : A), (0 : B)) • x
  rw [← mul_smul]
  simp

/-- An indecomposable module over `A × B` is supported on at most one
factor: one of its two central-idempotent summands is a singleton. -/
theorem indecomposable_leftPart_or_rightPart_subsingleton
    (M : ModuleCat.{v} (A × B))
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) M) :
    Subsingleton (leftPart M) ∨ Subsingleton (rightPart M) := by
  rcases hM.eq_zero_or_eq_one_of_isIdempotentElem
      (leftProjection_isIdempotentElem M) with hzero | hone
  · left
    constructor
    intro x y
    apply Subtype.ext
    have hx : (x : M) = 0 := by
      rw [← leftPart_fixed M x]
      change leftProjection M (x : M) = 0
      rw [hzero]
      rfl
    have hy : (y : M) = 0 := by
      rw [← leftPart_fixed M y]
      change leftProjection M (y : M) = 0
      rw [hzero]
      rfl
    exact hx.trans hy.symm
  · right
    constructor
    intro x y
    apply Subtype.ext
    have hx : (x : M) = 0 := by
      have hproj : leftProjection M (x : M) = (x : M) := by
        rw [hone]
        rfl
      rw [← hproj]
      exact left_smul_rightPart M x
    have hy : (y : M) = 0 := by
      have hproj : leftProjection M (y : M) = (y : M) := by
        rw [hone]
        rfl
      rw [← hproj]
      exact left_smul_rightPart M y
    exact hx.trans hy.symm

/-- If a componentwise product module is indecomposable and its right
component is trivial, then its left component is indecomposable. -/
theorem left_indecomposable_of_product
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B)
    (hY : Subsingleton Y)
    (h : letI := productModule X Y
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) (X × Y)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A X := by
  letI := productModule X Y
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · apply not_subsingleton_iff_nontrivial.mp
    intro hX
    haveI : Subsingleton X := hX
    haveI : Subsingleton Y := hY
    have hprod : Subsingleton (X × Y) := inferInstance
    exact not_subsingleton_iff_nontrivial.mpr h.nontrivial hprod
  · intro f hf
    let F : Module.End (A × B) (X × Y) :=
      productMap (ModuleCat.ofHom f) (0 : Y ⟶ Y)
    have hF : IsIdempotentElem F := by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · exact DFunLike.congr_fun hf z.1
      · exact Subsingleton.elim _ _
    rcases h.eq_zero_or_eq_one_of_isIdempotentElem hF with hzero | hone
    · left
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun hzero (x, (0 : Y))
      exact congrArg Prod.fst hx
    · right
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun hone (x, (0 : Y))
      exact congrArg Prod.fst hx

/-- If a componentwise product module is indecomposable and its left
component is trivial, then its right component is indecomposable. -/
theorem right_indecomposable_of_product
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B)
    (hX : Subsingleton X)
    (h : letI := productModule X Y
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) (X × Y)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule B Y := by
  letI := productModule X Y
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  constructor
  · apply not_subsingleton_iff_nontrivial.mp
    intro hY
    haveI : Subsingleton X := hX
    haveI : Subsingleton Y := hY
    have hprod : Subsingleton (X × Y) := inferInstance
    exact not_subsingleton_iff_nontrivial.mpr h.nontrivial hprod
  · intro f hf
    let F : Module.End (A × B) (X × Y) :=
      productMap (0 : X ⟶ X) (ModuleCat.ofHom f)
    have hF : IsIdempotentElem F := by
      apply LinearMap.ext
      intro z
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact DFunLike.congr_fun hf z.2
    rcases h.eq_zero_or_eq_one_of_isIdempotentElem hF with hzero | hone
    · left
      apply LinearMap.ext
      intro y
      have hy := DFunLike.congr_fun hzero ((0 : X), y)
      exact congrArg Prod.snd hy
    · right
      apply LinearMap.ext
      intro y
      have hy := DFunLike.congr_fun hone ((0 : X), y)
      exact congrArg Prod.snd hy

/-- An indecomposable left module, paired with a trivial right module, is
indecomposable for the product ring. -/
theorem product_indecomposable_of_left
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B)
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A X)
    (hY : Subsingleton Y) :
    letI := productModule X Y
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) (X × Y) := by
  letI := productModule X Y
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  letI : Nontrivial X := hX.nontrivial
  constructor
  · infer_instance
  · intro F hF
    let f : Module.End A X :=
      { toFun := fun x ↦ (F (x, (0 : Y))).1
        map_add' := fun x y ↦ by
          simpa using congrArg Prod.fst (F.map_add (x, (0 : Y)) (y, 0))
        map_smul' := fun a x ↦ by
          have h := congrArg Prod.fst
            (F.map_smul (a, (0 : B)) (x, (0 : Y)))
          have hs : ((a, (0 : B)) • (x, (0 : Y)) : X × Y) =
              (a • x, (0 : Y)) := by
            apply Prod.ext
            · rfl
            · exact zero_smul B (0 : Y)
          have ht : ((a, (0 : B)) • F (x, (0 : Y))) =
              (a • (F (x, (0 : Y))).1, (0 : Y)) := by
            apply Prod.ext
            · rfl
            · exact zero_smul B (F (x, (0 : Y))).2
          rw [hs, ht] at h
          exact h }
    have hf : IsIdempotentElem f := by
      apply LinearMap.ext
      intro x
      have hpair : ((F (x, (0 : Y))).1, (0 : Y)) = F (x, 0) := by
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
      change (F ((F (x, (0 : Y))).1, (0 : Y))).1 =
        (F (x, (0 : Y))).1
      rw [hpair]
      exact congrArg Prod.fst (DFunLike.congr_fun hF (x, (0 : Y)))
    rcases hX.eq_zero_or_eq_one_of_isIdempotentElem hf with
        hzero | hone
    · left
      apply LinearMap.ext
      intro z
      have hz : z = (z.1, (0 : Y)) := by
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
      apply Prod.ext
      · rw [hz]
        exact congrArg (fun g : Module.End A X ↦ g z.1) hzero
      · exact Subsingleton.elim _ _
    · right
      apply LinearMap.ext
      intro z
      have hz : z = (z.1, (0 : Y)) := by
        apply Prod.ext
        · rfl
        · exact Subsingleton.elim _ _
      apply Prod.ext
      · rw [hz]
        exact congrArg (fun g : Module.End A X ↦ g z.1) hone
      · exact Subsingleton.elim _ _

/-- An indecomposable right module, paired with a trivial left module, is
indecomposable for the product ring. -/
theorem product_indecomposable_of_right
    (X : ModuleCat.{v} A) (Y : ModuleCat.{v} B)
    (hX : Subsingleton X)
    (hY : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule B Y) :
    letI := productModule X Y
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) (X × Y) := by
  letI := productModule X Y
  rw [QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  letI : Nontrivial Y := hY.nontrivial
  constructor
  · infer_instance
  · intro F hF
    let f : Module.End B Y :=
      { toFun := fun y ↦ (F ((0 : X), y)).2
        map_add' := fun x y ↦ by
          simpa using congrArg Prod.snd (F.map_add ((0 : X), x) (0, y))
        map_smul' := fun b y ↦ by
          have h := congrArg Prod.snd
            (F.map_smul ((0 : A), b) ((0 : X), y))
          have hs : (((0 : A), b) • ((0 : X), y) : X × Y) =
              ((0 : X), b • y) := by
            apply Prod.ext
            · exact zero_smul A (0 : X)
            · rfl
          have ht : (((0 : A), b) • F ((0 : X), y)) =
              ((0 : X), b • (F ((0 : X), y)).2) := by
            apply Prod.ext
            · exact zero_smul A (F ((0 : X), y)).1
            · rfl
          rw [hs, ht] at h
          exact h }
    have hf : IsIdempotentElem f := by
      apply LinearMap.ext
      intro y
      have hpair : ((0 : X), (F ((0 : X), y)).2) = F (0, y) := by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      change (F ((0 : X), (F ((0 : X), y)).2)).2 =
        (F ((0 : X), y)).2
      rw [hpair]
      exact congrArg Prod.snd (DFunLike.congr_fun hF ((0 : X), y))
    rcases hY.eq_zero_or_eq_one_of_isIdempotentElem hf with
        hzero | hone
    · left
      apply LinearMap.ext
      intro z
      have hz : z = ((0 : X), z.2) := by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rw [hz]
        exact congrArg (fun g : Module.End B Y ↦ g z.2) hzero
    · right
      apply LinearMap.ext
      intro z
      have hz : z = ((0 : X), z.2) := by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · rfl
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rw [hz]
        exact congrArg (fun g : Module.End B Y ↦ g z.2) hone

/-- Complete one-factor classification for an indecomposable product-ring
module: exactly one central summand carries an indecomposable factor module,
while the other summand is trivial. -/
theorem indecomposable_component_classification
    (M : ModuleCat.{v} (A × B))
    (hM : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B) M) :
    (QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A (leftPart M) ∧
        Subsingleton (rightPart M)) ∨
      (Subsingleton (leftPart M) ∧
        QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule B (rightPart M)) := by
  have hsplit :=
    @QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule.of_linearEquiv
      (A × B) M _ _ _ (leftPart M × rightPart M) _
      (productModule (leftPartObj M) (rightPartObj M)) hM
      (splitAssembleLinearEquiv M)
  rcases indecomposable_leftPart_or_rightPart_subsingleton M hM with
      hleft | hright
  · exact Or.inr ⟨hleft,
      right_indecomposable_of_product
        (leftPartObj M) (rightPartObj M) hleft hsplit⟩
  · exact Or.inl ⟨
      left_indecomposable_of_product
        (leftPartObj M) (rightPartObj M) hright hsplit,
      hright⟩

/-! ## The two fully supported factor embeddings -/

/-- A concrete zero object in the finitely generated module category. -/
def zeroFGModule (R : Type u) [Ring R] : FGModuleCat.{v} R :=
  FGModuleCat.of R PUnit

instance zeroFGModule_subsingleton (R : Type u) [Ring R] :
    Subsingleton (zeroFGModule R : FGModuleCat.{v} R) := by
  dsimp [zeroFGModule]
  infer_instance

/-- Embed a finitely generated left-factor module by adjoining the zero
right-factor module. -/
def leftEmbedding (X : FGModuleCat.{v} A) :
    FGModuleCat.{v} (A × B) :=
  fgAssembleFunctor.obj (X, zeroFGModule B)

/-- Embed a finitely generated right-factor module by adjoining the zero
left-factor module. -/
def rightEmbedding (Y : FGModuleCat.{v} B) :
    FGModuleCat.{v} (A × B) :=
  fgAssembleFunctor.obj (zeroFGModule A, Y)

/-- Functorial left-factor embedding. -/
def leftPairFunctor :
    FGModuleCat.{v} A ⥤
      (FGModuleCat.{v} A × FGModuleCat.{v} B) where
  obj X := (X, zeroFGModule B)
  map f := Prod.mkHom f (𝟙 (zeroFGModule B))
  map_id X := by
    apply Prod.hom_ext <;> rfl
  map_comp f g := by
    apply Prod.hom_ext <;> simp

/-- Functorial right-factor embedding. -/
def rightPairFunctor :
    FGModuleCat.{v} B ⥤
      (FGModuleCat.{v} A × FGModuleCat.{v} B) where
  obj Y := (zeroFGModule A, Y)
  map f := Prod.mkHom (𝟙 (zeroFGModule A)) f
  map_id Y := by
    apply Prod.hom_ext <;> rfl
  map_comp f g := by
    apply Prod.hom_ext <;> simp

/-- The left-factor embedding as a functor. -/
def leftEmbeddingFunctor :
    FGModuleCat.{v} A ⥤ FGModuleCat.{v} (A × B) :=
  leftPairFunctor ⋙ (fgModuleEquivalence (A := A) (B := B)).inverse

/-- The right-factor embedding as a functor. -/
def rightEmbeddingFunctor :
    FGModuleCat.{v} B ⥤ FGModuleCat.{v} (A × B) :=
  rightPairFunctor ⋙ (fgModuleEquivalence (A := A) (B := B)).inverse

instance leftEmbeddingFunctor_additive :
    (leftEmbeddingFunctor (A := A) (B := B)).Additive where
  map_add {X Y} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

instance rightEmbeddingFunctor_additive :
    (rightEmbeddingFunctor (A := A) (B := B)).Additive where
  map_add {X Y} f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The left embedding preserves epimorphisms. -/
theorem leftEmbeddingFunctor_map_epi {X Y : FGModuleCat.{v} A}
    (f : X ⟶ Y) [Epi f] :
    Epi (leftEmbeddingFunctor (B := B) |>.map f) := by
  let pairMap := Prod.mkHom f (𝟙 (zeroFGModule B))
  letI : Epi pairMap :=
    ⟨fun g h hgh ↦ by
      apply Prod.hom_ext
      · apply (cancel_epi f).1
        exact congrArg Prod.fst hgh
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx]
        simp⟩
  change Epi ((fgModuleEquivalence (A := A) (B := B)).inverse.map pairMap)
  exact (fgModuleEquivalence (A := A) (B := B)).inverse.map_epi pairMap

/-- The left embedding preserves monomorphisms. -/
theorem leftEmbeddingFunctor_map_mono {X Y : FGModuleCat.{v} A}
    (f : X ⟶ Y) [Mono f] :
    Mono (leftEmbeddingFunctor (B := B) |>.map f) := by
  let pairMap := Prod.mkHom f (𝟙 (zeroFGModule B))
  letI : Mono pairMap :=
    ⟨fun g h hgh ↦ by
      apply Prod.hom_ext
      · apply (cancel_mono f).1
        exact congrArg Prod.fst hgh
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _⟩
  change Mono ((fgModuleEquivalence (A := A) (B := B)).inverse.map pairMap)
  exact (fgModuleEquivalence (A := A) (B := B)).inverse.map_mono pairMap

/-- The right embedding preserves epimorphisms. -/
theorem rightEmbeddingFunctor_map_epi {X Y : FGModuleCat.{v} B}
    (f : X ⟶ Y) [Epi f] :
    Epi (rightEmbeddingFunctor (A := A) |>.map f) := by
  let pairMap := Prod.mkHom (𝟙 (zeroFGModule A)) f
  letI : Epi pairMap :=
    ⟨fun g h hgh ↦ by
      apply Prod.hom_ext
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have hx : x = 0 := Subsingleton.elim _ _
        rw [hx]
        simp
      · apply (cancel_epi f).1
        exact congrArg Prod.snd hgh⟩
  change Epi ((fgModuleEquivalence (A := A) (B := B)).inverse.map pairMap)
  exact (fgModuleEquivalence (A := A) (B := B)).inverse.map_epi pairMap

/-- The right embedding preserves monomorphisms. -/
theorem rightEmbeddingFunctor_map_mono {X Y : FGModuleCat.{v} B}
    (f : X ⟶ Y) [Mono f] :
    Mono (rightEmbeddingFunctor (A := A) |>.map f) := by
  let pairMap := Prod.mkHom (𝟙 (zeroFGModule A)) f
  letI : Mono pairMap :=
    ⟨fun g h hgh ↦ by
      apply Prod.hom_ext
      · apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      · apply (cancel_mono f).1
        exact congrArg Prod.snd hgh⟩
  change Mono ((fgModuleEquivalence (A := A) (B := B)).inverse.map pairMap)
  exact (fgModuleEquivalence (A := A) (B := B)).inverse.map_mono pairMap

/-- The left embedding preserves indecomposability. -/
theorem leftEmbedding_indecomposable (X : FGModuleCat.{v} A)
    (hX : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule A X) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B)
      (leftEmbedding (B := B) X) := by
  exact product_indecomposable_of_left X.obj
    (zeroFGModule B).obj hX inferInstance

/-- The right embedding preserves indecomposability. -/
theorem rightEmbedding_indecomposable (Y : FGModuleCat.{v} B)
    (hY : QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule B Y) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B)
      (rightEmbedding (A := A) Y) := by
  exact product_indecomposable_of_right
    (zeroFGModule A).obj Y.obj inferInstance hY

/-- Splitting the left embedding recovers its left component. -/
def splitLeftEmbeddingIso (X : FGModuleCat.{v} A) :
    (fgSplitFunctor.obj (leftEmbedding (B := B) X)).1 ≅ X :=
  (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
    (FGModuleCat.{v} B)).mapIso
      (fgSplitAssembleCounitIso.app (X, zeroFGModule B))

/-- Splitting the right embedding recovers its right component. -/
def splitRightEmbeddingIso (Y : FGModuleCat.{v} B) :
    (fgSplitFunctor.obj (rightEmbedding (A := A) Y)).2 ≅ Y :=
  (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
    (FGModuleCat.{v} B)).mapIso
      (fgSplitAssembleCounitIso.app (zeroFGModule A, Y))

/-- The unused component of the left embedding is zero. -/
def splitLeftEmbeddingRightIso (X : FGModuleCat.{v} A) :
    (fgSplitFunctor.obj (leftEmbedding (B := B) X)).2 ≅
      zeroFGModule B :=
  (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
    (FGModuleCat.{v} B)).mapIso
      (fgSplitAssembleCounitIso.app (X, zeroFGModule B))

/-- The unused component of the right embedding is zero. -/
def splitRightEmbeddingLeftIso (Y : FGModuleCat.{v} B) :
    (fgSplitFunctor.obj (rightEmbedding (A := A) Y)).1 ≅
      zeroFGModule A :=
  (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
    (FGModuleCat.{v} B)).mapIso
      (fgSplitAssembleCounitIso.app (zeroFGModule A, Y))

/-- Any two trivial finitely generated modules are isomorphic. -/
def subsingletonFGIso {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R)
    (hX : Subsingleton X) (hY : Subsingleton Y) : X ≅ Y := by
  letI : Subsingleton X := hX
  letI : Subsingleton Y := hY
  exact
    { hom := 0
      inv := 0
      hom_inv_id := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      inv_hom_id := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        exact Subsingleton.elim _ _ }

/-- A finitely generated module with a singleton carrier is a zero object
of `FGModuleCat`. -/
theorem isZeroFG_of_subsingleton {R : Type u} [Ring R]
    (X : FGModuleCat.{v} R) (hX : Subsingleton X) : IsZero X := by
  letI : Subsingleton X := hX
  refine
    { unique_to := fun Y ↦ ⟨⟨⟨0⟩, ?_⟩⟩
      unique_from := fun Y ↦ ⟨⟨⟨0⟩, ?_⟩⟩ }
  · intro f
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp
  · intro f
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact Subsingleton.elim _ _

/-- A finite biproduct of zero finitely generated modules is zero. -/
theorem isZero_biproduct_FG {R : Type u} [Ring R]
    (L : FintypeCat.{0}) (F : L → FGModuleCat.{v} R)
    (hF : ∀ t, IsZero (F t)) : IsZero (⨁ F) := by
  refine
    { unique_to := fun X ↦ ⟨⟨⟨0⟩, ?_⟩⟩
      unique_from := fun X ↦ ⟨⟨⟨0⟩, ?_⟩⟩ }
  · intro f
    apply biproduct.hom_ext'
    intro t
    exact (hF t).eq_of_src _ _
  · intro f
    apply biproduct.hom_ext
    intro t
    exact (hF t).eq_of_tgt _ _

/-- Epimorphisms in a product category are epimorphic in the first
component. -/
theorem prod_fst_epi
    {X Y : FGModuleCat.{v} A × FGModuleCat.{v} B}
    (f : X ⟶ Y) [Epi f] : Epi f.1 := by
  constructor
  intro Z g h hgh
  let gz : Y ⟶ (Z, zeroFGModule B) := Prod.mkHom g 0
  let hz : Y ⟶ (Z, zeroFGModule B) := Prod.mkHom h 0
  have hp : gz = hz := by
    apply (cancel_epi f).1
    apply Prod.hom_ext
    · exact hgh
    · simp [gz, hz]
  exact congrArg Prod.fst hp

/-- Epimorphisms in a product category are epimorphic in the second
component. -/
theorem prod_snd_epi
    {X Y : FGModuleCat.{v} A × FGModuleCat.{v} B}
    (f : X ⟶ Y) [Epi f] : Epi f.2 := by
  constructor
  intro Z g h hgh
  let gz : Y ⟶ (zeroFGModule A, Z) := Prod.mkHom 0 g
  let hz : Y ⟶ (zeroFGModule A, Z) := Prod.mkHom 0 h
  have hp : gz = hz := by
    apply (cancel_epi f).1
    apply Prod.hom_ext
    · simp [gz, hz]
    · exact hgh
  exact congrArg Prod.snd hp

/-- Monomorphisms in a product category are monomorphic in the first
component. -/
theorem prod_fst_mono
    {X Y : FGModuleCat.{v} A × FGModuleCat.{v} B}
    (f : X ⟶ Y) [Mono f] : Mono f.1 := by
  constructor
  intro Z g h hgh
  let gz : (Z, zeroFGModule B) ⟶ X := Prod.mkHom g 0
  let hz : (Z, zeroFGModule B) ⟶ X := Prod.mkHom h 0
  have hp : gz = hz := by
    apply (cancel_mono f).1
    apply Prod.hom_ext
    · exact hgh
    · simp [gz, hz]
  exact congrArg Prod.fst hp

/-- Monomorphisms in a product category are monomorphic in the second
component. -/
theorem prod_snd_mono
    {X Y : FGModuleCat.{v} A × FGModuleCat.{v} B}
    (f : X ⟶ Y) [Mono f] : Mono f.2 := by
  constructor
  intro Z g h hgh
  let gz : (zeroFGModule A, Z) ⟶ X := Prod.mkHom 0 g
  let hz : (zeroFGModule A, Z) ⟶ X := Prod.mkHom 0 h
  have hp : gz = hz := by
    apply (cancel_mono f).1
    apply Prod.hom_ext
    · simp [gz, hz]
    · exact hgh
  exact congrArg Prod.snd hp

instance fgSplitFunctor_additive :
    (fgSplitFunctor (A := A) (B := B)).Additive where
  map_add {X Y} f g := by
    letI : Module.Finite A (leftPart X.obj) := leftPart_finite X
    letI : Module.Finite A (leftPart Y.obj) := leftPart_finite Y
    letI : Module.Finite B (rightPart X.obj) := rightPart_finite X
    letI : Module.Finite B (rightPart Y.obj) := rightPart_finite Y
    have hfg : (f + g).hom.hom = f.hom.hom + g.hom.hom := by
      rfl
    apply Prod.hom_ext
    · change
        FGModuleCat.ofHom (leftPartMap (f + g).hom) =
          FGModuleCat.ofHom (leftPartMap f.hom) +
            FGModuleCat.ofHom (leftPartMap g.hom)
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      dsimp [fgSplitFunctor, leftPartMap]
      change (f + g).hom.hom x.1 =
        f.hom.hom x.1 + g.hom.hom x.1
      rw [hfg]
      rfl
    · change
        FGModuleCat.ofHom (rightPartMap (f + g).hom) =
          FGModuleCat.ofHom (rightPartMap f.hom) +
            FGModuleCat.ofHom (rightPartMap g.hom)
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      dsimp [fgSplitFunctor, rightPartMap]
      change (f + g).hom.hom x.1 =
        f.hom.hom x.1 + g.hom.hom x.1
      rw [hfg]
      rfl

section SkeletonLabels

variable [IsNoetherianRing A] [IsNoetherianRing B]
  [IsNoetherianRing (A × B)]
  {I J K : Type w}
  (sigma : IndecomposableSkeleton.{u, w, v} A I)
  (tau : IndecomposableSkeleton.{u, w, v} B J)
  (rho : IndecomposableSkeleton.{u, w, v} (A × B) K)

/-- The product-ring module represented by a factor label. -/
def sumEmbeddingObj : I ⊕ J → FGModuleCat.{v} (A × B)
  | Sum.inl i => leftEmbedding (B := B) (sigma.obj i)
  | Sum.inr j => rightEmbedding (A := A) (tau.obj j)

omit [IsNoetherianRing (A × B)] in
/-- Each factor label embeds as an indecomposable product-ring module. -/
theorem sumEmbeddingObj_indecomposable (z : I ⊕ J) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (A × B)
      (sumEmbeddingObj sigma tau z) := by
  cases z with
  | inl i => exact leftEmbedding_indecomposable _ (sigma.indecomposable i)
  | inr j => exact rightEmbedding_indecomposable _ (tau.indecomposable j)

/-- Select the ambient skeleton label representing an embedded factor
indecomposable. -/
def sumEmbeddingLabel (z : I ⊕ J) : K :=
  Classical.choose
    (rho.complete (sumEmbeddingObj sigma tau z)
      (sumEmbeddingObj_indecomposable sigma tau z))

/-- The selected ambient representative is isomorphic to the embedded
factor module. -/
def sumEmbeddingObjIso (z : I ⊕ J) :
    sumEmbeddingObj sigma tau z ≅
      rho.obj (sumEmbeddingLabel sigma tau rho z) :=
  Classical.choice
    (Classical.choose_spec
      (rho.complete (sumEmbeddingObj sigma tau z)
        (sumEmbeddingObj_indecomposable sigma tau z)))

/-- Embedded factor labels do not acquire duplicates in the product-ring
skeleton. -/
theorem sumEmbeddingLabel_injective :
    Function.Injective (sumEmbeddingLabel sigma tau rho) := by
  intro z z' hzz'
  let e : sumEmbeddingObj sigma tau z ≅
      sumEmbeddingObj sigma tau z' :=
    sumEmbeddingObjIso sigma tau rho z ≪≫
      eqToIso (congrArg rho.obj hzz') ≪≫
      (sumEmbeddingObjIso sigma tau rho z').symm
  cases z with
  | inl i =>
      cases z' with
      | inl i' =>
          apply congrArg Sum.inl
          apply sigma.eq_of_iso
          exact ⟨(splitLeftEmbeddingIso (B := B) (sigma.obj i)).symm ≪≫
            (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
              (FGModuleCat.{v} B)).mapIso
                (fgSplitFunctor.mapIso e) ≪≫
            splitLeftEmbeddingIso (B := B) (sigma.obj i')⟩
      | inr j' =>
          exfalso
          let ezero : sigma.obj i ≅ zeroFGModule A :=
            (splitLeftEmbeddingIso (B := B) (sigma.obj i)).symm ≪≫
              (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
                (FGModuleCat.{v} B)).mapIso
                  (fgSplitFunctor.mapIso e) ≪≫
              splitRightEmbeddingLeftIso (A := A) (tau.obj j')
          have hsub : Subsingleton (sigma.obj i) :=
            ⟨fun x y ↦ (FGModuleCat.isoToLinearEquiv ezero).injective
              (Subsingleton.elim _ _)⟩
          exact not_subsingleton_iff_nontrivial.mpr
            (sigma.indecomposable i).nontrivial hsub
  | inr j =>
      cases z' with
      | inl i' =>
          exfalso
          let ezero : tau.obj j ≅ zeroFGModule B :=
            (splitRightEmbeddingIso (A := A) (tau.obj j)).symm ≪≫
              (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
                (FGModuleCat.{v} B)).mapIso
                  (fgSplitFunctor.mapIso e) ≪≫
              splitLeftEmbeddingRightIso (B := B) (sigma.obj i')
          have hsub : Subsingleton (tau.obj j) :=
            ⟨fun x y ↦ (FGModuleCat.isoToLinearEquiv ezero).injective
              (Subsingleton.elim _ _)⟩
          exact not_subsingleton_iff_nontrivial.mpr
            (tau.indecomposable j).nontrivial hsub
      | inr j' =>
          apply congrArg Sum.inr
          apply tau.eq_of_iso
          exact ⟨(splitRightEmbeddingIso (A := A) (tau.obj j)).symm ≪≫
            (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
              (FGModuleCat.{v} B)).mapIso
                (fgSplitFunctor.mapIso e) ≪≫
            splitRightEmbeddingIso (A := A) (tau.obj j')⟩

/-- Every ambient product-ring indecomposable is represented by an embedded
factor label. -/
theorem sumEmbeddingLabel_surjective :
    Function.Surjective (sumEmbeddingLabel sigma tau rho) := by
  intro k
  rcases indecomposable_component_classification (rho.obj k).obj
      (rho.indecomposable k) with hleft | hright
  · obtain ⟨i, ⟨eleft⟩⟩ :=
      sigma.complete (fgSplitFunctor.obj (rho.obj k)).1 hleft.1
    let eright : (fgSplitFunctor.obj (rho.obj k)).2 ≅
        zeroFGModule B :=
      subsingletonFGIso _ _ hleft.2 inferInstance
    let epair : fgSplitFunctor.obj (rho.obj k) ≅
        (sigma.obj i, zeroFGModule B) :=
      Iso.prod eleft eright
    let eembed : rho.obj k ≅ leftEmbedding (B := B) (sigma.obj i) :=
      fgSplitAssembleUnitIso.app (rho.obj k) ≪≫
        fgAssembleFunctor.mapIso epair
    refine ⟨Sum.inl i, ?_⟩
    apply rho.eq_of_iso
    exact ⟨(sumEmbeddingObjIso sigma tau rho (Sum.inl i)).symm ≪≫
      eembed.symm⟩
  · obtain ⟨j, ⟨eright⟩⟩ :=
      tau.complete (fgSplitFunctor.obj (rho.obj k)).2 hright.2
    let eleft : (fgSplitFunctor.obj (rho.obj k)).1 ≅
        zeroFGModule A :=
      subsingletonFGIso _ _ hright.1 inferInstance
    let epair : fgSplitFunctor.obj (rho.obj k) ≅
        (zeroFGModule A, tau.obj j) :=
      Iso.prod eleft eright
    let eembed : rho.obj k ≅ rightEmbedding (A := A) (tau.obj j) :=
      fgSplitAssembleUnitIso.app (rho.obj k) ≪≫
        fgAssembleFunctor.mapIso epair
    refine ⟨Sum.inr j, ?_⟩
    apply rho.eq_of_iso
    exact ⟨(sumEmbeddingObjIso sigma tau rho (Sum.inr j)).symm ≪≫
      eembed.symm⟩

/-- The exact disjoint-sum classification of product-ring skeleton labels. -/
def sumEmbeddingLabelEquiv : (I ⊕ J) ≃ K :=
  Equiv.ofBijective (sumEmbeddingLabel sigma tau rho)
    ⟨sumEmbeddingLabel_injective sigma tau rho,
      sumEmbeddingLabel_surjective sigma tau rho⟩

/-- The genuine product-ring indecomposable skeleton indexed by the
disjoint sum of the two factor skeletons.  Its structural fields are
transported from the ambient skeleton along the objectwise isomorphisms,
while its displayed objects are the concrete one-factor embeddings. -/
def sumEmbeddingSkeleton :
    IndecomposableSkeleton.{u, w, v} (A × B) (I ⊕ J) where
  obj := sumEmbeddingObj sigma tau
  indecomposable := sumEmbeddingObj_indecomposable sigma tau
  finiteLength z := by
    exact (rho.finiteLength (sumEmbeddingLabel sigma tau rho z)).of_injective
      (FGModuleCat.isoToLinearEquiv
        (sumEmbeddingObjIso sigma tau rho z)).injective
  eq_of_iso {z z'} h := by
    apply sumEmbeddingLabel_injective sigma tau rho
    apply rho.eq_of_iso
    obtain ⟨e⟩ := h
    exact ⟨(sumEmbeddingObjIso sigma tau rho z).symm ≪≫
      e ≪≫ sumEmbeddingObjIso sigma tau rho z'⟩
  complete X hX := by
    obtain ⟨k, ⟨eX⟩⟩ := rho.complete X hX
    let labelEquiv := sumEmbeddingLabelEquiv sigma tau rho
    refine ⟨labelEquiv.symm k, ⟨?_⟩⟩
    exact eX ≪≫
      eqToIso (congrArg rho.obj (labelEquiv.apply_symm_apply k).symm) ≪≫
      (sumEmbeddingObjIso sigma tau rho (labelEquiv.symm k)).symm
  decomposes X := by
    obtain ⟨n, a, ⟨eX⟩⟩ := rho.decomposes X
    let labelEquiv := sumEmbeddingLabelEquiv sigma tau rho
    let b : Fin n → I ⊕ J := fun t ↦ labelEquiv.symm (a t)
    let esummand (t : Fin n) :
        rho.obj (a t) ≅ sumEmbeddingObj sigma tau (b t) :=
      eqToIso (congrArg rho.obj
          (labelEquiv.apply_symm_apply (a t)).symm) ≪≫
        (sumEmbeddingObjIso sigma tau rho (b t)).symm
    exact ⟨n, b, ⟨eX ≪≫ biproduct.mapIso esummand⟩⟩

/-- The concrete sum skeleton and the ambient skeleton are aligned by the
identity equivalence of the product-ring module category. -/
def sumEmbeddingAlignedEquivalence :
    IndecomposableSkeleton.AlignedEquivalence
      (sumEmbeddingSkeleton sigma tau rho) rho where
  categoryEquiv := CategoryTheory.Equivalence.refl
  labelEquiv := sumEmbeddingLabelEquiv sigma tau rho
  objIso z :=
    sumEmbeddingObjIso sigma tau rho z

/-- Splitting commutes with each finite displayed sum. -/
def splitSumIso (L : FintypeCat.{0}) (a : L → I ⊕ J) :
    (fgSplitFunctor (A := A) (B := B)).obj
        ((sumEmbeddingSkeleton sigma tau rho).sumOver L a) ≅
      (⨁ fun t : L ↦
        (fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))) :=
  (fgSplitFunctor (A := A) (B := B)).mapIso
      (biproduct.isoCoproduct
        (fun t : L ↦
          (sumEmbeddingSkeleton sigma tau rho).obj (a t))) ≪≫
    PreservesCoproduct.iso (fgSplitFunctor (A := A) (B := B))
      (fun t : L ↦
        (sumEmbeddingSkeleton sigma tau rho).obj (a t)) ≪≫
    (biproduct.isoCoproduct
      (fun t : L ↦
        (fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t)))).symm

/-- The left component of a split displayed sum is the displayed sum of
the left components. -/
def splitLeftSumIso (L : FintypeCat.{0}) (a : L → I ⊕ J) :
    ((fgSplitFunctor (A := A) (B := B)).obj
        ((sumEmbeddingSkeleton sigma tau rho).sumOver L a)).1 ≅
      (⨁ fun t : L ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))).1) :=
  (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
      (FGModuleCat.{v} B)).mapIso
      (splitSumIso sigma tau rho L a) ≪≫
    (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
      (FGModuleCat.{v} B)).mapIso
      (biproduct.isoCoproduct
        (fun t : L ↦
          (fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (a t)))) ≪≫
    PreservesCoproduct.iso
      (CategoryTheory.Prod.fst (FGModuleCat.{v} A)
        (FGModuleCat.{v} B))
      (fun t : L ↦
        (fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))) ≪≫
    (biproduct.isoCoproduct
      (fun t : L ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))).1)).symm

/-- The right component of a split displayed sum is the displayed sum of
the right components. -/
def splitRightSumIso (L : FintypeCat.{0}) (a : L → I ⊕ J) :
    ((fgSplitFunctor (A := A) (B := B)).obj
        ((sumEmbeddingSkeleton sigma tau rho).sumOver L a)).2 ≅
      (⨁ fun t : L ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))).2) :=
  (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
      (FGModuleCat.{v} B)).mapIso
      (splitSumIso sigma tau rho L a) ≪≫
    (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
      (FGModuleCat.{v} B)).mapIso
      (biproduct.isoCoproduct
        (fun t : L ↦
          (fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (a t)))) ≪≫
    PreservesCoproduct.iso
      (CategoryTheory.Prod.snd (FGModuleCat.{v} A)
        (FGModuleCat.{v} B))
      (fun t : L ↦
        (fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))) ≪≫
    (biproduct.isoCoproduct
      (fun t : L ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (a t))).2)).symm

/-- The left component of a mixed quotient presentation. -/
def leftComponentFacMap {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    (⨁ fun t : P.index ↦
      ((fgSplitFunctor (A := A) (B := B)).obj
        ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) ⟶
      sigma.obj i :=
  (splitLeftSumIso sigma tau rho P.index P.label).inv ≫
    ((fgSplitFunctor (A := A) (B := B)).map P.map).1 ≫
    (splitLeftEmbeddingIso (B := B) (sigma.obj i)).hom

/-- The left component of a quotient presentation remains epimorphic. -/
theorem leftComponentFacMap_epi {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    Epi (leftComponentFacMap sigma tau rho P) := by
  letI : Epi P.map := P.epi
  haveI : Epi ((fgSplitFunctor (A := A) (B := B)).map P.map) :=
    (fgModuleEquivalence (A := A) (B := B)).functor.map_epi P.map
  haveI : Epi (((fgSplitFunctor (A := A) (B := B)).map P.map).1) :=
    prod_fst_epi ((fgSplitFunctor (A := A) (B := B)).map P.map)
  dsimp only [leftComponentFacMap]
  infer_instance

/-- The left component of a mixed submodule presentation. -/
def leftComponentSubMap {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    sigma.obj i ⟶
      (⨁ fun t : P.index ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) :=
  (splitLeftEmbeddingIso (B := B) (sigma.obj i)).inv ≫
    ((fgSplitFunctor (A := A) (B := B)).map P.map).1 ≫
    (splitLeftSumIso sigma tau rho P.index P.label).hom

/-- The left component of a submodule presentation remains monomorphic. -/
theorem leftComponentSubMap_mono {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    Mono (leftComponentSubMap sigma tau rho P) := by
  letI : Mono P.map := P.mono
  haveI : Mono ((fgSplitFunctor (A := A) (B := B)).map P.map) :=
    (fgModuleEquivalence (A := A) (B := B)).functor.map_mono P.map
  haveI : Mono (((fgSplitFunctor (A := A) (B := B)).map P.map).1) :=
    prod_fst_mono ((fgSplitFunctor (A := A) (B := B)).map P.map)
  dsimp only [leftComponentSubMap]
  apply mono_comp'
  · infer_instance
  · apply mono_comp'
    · exact prod_fst_mono
        ((fgSplitFunctor (A := A) (B := B)).map P.map)
    · infer_instance

/-- The right component of a mixed quotient presentation. -/
def rightComponentFacMap {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    (⨁ fun t : P.index ↦
      ((fgSplitFunctor (A := A) (B := B)).obj
        ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) ⟶
      tau.obj j :=
  (splitRightSumIso sigma tau rho P.index P.label).inv ≫
    ((fgSplitFunctor (A := A) (B := B)).map P.map).2 ≫
    (splitRightEmbeddingIso (A := A) (tau.obj j)).hom

/-- The right component of a quotient presentation remains epimorphic. -/
theorem rightComponentFacMap_epi {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    Epi (rightComponentFacMap sigma tau rho P) := by
  letI : Epi P.map := P.epi
  haveI : Epi ((fgSplitFunctor (A := A) (B := B)).map P.map) :=
    (fgModuleEquivalence (A := A) (B := B)).functor.map_epi P.map
  haveI : Epi (((fgSplitFunctor (A := A) (B := B)).map P.map).2) :=
    prod_snd_epi ((fgSplitFunctor (A := A) (B := B)).map P.map)
  dsimp only [rightComponentFacMap]
  infer_instance

/-- The right component of a mixed submodule presentation. -/
def rightComponentSubMap {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    tau.obj j ⟶
      (⨁ fun t : P.index ↦
        ((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) :=
  (splitRightEmbeddingIso (A := A) (tau.obj j)).inv ≫
    ((fgSplitFunctor (A := A) (B := B)).map P.map).2 ≫
    (splitRightSumIso sigma tau rho P.index P.label).hom

/-- The right component of a submodule presentation remains monomorphic. -/
theorem rightComponentSubMap_mono {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    Mono (rightComponentSubMap sigma tau rho P) := by
  letI : Mono P.map := P.mono
  haveI : Mono ((fgSplitFunctor (A := A) (B := B)).map P.map) :=
    (fgModuleEquivalence (A := A) (B := B)).functor.map_mono P.map
  haveI : Mono (((fgSplitFunctor (A := A) (B := B)).map P.map).2) :=
    prod_snd_mono ((fgSplitFunctor (A := A) (B := B)).map P.map)
  dsimp only [rightComponentSubMap]
  apply mono_comp'
  · infer_instance
  · apply mono_comp'
    · exact prod_snd_mono
        ((fgSplitFunctor (A := A) (B := B)).map P.map)
    · infer_instance

/-- A zero finitely generated module has a singleton carrier. -/
theorem subsingletonFG_of_isZero {R : Type u} [Ring R]
    (X : FGModuleCat.{v} R) (hX : IsZero X) : Subsingleton X := by
  constructor
  intro x y
  have hid : (𝟙 X) = 0 := (IsZero.iff_id_eq_zero X).mp hX
  have hx := congrArg (fun f : X ⟶ X ↦ f.hom.hom x) hid
  have hy := congrArg (fun f : X ⟶ X ↦ f.hom.hom y) hid
  simpa using hx.trans hy.symm

/-- A quotient presentation of a nonzero left block must use at least one
left label. -/
theorem exists_left_label_of_fac {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    ∃ i' : I, Sum.inl i' ∈ T := by
  classical
  by_contra hnone
  have hzero (t : P.index) :
      IsZero
        (((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) := by
    cases hlabel : P.label t with
    | inl i' =>
        exfalso
        apply hnone
        exact ⟨i', by simpa [hlabel] using P.mem t⟩
    | inr j' =>
        apply IsZero.of_iso
          (isZeroFG_of_subsingleton (zeroFGModule A) inferInstance)
        simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
          (splitRightEmbeddingLeftIso (A := A) (tau.obj j'))
  have hsource :
      IsZero
        (⨁ fun t : P.index ↦
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) :=
    isZero_biproduct_FG P.index _ hzero
  letI : Epi (leftComponentFacMap sigma tau rho P) :=
    leftComponentFacMap_epi sigma tau rho P
  have htarget : IsZero (sigma.obj i) :=
    IsZero.of_epi_eq_zero (leftComponentFacMap sigma tau rho P)
      (hsource.eq_zero_of_src _)
  exact not_subsingleton_iff_nontrivial.mpr
    (sigma.indecomposable i).nontrivial
    (subsingletonFG_of_isZero (sigma.obj i) htarget)

/-- A submodule presentation of a nonzero left block must use at least
one left label. -/
theorem exists_left_label_of_sub {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    ∃ i' : I, Sum.inl i' ∈ T := by
  classical
  by_contra hnone
  have hzero (t : P.index) :
      IsZero
        (((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) := by
    cases hlabel : P.label t with
    | inl i' =>
        exfalso
        apply hnone
        exact ⟨i', by simpa [hlabel] using P.mem t⟩
    | inr j' =>
        apply IsZero.of_iso
          (isZeroFG_of_subsingleton (zeroFGModule A) inferInstance)
        simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
          (splitRightEmbeddingLeftIso (A := A) (tau.obj j'))
  have htarget :
      IsZero
        (⨁ fun t : P.index ↦
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1) :=
    isZero_biproduct_FG P.index _ hzero
  letI : Mono (leftComponentSubMap sigma tau rho P) :=
    leftComponentSubMap_mono sigma tau rho P
  have hsource : IsZero (sigma.obj i) :=
    IsZero.of_mono_eq_zero (leftComponentSubMap sigma tau rho P)
      (htarget.eq_zero_of_tgt _)
  exact not_subsingleton_iff_nontrivial.mpr
    (sigma.indecomposable i).nontrivial
    (subsingletonFG_of_isZero (sigma.obj i) hsource)

/-- Discard the right-block content of a mixed quotient presentation by
replacing its zero left components with one witnessed left label. -/
def restrictLeftFacPresentation {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    sigma.FacPresentation
      (SetClosure.ComponentwiseProduct.leftPart T) (sigma.obj i) := by
  classical
  let i0 : I := Classical.choose
    (exists_left_label_of_fac sigma tau rho P)
  have hi0 : Sum.inl i0 ∈ T := Classical.choose_spec
    (exists_left_label_of_fac sigma tau rho P)
  let b : P.index → I := fun t ↦
    match P.label t with
    | Sum.inl i' => i'
    | Sum.inr _ => i0
  let eData (t : P.index) :
      { f : sigma.obj (b t) ⟶
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1 //
        Epi f } := by
    cases hlabel : P.label t with
    | inl i' =>
        have hb : b t = i' := by simp [b, hlabel]
        rw [hb]
        let f := (splitLeftEmbeddingIso (B := B) (sigma.obj i')).inv
        haveI : Epi f := inferInstance
        simpa [b, hlabel, sumEmbeddingSkeleton, sumEmbeddingObj] using
          (⟨f, inferInstance⟩ : { g // Epi g })
    | inr j' =>
        have hb : b t = i0 := by simp [b, hlabel]
        rw [hb]
        let hzero :
            IsZero
              (((fgSplitFunctor (A := A) (B := B)).obj
                ((sumEmbeddingSkeleton sigma tau rho).obj
                  (Sum.inr j'))).1) := by
          apply IsZero.of_iso
            (isZeroFG_of_subsingleton (zeroFGModule A) inferInstance)
          simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
            (splitRightEmbeddingLeftIso (A := A) (tau.obj j'))
        exact ⟨0, hzero.epi 0⟩
  let e (t : P.index) := (eData t).1
  have hepi (t : P.index) : Epi (e t) := (eData t).2
  refine
    { index := P.index
      label := b
      mem := ?_
      map := biproduct.map e ≫ leftComponentFacMap sigma tau rho P
      epi := ?_ }
  · intro t
    change Sum.inl (b t) ∈ T
    cases hlabel : P.label t with
    | inl i' => simpa [b, hlabel] using P.mem t
    | inr j' => simpa [b, hlabel] using hi0
  · letI (t : P.index) : Epi (e t) := hepi t
    letI : Epi (leftComponentFacMap sigma tau rho P) :=
      leftComponentFacMap_epi sigma tau rho P
    infer_instance

/-- Discard the right-block content of a mixed submodule presentation by
replacing its zero left components with one witnessed left label. -/
def restrictLeftSubPresentation {T : Set (I ⊕ J)} {i : I}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i))) :
    sigma.SubPresentation
      (SetClosure.ComponentwiseProduct.leftPart T) (sigma.obj i) := by
  classical
  let i0 : I := Classical.choose
    (exists_left_label_of_sub sigma tau rho P)
  have hi0 : Sum.inl i0 ∈ T := Classical.choose_spec
    (exists_left_label_of_sub sigma tau rho P)
  let b : P.index → I := fun t ↦
    match P.label t with
    | Sum.inl i' => i'
    | Sum.inr _ => i0
  let eData (t : P.index) :
      { f :
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).1 ⟶
            sigma.obj (b t) // Mono f } := by
    cases hlabel : P.label t with
    | inl i' =>
        have hb : b t = i' := by simp [b, hlabel]
        rw [hb]
        let f := (splitLeftEmbeddingIso (B := B) (sigma.obj i')).hom
        haveI : Mono f := inferInstance
        simpa [b, hlabel, sumEmbeddingSkeleton, sumEmbeddingObj] using
          (⟨f, inferInstance⟩ : { g // Mono g })
    | inr j' =>
        have hb : b t = i0 := by simp [b, hlabel]
        rw [hb]
        let hzero :
            IsZero
              (((fgSplitFunctor (A := A) (B := B)).obj
                ((sumEmbeddingSkeleton sigma tau rho).obj
                  (Sum.inr j'))).1) := by
          apply IsZero.of_iso
            (isZeroFG_of_subsingleton (zeroFGModule A) inferInstance)
          simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
            (splitRightEmbeddingLeftIso (A := A) (tau.obj j'))
        exact ⟨0, hzero.mono 0⟩
  let e (t : P.index) := (eData t).1
  have hmono (t : P.index) : Mono (e t) := (eData t).2
  refine
    { index := P.index
      label := b
      mem := ?_
      map := leftComponentSubMap sigma tau rho P ≫ biproduct.map e
      mono := ?_ }
  · intro t
    change Sum.inl (b t) ∈ T
    cases hlabel : P.label t with
    | inl i' => simpa [b, hlabel] using P.mem t
    | inr j' => simpa [b, hlabel] using hi0
  · letI (t : P.index) : Mono (e t) := hmono t
    letI : Mono (leftComponentSubMap sigma tau rho P) :=
      leftComponentSubMap_mono sigma tau rho P
    infer_instance

/-- A quotient presentation of a nonzero right block must use at least one
right label. -/
theorem exists_right_label_of_fac {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    ∃ j' : J, Sum.inr j' ∈ T := by
  classical
  by_contra hnone
  have hzero (t : P.index) :
      IsZero
        (((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) := by
    cases hlabel : P.label t with
    | inl i' =>
        apply IsZero.of_iso
          (isZeroFG_of_subsingleton (zeroFGModule B) inferInstance)
        simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
          (splitLeftEmbeddingRightIso (B := B) (sigma.obj i'))
    | inr j' =>
        exfalso
        apply hnone
        exact ⟨j', by simpa [hlabel] using P.mem t⟩
  have hsource :
      IsZero
        (⨁ fun t : P.index ↦
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) :=
    isZero_biproduct_FG P.index _ hzero
  letI : Epi (rightComponentFacMap sigma tau rho P) :=
    rightComponentFacMap_epi sigma tau rho P
  have htarget : IsZero (tau.obj j) :=
    IsZero.of_epi_eq_zero (rightComponentFacMap sigma tau rho P)
      (hsource.eq_zero_of_src _)
  exact not_subsingleton_iff_nontrivial.mpr
    (tau.indecomposable j).nontrivial
    (subsingletonFG_of_isZero (tau.obj j) htarget)

/-- A submodule presentation of a nonzero right block must use at least
one right label. -/
theorem exists_right_label_of_sub {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    ∃ j' : J, Sum.inr j' ∈ T := by
  classical
  by_contra hnone
  have hzero (t : P.index) :
      IsZero
        (((fgSplitFunctor (A := A) (B := B)).obj
          ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) := by
    cases hlabel : P.label t with
    | inl i' =>
        apply IsZero.of_iso
          (isZeroFG_of_subsingleton (zeroFGModule B) inferInstance)
        simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
          (splitLeftEmbeddingRightIso (B := B) (sigma.obj i'))
    | inr j' =>
        exfalso
        apply hnone
        exact ⟨j', by simpa [hlabel] using P.mem t⟩
  have htarget :
      IsZero
        (⨁ fun t : P.index ↦
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2) :=
    isZero_biproduct_FG P.index _ hzero
  letI : Mono (rightComponentSubMap sigma tau rho P) :=
    rightComponentSubMap_mono sigma tau rho P
  have hsource : IsZero (tau.obj j) :=
    IsZero.of_mono_eq_zero (rightComponentSubMap sigma tau rho P)
      (htarget.eq_zero_of_tgt _)
  exact not_subsingleton_iff_nontrivial.mpr
    (tau.indecomposable j).nontrivial
    (subsingletonFG_of_isZero (tau.obj j) hsource)

/-- Discard the left-block content of a mixed quotient presentation by
replacing its zero right components with one witnessed right label. -/
def restrictRightFacPresentation {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).FacPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    tau.FacPresentation
      (SetClosure.ComponentwiseProduct.rightPart T) (tau.obj j) := by
  classical
  let j0 : J := Classical.choose
    (exists_right_label_of_fac sigma tau rho P)
  have hj0 : Sum.inr j0 ∈ T := Classical.choose_spec
    (exists_right_label_of_fac sigma tau rho P)
  let b : P.index → J := fun t ↦
    match P.label t with
    | Sum.inl _ => j0
    | Sum.inr j' => j'
  let eData (t : P.index) :
      { f : tau.obj (b t) ⟶
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2 //
        Epi f } := by
    cases hlabel : P.label t with
    | inl i' =>
        have hb : b t = j0 := by simp [b, hlabel]
        rw [hb]
        let hzero :
            IsZero
              (((fgSplitFunctor (A := A) (B := B)).obj
                ((sumEmbeddingSkeleton sigma tau rho).obj
                  (Sum.inl i'))).2) := by
          apply IsZero.of_iso
            (isZeroFG_of_subsingleton (zeroFGModule B) inferInstance)
          simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
            (splitLeftEmbeddingRightIso (B := B) (sigma.obj i'))
        exact ⟨0, hzero.epi 0⟩
    | inr j' =>
        have hb : b t = j' := by simp [b, hlabel]
        rw [hb]
        let f := (splitRightEmbeddingIso (A := A) (tau.obj j')).inv
        haveI : Epi f := inferInstance
        simpa [b, hlabel, sumEmbeddingSkeleton, sumEmbeddingObj] using
          (⟨f, inferInstance⟩ : { g // Epi g })
  let e (t : P.index) := (eData t).1
  have hepi (t : P.index) : Epi (e t) := (eData t).2
  refine
    { index := P.index
      label := b
      mem := ?_
      map := biproduct.map e ≫ rightComponentFacMap sigma tau rho P
      epi := ?_ }
  · intro t
    change Sum.inr (b t) ∈ T
    cases hlabel : P.label t with
    | inl i' => simpa [b, hlabel] using hj0
    | inr j' => simpa [b, hlabel] using P.mem t
  · letI (t : P.index) : Epi (e t) := hepi t
    letI : Epi (rightComponentFacMap sigma tau rho P) :=
      rightComponentFacMap_epi sigma tau rho P
    infer_instance

/-- Discard the left-block content of a mixed submodule presentation by
replacing its zero right components with one witnessed right label. -/
def restrictRightSubPresentation {T : Set (I ⊕ J)} {j : J}
    (P : (sumEmbeddingSkeleton sigma tau rho).SubPresentation T
      ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j))) :
    tau.SubPresentation
      (SetClosure.ComponentwiseProduct.rightPart T) (tau.obj j) := by
  classical
  let j0 : J := Classical.choose
    (exists_right_label_of_sub sigma tau rho P)
  have hj0 : Sum.inr j0 ∈ T := Classical.choose_spec
    (exists_right_label_of_sub sigma tau rho P)
  let b : P.index → J := fun t ↦
    match P.label t with
    | Sum.inl _ => j0
    | Sum.inr j' => j'
  let eData (t : P.index) :
      { f :
          ((fgSplitFunctor (A := A) (B := B)).obj
            ((sumEmbeddingSkeleton sigma tau rho).obj (P.label t))).2 ⟶
            tau.obj (b t) // Mono f } := by
    cases hlabel : P.label t with
    | inl i' =>
        have hb : b t = j0 := by simp [b, hlabel]
        rw [hb]
        let hzero :
            IsZero
              (((fgSplitFunctor (A := A) (B := B)).obj
                ((sumEmbeddingSkeleton sigma tau rho).obj
                  (Sum.inl i'))).2) := by
          apply IsZero.of_iso
            (isZeroFG_of_subsingleton (zeroFGModule B) inferInstance)
          simpa [sumEmbeddingSkeleton, sumEmbeddingObj] using
            (splitLeftEmbeddingRightIso (B := B) (sigma.obj i'))
        exact ⟨0, hzero.mono 0⟩
    | inr j' =>
        have hb : b t = j' := by simp [b, hlabel]
        rw [hb]
        let f := (splitRightEmbeddingIso (A := A) (tau.obj j')).hom
        haveI : Mono f := inferInstance
        simpa [b, hlabel, sumEmbeddingSkeleton, sumEmbeddingObj] using
          (⟨f, inferInstance⟩ : { g // Mono g })
  let e (t : P.index) := (eData t).1
  have hmono (t : P.index) : Mono (e t) := (eData t).2
  refine
    { index := P.index
      label := b
      mem := ?_
      map := rightComponentSubMap sigma tau rho P ≫ biproduct.map e
      mono := ?_ }
  · intro t
    change Sum.inr (b t) ∈ T
    cases hlabel : P.label t with
    | inl i' => simpa [b, hlabel] using hj0
    | inr j' => simpa [b, hlabel] using P.mem t
  · letI (t : P.index) : Mono (e t) := hmono t
    letI : Mono (rightComponentSubMap sigma tau rho P) :=
      rightComponentSubMap_mono sigma tau rho P
    infer_instance

/-- The left embedding carries a displayed factor sum to the displayed
sum of the corresponding left labels in the concrete sum skeleton. -/
def leftEmbeddingSumIso (L : FintypeCat.{0}) (a : L → I) :
    (leftEmbeddingFunctor (A := A) (B := B)).obj
        (sigma.sumOver L a) ≅
      (sumEmbeddingSkeleton sigma tau rho).sumOver L
        (fun t ↦ Sum.inl (a t)) :=
  (leftEmbeddingFunctor (A := A) (B := B)).mapIso
      (biproduct.isoCoproduct (fun t : L ↦ sigma.obj (a t))) ≪≫
    PreservesCoproduct.iso (leftEmbeddingFunctor (A := A) (B := B))
      (fun t : L ↦ sigma.obj (a t)) ≪≫
    (biproduct.isoCoproduct
      (fun t : L ↦
        (leftEmbeddingFunctor (A := A) (B := B)).obj
          (sigma.obj (a t)))).symm

/-- The analogous displayed-sum comparison for the right embedding. -/
def rightEmbeddingSumIso (L : FintypeCat.{0}) (a : L → J) :
    (rightEmbeddingFunctor (A := A) (B := B)).obj
        (tau.sumOver L a) ≅
      (sumEmbeddingSkeleton sigma tau rho).sumOver L
        (fun t ↦ Sum.inr (a t)) :=
  (rightEmbeddingFunctor (A := A) (B := B)).mapIso
      (biproduct.isoCoproduct (fun t : L ↦ tau.obj (a t))) ≪≫
    PreservesCoproduct.iso (rightEmbeddingFunctor (A := A) (B := B))
      (fun t : L ↦ tau.obj (a t)) ≪≫
    (biproduct.isoCoproduct
      (fun t : L ↦
        (rightEmbeddingFunctor (A := A) (B := B)).obj
          (tau.obj (a t)))).symm

/-- A quotient presentation in the left factor gives a quotient
presentation by the corresponding left labels in the product skeleton. -/
def mapLeftFacPresentation {S : Set I} {i : I}
    (P : sigma.FacPresentation S (sigma.obj i)) :
    (sumEmbeddingSkeleton sigma tau rho).FacPresentation
      (Sum.inl '' S) ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i)) where
  index := P.index
  label := fun t ↦ Sum.inl (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map := (leftEmbeddingSumIso sigma tau rho P.index P.label).inv ≫
    (leftEmbeddingFunctor (A := A) (B := B)).map P.map
  epi := by
    letI : Epi P.map := P.epi
    exact epi_comp'
      (inferInstance : Epi
        (leftEmbeddingSumIso sigma tau rho P.index P.label).inv)
      (leftEmbeddingFunctor_map_epi P.map)

/-- A submodule presentation in the left factor gives a submodule
presentation by the corresponding left labels in the product skeleton. -/
def mapLeftSubPresentation {S : Set I} {i : I}
    (P : sigma.SubPresentation S (sigma.obj i)) :
    (sumEmbeddingSkeleton sigma tau rho).SubPresentation
      (Sum.inl '' S) ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inl i)) where
  index := P.index
  label := fun t ↦ Sum.inl (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map := (leftEmbeddingFunctor (A := A) (B := B)).map P.map ≫
    (leftEmbeddingSumIso sigma tau rho P.index P.label).hom
  mono := by
    letI : Mono P.map := P.mono
    exact mono_comp'
      (leftEmbeddingFunctor_map_mono P.map)
      (inferInstance : Mono
        (leftEmbeddingSumIso sigma tau rho P.index P.label).hom)

/-- Right-factor quotient presentations embed in the product skeleton. -/
def mapRightFacPresentation {S : Set J} {j : J}
    (P : tau.FacPresentation S (tau.obj j)) :
    (sumEmbeddingSkeleton sigma tau rho).FacPresentation
      (Sum.inr '' S) ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j)) where
  index := P.index
  label := fun t ↦ Sum.inr (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map := (rightEmbeddingSumIso sigma tau rho P.index P.label).inv ≫
    (rightEmbeddingFunctor (A := A) (B := B)).map P.map
  epi := by
    letI : Epi P.map := P.epi
    exact epi_comp'
      (inferInstance : Epi
        (rightEmbeddingSumIso sigma tau rho P.index P.label).inv)
      (rightEmbeddingFunctor_map_epi P.map)

/-- Right-factor submodule presentations embed in the product skeleton. -/
def mapRightSubPresentation {S : Set J} {j : J}
    (P : tau.SubPresentation S (tau.obj j)) :
    (sumEmbeddingSkeleton sigma tau rho).SubPresentation
      (Sum.inr '' S) ((sumEmbeddingSkeleton sigma tau rho).obj (Sum.inr j)) where
  index := P.index
  label := fun t ↦ Sum.inr (P.label t)
  mem t := ⟨P.label t, P.mem t, rfl⟩
  map := (rightEmbeddingFunctor (A := A) (B := B)).map P.map ≫
    (rightEmbeddingSumIso sigma tau rho P.index P.label).hom
  mono := by
    letI : Mono P.map := P.mono
    exact mono_comp'
      (rightEmbeddingFunctor_map_mono P.map)
      (inferInstance : Mono
        (rightEmbeddingSumIso sigma tau rho P.index P.label).hom)

/-- Left-factor quotient closure maps into the quotient closure of the
concrete product skeleton. -/
theorem mem_sum_qClosure_inl_of_mem {T : Set (I ⊕ J)} {i : I}
    (hi : i ∈ sigma.qClosure
      (SetClosure.ComponentwiseProduct.leftPart T)) :
    Sum.inl i ∈ (sumEmbeddingSkeleton sigma tau rho).qClosure T := by
  obtain ⟨P⟩ := hi
  refine ⟨IndecomposableSkeleton.FacPresentation.of_subset
    (sumEmbeddingSkeleton sigma tau rho)
    (mapLeftFacPresentation sigma tau rho P) ?_⟩
  rintro _ ⟨i', hi', rfl⟩
  exact hi'

/-- Left-factor submodule closure maps into the submodule closure of the
concrete product skeleton. -/
theorem mem_sum_sClosure_inl_of_mem {T : Set (I ⊕ J)} {i : I}
    (hi : i ∈ sigma.sClosure
      (SetClosure.ComponentwiseProduct.leftPart T)) :
    Sum.inl i ∈ (sumEmbeddingSkeleton sigma tau rho).sClosure T := by
  obtain ⟨P⟩ := hi
  refine ⟨IndecomposableSkeleton.SubPresentation.of_subset
    (sumEmbeddingSkeleton sigma tau rho)
    (mapLeftSubPresentation sigma tau rho P) ?_⟩
  rintro _ ⟨i', hi', rfl⟩
  exact hi'

/-- Right-factor quotient closure maps into the quotient closure of the
concrete product skeleton. -/
theorem mem_sum_qClosure_inr_of_mem {T : Set (I ⊕ J)} {j : J}
    (hj : j ∈ tau.qClosure
      (SetClosure.ComponentwiseProduct.rightPart T)) :
    Sum.inr j ∈ (sumEmbeddingSkeleton sigma tau rho).qClosure T := by
  obtain ⟨P⟩ := hj
  refine ⟨IndecomposableSkeleton.FacPresentation.of_subset
    (sumEmbeddingSkeleton sigma tau rho)
    (mapRightFacPresentation sigma tau rho P) ?_⟩
  rintro _ ⟨j', hj', rfl⟩
  exact hj'

/-- Right-factor submodule closure maps into the submodule closure of the
concrete product skeleton. -/
theorem mem_sum_sClosure_inr_of_mem {T : Set (I ⊕ J)} {j : J}
    (hj : j ∈ tau.sClosure
      (SetClosure.ComponentwiseProduct.rightPart T)) :
    Sum.inr j ∈ (sumEmbeddingSkeleton sigma tau rho).sClosure T := by
  obtain ⟨P⟩ := hj
  refine ⟨IndecomposableSkeleton.SubPresentation.of_subset
    (sumEmbeddingSkeleton sigma tau rho)
    (mapRightSubPresentation sigma tau rho P) ?_⟩
  rintro _ ⟨j', hj', rfl⟩
  exact hj'

/-- Membership of a left label in the mixed quotient closure restricts
back to quotient closure in the left factor. -/
theorem mem_left_qClosure_of_mem_sum_inl {T : Set (I ⊕ J)} {i : I}
    (hi : Sum.inl i ∈
      (sumEmbeddingSkeleton sigma tau rho).qClosure T) :
    i ∈ sigma.qClosure
      (SetClosure.ComponentwiseProduct.leftPart T) := by
  obtain ⟨P⟩ := hi
  exact ⟨restrictLeftFacPresentation sigma tau rho P⟩

/-- Membership of a left label in the mixed submodule closure restricts
back to submodule closure in the left factor. -/
theorem mem_left_sClosure_of_mem_sum_inl {T : Set (I ⊕ J)} {i : I}
    (hi : Sum.inl i ∈
      (sumEmbeddingSkeleton sigma tau rho).sClosure T) :
    i ∈ sigma.sClosure
      (SetClosure.ComponentwiseProduct.leftPart T) := by
  obtain ⟨P⟩ := hi
  exact ⟨restrictLeftSubPresentation sigma tau rho P⟩

/-- Membership of a right label in the mixed quotient closure restricts
back to quotient closure in the right factor. -/
theorem mem_right_qClosure_of_mem_sum_inr {T : Set (I ⊕ J)} {j : J}
    (hj : Sum.inr j ∈
      (sumEmbeddingSkeleton sigma tau rho).qClosure T) :
    j ∈ tau.qClosure
      (SetClosure.ComponentwiseProduct.rightPart T) := by
  obtain ⟨P⟩ := hj
  exact ⟨restrictRightFacPresentation sigma tau rho P⟩

/-- Membership of a right label in the mixed submodule closure restricts
back to submodule closure in the right factor. -/
theorem mem_right_sClosure_of_mem_sum_inr {T : Set (I ⊕ J)} {j : J}
    (hj : Sum.inr j ∈
      (sumEmbeddingSkeleton sigma tau rho).sClosure T) :
    j ∈ tau.sClosure
      (SetClosure.ComponentwiseProduct.rightPart T) := by
  obtain ⟨P⟩ := hj
  exact ⟨restrictRightSubPresentation sigma tau rho P⟩

/-- Quotient closure on the concrete product skeleton is exactly the
componentwise product of the two factor quotient closures. -/
theorem sum_qClosure_eq_productClosure :
    (sumEmbeddingSkeleton sigma tau rho).qClosure =
      SetClosure.ComponentwiseProduct.productClosure
        sigma.qClosure tau.qClosure := by
  apply DFunLike.ext _ _
  intro T
  ext z
  cases z with
  | inl i =>
      have hiff :
          (Sum.inl i ∈
              (sumEmbeddingSkeleton sigma tau rho).qClosure T) ↔
            i ∈ sigma.qClosure
              (SetClosure.ComponentwiseProduct.leftPart T) :=
        ⟨mem_left_qClosure_of_mem_sum_inl sigma tau rho,
          mem_sum_qClosure_inl_of_mem sigma tau rho⟩
      change
        (Sum.inl i ∈
            (sumEmbeddingSkeleton sigma tau rho).qClosure T) ↔
          Sum.inl i ∈
            SetClosure.ComponentwiseProduct.assemble
              (sigma.qClosure
                (SetClosure.ComponentwiseProduct.leftPart T))
              (tau.qClosure
                (SetClosure.ComponentwiseProduct.rightPart T))
      simpa [SetClosure.ComponentwiseProduct.assemble] using hiff
  | inr j =>
      have hiff :
          (Sum.inr j ∈
              (sumEmbeddingSkeleton sigma tau rho).qClosure T) ↔
            j ∈ tau.qClosure
              (SetClosure.ComponentwiseProduct.rightPart T) :=
        ⟨mem_right_qClosure_of_mem_sum_inr sigma tau rho,
          mem_sum_qClosure_inr_of_mem sigma tau rho⟩
      change
        (Sum.inr j ∈
            (sumEmbeddingSkeleton sigma tau rho).qClosure T) ↔
          Sum.inr j ∈
            SetClosure.ComponentwiseProduct.assemble
              (sigma.qClosure
                (SetClosure.ComponentwiseProduct.leftPart T))
              (tau.qClosure
                (SetClosure.ComponentwiseProduct.rightPart T))
      simpa [SetClosure.ComponentwiseProduct.assemble] using hiff

/-- Submodule closure on the concrete product skeleton is exactly the
componentwise product of the two factor submodule closures. -/
theorem sum_sClosure_eq_productClosure :
    (sumEmbeddingSkeleton sigma tau rho).sClosure =
      SetClosure.ComponentwiseProduct.productClosure
        sigma.sClosure tau.sClosure := by
  apply DFunLike.ext _ _
  intro T
  ext z
  cases z with
  | inl i =>
      have hiff :
          (Sum.inl i ∈
              (sumEmbeddingSkeleton sigma tau rho).sClosure T) ↔
            i ∈ sigma.sClosure
              (SetClosure.ComponentwiseProduct.leftPart T) :=
        ⟨mem_left_sClosure_of_mem_sum_inl sigma tau rho,
          mem_sum_sClosure_inl_of_mem sigma tau rho⟩
      change
        (Sum.inl i ∈
            (sumEmbeddingSkeleton sigma tau rho).sClosure T) ↔
          Sum.inl i ∈
            SetClosure.ComponentwiseProduct.assemble
              (sigma.sClosure
                (SetClosure.ComponentwiseProduct.leftPart T))
              (tau.sClosure
                (SetClosure.ComponentwiseProduct.rightPart T))
      simpa [SetClosure.ComponentwiseProduct.assemble] using hiff

  | inr j =>
      have hiff :
          (Sum.inr j ∈
              (sumEmbeddingSkeleton sigma tau rho).sClosure T) ↔
            j ∈ tau.sClosure
              (SetClosure.ComponentwiseProduct.rightPart T) :=
        ⟨mem_right_sClosure_of_mem_sum_inr sigma tau rho,
          mem_sum_sClosure_inr_of_mem sigma tau rho⟩
      change
        (Sum.inr j ∈
            (sumEmbeddingSkeleton sigma tau rho).sClosure T) ↔
          Sum.inr j ∈
            SetClosure.ComponentwiseProduct.assemble
              (sigma.sClosure
                (SetClosure.ComponentwiseProduct.leftPart T))
              (tau.sClosure
                (SetClosure.ComponentwiseProduct.rightPart T))
      simpa [SetClosure.ComponentwiseProduct.assemble] using hiff

/-- The factorwise quotient product is relabeled to quotient closure on
the ambient product-ring skeleton. -/
def productQClosureRelabeling :
    SetClosure.RelabelingEquiv
      (SetClosure.ComponentwiseProduct.productClosure
        sigma.qClosure tau.qClosure)
      rho.qClosure where
  equiv := sumEmbeddingLabelEquiv sigma tau rho
  map_closure T := by
    rw [← sum_qClosure_eq_productClosure sigma tau rho]
    exact
      IndecomposableSkeleton.AlignedEquivalence.image_qClosure
        (sumEmbeddingSkeleton sigma tau rho) rho
        (sumEmbeddingAlignedEquivalence sigma tau rho) T

/-- The factorwise submodule product is relabeled to submodule closure on
the ambient product-ring skeleton. -/
def productSClosureRelabeling :
    SetClosure.RelabelingEquiv
      (SetClosure.ComponentwiseProduct.productClosure
        sigma.sClosure tau.sClosure)
      rho.sClosure where
  equiv := sumEmbeddingLabelEquiv sigma tau rho
  map_closure T := by
    rw [← sum_sClosure_eq_productClosure sigma tau rho]
    exact
      IndecomposableSkeleton.AlignedEquivalence.image_sClosure
        (sumEmbeddingSkeleton sigma tau rho) rho
        (sumEmbeddingAlignedEquivalence sigma tau rho) T

/-- The disconnected product-ring endpoint: componentwise equality of
quotient and submodule levels through four implies ambient equality at
levels three and four. -/
theorem productRing_levelCount_three_and_four_eq
    [Finite I] [Finite J] [Finite K]
    (hleft : ∀ n ≤ 4,
      sigma.qClosure.levelCount n = sigma.sClosure.levelCount n)
    (hright : ∀ n ≤ 4,
      tau.qClosure.levelCount n = tau.sClosure.levelCount n) :
    rho.qClosure.levelCount 3 = rho.sClosure.levelCount 3 ∧
      rho.qClosure.levelCount 4 = rho.sClosure.levelCount 4 :=
  SetClosure.ComponentwiseProduct.relabeledProduct_levelCount_three_and_four_eq
    sigma.qClosure sigma.sClosure tau.qClosure tau.sClosure
    rho.qClosure rho.sClosure
    (productQClosureRelabeling sigma tau rho)
    (productSClosureRelabeling sigma tau rho)
    hleft hright

end SkeletonLabels

end QuotientSubmoduleEquidistribution.ProductModules
