import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB0Modules

/-!
# Extracting finite lollipop data from an arbitrary genuine module

The algebra idempotents split every finitely generated `B0Model`-module into
its two vertex spaces.  This file constructs the corresponding
`FiniteB0Rep` and a vector-space equivalence from its carrier back to the
original module.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ModuleExtraction

universe u

variable (K : Type u) [Field K]

/-- A named scalar-restriction wrapper.  The wrapper prevents the induced
`K`-module instance from competing with unrelated module structures on the
same underlying type. -/
def RestrictedCarrier (M : FGModuleCat.{u} (B0Model K)) := M

instance (M : FGModuleCat.{u} (B0Model K)) :
    AddCommGroup (RestrictedCarrier K M) :=
  inferInstanceAs (AddCommGroup M)

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module (B0Model K) (RestrictedCarrier K M) :=
  inferInstanceAs (Module (B0Model K) M)

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module K (RestrictedCarrier K M) :=
  Module.compHom (RestrictedCarrier K M) (algebraMap K (B0Model K))

instance (M : FGModuleCat.{u} (B0Model K)) :
    IsScalarTower K (B0Model K) (RestrictedCarrier K M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

instance (M : FGModuleCat.{u} (B0Model K)) :
    Module.Finite K (RestrictedCarrier K M) :=
  Module.Finite.trans (B0Model K) (RestrictedCarrier K M)

/-- Multiplication by an algebra element, viewed as a `K`-linear map. -/
def actionLinear (M : FGModuleCat.{u} (B0Model K)) (r : B0Model K) :
    RestrictedCarrier K M →ₗ[K] RestrictedCarrier K M :=
  (Algebra.lsmul K K (RestrictedCarrier K M)) r

@[simp] theorem actionLinear_apply
    (M : FGModuleCat.{u} (B0Model K)) (r : B0Model K)
    (m : RestrictedCarrier K M) :
    actionLinear K M r m = r • m := rfl

/-- The vertex-one image. -/
def vertexOne (M : FGModuleCat.{u} (B0Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e1 K))

/-- The vertex-two image. -/
def vertexTwo (M : FGModuleCat.{u} (B0Model K)) :
    Submodule K (RestrictedCarrier K M) :=
  LinearMap.range (actionLinear K M (e2 K))

theorem e1_fixed
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    e1 K • (v.1 : RestrictedCarrier K M) = v.1 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e1 K • (e1 K • m) = e1 K • m
  rw [← mul_smul, e1_sq]

theorem e2_kills_vertexOne
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    e2 K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e2 K • (e1 K • m) = 0
  rw [← mul_smul, e2_mul_e1, zero_smul]

theorem e2_fixed
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexTwo K M) :
    e2 K • (v.1 : RestrictedCarrier K M) = v.1 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e2 K • (e2 K • m) = e2 K • m
  rw [← mul_smul, e2_sq]

theorem e1_kills_vertexTwo
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexTwo K M) :
    e1 K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change e1 K • (e2 K • m) = 0
  rw [← mul_smul, e1_mul_e2, zero_smul]

theorem x_kills_vertexTwo
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexTwo K M) :
    x K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change x K • (e2 K • m) = 0
  rw [← mul_smul, x_mul_e2, zero_smul]

theorem a_kills_vertexTwo
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexTwo K M) :
    a K • (v.1 : RestrictedCarrier K M) = 0 := by
  rcases v.2 with ⟨m, hm⟩
  rw [← hm]
  change a K • (e2 K • m) = 0
  rw [← mul_smul, a_mul_e2, zero_smul]

/-- The loop induced by multiplication by `x`. -/
def extractedLoopLinear (M : FGModuleCat.{u} (B0Model K)) :
    vertexOne K M →ₗ[K] vertexOne K M where
  toFun v := ⟨x K • (v.1 : RestrictedCarrier K M), by
    refine ⟨x K • (v.1 : RestrictedCarrier K M), ?_⟩
    change e1 K • (x K • (v.1 : RestrictedCarrier K M)) =
      x K • v.1
    rw [← mul_smul, e1_mul_x] ⟩
  map_add' v w := by
    apply Subtype.ext
    exact smul_add (x K) v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact (smul_comm c (x K) v.1).symm

/-- The stem induced by multiplication by `a`. -/
def extractedStemLinear (M : FGModuleCat.{u} (B0Model K)) :
    vertexOne K M →ₗ[K] vertexTwo K M where
  toFun v := ⟨a K • (v.1 : RestrictedCarrier K M), by
    refine ⟨a K • (v.1 : RestrictedCarrier K M), ?_⟩
    change e2 K • (a K • (v.1 : RestrictedCarrier K M)) =
      a K • v.1
    rw [← mul_smul, e2_mul_a] ⟩
  map_add' v w := by
    apply Subtype.ext
    exact smul_add (a K) v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact (smul_comm c (a K) v.1).symm

theorem extractedLoop_sq
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    extractedLoopLinear K M (extractedLoopLinear K M v) = 0 := by
  apply Subtype.ext
  change x K • (x K • (v.1 : RestrictedCarrier K M)) = 0
  rw [← mul_smul, x_sq, zero_smul]

theorem extractedStem_loop
    (M : FGModuleCat.{u} (B0Model K)) (v : vertexOne K M) :
    extractedStemLinear K M (extractedLoopLinear K M v) = 0 := by
  apply Subtype.ext
  change a K • (x K • (v.1 : RestrictedCarrier K M)) = 0
  rw [← mul_smul, a_mul_x, zero_smul]

/-- The finite representation extracted from an arbitrary genuine finitely
generated module. -/
def extractedRep (M : FGModuleCat.{u} (B0Model K)) : FiniteB0Rep K where
  V₁ := FGModuleCat.of K (vertexOne K M)
  V₂ := FGModuleCat.of K (vertexTwo K M)
  loop := FGModuleCat.ofHom (extractedLoopLinear K M)
  stem := FGModuleCat.ofHom (extractedStemLinear K M)
  loop_sq := extractedLoop_sq K M
  stem_loop := extractedStem_loop K M

/-- Adding the two vertex coordinates recovers the original underlying
`K`-vector space. -/
def carrierLinearEquiv (M : FGModuleCat.{u} (B0Model K)) :
    FiniteB0Rep.Carrier K (extractedRep K M) ≃ₗ[K]
      RestrictedCarrier K M where
  toFun p := p.1.1 + p.2.1
  invFun m :=
    (⟨e1 K • m, ⟨m, rfl⟩⟩,
      ⟨e2 K • m, ⟨m, rfl⟩⟩)
  left_inv p := by
    rcases p with ⟨v, w⟩
    apply Prod.ext <;> apply Subtype.ext
    · change e1 K • (v.1 + w.1) = v.1
      rw [smul_add, e1_fixed K M, e1_kills_vertexTwo K M, add_zero]
    · change e2 K • (v.1 + w.1) = w.1
      rw [smul_add, e2_kills_vertexOne K M, e2_fixed K M, zero_add]
  right_inv m := by
    change e1 K • m + e2 K • m = m
    rw [← add_smul, e1_add_e2, one_smul]
  map_add' p q := by
    change (p.1.1 + q.1.1) + (p.2.1 + q.2.1) =
      (p.1.1 + p.2.1) + (q.1.1 + q.2.1)
    abel
  map_smul' c p := by
    change c • p.1.1 + c • p.2.1 = c • (p.1.1 + p.2.1)
    rw [smul_add]

/-- Coordinate expansion in the four distinguished algebra generators. -/
theorem algebra_coordinate_decomposition (r : B0Model K) :
    r = (TrivSqZeroExt.fst r).1 • e1 K +
      (TrivSqZeroExt.fst r).2 • e2 K +
      (TrivSqZeroExt.snd r).x • x K +
      (TrivSqZeroExt.snd r).a • a K := by
  ext <;> simp [e1, e2, x, a]

theorem carrierLinearEquiv_e1
    (M : FGModuleCat.{u} (B0Model K))
    (p : FiniteB0Rep.Carrier K (extractedRep K M)) :
    carrierLinearEquiv K M (e1 K • p) =
      e1 K • carrierLinearEquiv K M p := by
  rw [FiniteB0Rep.e1_smul]
  change p.1.1 + 0 = e1 K • (p.1.1 + p.2.1)
  rw [add_zero, smul_add, e1_fixed K M, e1_kills_vertexTwo K M,
    add_zero]

theorem carrierLinearEquiv_e2
    (M : FGModuleCat.{u} (B0Model K))
    (p : FiniteB0Rep.Carrier K (extractedRep K M)) :
    carrierLinearEquiv K M (e2 K • p) =
      e2 K • carrierLinearEquiv K M p := by
  rw [FiniteB0Rep.e2_smul]
  change 0 + p.2.1 = e2 K • (p.1.1 + p.2.1)
  rw [zero_add, smul_add, e2_kills_vertexOne K M, e2_fixed K M,
    zero_add]

theorem carrierLinearEquiv_x
    (M : FGModuleCat.{u} (B0Model K))
    (p : FiniteB0Rep.Carrier K (extractedRep K M)) :
    carrierLinearEquiv K M (x K • p) =
      x K • carrierLinearEquiv K M p := by
  rw [FiniteB0Rep.x_smul]
  change x K • p.1.1 + 0 = x K • (p.1.1 + p.2.1)
  rw [add_zero, smul_add, x_kills_vertexTwo K M, add_zero]

theorem carrierLinearEquiv_a
    (M : FGModuleCat.{u} (B0Model K))
    (p : FiniteB0Rep.Carrier K (extractedRep K M)) :
    carrierLinearEquiv K M (a K • p) =
      a K • carrierLinearEquiv K M p := by
  rw [FiniteB0Rep.a_smul]
  change 0 + a K • p.1.1 = a K • (p.1.1 + p.2.1)
  rw [zero_add, smul_add, a_kills_vertexTwo K M, add_zero]

theorem carrierLinearEquiv_smul
    (M : FGModuleCat.{u} (B0Model K)) (r : B0Model K)
    (p : FiniteB0Rep.Carrier K (extractedRep K M)) :
    carrierLinearEquiv K M (r • p) =
      r • carrierLinearEquiv K M p := by
  rw [algebra_coordinate_decomposition K r]
  simp only [add_smul, IsScalarTower.smul_assoc, map_add, map_smul]
  rw [carrierLinearEquiv_e1 K M, carrierLinearEquiv_e2 K M,
    carrierLinearEquiv_x K M, carrierLinearEquiv_a K M]

/-- The extraction equivalence upgraded from a vector-space equivalence to a
genuine `B0Model`-linear equivalence. -/
def carrierModuleLinearEquiv
    (M : FGModuleCat.{u} (B0Model K)) :
    FiniteB0Rep.Carrier K (extractedRep K M) ≃ₗ[B0Model K]
      RestrictedCarrier K M :=
  LinearEquiv.ofBijective
    { toFun := carrierLinearEquiv K M
      map_add' := (carrierLinearEquiv K M).map_add
      map_smul' := carrierLinearEquiv_smul K M }
    (carrierLinearEquiv K M).bijective

/-- The extracted representation recovers the original object in the genuine
finitely generated module category. -/
def extractedModuleIso
    (M : FGModuleCat.{u} (B0Model K)) :
    FiniteB0Rep.asFGModule K (extractedRep K M) ≅ M where
  hom := ConcreteCategory.ofHom (carrierModuleLinearEquiv K M).toLinearMap
  inv := ConcreteCategory.ofHom (carrierModuleLinearEquiv K M).symm.toLinearMap
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    exact (carrierModuleLinearEquiv K M).left_inv p
  inv_hom_id := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (carrierModuleLinearEquiv K M).right_inv m

end QuotientSubmoduleEquidistribution.LollipopConcrete.ModuleLayer.ModuleExtraction
