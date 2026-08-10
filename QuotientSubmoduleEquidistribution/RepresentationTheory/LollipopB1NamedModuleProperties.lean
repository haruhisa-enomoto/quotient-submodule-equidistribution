import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules
import QuotientSubmoduleEquidistribution.RepresentationTheory.FiniteType

/-!
# Properties of the seven named live-path lollipop modules

The seven displayed genuine `B₁`-modules `S₁, S₂, X, A, U, W, P` are
nonzero and indecomposable. Their underlying dimensions are
`1, 1, 2, 2, 3, 3, 4`; the three equal-dimension pairs are separated by the
actions of `e₁`, `a`, and the live path `u`, respectively.

This scratch file deliberately makes no exhaustiveness claim.
-/

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.NamedModuleProperties

universe u

variable (K : Type u) [Field K]

/-! ## Components of a module homomorphism -/

theorem map_smul_ground
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (c : K) (v : FiniteB1Rep.Carrier K D) :
    f (c • v) = c • f v := by
  rw [← IsScalarTower.algebraMap_smul (B1Model K) c v,
    f.map_smul, IsScalarTower.algebraMap_smul]

def inV1 (D : FiniteB1Rep K) : D.V₁ →ₗ[K] D.Carrier := by
  change D.V₁ →ₗ[K] D.V₁ × D.V₂
  exact LinearMap.inl K D.V₁ D.V₂

def inV2 (D : FiniteB1Rep K) : D.V₂ →ₗ[K] D.Carrier := by
  change D.V₂ →ₗ[K] D.V₁ × D.V₂
  exact LinearMap.inr K D.V₁ D.V₂

def outV1 (D : FiniteB1Rep K) : D.Carrier →ₗ[K] D.V₁ := by
  change D.V₁ × D.V₂ →ₗ[K] D.V₁
  exact LinearMap.fst K D.V₁ D.V₂

def outV2 (D : FiniteB1Rep K) : D.Carrier →ₗ[K] D.V₂ := by
  change D.V₁ × D.V₂ →ₗ[K] D.V₂
  exact LinearMap.snd K D.V₁ D.V₂

def homV1
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E) :
    D.V₁ →ₗ[K] E.V₁ :=
  (outV1 K E).comp ((f.restrictScalars K).comp (inV1 K D))

def homV2
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E) :
    D.V₂ →ₗ[K] E.V₂ :=
  (outV2 K E).comp ((f.restrictScalars K).comp (inV2 K D))

theorem map_ofV1
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (v : D.V₁) :
    f (FiniteB1Rep.ofV₁ K D v) =
      FiniteB1Rep.ofV₁ K E (homV1 K f v) := by
  have he1D :
      e1 K • FiniteB1Rep.ofV₁ K D v =
        FiniteB1Rep.ofV₁ K D v := by
    rw [FiniteB1Rep.e1_smul]
    rfl
  calc
    f (FiniteB1Rep.ofV₁ K D v) =
        f (e1 K • FiniteB1Rep.ofV₁ K D v) := by rw [he1D]
    _ = e1 K • f (FiniteB1Rep.ofV₁ K D v) := by rw [f.map_smul]
    _ = FiniteB1Rep.ofV₁ K E (homV1 K f v) := by
      rw [FiniteB1Rep.e1_smul]
      rfl

theorem map_ofV2
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (v : D.V₂) :
    f (FiniteB1Rep.ofV₂ K D v) =
      FiniteB1Rep.ofV₂ K E (homV2 K f v) := by
  have he2D :
      e2 K • FiniteB1Rep.ofV₂ K D v =
        FiniteB1Rep.ofV₂ K D v := by
    rw [FiniteB1Rep.e2_smul]
    rfl
  calc
    f (FiniteB1Rep.ofV₂ K D v) =
        f (e2 K • FiniteB1Rep.ofV₂ K D v) := by rw [he2D]
    _ = e2 K • f (FiniteB1Rep.ofV₂ K D v) := by rw [f.map_smul]
    _ = FiniteB1Rep.ofV₂ K E (homV2 K f v) := by
      rw [FiniteB1Rep.e2_smul]
      rfl

theorem map_eq_components
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (v : FiniteB1Rep.Carrier K D) :
    f v = FiniteB1Rep.ofV₁ K E
        (homV1 K f (FiniteB1Rep.fst K D v)) +
      FiniteB1Rep.ofV₂ K E
        (homV2 K f (FiniteB1Rep.snd K D v)) := by
  calc
    f v = f (FiniteB1Rep.ofV₁ K D (FiniteB1Rep.fst K D v) +
        FiniteB1Rep.ofV₂ K D (FiniteB1Rep.snd K D v)) := by
      congr 1
      rcases v with ⟨v1, v2⟩
      change (v1, v2) = (v1, 0) + (0, v2)
      apply Prod.ext
      · change v1 = v1 + 0
        simp
      · change v2 = 0 + v2
        simp
    _ = f (FiniteB1Rep.ofV₁ K D (FiniteB1Rep.fst K D v)) +
        f (FiniteB1Rep.ofV₂ K D (FiniteB1Rep.snd K D v)) := by rw [map_add]
    _ = FiniteB1Rep.ofV₁ K E
          (homV1 K f (FiniteB1Rep.fst K D v)) +
        FiniteB1Rep.ofV₂ K E
          (homV2 K f (FiniteB1Rep.snd K D v)) := by
      rw [map_ofV1 K f, map_ofV2 K f]

theorem hom_ext
    {D E : FiniteB1Rep K}
    {f g : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E}
    (h1 : homV1 K f = homV1 K g)
    (h2 : homV2 K f = homV2 K g) : f = g := by
  apply LinearMap.ext
  intro v
  rw [map_eq_components K f v, map_eq_components K g v, h1, h2]

theorem homV1_loop
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (v : D.V₁) :
    homV1 K f (D.loop.hom.hom v) =
      E.loop.hom.hom (homV1 K f v) := by
  have hxD :
      x K • FiniteB1Rep.ofV₁ K D v =
        FiniteB1Rep.ofV₁ K D (D.loop.hom.hom v) := by
    rw [FiniteB1Rep.x_smul]
    rfl
  have hxE :
      x K • FiniteB1Rep.ofV₁ K E (homV1 K f v) =
        FiniteB1Rep.ofV₁ K E (E.loop.hom.hom (homV1 K f v)) := by
    rw [FiniteB1Rep.x_smul]
    rfl
  calc
    homV1 K f (D.loop.hom.hom v) =
        FiniteB1Rep.fst K E
          (f (FiniteB1Rep.ofV₁ K D (D.loop.hom.hom v))) := rfl
    _ = FiniteB1Rep.fst K E
          (f (x K • FiniteB1Rep.ofV₁ K D v)) := by rw [hxD]
    _ = FiniteB1Rep.fst K E
          (x K • f (FiniteB1Rep.ofV₁ K D v)) := by rw [f.map_smul]
    _ = FiniteB1Rep.fst K E
          (x K • FiniteB1Rep.ofV₁ K E (homV1 K f v)) := by
      rw [map_ofV1 K f]
    _ = E.loop.hom.hom (homV1 K f v) := by
      rw [hxE]
      rfl

theorem homV2_stem
    {D E : FiniteB1Rep K}
    (f : FiniteB1Rep.Carrier K D →ₗ[B1Model K]
      FiniteB1Rep.Carrier K E)
    (v : D.V₁) :
    homV2 K f (D.stem.hom.hom v) =
      E.stem.hom.hom (homV1 K f v) := by
  calc
    homV2 K f (D.stem.hom.hom v) =
        FiniteB1Rep.snd K E
          (f (FiniteB1Rep.ofV₂ K D (D.stem.hom.hom v))) := rfl
    _ = FiniteB1Rep.snd K E
          (f (a K • FiniteB1Rep.ofV₁ K D v)) := by
      rw [FiniteB1Rep.a_smul]
      rfl
    _ = FiniteB1Rep.snd K E
          (a K • f (FiniteB1Rep.ofV₁ K D v)) := by rw [f.map_smul]
    _ = FiniteB1Rep.snd K E
          (a K • FiniteB1Rep.ofV₁ K E (homV1 K f v)) := by
      rw [map_ofV1 K f]
    _ = E.stem.hom.hom (homV1 K f v) := by
      rw [FiniteB1Rep.a_smul]
      rfl

/-! ## Nontriviality and dimensions -/

theorem S1_nontrivial : Nontrivial (S1Module K) := by
  change Nontrivial (K × (Fin 0 → K))
  infer_instance

theorem S2_nontrivial : Nontrivial (S2Module K) := by
  change Nontrivial ((Fin 0 → K) × K)
  infer_instance

theorem X_nontrivial : Nontrivial (XModule K) := by
  change Nontrivial ((K × K) × (Fin 0 → K))
  infer_instance

theorem A_nontrivial : Nontrivial (AModule K) := by
  change Nontrivial (K × K)
  infer_instance

theorem U_nontrivial : Nontrivial (UModule K) := by
  change Nontrivial ((K × K) × K)
  infer_instance

theorem W_nontrivial : Nontrivial (WModule K) := by
  change Nontrivial ((K × K) × K)
  infer_instance

theorem P_nontrivial : Nontrivial (PModule K) := by
  change Nontrivial ((K × K) × (K × K))
  infer_instance

@[simp] theorem finrank_S1 : Module.finrank K (S1Module K) = 1 := by
  change Module.finrank K (K × (Fin 0 → K)) = 1
  simp

@[simp] theorem finrank_S2 : Module.finrank K (S2Module K) = 1 := by
  change Module.finrank K ((Fin 0 → K) × K) = 1
  simp

@[simp] theorem finrank_X : Module.finrank K (XModule K) = 2 := by
  change Module.finrank K ((K × K) × (Fin 0 → K)) = 2
  simp

@[simp] theorem finrank_A : Module.finrank K (AModule K) = 2 := by
  change Module.finrank K (K × K) = 2
  simp

@[simp] theorem finrank_U : Module.finrank K (UModule K) = 3 := by
  change Module.finrank K ((K × K) × K) = 3
  simp

@[simp] theorem finrank_W : Module.finrank K (WModule K) = 3 := by
  change Module.finrank K ((K × K) × K) = 3
  simp

@[simp] theorem finrank_P : Module.finrank K (PModule K) = 4 := by
  change Module.finrank K ((K × K) × (K × K)) = 4
  simp

/-! ## Idempotent endomorphisms -/

theorem linearMap_K_apply
    (g : K →ₗ[K] K) (c : K) : g c = c * g 1 := by
  calc
    g c = g (c • (1 : K)) := by simp
    _ = c • g 1 := by rw [map_smul]
    _ = c * g 1 := rfl

theorem homV1_idempotent_apply
    {D : FiniteB1Rep K}
    (f : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
    (hf : IsIdempotentElem f) (v : D.V₁) :
    homV1 K f (homV1 K f v) = homV1 K f v := by
  have hff : f (f (FiniteB1Rep.ofV₁ K D v)) =
      f (FiniteB1Rep.ofV₁ K D v) := by
    simpa [Module.End.mul_apply] using
      DFunLike.congr_fun hf (FiniteB1Rep.ofV₁ K D v)
  rw [map_ofV1 K f, map_ofV1 K f] at hff
  have h := congrArg (fun z : FiniteB1Rep.Carrier K D => z.1) hff
  simpa only [FiniteB1Rep.ofV₁] using h

theorem homV2_idempotent_apply
    {D : FiniteB1Rep K}
    (f : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
    (hf : IsIdempotentElem f) (v : D.V₂) :
    homV2 K f (homV2 K f v) = homV2 K f v := by
  have hff : f (f (FiniteB1Rep.ofV₂ K D v)) =
      f (FiniteB1Rep.ofV₂ K D v) := by
    simpa [Module.End.mul_apply] using
      DFunLike.congr_fun hf (FiniteB1Rep.ofV₂ K D v)
  rw [map_ofV2 K f, map_ofV2 K f] at hff
  have h := congrArg (fun z : FiniteB1Rep.Carrier K D => z.2) hff
  simpa only [FiniteB1Rep.ofV₂] using h

@[simp] theorem homV1_zero {D : FiniteB1Rep K} :
    homV1 K
      (0 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D)) = 0 := by
  apply LinearMap.ext
  intro v
  change FiniteB1Rep.fst K D
    ((0 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
      (FiniteB1Rep.ofV₁ K D v)) = 0
  rw [LinearMap.zero_apply]
  rfl

@[simp] theorem homV2_zero {D : FiniteB1Rep K} :
    homV2 K
      (0 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D)) = 0 := by
  apply LinearMap.ext
  intro v
  change FiniteB1Rep.snd K D
    ((0 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
      (FiniteB1Rep.ofV₂ K D v)) = 0
  rw [LinearMap.zero_apply]
  rfl

@[simp] theorem homV1_one {D : FiniteB1Rep K} :
    homV1 K
      (1 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change FiniteB1Rep.fst K D
    ((1 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
      (FiniteB1Rep.ofV₁ K D v)) = v
  rw [Module.End.one_apply]
  rfl

@[simp] theorem homV2_one {D : FiniteB1Rep K} :
    homV2 K
      (1 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  change FiniteB1Rep.snd K D
    ((1 : Module.End (B1Model K) (FiniteB1Rep.Carrier K D))
      (FiniteB1Rep.ofV₂ K D v)) = v
  rw [Module.End.one_apply]
  rfl

theorem linearMap_commuting_jordan_formula
    (g : K × K →ₗ[K] K × K)
    (hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1))
    (r s : K) :
    g (r, s) =
      (r * (g (1, 0)).1,
        r * (g (1, 0)).2 + s * (g (1, 0)).1) := by
  have h01 : g (0, 1) = (0, (g (1, 0)).1) := by
    simpa using hcomm (1, 0)
  have hrs : (r, s) = r • (1, 0) + s • (0, 1) := by
    ext <;> simp
  rw [hrs, map_add, map_smul, map_smul, h01]
  ext <;> simp

theorem jordan_idempotent_eq_zero_or_id
    (g : K × K →ₗ[K] K × K)
    (hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1))
    (hidem : ∀ p : K × K, g (g p) = g p) :
    g = 0 ∨ g = LinearMap.id := by
  let alpha : K := (g (1, 0)).1
  let beta : K := (g (1, 0)).2
  have hone := hidem (1, 0)
  rw [linearMap_commuting_jordan_formula K g hcomm] at hone
  have halpha : alpha ^ 2 = alpha := by
    have h := congrArg Prod.fst hone
    simpa [alpha, pow_two] using h
  have hbeta : alpha * beta + beta * alpha = beta := by
    have h := congrArg Prod.snd hone
    simpa [alpha, beta] using h
  rcases eq_zero_or_one_of_sq_eq_self halpha with ha | ha
  · have hb : beta = 0 := by simpa [ha] using hbeta.symm
    left
    apply LinearMap.ext
    intro p
    rcases p with ⟨r, s⟩
    rw [linearMap_commuting_jordan_formula K g hcomm]
    change (r * alpha, r * beta + s * alpha) = 0
    simp [ha, hb]
  · have hb : beta = 0 := by simpa [ha] using hbeta
    right
    apply LinearMap.ext
    intro p
    rcases p with ⟨r, s⟩
    rw [linearMap_commuting_jordan_formula K g hcomm]
    change (r * alpha, r * beta + s * alpha) = (r, s)
    simp [ha, hb]

theorem oneDim_idempotent_eq_zero_or_id
    (g : K →ₗ[K] K) (hidem : ∀ c, g (g c) = g c) :
    g = 0 ∨ g = LinearMap.id := by
  have hsq : g 1 * g 1 = g 1 := by
    have h := hidem 1
    rw [linearMap_K_apply K] at h
    exact h
  have hpow : (g 1) ^ 2 = g 1 := by simpa [pow_two] using hsq
  rcases eq_zero_or_one_of_sq_eq_self hpow with hzero | hone
  · left
    apply LinearMap.ext
    intro c
    rw [linearMap_K_apply K, hzero]
    simp
  · right
    apply LinearMap.ext
    intro c
    rw [linearMap_K_apply K, hone, mul_one]
    rfl

/-! ## Indecomposability -/

theorem S1_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (S1Module K) := by
  letI : Nontrivial (S1Module K) := S1_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  have hidem : ∀ c : K, homV1 K f (homV1 K f c) = homV1 K f c :=
    homV1_idempotent_apply K f hf
  rcases oneDim_idempotent_eq_zero_or_id K (homV1 K f) hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := S1Data K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := S1Data K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _

theorem S2_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (S2Module K) := by
  letI : Nontrivial (S2Module K) := S2_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  have hidem : ∀ c : K, homV2 K f (homV2 K f c) = homV2 K f c :=
    homV2_idempotent_apply K f hf
  rcases oneDim_idempotent_eq_zero_or_id K (homV2 K f) hidem with hg | hg
  · left
    apply hom_ext K
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
    · exact hg.trans (homV2_zero K (D := S2Data K)).symm
  · right
    apply hom_ext K
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
    · exact hg.trans (homV2_one K (D := S2Data K)).symm

theorem A_hom_components_eq
    (f : Module.End (B1Model K) (AModule K)) (c : K) :
    homV2 K f c = homV1 K f c := by
  simpa using homV2_stem K f c

theorem A_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (AModule K) := by
  letI : Nontrivial (AModule K) := A_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  have hidem : ∀ c : K, homV1 K f (homV1 K f c) = homV1 K f c :=
    homV1_idempotent_apply K f hf
  rcases oneDim_idempotent_eq_zero_or_id K (homV1 K f) hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := AData K)).symm
    · apply LinearMap.ext
      intro c
      rw [A_hom_components_eq K]
      change homV1 K f c = (0 : K →ₗ[K] K) c
      rw [hg]
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := AData K)).symm
    · apply LinearMap.ext
      intro c
      rw [A_hom_components_eq K]
      change homV1 K f c = LinearMap.id c
      rw [hg]

theorem X_homV1_commutes_jordan
    (f : Module.End (B1Model K) (XModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem U_homV1_commutes_jordan
    (f : Module.End (B1Model K) (UModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem W_homV1_commutes_jordan
    (f : Module.End (B1Model K) (WModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem P_homV1_commutes_jordan
    (f : Module.End (B1Model K) (PModule K)) (p : K × K) :
    homV1 K f (0, p.1) = (0, (homV1 K f p).1) := by
  have h := homV1_loop K f p
  change homV1 K f (0, p.1) = (0, (homV1 K f p).1) at h
  exact h

theorem X_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (XModule K) := by
  letI : Nontrivial (XModule K) := X_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact X_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := XData K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := XData K)).symm
    · apply LinearMap.ext
      intro v
      exact Subsingleton.elim _ _

theorem U_homV2_eq_homV1_snd
    (f : Module.End (B1Model K) (UModule K)) (p : K × K) :
    homV2 K f p.2 = (homV1 K f p).2 := by
  have h := homV2_stem K f p
  change homV2 K f p.2 = (homV1 K f p).2 at h
  exact h

theorem W_homV2_eq_homV1_fst
    (f : Module.End (B1Model K) (WModule K)) (p : K × K) :
    homV2 K f p.1 = (homV1 K f p).1 := by
  have h := homV2_stem K f p
  change homV2 K f p.1 = (homV1 K f p).1 at h
  exact h

theorem P_homV2_eq_homV1
    (f : Module.End (B1Model K) (PModule K)) (p : K × K) :
    homV2 K f p = homV1 K f p := by
  simpa using homV2_stem K f p

theorem U_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (UModule K) := by
  letI : Nontrivial (UModule K) := U_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact U_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := UData K)).symm
    · apply LinearMap.ext
      intro c
      rw [U_homV2_eq_homV1_snd K f (0, c)]
      change (g (0, c)).2 = 0
      rw [hg]
      rfl
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := UData K)).symm
    · apply LinearMap.ext
      intro c
      rw [U_homV2_eq_homV1_snd K f (0, c)]
      change (g (0, c)).2 = c
      rw [hg]
      rfl

theorem W_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (WModule K) := by
  letI : Nontrivial (WModule K) := W_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact W_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := WData K)).symm
    · apply LinearMap.ext
      intro c
      rw [W_homV2_eq_homV1_fst K f (c, 0)]
      change (g (c, 0)).1 = 0
      rw [hg]
      rfl
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := WData K)).symm
    · apply LinearMap.ext
      intro c
      rw [W_homV2_eq_homV1_fst K f (c, 0)]
      change (g (c, 0)).1 = c
      rw [hg]
      rfl

theorem P_indec :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (PModule K) := by
  letI : Nontrivial (PModule K) := P_nontrivial K
  apply QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_forall_isIdempotentElem
  intro f hf
  let g : K × K →ₗ[K] K × K := homV1 K f
  have hcomm : ∀ p : K × K, g (0, p.1) = (0, (g p).1) := by
    intro p
    exact P_homV1_commutes_jordan K f p
  have hidem : ∀ p : K × K, g (g p) = g p := by
    intro p
    exact homV1_idempotent_apply K f hf p
  rcases jordan_idempotent_eq_zero_or_id K g hcomm hidem with hg | hg
  · left
    apply hom_ext K
    · exact hg.trans (homV1_zero K (D := PData K)).symm
    · have hV2zero : homV2 K f = 0 := by
        apply LinearMap.ext
        intro p
        rw [P_homV2_eq_homV1 K f p]
        change g p = 0
        rw [hg]
        rfl
      exact hV2zero.trans (homV2_zero K (D := PData K)).symm
  · right
    apply hom_ext K
    · exact hg.trans (homV1_one K (D := PData K)).symm
    · have hV2one : homV2 K f = LinearMap.id := by
        apply LinearMap.ext
        intro p
        rw [P_homV2_eq_homV1 K f p]
        change g p = p
        rw [hg]
        rfl
      exact hV2one.trans (homV2_one K (D := PData K)).symm

/-! ## Pairwise nonisomorphism -/

theorem not_iso_of_finrank_ne
    {D E : FiniteB1Rep K}
    (h : Module.finrank K (FiniteB1Rep.Carrier K D) ≠
      Module.finrank K (FiniteB1Rep.Carrier K E)) :
    ¬ Nonempty
      (FiniteB1Rep.asFGModule K D ≅ FiniteB1Rep.asFGModule K E) := by
  rintro ⟨e⟩
  apply h
  exact ((FGModuleCat.isoToLinearEquiv e).restrictScalars K).finrank_eq

theorem not_iso_symm
    {M N : FGModuleCat (B1Model K)}
    (h : ¬ Nonempty (M ≅ N)) : ¬ Nonempty (N ≅ M) := by
  rintro ⟨e⟩
  exact h ⟨e.symm⟩

theorem S2_e1_smul_eq_zero (z : S2Module K) : e1 K • z = 0 := by
  rw [FiniteB1Rep.e1_smul]
  apply FiniteB1Rep.carrier_ext K (S2Data K)
  · exact Subsingleton.elim _ _
  · rfl

theorem S1_not_iso_S2 : ¬ Nonempty (S1Module K ≅ S2Module K) := by
  rintro ⟨e⟩
  let v : S1Module K := FiniteB1Rep.ofV₁ K (S1Data K) (1 : K)
  let g : S1Module K ≃ₗ[B1Model K] S2Module K :=
    FGModuleCat.isoToLinearEquiv e
  have hgv : g v = 0 := by
    calc
      g v = g (e1 K • v) := by
        congr 1
        rw [FiniteB1Rep.e1_smul]
        rfl
      _ = e1 K • g v := by rw [map_smul]
      _ = 0 := S2_e1_smul_eq_zero K _
  have hgv0 : g v = g 0 := by simpa using hgv
  have hvzero : v = 0 := g.injective hgv0
  have hcoord := congrArg (fun z : S1Module K => z.1) hvzero
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem X_a_smul_eq_zero (z : XModule K) : a K • z = 0 := by
  rw [FiniteB1Rep.a_smul]
  apply FiniteB1Rep.carrier_ext K (XData K)
  · rfl
  · exact Subsingleton.elim _ _

theorem X_not_iso_A : ¬ Nonempty (XModule K ≅ AModule K) := by
  rintro ⟨e⟩
  let w : AModule K := FiniteB1Rep.ofV₁ K (AData K) (1 : K)
  let g : AModule K ≃ₗ[B1Model K] XModule K :=
    (FGModuleCat.isoToLinearEquiv e).symm
  have hmap : g (a K • w) = 0 := by
    calc
      g (a K • w) = a K • g w := by rw [map_smul]
      _ = 0 := X_a_smul_eq_zero K _
  have hmap0 : g (a K • w) = g 0 := by simpa using hmap
  have haw : a K • w = 0 := g.injective hmap0
  rw [FiniteB1Rep.a_smul] at haw
  have hcoord := congrArg (fun z : AModule K => z.2) haw
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem U_not_iso_W : ¬ Nonempty (UModule K ≅ WModule K) := by
  rintro ⟨e⟩
  let v : UModule K := FiniteB1Rep.ofV₁ K (UData K) (1, 0)
  let g : UModule K ≃ₗ[B1Model K] WModule K :=
    FGModuleCat.isoToLinearEquiv e
  have hmap : g (u K • v) = 0 := by
    calc
      g (u K • v) = u K • g v := by rw [map_smul]
      _ = 0 := W_u_smul_eq_zero K _
  have hmap0 : g (u K • v) = g 0 := by simpa using hmap
  have huv : u K • v = 0 := g.injective hmap0
  exact U_u_smul_top_ne_zero K huv

theorem S1_not_iso_X : ¬ Nonempty (S1Module K ≅ XModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × (Fin 0 → K))
  simp

theorem S1_not_iso_A : ¬ Nonempty (S1Module K ≅ AModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K (K × K)
  simp

theorem S1_not_iso_U : ¬ Nonempty (S1Module K ≅ UModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S1_not_iso_W : ¬ Nonempty (S1Module K ≅ WModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S1_not_iso_P : ¬ Nonempty (S1Module K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem S2_not_iso_X : ¬ Nonempty (S2Module K ≅ XModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × (Fin 0 → K))
  simp

theorem S2_not_iso_A : ¬ Nonempty (S2Module K ≅ AModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K (K × K)
  simp

theorem S2_not_iso_U : ¬ Nonempty (S2Module K ≅ UModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S2_not_iso_W : ¬ Nonempty (S2Module K ≅ WModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem S2_not_iso_P : ¬ Nonempty (S2Module K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((Fin 0 → K) × K) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem X_not_iso_U : ¬ Nonempty (XModule K ≅ UModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem X_not_iso_W : ¬ Nonempty (XModule K ≅ WModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem X_not_iso_P : ¬ Nonempty (XModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × (Fin 0 → K)) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem A_not_iso_U : ¬ Nonempty (AModule K ≅ UModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem A_not_iso_W : ¬ Nonempty (AModule K ≅ WModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × K) ≠
    Module.finrank K ((K × K) × K)
  simp

theorem A_not_iso_P : ¬ Nonempty (AModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K (K × K) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem U_not_iso_P : ¬ Nonempty (UModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × K) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem W_not_iso_P : ¬ Nonempty (WModule K ≅ PModule K) := by
  apply not_iso_of_finrank_ne K
  change Module.finrank K ((K × K) × K) ≠
    Module.finrank K ((K × K) × (K × K))
  simp

theorem namedModule_nontrivial (i : NamedLabel) :
    Nontrivial (namedModule K i) := by
  cases i
  · exact S1_nontrivial K
  · exact S2_nontrivial K
  · exact X_nontrivial K
  · exact A_nontrivial K
  · exact U_nontrivial K
  · exact W_nontrivial K
  · exact P_nontrivial K

theorem namedModule_indec (i : NamedLabel) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule (B1Model K) (namedModule K i) := by
  cases i
  · exact S1_indec K
  · exact S2_indec K
  · exact X_indec K
  · exact A_indec K
  · exact U_indec K
  · exact W_indec K
  · exact P_indec K

theorem namedModule_not_iso_of_ne
    {i j : NamedLabel} (hij : i ≠ j) :
    ¬ Nonempty (namedModule K i ≅ namedModule K j) := by
  cases i <;> cases j
  all_goals simp at hij
  all_goals
    first
    | exact S1_not_iso_S2 K
    | exact not_iso_symm K (S1_not_iso_S2 K)
    | exact X_not_iso_A K
    | exact not_iso_symm K (X_not_iso_A K)
    | exact U_not_iso_W K
    | exact not_iso_symm K (U_not_iso_W K)
    | exact S1_not_iso_X K
    | exact not_iso_symm K (S1_not_iso_X K)
    | exact S1_not_iso_A K
    | exact not_iso_symm K (S1_not_iso_A K)
    | exact S1_not_iso_U K
    | exact not_iso_symm K (S1_not_iso_U K)
    | exact S1_not_iso_W K
    | exact not_iso_symm K (S1_not_iso_W K)
    | exact S1_not_iso_P K
    | exact not_iso_symm K (S1_not_iso_P K)
    | exact S2_not_iso_X K
    | exact not_iso_symm K (S2_not_iso_X K)
    | exact S2_not_iso_A K
    | exact not_iso_symm K (S2_not_iso_A K)
    | exact S2_not_iso_U K
    | exact not_iso_symm K (S2_not_iso_U K)
    | exact S2_not_iso_W K
    | exact not_iso_symm K (S2_not_iso_W K)
    | exact S2_not_iso_P K
    | exact not_iso_symm K (S2_not_iso_P K)
    | exact X_not_iso_U K
    | exact not_iso_symm K (X_not_iso_U K)
    | exact X_not_iso_W K
    | exact not_iso_symm K (X_not_iso_W K)
    | exact X_not_iso_P K
    | exact not_iso_symm K (X_not_iso_P K)
    | exact A_not_iso_U K
    | exact not_iso_symm K (A_not_iso_U K)
    | exact A_not_iso_W K
    | exact not_iso_symm K (A_not_iso_W K)
    | exact A_not_iso_P K
    | exact not_iso_symm K (A_not_iso_P K)
    | exact U_not_iso_P K
    | exact not_iso_symm K (U_not_iso_P K)
    | exact W_not_iso_P K
    | exact not_iso_symm K (W_not_iso_P K)

theorem namedModules_pairwise_nonisomorphic :
    Pairwise (fun i j : NamedLabel =>
      ¬ Nonempty (namedModule K i ≅ namedModule K j)) := by
  intro i j hij
  exact namedModule_not_iso_of_ne K hij

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.NamedModuleProperties
