import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopB1Modules
import QuotientSubmoduleEquidistribution.RepresentationTheory.LollipopTableCertificates

/-!
# Explicit submodule rows for the live-path lollipop

Verification against the tracked `B1Model` and its seven named
modules.  All closure proxies below quantify only over the explicitly listed
named targets and their finite biproducts.  No indecomposable classification,
skeleton exhaustion, or closure claim is made.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SubmoduleRows

universe u v w

variable (K : Type u) [Field K]

/-! ## Componentwise morphism constructor -/

theorem b1Action_formula
    (V₁ V₂ : Type u)
    [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₂] [Module K V₂]
    (loop : V₁ →ₗ[K] V₁) (stem : V₁ →ₗ[K] V₂)
    (hloop : ∀ z, loop (loop z) = 0)
    (b : B1Model K) (z : V₁ × V₂) :
    b1Action K V₁ V₂ loop stem hloop b z =
      (b.fst.1.fst • z.1 + b.fst.1.snd • loop z.1,
        b.fst.2 • z.2 +
          (b.snd.fst • stem z.1 + b.snd.snd • stem (loop z.1))) := by
  unfold b1Action
  rw [TrivSqZeroExt.lift_def]
  simp [baseAction, arrowAction, loopCornerAction_apply]

theorem smul_formula (D : FiniteB1Rep K) (b : B1Model K) (z : D.Carrier K) :
    b • z =
      (b.fst.1.fst • z.1 + b.fst.1.snd • D.loop.hom.hom z.1,
        b.fst.2 • z.2 +
          (b.snd.fst • D.stem.hom.hom z.1 +
            b.snd.snd • D.stem.hom.hom (D.loop.hom.hom z.1))) := by
  change FiniteB1Rep.actionHom K D b z = _
  exact b1Action_formula K D.V₁ D.V₂ D.loop.hom.hom D.stem.hom.hom
    D.loop_sq b z

/-- A pair of vertex maps commuting with the loop and stem induces a genuine
`B1Model`-linear map. -/
def homOfComponents
    (D E : FiniteB1Rep K)
    (f₁ : D.V₁ →ₗ[K] E.V₁) (f₂ : D.V₂ →ₗ[K] E.V₂)
    (hloop : ∀ z, f₁ (D.loop.hom.hom z) = E.loop.hom.hom (f₁ z))
    (hstem : ∀ z, f₂ (D.stem.hom.hom z) = E.stem.hom.hom (f₁ z)) :
    D.asFGModule K ⟶ E.asFGModule K :=
  FGModuleCat.ofHom
    { toFun := fun z ↦ (f₁ z.1, f₂ z.2)
      map_add' := by
        intro z z'
        exact (f₁.prodMap f₂).map_add z z'
      map_smul' := by
        intro b z
        rw [smul_formula K D, smul_formula K E]
        apply Prod.ext
        · simp [hloop]
        · simp [hloop, hstem] }

@[simp] theorem homOfComponents_apply
    (D E : FiniteB1Rep K)
    (f₁ : D.V₁ →ₗ[K] E.V₁) (f₂ : D.V₂ →ₗ[K] E.V₂)
    (hloop : ∀ z, f₁ (D.loop.hom.hom z) = E.loop.hom.hom (f₁ z))
    (hstem : ∀ z, f₂ (D.stem.hom.hom z) = E.stem.hom.hom (f₁ z))
    (z : D.asFGModule K) :
    (homOfComponents K D E f₁ f₂ hloop hstem).hom.hom z =
      (f₁ z.1, f₂ z.2) := rfl

/-! ## Nonzero candidate kernel lines -/

def uTopGenerator : UModule K := FiniteB1Rep.ofV₁ K (UData K) (1, 0)
def uSocleGenerator : UModule K := FiniteB1Rep.ofV₁ K (UData K) (0, 1)

def xTopGenerator : XModule K := FiniteB1Rep.ofV₁ K (XData K) (1, 0)
def xSocleGenerator : XModule K := FiniteB1Rep.ofV₁ K (XData K) (0, 1)

def wTopGenerator : WModule K := FiniteB1Rep.ofV₁ K (WData K) (1, 0)
def wSocleGenerator : WModule K := FiniteB1Rep.ofV₁ K (WData K) (0, 1)

def s1Generator : S1Module K := FiniteB1Rep.ofV₁ K (S1Data K) 1

@[simp] theorem uSocleGenerator_eq_x_smul :
    uSocleGenerator K = x K • uTopGenerator K := by
  rw [FiniteB1Rep.x_smul]
  rfl

@[simp] theorem xSocleGenerator_eq_x_smul :
    xSocleGenerator K = x K • xTopGenerator K := by
  rw [FiniteB1Rep.x_smul]
  rfl

@[simp] theorem wSocleGenerator_eq_x_smul :
    wSocleGenerator K = x K • wTopGenerator K := by
  rw [FiniteB1Rep.x_smul]
  rfl

def uSocleLine : Submodule (B1Model K) (UModule K) :=
  Submodule.span (B1Model K) {uSocleGenerator K}

def xSocleLine : Submodule (B1Model K) (XModule K) :=
  Submodule.span (B1Model K) {xSocleGenerator K}

def wSocleLine : Submodule (B1Model K) (WModule K) :=
  Submodule.span (B1Model K) {wSocleGenerator K}

def s1GeneratorLine : Submodule (B1Model K) (S1Module K) :=
  Submodule.span (B1Model K) {s1Generator K}

theorem uSocleGenerator_ne_zero : uSocleGenerator K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : UModule K ↦ z.1.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem xSocleGenerator_ne_zero : xSocleGenerator K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : XModule K ↦ z.1.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem wSocleGenerator_ne_zero : wSocleGenerator K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : WModule K ↦ z.1.2) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

theorem s1Generator_ne_zero : s1Generator K ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : S1Module K ↦ z.1) h
  change (1 : K) = 0 at hcoord
  exact one_ne_zero hcoord

private theorem span_singleton_ne_bot
    {M : Type*} [AddCommGroup M] [Module (B1Model K) M]
    (g : M) (hg : g ≠ 0) :
    Submodule.span (B1Model K) {g} ≠ ⊥ := by
  intro hbot
  apply hg
  have hmem : g ∈ (⊥ : Submodule (B1Model K) M) := by
    rw [← hbot]
    exact Submodule.subset_span (Set.mem_singleton g)
  simpa using hmem

theorem uSocleLine_ne_bot : uSocleLine K ≠ ⊥ :=
  span_singleton_ne_bot K _ (uSocleGenerator_ne_zero K)

theorem xSocleLine_ne_bot : xSocleLine K ≠ ⊥ :=
  span_singleton_ne_bot K _ (xSocleGenerator_ne_zero K)

theorem wSocleLine_ne_bot : wSocleLine K ≠ ⊥ :=
  span_singleton_ne_bot K _ (wSocleGenerator_ne_zero K)

theorem s1GeneratorLine_ne_bot : s1GeneratorLine K ≠ ⊥ :=
  span_singleton_ne_bot K _ (s1Generator_ne_zero K)

/-! ## Generator-killing lemmas -/

/-- A target with zero loop kills the image of any source loop vector. -/
theorem map_x_smul_eq_zero_of_target_loop_eq_zero
    (D E : FiniteB1Rep K)
    (hloop : ∀ z, E.loop.hom.hom z = 0)
    (f : D.asFGModule K ⟶ E.asFGModule K) (g : D.asFGModule K) :
    f.hom.hom (x K • g) = 0 := by
  calc
    f.hom.hom (x K • g) = x K • f.hom.hom g := f.hom.hom.map_smul _ _
    _ = 0 := by
      rw [FiniteB1Rep.x_smul]
      apply FiniteB1Rep.carrier_ext K E
      · exact hloop _
      · rfl

theorem map_uSocle_to_loopZero_eq_zero
    (E : FiniteB1Rep K) (hloop : ∀ z, E.loop.hom.hom z = 0)
    (f : UModule K ⟶ E.asFGModule K) :
    f.hom.hom (uSocleGenerator K) = 0 := by
  rw [uSocleGenerator_eq_x_smul]
  exact map_x_smul_eq_zero_of_target_loop_eq_zero K (UData K) E hloop f _

theorem map_xSocle_to_loopZero_eq_zero
    (E : FiniteB1Rep K) (hloop : ∀ z, E.loop.hom.hom z = 0)
    (f : XModule K ⟶ E.asFGModule K) :
    f.hom.hom (xSocleGenerator K) = 0 := by
  rw [xSocleGenerator_eq_x_smul]
  exact map_x_smul_eq_zero_of_target_loop_eq_zero K (XData K) E hloop f _

theorem map_wSocle_to_loopZero_eq_zero
    (E : FiniteB1Rep K) (hloop : ∀ z, E.loop.hom.hom z = 0)
    (f : WModule K ⟶ E.asFGModule K) :
    f.hom.hom (wSocleGenerator K) = 0 := by
  rw [wSocleGenerator_eq_x_smul]
  exact map_x_smul_eq_zero_of_target_loop_eq_zero K (WData K) E hloop f _

/-- If the chosen source top is killed by `a`, its loop vector maps to zero
in `P`, whose stem is the identity. -/
theorem map_x_smul_to_P_eq_zero_of_a_top_eq_zero
    (D : FiniteB1Rep K) (g : D.asFGModule K)
    (hag : a K • g = 0)
    (f : D.asFGModule K ⟶ PModule K) :
    f.hom.hom (x K • g) = 0 := by
  have haimage : a K • f.hom.hom g = 0 := by
    calc
      a K • f.hom.hom g = f.hom.hom (a K • g) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hag, map_zero]
  have hfst : (f.hom.hom g).1 = 0 := by
    rw [FiniteB1Rep.a_smul] at haimage
    exact congrArg Prod.snd haimage
  calc
    f.hom.hom (x K • g) = x K • f.hom.hom g := f.hom.hom.map_smul _ _
    _ = 0 := by rw [FiniteB1Rep.x_smul, hfst]; rfl

theorem map_uSocle_to_P_eq_zero (f : UModule K ⟶ PModule K) :
    f.hom.hom (uSocleGenerator K) = 0 := by
  rw [uSocleGenerator_eq_x_smul]
  apply map_x_smul_to_P_eq_zero_of_a_top_eq_zero K (UData K) (uTopGenerator K)
  · rw [FiniteB1Rep.a_smul]
    rfl

theorem map_xSocle_to_P_eq_zero (f : XModule K ⟶ PModule K) :
    f.hom.hom (xSocleGenerator K) = 0 := by
  rw [xSocleGenerator_eq_x_smul]
  apply map_x_smul_to_P_eq_zero_of_a_top_eq_zero K (XData K) (xTopGenerator K)
  · rw [FiniteB1Rep.a_smul]
    rfl

/-- The live coordinate vanishes on the chosen `W` top; in `P`, that
coordinate detects precisely the loop of the vertex-one component. -/
theorem map_wSocle_to_P_eq_zero (f : WModule K ⟶ PModule K) :
    f.hom.hom (wSocleGenerator K) = 0 := by
  have huSource : u K • wTopGenerator K = 0 := W_u_smul_eq_zero K _
  have huimage : u K • f.hom.hom (wTopGenerator K) = 0 := by
    calc
      u K • f.hom.hom (wTopGenerator K) =
          f.hom.hom (u K • wTopGenerator K) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [huSource, map_zero]
  have hloop : (PData K).loop.hom.hom (f.hom.hom (wTopGenerator K)).1 = 0 := by
    rw [FiniteB1Rep.u_smul] at huimage
    exact congrArg Prod.snd huimage
  rw [wSocleGenerator_eq_x_smul, f.hom.hom.map_smul, FiniteB1Rep.x_smul,
    hloop]
  rfl

/-- In `U`, the live coordinate detects the top coordinate, hence forces the
target loop vector to vanish. -/
theorem map_x_smul_to_U_eq_zero_of_u_top_eq_zero
    (D : FiniteB1Rep K) (g : D.asFGModule K)
    (hug : u K • g = 0)
    (f : D.asFGModule K ⟶ UModule K) :
    f.hom.hom (x K • g) = 0 := by
  have huimage : u K • f.hom.hom g = 0 := by
    calc
      u K • f.hom.hom g = f.hom.hom (u K • g) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hug, map_zero]
  have htop : (f.hom.hom g).1.1 = 0 := by
    rw [FiniteB1Rep.u_smul] at huimage
    have hcoord := congrArg (fun z : UModule K ↦ z.2) huimage
    change (f.hom.hom g).1.1 = 0 at hcoord
    exact hcoord
  calc
    f.hom.hom (x K • g) = x K • f.hom.hom g := f.hom.hom.map_smul _ _
    _ = 0 := by
      rw [FiniteB1Rep.x_smul]
      change ((0, (f.hom.hom g).1.1), 0) = 0
      rw [htop]
      rfl

theorem map_xSocle_to_U_eq_zero (f : XModule K ⟶ UModule K) :
    f.hom.hom (xSocleGenerator K) = 0 := by
  rw [xSocleGenerator_eq_x_smul]
  apply map_x_smul_to_U_eq_zero_of_u_top_eq_zero K (XData K) (xTopGenerator K)
  · rw [FiniteB1Rep.u_smul]
    rfl

theorem map_wSocle_to_U_eq_zero (f : WModule K ⟶ UModule K) :
    f.hom.hom (wSocleGenerator K) = 0 := by
  rw [wSocleGenerator_eq_x_smul]
  exact map_x_smul_to_U_eq_zero_of_u_top_eq_zero K (WData K)
    (wTopGenerator K) (W_u_smul_eq_zero K _) f

theorem image_ofV₁_snd_eq_zero
    (D E : FiniteB1Rep K)
    (f : D.asFGModule K ⟶ E.asFGModule K) (q : D.V₁) :
    (f.hom.hom (FiniteB1Rep.ofV₁ K D q)).2 = 0 := by
  have hfixed :
      e1 K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) =
        f.hom.hom (FiniteB1Rep.ofV₁ K D q) := by
    calc
      e1 K • f.hom.hom (FiniteB1Rep.ofV₁ K D q) =
          f.hom.hom (e1 K • FiniteB1Rep.ofV₁ K D q) :=
        (f.hom.hom.map_smul _ _).symm
      _ = f.hom.hom (FiniteB1Rep.ofV₁ K D q) := by
        rw [FiniteB1Rep.e1_smul]
        simp [FiniteB1Rep.ofV₁]
  rw [FiniteB1Rep.e1_smul] at hfixed
  exact (congrArg Prod.snd hfixed).symm

theorem map_s1Generator_to_stemInjective_eq_zero
    (E : FiniteB1Rep K)
    (hstem : Function.Injective E.stem.hom.hom)
    (f : S1Module K ⟶ E.asFGModule K) :
    f.hom.hom (s1Generator K) = 0 := by
  have hag : a K • s1Generator K = 0 := by
    rw [FiniteB1Rep.a_smul]
    rfl
  have haimage : a K • f.hom.hom (s1Generator K) = 0 := by
    calc
      a K • f.hom.hom (s1Generator K) = f.hom.hom (a K • s1Generator K) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hag, map_zero]
  have hstemZero : E.stem.hom.hom (f.hom.hom (s1Generator K)).1 = 0 := by
    rw [FiniteB1Rep.a_smul] at haimage
    exact congrArg Prod.snd haimage
  have hfst : (f.hom.hom (s1Generator K)).1 = 0 := by
    apply hstem
    simpa using hstemZero
  have hsnd : (f.hom.hom (s1Generator K)).2 = 0 :=
    image_ofV₁_snd_eq_zero K (S1Data K) E f 1
  exact Prod.ext hfst hsnd

theorem map_s1Generator_to_P_eq_zero (f : S1Module K ⟶ PModule K) :
    f.hom.hom (s1Generator K) = 0 :=
  map_s1Generator_to_stemInjective_eq_zero K (PData K) (by intro q q' h; exact h) f

theorem map_s1Generator_to_A_eq_zero (f : S1Module K ⟶ AModule K) :
    f.hom.hom (s1Generator K) = 0 :=
  map_s1Generator_to_stemInjective_eq_zero K (AData K) (by intro q q' h; exact h) f

theorem map_s1Generator_to_S2_eq_zero (f : S1Module K ⟶ S2Module K) :
    f.hom.hom (s1Generator K) = 0 := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact image_ofV₁_snd_eq_zero K (S1Data K) (S2Data K) f 1

theorem map_s1Generator_to_U_eq_zero (f : S1Module K ⟶ UModule K) :
    f.hom.hom (s1Generator K) = 0 := by
  have hxg : x K • s1Generator K = 0 := by
    rw [FiniteB1Rep.x_smul]
    rfl
  have hag : a K • s1Generator K = 0 := by
    rw [FiniteB1Rep.a_smul]
    rfl
  have hximage : x K • f.hom.hom (s1Generator K) = 0 := by
    calc
      x K • f.hom.hom (s1Generator K) = f.hom.hom (x K • s1Generator K) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hxg, map_zero]
  have haimage : a K • f.hom.hom (s1Generator K) = 0 := by
    calc
      a K • f.hom.hom (s1Generator K) = f.hom.hom (a K • s1Generator K) :=
        (f.hom.hom.map_smul _ _).symm
      _ = 0 := by rw [hag, map_zero]
  have htop : (f.hom.hom (s1Generator K)).1.1 = 0 := by
    rw [FiniteB1Rep.x_smul] at hximage
    have hcoord := congrArg (fun z : UModule K ↦ z.1.2) hximage
    change (f.hom.hom (s1Generator K)).1.1 = 0 at hcoord
    exact hcoord
  have hbottom : (f.hom.hom (s1Generator K)).1.2 = 0 := by
    rw [FiniteB1Rep.a_smul] at haimage
    exact congrArg Prod.snd haimage
  have hfst : (f.hom.hom (s1Generator K)).1 = 0 := Prod.ext htop hbottom
  have hsnd : (f.hom.hom (s1Generator K)).2 = 0 :=
    image_ofV₁_snd_eq_zero K (S1Data K) (UData K) f 1
  exact Prod.ext hfst hsnd

/-! ## Pointwise common kernels for the two good rows -/

/-- The four selected targets in `core {P,S₂,A} + S₁`. -/
inductive S1RowTarget where
  | p
  | s2
  | a
  | s1
  deriving DecidableEq

def s1RowTargetModule : S1RowTarget → FGModuleCat (B1Model K)
  | .p => PModule K
  | .s2 => S2Module K
  | .a => AModule K
  | .s1 => S1Module K

theorem s1Row_map_uSocle_eq_zero
    (i : S1RowTarget) (f : UModule K ⟶ s1RowTargetModule K i) :
    f.hom.hom (uSocleGenerator K) = 0 := by
  cases i with
  | p => exact map_uSocle_to_P_eq_zero K f
  | s2 => exact map_uSocle_to_loopZero_eq_zero K (S2Data K) (by intro z; rfl) f
  | a => exact map_uSocle_to_loopZero_eq_zero K (AData K) (by intro z; rfl) f
  | s1 => exact map_uSocle_to_loopZero_eq_zero K (S1Data K) (by intro z; rfl) f

theorem s1Row_map_xSocle_eq_zero
    (i : S1RowTarget) (f : XModule K ⟶ s1RowTargetModule K i) :
    f.hom.hom (xSocleGenerator K) = 0 := by
  cases i with
  | p => exact map_xSocle_to_P_eq_zero K f
  | s2 => exact map_xSocle_to_loopZero_eq_zero K (S2Data K) (by intro z; rfl) f
  | a => exact map_xSocle_to_loopZero_eq_zero K (AData K) (by intro z; rfl) f
  | s1 => exact map_xSocle_to_loopZero_eq_zero K (S1Data K) (by intro z; rfl) f

theorem s1Row_map_wSocle_eq_zero
    (i : S1RowTarget) (f : WModule K ⟶ s1RowTargetModule K i) :
    f.hom.hom (wSocleGenerator K) = 0 := by
  cases i with
  | p => exact map_wSocle_to_P_eq_zero K f
  | s2 => exact map_wSocle_to_loopZero_eq_zero K (S2Data K) (by intro z; rfl) f
  | a => exact map_wSocle_to_loopZero_eq_zero K (AData K) (by intro z; rfl) f
  | s1 => exact map_wSocle_to_loopZero_eq_zero K (S1Data K) (by intro z; rfl) f

private theorem span_singleton_le_ker_of_map_eq_zero
    {M N : FGModuleCat (B1Model K)} (g : M)
    (f : M ⟶ N) (h : f.hom.hom g = 0) :
    Submodule.span (B1Model K) {g} ≤ LinearMap.ker f.hom.hom := by
  rw [Submodule.span_le]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact LinearMap.mem_ker.mpr h

theorem uSocleLine_le_ker_s1Row
    (i : S1RowTarget) (f : UModule K ⟶ s1RowTargetModule K i) :
    uSocleLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (s1Row_map_uSocle_eq_zero K i f)

theorem xSocleLine_le_ker_s1Row
    (i : S1RowTarget) (f : XModule K ⟶ s1RowTargetModule K i) :
    xSocleLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (s1Row_map_xSocle_eq_zero K i f)

theorem wSocleLine_le_ker_s1Row
    (i : S1RowTarget) (f : WModule K ⟶ s1RowTargetModule K i) :
    wSocleLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (s1Row_map_wSocle_eq_zero K i f)

/-- The four selected targets in `core {P,S₂,A} + U`. -/
inductive URowTarget where
  | p
  | s2
  | a
  | u
  deriving DecidableEq

def uRowTargetModule : URowTarget → FGModuleCat (B1Model K)
  | .p => PModule K
  | .s2 => S2Module K
  | .a => AModule K
  | .u => UModule K

theorem uRow_map_s1Generator_eq_zero
    (i : URowTarget) (f : S1Module K ⟶ uRowTargetModule K i) :
    f.hom.hom (s1Generator K) = 0 := by
  cases i with
  | p => exact map_s1Generator_to_P_eq_zero K f
  | s2 => exact map_s1Generator_to_S2_eq_zero K f
  | a => exact map_s1Generator_to_A_eq_zero K f
  | u => exact map_s1Generator_to_U_eq_zero K f

theorem uRow_map_xSocle_eq_zero
    (i : URowTarget) (f : XModule K ⟶ uRowTargetModule K i) :
    f.hom.hom (xSocleGenerator K) = 0 := by
  cases i with
  | p => exact map_xSocle_to_P_eq_zero K f
  | s2 => exact map_xSocle_to_loopZero_eq_zero K (S2Data K) (by intro z; rfl) f
  | a => exact map_xSocle_to_loopZero_eq_zero K (AData K) (by intro z; rfl) f
  | u => exact map_xSocle_to_U_eq_zero K f

theorem uRow_map_wSocle_eq_zero
    (i : URowTarget) (f : WModule K ⟶ uRowTargetModule K i) :
    f.hom.hom (wSocleGenerator K) = 0 := by
  cases i with
  | p => exact map_wSocle_to_P_eq_zero K f
  | s2 => exact map_wSocle_to_loopZero_eq_zero K (S2Data K) (by intro z; rfl) f
  | a => exact map_wSocle_to_loopZero_eq_zero K (AData K) (by intro z; rfl) f
  | u => exact map_wSocle_to_U_eq_zero K f

theorem s1GeneratorLine_le_ker_uRow
    (i : URowTarget) (f : S1Module K ⟶ uRowTargetModule K i) :
    s1GeneratorLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (uRow_map_s1Generator_eq_zero K i f)

theorem xSocleLine_le_ker_uRow
    (i : URowTarget) (f : XModule K ⟶ uRowTargetModule K i) :
    xSocleLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (uRow_map_xSocle_eq_zero K i f)

theorem wSocleLine_le_ker_uRow
    (i : URowTarget) (f : WModule K ⟶ uRowTargetModule K i) :
    wSocleLine K ≤ LinearMap.ker f.hom.hom :=
  span_singleton_le_ker_of_map_eq_zero K _ f (uRow_map_wSocle_eq_zero K i f)

/-! ## Aggregation over arbitrary finite sums of exactly the named targets -/

structure EnumeratedCommonKernelCertificate
    {R : Type u} [Ring R]
    (I : Type v) (source : FGModuleCat.{w} R)
    (target : I → FGModuleCat.{w} R) where
  witness : Submodule R source
  witness_ne_bot : witness ≠ ⊥
  witness_le_ker : ∀ i (f : source ⟶ target i),
    witness ≤ LinearMap.ker f.hom.hom

attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts

structure EnumeratedSelectedMapFrom
    {R : Type u} [Ring R]
    (I : Type v) (source : FGModuleCat.{w} R)
    (target : I → FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → I
  map : source ⟶ biproduct fun t ↦ target (label t)

/-- Reject against all maps into finite direct sums of the explicitly
enumerated targets, with repetitions allowed. -/
def enumeratedReject
    {R : Type u} [Ring R]
    {I : Type v} (source : FGModuleCat.{w} R)
    (target : I → FGModuleCat.{w} R) : Submodule R source :=
  ⨅ f : EnumeratedSelectedMapFrom I source target, LinearMap.ker f.map.hom.hom

private theorem biproduct_apply_eq_zero_of_components
    {R : Type u} [Ring R]
    {J : Type*} [Fintype J]
    {source : FGModuleCat.{w} R} {target : J → FGModuleCat.{w} R}
    (g : source ⟶ ⨁ target) (z : source)
    (h : ∀ j, (g ≫ biproduct.π target j).hom.hom z = 0) :
    g.hom.hom z = 0 := by
  classical
  let C : Submodule R source := R ∙ z
  letI : Module.Finite R C :=
    Module.Finite.of_fg (Submodule.fg_span_singleton z)
  let e : FGModuleCat.of R C ⟶ source := FGModuleCat.ofHom C.subtype
  have he : e ≫ g = 0 := by
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, zero_comp]
    apply FGModuleCat.hom_ext
    ext y
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp y.2
    change (g ≫ biproduct.π target j).hom.hom y.1 = 0
    rw [← hr, map_smul, h j, smul_zero]
  let y : C := ⟨z, Submodule.mem_span_singleton_self z⟩
  have hy := congrArg (fun f : FGModuleCat.of R C ⟶ ⨁ target ↦ f.hom.hom y) he
  change g.hom.hom (C.subtype y) = 0 at hy
  exact hy

namespace EnumeratedCommonKernelCertificate

theorem witness_le_enumeratedReject
    {R : Type u} [Ring R]
    {I : Type v} {source : FGModuleCat.{w} R}
    {target : I → FGModuleCat.{w} R}
    (C : EnumeratedCommonKernelCertificate I source target) :
    C.witness ≤ SubmoduleRows.enumeratedReject source target := by
  apply le_iInf
  intro f
  letI : Fintype f.index := FintypeCat.fintype
  intro z hz
  rw [LinearMap.mem_ker]
  apply biproduct_apply_eq_zero_of_components f.map z
  intro t
  exact LinearMap.mem_ker.mp
    (C.witness_le_ker (f.label t)
      (f.map ≫ biproduct.π (fun s ↦ target (f.label s)) t) hz)

end EnumeratedCommonKernelCertificate

def s1RowUCommonKernelCertificate :
    EnumeratedCommonKernelCertificate S1RowTarget (UModule K)
      (s1RowTargetModule K) where
  witness := uSocleLine K
  witness_ne_bot := uSocleLine_ne_bot K
  witness_le_ker := uSocleLine_le_ker_s1Row K

def s1RowXCommonKernelCertificate :
    EnumeratedCommonKernelCertificate S1RowTarget (XModule K)
      (s1RowTargetModule K) where
  witness := xSocleLine K
  witness_ne_bot := xSocleLine_ne_bot K
  witness_le_ker := xSocleLine_le_ker_s1Row K

def s1RowWCommonKernelCertificate :
    EnumeratedCommonKernelCertificate S1RowTarget (WModule K)
      (s1RowTargetModule K) where
  witness := wSocleLine K
  witness_ne_bot := wSocleLine_ne_bot K
  witness_le_ker := wSocleLine_le_ker_s1Row K

def uRowS1CommonKernelCertificate :
    EnumeratedCommonKernelCertificate URowTarget (S1Module K)
      (uRowTargetModule K) where
  witness := s1GeneratorLine K
  witness_ne_bot := s1GeneratorLine_ne_bot K
  witness_le_ker := s1GeneratorLine_le_ker_uRow K

def uRowXCommonKernelCertificate :
    EnumeratedCommonKernelCertificate URowTarget (XModule K)
      (uRowTargetModule K) where
  witness := xSocleLine K
  witness_ne_bot := xSocleLine_ne_bot K
  witness_le_ker := xSocleLine_le_ker_uRow K

def uRowWCommonKernelCertificate :
    EnumeratedCommonKernelCertificate URowTarget (WModule K)
      (uRowTargetModule K) where
  witness := wSocleLine K
  witness_ne_bot := wSocleLine_ne_bot K
  witness_le_ker := wSocleLine_le_ker_uRow K

theorem uSocleLine_le_s1Row_enumeratedReject :
    uSocleLine K ≤ enumeratedReject (UModule K) (s1RowTargetModule K) :=
  (s1RowUCommonKernelCertificate K).witness_le_enumeratedReject

theorem xSocleLine_le_s1Row_enumeratedReject :
    xSocleLine K ≤ enumeratedReject (XModule K) (s1RowTargetModule K) :=
  (s1RowXCommonKernelCertificate K).witness_le_enumeratedReject

theorem wSocleLine_le_s1Row_enumeratedReject :
    wSocleLine K ≤ enumeratedReject (WModule K) (s1RowTargetModule K) :=
  (s1RowWCommonKernelCertificate K).witness_le_enumeratedReject

theorem s1GeneratorLine_le_uRow_enumeratedReject :
    s1GeneratorLine K ≤ enumeratedReject (S1Module K) (uRowTargetModule K) :=
  (uRowS1CommonKernelCertificate K).witness_le_enumeratedReject

theorem xSocleLine_le_uRow_enumeratedReject :
    xSocleLine K ≤ enumeratedReject (XModule K) (uRowTargetModule K) :=
  (uRowXCommonKernelCertificate K).witness_le_enumeratedReject

theorem wSocleLine_le_uRow_enumeratedReject :
    wSocleLine K ≤ enumeratedReject (WModule K) (uRowTargetModule K) :=
  (uRowWCommonKernelCertificate K).witness_le_enumeratedReject

/-! ## Explicit presentations for the two bad outsiders -/

/-- Lower-coordinate inclusion `t ↦ (0,t)`. -/
def lowerInclusion : K →ₗ[K] K × K where
  toFun t := (0, t)
  map_add' := by simp
  map_smul' := by simp

/-- Forget the vertex-two coordinate of `W`; this is a map `W → X`. -/
def wToX : WModule K ⟶ XModule K :=
  homOfComponents K (WData K) (XData K)
    LinearMap.id 0
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem wToX_apply (z : WModule K) :
    (wToX K).hom.hom z = (z.1, 0) := rfl

/-- The complementary map `W → P`, sending `((r,s),t)` to
`((0,r),(0,t))`. -/
def wToP : WModule K ⟶ PModule K :=
  homOfComponents K (WData K) (PData K)
    (jordan K).hom.hom (lowerInclusion K)
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem wToP_apply (z : WModule K) :
    (wToP K).hom.hom z = ((0, z.1.1), (0, z.2)) := rfl

/-- The loop-socle inclusion `S₁ → W`, `q ↦ ((0,q),0)`. -/
def s1ToW : S1Module K ⟶ WModule K :=
  homOfComponents K (S1Data K) (WData K)
    (lowerInclusion K) 0
    (by intro z; rfl)
    (by intro z; rfl)

@[simp] theorem s1ToW_apply (z : S1Module K) :
    (s1ToW K).hom.hom z = ((0, z.1), 0) := rfl

theorem s1ToW_injective : Function.Injective (s1ToW K).hom.hom := by
  intro z z' h
  have hfst := congrArg (fun q : WModule K ↦ q.1.2) h
  change z.1 = z'.1 at hfst
  apply Prod.ext
  · exact hfst
  · exact Subsingleton.elim _ _

theorem s1ToW_mono : Mono (s1ToW K) :=
  (IndecomposableSkeleton.fg_mono_iff_injective (s1ToW K)).mpr
    (s1ToW_injective K)

/-- Named selected targets after adjoining the bad outsider `X`. -/
inductive XBadRowTarget where
  | p
  | s2
  | a
  | x
  deriving DecidableEq

def xBadRowTargetModule : XBadRowTarget → FGModuleCat (B1Model K)
  | .p => PModule K
  | .s2 => S2Module K
  | .a => AModule K
  | .x => XModule K

def xBadPairLabel : FintypeCat.of Bool → XBadRowTarget
  | false => .x
  | true => .p

/-- The explicit two-summand map `W → X ⊕ P`. -/
def wIntoXBadRowSum :
    WModule K ⟶
      biproduct (fun t : FintypeCat.of Bool ↦
        xBadRowTargetModule K (xBadPairLabel t)) :=
  biproduct.lift fun t ↦
    match t with
    | false => wToX K
    | true => wToP K

@[simp] theorem wIntoXBadRowSum_false :
    wIntoXBadRowSum K ≫
        biproduct.π
          (fun t : FintypeCat.of Bool ↦ xBadRowTargetModule K (xBadPairLabel t))
          false =
      wToX K := by
  simp [wIntoXBadRowSum]

@[simp] theorem wIntoXBadRowSum_true :
    wIntoXBadRowSum K ≫
        biproduct.π
          (fun t : FintypeCat.of Bool ↦ xBadRowTargetModule K (xBadPairLabel t))
          true =
      wToP K := by
  simp [wIntoXBadRowSum]

theorem wIntoXBadRowSum_injective :
    Function.Injective (wIntoXBadRowSum K).hom.hom := by
  intro z z' h
  have hxmap : (wToX K).hom.hom z = (wToX K).hom.hom z' := by
    have h' := congrArg
      (fun q ↦
        (biproduct.π
          (fun t : FintypeCat.of Bool ↦ xBadRowTargetModule K (xBadPairLabel t))
          false).hom.hom q) h
    rw [← wIntoXBadRowSum_false K]
    exact h'
  have hpmap : (wToP K).hom.hom z = (wToP K).hom.hom z' := by
    have h' := congrArg
      (fun q ↦
        (biproduct.π
          (fun t : FintypeCat.of Bool ↦ xBadRowTargetModule K (xBadPairLabel t))
          true).hom.hom q) h
    rw [← wIntoXBadRowSum_true K]
    exact h'
  have hV₁ : z.1 = z'.1 := by
    have hcoord := congrArg (fun q : XModule K ↦ q.1) hxmap
    change z.1 = z'.1 at hcoord
    exact hcoord
  have hV₂ : z.2 = z'.2 := by
    have hcoord := congrArg (fun q : PModule K ↦ q.2.2) hpmap
    change z.2 = z'.2 at hcoord
    exact hcoord
  exact Prod.ext hV₁ hV₂

theorem wIntoXBadRowSum_mono : Mono (wIntoXBadRowSum K) :=
  (IndecomposableSkeleton.fg_mono_iff_injective (wIntoXBadRowSum K)).mpr
    (wIntoXBadRowSum_injective K)

/-- Named selected targets after adjoining the bad outsider `W`. -/
inductive WBadRowTarget where
  | p
  | s2
  | a
  | w
  deriving DecidableEq

def wBadRowTargetModule : WBadRowTarget → FGModuleCat (B1Model K)
  | .p => PModule K
  | .s2 => S2Module K
  | .a => AModule K
  | .w => WModule K

def wBadSingletonLabel : FintypeCat.of (Fin 1) → WBadRowTarget := fun _ ↦ .w

/-- The singleton-sum form of the explicit monomorphism `S₁ → W`. -/
def s1IntoWBadRowSum :
    S1Module K ⟶
      biproduct (fun t : FintypeCat.of (Fin 1) ↦
        wBadRowTargetModule K (wBadSingletonLabel t)) :=
  biproduct.lift fun _ ↦ s1ToW K

@[simp] theorem s1IntoWBadRowSum_component :
    s1IntoWBadRowSum K ≫
        biproduct.π
          (fun t : FintypeCat.of (Fin 1) ↦
            wBadRowTargetModule K (wBadSingletonLabel t)) 0 =
      s1ToW K := by
  simp [s1IntoWBadRowSum]

theorem s1IntoWBadRowSum_injective :
    Function.Injective (s1IntoWBadRowSum K).hom.hom := by
  intro z z' h
  apply s1ToW_injective K
  have h' := congrArg
    (fun q ↦
      (biproduct.π
        (fun t : FintypeCat.of (Fin 1) ↦
          wBadRowTargetModule K (wBadSingletonLabel t)) 0).hom.hom q) h
  rw [← s1IntoWBadRowSum_component K]
  exact h'

theorem s1IntoWBadRowSum_mono : Mono (s1IntoWBadRowSum K) :=
  (IndecomposableSkeleton.fg_mono_iff_injective (s1IntoWBadRowSum K)).mpr
    (s1IntoWBadRowSum_injective K)

/-- A named finite-sum submodule presentation, independent of any ambient
indecomposable skeleton. -/
structure EnumeratedSubPresentation
    {R : Type u} [Ring R]
    (I : Type v) (source : FGModuleCat.{w} R)
    (target : I → FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  label : index → I
  map : source ⟶ biproduct fun t ↦ target (label t)
  mono : Mono map

/-- Adding `X` to the named core produces the omitted `W` via the explicit
monomorphism `W → X ⊕ P`. -/
def xBadRowGeneratesW :
    EnumeratedSubPresentation XBadRowTarget (WModule K)
      (xBadRowTargetModule K) where
  index := FintypeCat.of Bool
  label := xBadPairLabel
  map := wIntoXBadRowSum K
  mono := wIntoXBadRowSum_mono K

/-- Adding `W` to the named core produces the omitted `S₁` via the explicit
monomorphism `S₁ → W`. -/
def wBadRowGeneratesS1 :
    EnumeratedSubPresentation WBadRowTarget (S1Module K)
      (wBadRowTargetModule K) where
  index := FintypeCat.of (Fin 1)
  label := wBadSingletonLabel
  map := s1IntoWBadRowSum K
  mono := s1IntoWBadRowSum_mono K

end QuotientSubmoduleEquidistribution.LollipopConcrete.B1.ModuleLayer.SubmoduleRows
