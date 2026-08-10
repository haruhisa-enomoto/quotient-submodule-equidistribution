import Mathlib.Data.BitVec
import Mathlib.Tactic
import Std.Tactic.BVDecide

/-!
# Normalized hookless classification on four vertices

This file isolates the finite combinatorial core of the converse half of
the manuscript's four-support lemma.  A four-vertex support with its unique
projective vertex relabelled as `0` is encoded by an irreducible-edge matrix
and three optional retained translation targets.  The theorem at the end
checks that the translation-quiver restrictions and the two repeated-pair
exclusions force every hookless bad witness into row `F` or row `T`.

The ladder coefficients are eight-bit unsigned vectors.  Only terms zero
through four occur in the certificate; their later adapter to the integral
factor ladder must prove the corresponding no-overflow bounds.  The
certificate is proved by `bv_decide`, which bit-blasts the universal finite
statement and checks the resulting LRAT certificate.
-/

set_option autoImplicit false

namespace OpConjecture.NormalizedFourVertexLadderClassification

/-- The normalized four-element vertex type. -/
abbrev Vertex := Fin 4

/-- Coefficients used for the first four normalized ladder terms. -/
abbrev Coefficient := BitVec 8

/-- A normalized four-vertex edge relation and retained partial
translation.  The edge matrix is row-major.  Translation code `0` means
that the translate is not retained, while codes `1` through `4` name
vertices `0` through `3`; `Axioms` excludes the unused codes.

Vertex `0` is the unique projective vertex and therefore has no translation
field. -/
structure Code where
  edges : BitVec 16
  tauOne : BitVec 3
  tauTwo : BitVec 3
  tauThree : BitVec 3

private def allVertices (f : Vertex → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3

private def anyVertex (f : Vertex → Bool) : Bool :=
  f 0 || f 1 || f 2 || f 3

/-- Decoded irreducible adjacency.  Diagonal bits are deliberately ignored. -/
def edge (C : Code) (x y : Vertex) : Bool :=
  x != y && C.edges.getLsbD (x.val * 4 + y.val)

/-- The three-bit retained-translation code at a vertex. -/
def tauCode (C : Code) (x : Vertex) : BitVec 3 :=
  if x = 1 then C.tauOne else if x = 2 then C.tauTwo else
    if x = 3 then C.tauThree else 0

/-- The retained translate of `x` is `y`. -/
def tauEq (C : Code) (x y : Vertex) : Bool :=
  tauCode C x == BitVec.ofNat 3 (y.val + 1)

/-- The translate of `x` is not retained. -/
def tauNone (C : Code) (x : Vertex) : Bool := tauCode C x == 0

/-- A missing translation code cannot simultaneously name a retained
target. -/
theorem tauEq_eq_false_of_tauNone
    {C : Code} {x : Vertex} (h : tauNone C x = true) (y : Vertex) :
    tauEq C x y = false := by
  fin_cases x <;> fin_cases y <;>
    simp [tauNone, tauEq, tauCode] at h ⊢ <;> bv_decide

/-- `a` is the unique predecessor of `x`. -/
def uniquePredecessor (C : Code) (x a : Vertex) : Bool :=
  allVertices fun y ↦ edge C y x == decide (y = a)

/-- The predecessor set of `x` is exactly `{a,b}`. -/
def exactlyTwoPredecessors (C : Code) (x a b : Vertex) : Bool :=
  a != b && allVertices fun y ↦
    edge C y x == decide (y = a ∨ y = b)

/-- Semantic form of `uniquePredecessor`, used when decoding the finite
certificate back into an AR packet. -/
theorem edge_eq_true_iff_of_uniquePredecessor
    {C : Code} {x a : Vertex} (h : uniquePredecessor C x a = true)
    (y : Vertex) : edge C y x = true ↔ y = a := by
  fin_cases y <;> fin_cases a <;>
    simp [uniquePredecessor, allVertices] at h ⊢ <;> aesop

/-- Semantic form of `exactlyTwoPredecessors`. -/
theorem edge_eq_true_iff_of_exactlyTwoPredecessors
    {C : Code} {x a b : Vertex}
    (h : exactlyTwoPredecessors C x a b = true) (y : Vertex) :
    edge C y x = true ↔ y = a ∨ y = b := by
  fin_cases y <;> fin_cases a <;> fin_cases b <;>
    simp [exactlyTwoPredecessors, allVertices] at h ⊢ <;> aesop

/-- The two named predecessors in an exact two-predecessor certificate are
distinct. -/
theorem ne_of_exactlyTwoPredecessors
    {C : Code} {x a b : Vertex}
    (h : exactlyTwoPredecessors C x a b = true) : a ≠ b := by
  have h' := h
  simp [exactlyTwoPredecessors] at h'
  exact h'.1

/-- Every vertex is reached from the normalized projective root by a path
of length at most three. -/
private def rooted (C : Code) : Bool :=
  allVertices fun x ↦ decide (x = 0) || edge C 0 x ||
    anyVertex (fun a ↦ edge C 0 a && edge C a x) ||
    anyVertex (fun a ↦ anyVertex fun b ↦
      edge C 0 a && edge C a b && edge C b x)

private def tauValid (C : Code) : Bool :=
  allVertices fun x ↦ tauNone C x || anyVertex (tauEq C x)

private def tauInjective (C : Code) : Bool :=
  allVertices fun x ↦ allVertices fun y ↦
    tauNone C x || tauNone C y || tauCode C x != tauCode C y ||
      decide (x = y)

/-- Internal mesh incidence: if `tau y = t`, then `x → y` exactly when
`t → x`. -/
private def mesh (C : Code) : Bool :=
  allVertices fun y ↦ allVertices fun t ↦
    !tauEq C y t || allVertices fun x ↦ edge C x y == edge C t x

/-- The fixed-point half of the local two-cycle lemma. -/
private def twoCycleFixed (C : Code) : Bool :=
  allVertices fun x ↦ allVertices fun y ↦
    !(edge C x y && edge C y x) || tauEq C x x || tauEq C y y

/-- If the projective root is an AR translate, it is noninjective, so the
projective half of the local two-cycle lemma excludes every two-cycle
through it. -/
private def translatedRootNoTwoCycle (C : Code) : Bool :=
  allVertices fun b ↦ !tauEq C b 0 ||
    allVertices fun z ↦ !(edge C 0 z && edge C z 0)

/-- The local translation-quiver assumptions consumed by the finite
classifier. -/
def Axioms (C : Code) : Bool :=
  rooted C && tauValid C && tauInjective C && mesh C &&
    twoCycleFixed C && translatedRootNoTwoCycle C

/-- A specified ordered triple is an admissible hook. -/
def HookAt (C : Code) (a u b : Vertex) : Bool :=
  decide (u ≠ 0) && decide (b ≠ 0) &&
    uniquePredecessor C u a && uniquePredecessor C b u && tauEq C b a

/-- The manuscript hook family is nonempty. -/
def HasHook (C : Code) : Bool :=
  anyVertex fun a ↦ anyVertex fun u ↦ anyVertex fun b ↦
    HookAt C a u b

/-- Semantic fields carried by a successful hook Boolean check. -/
structure HookConditions (C : Code) (a u b : Vertex) : Prop where
  u_ne_zero : u ≠ 0
  b_ne_zero : b ≠ 0
  predecessor_u : uniquePredecessor C u a = true
  predecessor_b : uniquePredecessor C b u = true
  tau_b : tauEq C b a = true

/-- Decode the conjunction in `HookAt`. -/
theorem hookConditions_of_hookAt
    {C : Code} {a u b : Vertex} (h : HookAt C a u b = true) :
    HookConditions C a u b := by
  fin_cases a <;> fin_cases u <;> fin_cases b <;>
    simp [HookAt] at h
  all_goals constructor <;> simp_all

/-- Specified labels realize row `F`. -/
def FixedPacketAt (C : Code) (a c z : Vertex) : Bool :=
  decide (a ≠ 0) && decide (c ≠ 0) && decide (z ≠ 0) &&
    edge C 0 a && edge C c a && uniquePredecessor C z c &&
    exactlyTwoPredecessors C c a z && tauEq C z a && tauEq C c c &&
    (tauEq C a z || tauNone C a) && !edge C 0 z

/-- Row `F` occurs on the normalized support. -/
def HasFixedPacket (C : Code) : Bool :=
  anyVertex fun a ↦ anyVertex fun c ↦ anyVertex fun z ↦
    FixedPacketAt C a c z

/-- Semantic fields carried by a successful row-`F` Boolean check. -/
structure FixedPacketConditions
    (C : Code) (a c z : Vertex) : Prop where
  a_ne_zero : a ≠ 0
  c_ne_zero : c ≠ 0
  z_ne_zero : z ≠ 0
  edge_root_a : edge C 0 a = true
  edge_c_a : edge C c a = true
  predecessor_z : uniquePredecessor C z c = true
  predecessor_c : exactlyTwoPredecessors C c a z = true
  tau_z : tauEq C z a = true
  tau_c : tauEq C c c = true
  tau_a : tauEq C a z = true ∨ tauNone C a = true
  root_not_to_z : edge C 0 z = false

/-- Decode the conjunction in `FixedPacketAt`. -/
theorem fixedPacketConditions_of_fixedPacketAt
    {C : Code} {a c z : Vertex}
    (h : FixedPacketAt C a c z = true) :
    FixedPacketConditions C a c z := by
  fin_cases a <;> fin_cases c <;> fin_cases z <;>
    simp [FixedPacketAt] at h
  all_goals constructor <;> simp_all <;> aesop

/-- Specified labels realize row `T`. -/
def TrianglePacketAt (C : Code) (A₁ A₂ x : Vertex) : Bool :=
  decide (A₁ ≠ 0) && decide (A₂ ≠ 0) && decide (x ≠ 0) &&
    edge C A₁ 0 && uniquePredecessor C A₁ A₂ &&
    exactlyTwoPredecessors C A₂ 0 x && uniquePredecessor C x A₁ &&
    tauEq C A₁ 0 && tauEq C A₂ A₁ && tauNone C x

/-- Row `T` occurs on the normalized support. -/
def HasTrianglePacket (C : Code) : Bool :=
  anyVertex fun A₁ ↦ anyVertex fun A₂ ↦ anyVertex fun x ↦
    TrianglePacketAt C A₁ A₂ x

/-- Semantic fields carried by a successful row-`T` Boolean check. -/
structure TrianglePacketConditions
    (C : Code) (A₁ A₂ x : Vertex) : Prop where
  A₁_ne_zero : A₁ ≠ 0
  A₂_ne_zero : A₂ ≠ 0
  x_ne_zero : x ≠ 0
  edge_A₁_root : edge C A₁ 0 = true
  predecessor_A₁ : uniquePredecessor C A₁ A₂ = true
  predecessor_A₂ : exactlyTwoPredecessors C A₂ 0 x = true
  predecessor_x : uniquePredecessor C x A₁ = true
  tau_A₁ : tauEq C A₁ 0 = true
  tau_A₂ : tauEq C A₂ A₁ = true
  tau_x : tauNone C x = true

/-- Decode the conjunction in `TrianglePacketAt`. -/
theorem trianglePacketConditions_of_trianglePacketAt
    {C : Code} {A₁ A₂ x : Vertex}
    (h : TrianglePacketAt C A₁ A₂ x = true) :
    TrianglePacketConditions C A₁ A₂ x := by
  fin_cases A₁ <;> fin_cases A₂ <;> fin_cases x <;>
    simp [TrianglePacketAt] at h
  all_goals constructor <;> simp_all

/-- Extract the labelled hook occurrence certified by `HasHook`. -/
theorem exists_hookAt_of_hasHook (C : Code) (h : HasHook C = true) :
    ∃ a u b, HookAt C a u b = true := by
  by_contra hn
  push Not at hn
  have hfalse : ∀ a u b, HookAt C a u b = false := by
    intro a u b
    cases hab : HookAt C a u b
    · rfl
    · exact (hn a u b hab).elim
  simp [HasHook, anyVertex, hfalse] at h

/-- Extract the labelled row-`F` occurrence certified by
`HasFixedPacket`. -/
theorem exists_fixedPacketAt_of_hasFixedPacket
    (C : Code) (h : HasFixedPacket C = true) :
    ∃ a c z, FixedPacketAt C a c z = true := by
  by_contra hn
  push Not at hn
  have hfalse : ∀ a c z, FixedPacketAt C a c z = false := by
    intro a c z
    cases hacz : FixedPacketAt C a c z
    · rfl
    · exact (hn a c z hacz).elim
  simp [HasFixedPacket, anyVertex, hfalse] at h

/-- Extract the labelled row-`T` occurrence certified by
`HasTrianglePacket`. -/
theorem exists_trianglePacketAt_of_hasTrianglePacket
    (C : Code) (h : HasTrianglePacket C = true) :
    ∃ A₁ A₂ x, TrianglePacketAt C A₁ A₂ x = true := by
  by_contra hn
  push Not at hn
  have hfalse : ∀ A₁ A₂ x, TrianglePacketAt C A₁ A₂ x = false := by
    intro A₁ A₂ x
    cases hA : TrianglePacketAt C A₁ A₂ x
    · rfl
    · exact (hn A₁ A₂ x hA).elim
  simp [HasTrianglePacket, anyVertex, hfalse] at h

private structure Vector where
  c0 : Coefficient
  c1 : Coefficient
  c2 : Coefficient
  c3 : Coefficient

private def Vector.coordinate (v : Vector) (x : Vertex) : Coefficient :=
  if x = 0 then v.c0 else if x = 1 then v.c1 else
    if x = 2 then v.c2 else v.c3

private def vectorOf (f : Vertex → Coefficient) : Vector :=
  ⟨f 0, f 1, f 2, f 3⟩

private def basis (x : Vertex) : Vector :=
  vectorOf fun y ↦ if y = x then 1 else 0

private def mask (b : Bool) (n : Coefficient) : Coefficient :=
  if b then n else 0

private def theta (C : Code) (v : Vector) : Vector := vectorOf fun y ↦
  mask (edge C y 0) (v.coordinate 0) +
  mask (edge C y 1) (v.coordinate 1) +
  mask (edge C y 2) (v.coordinate 2) +
  mask (edge C y 3) (v.coordinate 3)

private def tauVector (C : Code) (v : Vector) : Vector := vectorOf fun y ↦
  mask (tauEq C 0 y) (v.coordinate 0) +
  mask (tauEq C 1 y) (v.coordinate 1) +
  mask (tauEq C 2 y) (v.coordinate 2) +
  mask (tauEq C 3 y) (v.coordinate 3)

/-- Unsigned saturating subtraction.  The complement form avoids a
primitive unsupported by the bit-vector reflector. -/
private def saturatingSubtraction
    (a b : Coefficient) : Coefficient :=
  if a < b then 0 else a + ~~~b + 1

private def step (C : Code) (next previous : Vector) : Vector :=
  let a := theta C next
  let b := tauVector C previous
  ⟨saturatingSubtraction a.c0 b.c0,
    saturatingSubtraction a.c1 b.c1,
    saturatingSubtraction a.c2 b.c2,
    saturatingSubtraction a.c3 b.c3⟩

private def ladderZero (x : Vertex) := basis x
private def ladderOne (C : Code) (x : Vertex) := theta C (ladderZero x)
private def ladderTwo (C : Code) (x : Vertex) :=
  step C (ladderOne C x) (ladderZero x)
private def ladderThree (C : Code) (x : Vertex) :=
  step C (ladderTwo C x) (ladderOne C x)
private def ladderFour (C : Code) (x : Vertex) :=
  step C (ladderThree C x) (ladderTwo C x)

/-- Natural-number coefficient of the zeroth normalized ladder term. -/
def ladderCoefficientZero (x y : Vertex) : ℕ :=
  (ladderZero x).coordinate y |>.toNat

/-- Natural-number coefficient of the first normalized ladder term. -/
def ladderCoefficientOne (C : Code) (x y : Vertex) : ℕ :=
  (ladderOne C x).coordinate y |>.toNat

/-- Natural-number coefficient of the second normalized ladder term. -/
def ladderCoefficientTwo (C : Code) (x y : Vertex) : ℕ :=
  (ladderTwo C x).coordinate y |>.toNat

/-- Natural-number coefficient of the third normalized ladder term. -/
def ladderCoefficientThree (C : Code) (x y : Vertex) : ℕ :=
  (ladderThree C x).coordinate y |>.toNat

/-- Natural-number coefficient of the fourth normalized ladder term. -/
def ladderCoefficientFour (C : Code) (x y : Vertex) : ℕ :=
  (ladderFour C x).coordinate y |>.toNat

/-- Unbounded natural-number vectors used to state the exact semantics of
the first five bit-vector ladder terms. -/
abbrev NatVector := Vertex → ℕ

/-- Natural-number version of the Boolean coefficient mask. -/
def natMask (b : Bool) (n : ℕ) : ℕ :=
  if b then n else 0

/-- Unbounded adjacency operator underlying the normalized ladder. -/
def naturalTheta (C : Code) (v : NatVector) : NatVector := fun y ↦
  natMask (edge C y 0) (v 0) +
  natMask (edge C y 1) (v 1) +
  natMask (edge C y 2) (v 2) +
  natMask (edge C y 3) (v 3)

/-- Unbounded partial-translation operator underlying the normalized ladder. -/
def naturalTauVector (C : Code) (v : NatVector) : NatVector := fun y ↦
  natMask (tauEq C 0 y) (v 0) +
  natMask (tauEq C 1 y) (v 1) +
  natMask (tauEq C 2 y) (v 2) +
  natMask (tauEq C 3 y) (v 3)

/-- Unbounded positive-part recurrence step. -/
def naturalStep
    (C : Code) (next previous : NatVector) : NatVector := fun y ↦
  naturalTheta C next y - naturalTauVector C previous y

/-- Unbounded natural semantics of the zeroth normalized ladder term. -/
def naturalLadderZero (x : Vertex) : NatVector :=
  fun y ↦ if y = x then 1 else 0

/-- Unbounded natural semantics of the first normalized ladder term. -/
def naturalLadderOne (C : Code) (x : Vertex) : NatVector :=
  naturalTheta C (naturalLadderZero x)

/-- Unbounded natural semantics of the second normalized ladder term. -/
def naturalLadderTwo (C : Code) (x : Vertex) : NatVector :=
  naturalStep C (naturalLadderOne C x) (naturalLadderZero x)

/-- Unbounded natural semantics of the third normalized ladder term. -/
def naturalLadderThree (C : Code) (x : Vertex) : NatVector :=
  naturalStep C (naturalLadderTwo C x) (naturalLadderOne C x)

/-- Unbounded natural semantics of the fourth normalized ladder term. -/
def naturalLadderFour (C : Code) (x : Vertex) : NatVector :=
  naturalStep C (naturalLadderThree C x) (naturalLadderTwo C x)

private theorem saturatingSubtraction_toNat
    (a b : Coefficient) :
    (saturatingSubtraction a b).toNat = a.toNat - b.toNat := by
  rw [saturatingSubtraction]
  split
  next hlt =>
    have hlt' : a.toNat < b.toNat := BitVec.lt_def.mp hlt
    simp [Nat.sub_eq_zero_of_le hlt'.le]
  next hnlt =>
    have hle : b.toNat ≤ a.toNat := by
      rw [BitVec.lt_def] at hnlt
      omega
    have ha : a.toNat < 256 := a.toFin.isLt
    have heq : a + ~~~b + 1 = a - b := by
      have hneg : (~~~b + 1 : Coefficient) = -b :=
        (BitVec.neg_eq_not_add b).symm
      rw [add_assoc, hneg, BitVec.sub_eq_add_neg]
    rw [heq, BitVec.toNat_sub]
    norm_num
    have hcalc : 256 - b.toNat + a.toNat =
        256 + (a.toNat - b.toNat) := by omega
    rw [hcalc]
    have hd : a.toNat - b.toNat < 256 := by omega
    simp [Nat.mod_eq_of_lt hd]

private theorem mask_toNat (b : Bool) (n : Coefficient) :
    (mask b n).toNat = natMask b n.toNat := by
  cases b <;> simp [mask, natMask]

private theorem addFour_toNat
    (a b c d : Coefficient)
    (h : a.toNat + b.toNat + c.toNat + d.toNat < 256) :
    (a + b + c + d).toNat =
      a.toNat + b.toNat + c.toNat + d.toNat := by
  simp only [BitVec.toNat_add]
  have hab : a.toNat + b.toNat < 256 := by omega
  have habc : a.toNat + b.toNat + c.toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt habc,
    Nat.mod_eq_of_lt h]

private theorem addFourMask_toNat
    (ba bb bc bd : Bool) (a b c d : Coefficient)
    (h : natMask ba a.toNat + natMask bb b.toNat +
      natMask bc c.toNat + natMask bd d.toNat < 256) :
    (mask ba a + mask bb b + mask bc c + mask bd d).toNat =
      natMask ba a.toNat + natMask bb b.toNat +
        natMask bc c.toNat + natMask bd d.toNat := by
  have hadd := addFour_toNat
    (mask ba a) (mask bb b) (mask bc c) (mask bd d) (by
      simpa [mask_toNat] using h)
  simpa [mask_toNat] using hadd

private theorem vectorOf_coordinate
    (f : Vertex → Coefficient) (x : Vertex) :
    (vectorOf f).coordinate x = f x := by
  fin_cases x <;> rfl

private def EncodesNatural (v : Vector) (w : NatVector) : Prop :=
  ∀ y, (v.coordinate y).toNat = w y

private def NatBounded (v : NatVector) (M : ℕ) : Prop :=
  ∀ y, v y ≤ M

private theorem natMask_le (b : Bool) {n M : ℕ} (h : n ≤ M) :
    natMask b n ≤ M := by
  cases b <;> simp [natMask, h]

private theorem theta_encodesNatural
    (C : Code) {v : Vector} {w : NatVector}
    (hencode : EncodesNatural v w) {M : ℕ} (hbound : NatBounded w M)
    (hwidth : 4 * M < 256) :
    EncodesNatural (theta C v) (naturalTheta C w) := by
  intro y
  simp only [theta, vectorOf_coordinate, naturalTheta]
  have h0 := natMask_le (edge C y 0) (hbound 0)
  have h1 := natMask_le (edge C y 1) (hbound 1)
  have h2 := natMask_le (edge C y 2) (hbound 2)
  have h3 := natMask_le (edge C y 3) (hbound 3)
  have hadd := addFourMask_toNat
    (edge C y 0) (edge C y 1) (edge C y 2) (edge C y 3)
    (v.coordinate 0) (v.coordinate 1) (v.coordinate 2) (v.coordinate 3)
    (by rw [hencode 0, hencode 1, hencode 2, hencode 3]; omega)
  simpa [hencode 0, hencode 1, hencode 2, hencode 3] using hadd

private theorem tauVector_encodesNatural
    (C : Code) {v : Vector} {w : NatVector}
    (hencode : EncodesNatural v w) {M : ℕ} (hbound : NatBounded w M)
    (hwidth : 4 * M < 256) :
    EncodesNatural (tauVector C v) (naturalTauVector C w) := by
  intro y
  simp only [tauVector, vectorOf_coordinate, naturalTauVector]
  have h0 := natMask_le (tauEq C 0 y) (hbound 0)
  have h1 := natMask_le (tauEq C 1 y) (hbound 1)
  have h2 := natMask_le (tauEq C 2 y) (hbound 2)
  have h3 := natMask_le (tauEq C 3 y) (hbound 3)
  have hadd := addFourMask_toNat
    (tauEq C 0 y) (tauEq C 1 y) (tauEq C 2 y) (tauEq C 3 y)
    (v.coordinate 0) (v.coordinate 1) (v.coordinate 2) (v.coordinate 3)
    (by rw [hencode 0, hencode 1, hencode 2, hencode 3]; omega)
  simpa [hencode 0, hencode 1, hencode 2, hencode 3] using hadd

private theorem step_encodesNatural
    (C : Code) {next previous : Vector}
    {nextN previousN : NatVector}
    (hnext : EncodesNatural next nextN)
    (hprevious : EncodesNatural previous previousN)
    {M N : ℕ} (hnextBound : NatBounded nextN M)
    (hpreviousBound : NatBounded previousN N)
    (hnextWidth : 4 * M < 256) (hpreviousWidth : 4 * N < 256) :
    EncodesNatural (step C next previous)
      (naturalStep C nextN previousN) := by
  have htheta := theta_encodesNatural C hnext hnextBound hnextWidth
  have htau := tauVector_encodesNatural C hprevious
    hpreviousBound hpreviousWidth
  intro y
  have hs := saturatingSubtraction_toNat
    ((theta C next).coordinate y)
    ((tauVector C previous).coordinate y)
  rw [htheta y, htau y] at hs
  fin_cases y <;> simpa [step, naturalStep, Vector.coordinate] using hs

private theorem naturalTheta_bounded
    (C : Code) {v : NatVector} {M : ℕ}
    (h : NatBounded v M) : NatBounded (naturalTheta C v) (4 * M) := by
  intro y
  have h0 := natMask_le (edge C y 0) (h 0)
  have h1 := natMask_le (edge C y 1) (h 1)
  have h2 := natMask_le (edge C y 2) (h 2)
  have h3 := natMask_le (edge C y 3) (h 3)
  simp only [naturalTheta]
  omega

private theorem naturalStep_bounded
    (C : Code) {next previous : NatVector} {M : ℕ}
    (h : NatBounded next M) :
    NatBounded (naturalStep C next previous) (4 * M) := by
  intro y
  exact (Nat.sub_le _ _).trans (naturalTheta_bounded C h y)

private theorem basis_encodesNatural (x : Vertex) :
    EncodesNatural (basis x) (naturalLadderZero x) := by
  intro y
  by_cases h : y = x <;> simp [basis, naturalLadderZero, h,
    vectorOf_coordinate]

private theorem naturalLadderZero_bounded (x : Vertex) :
    NatBounded (naturalLadderZero x) 1 := by
  intro y
  by_cases h : y = x <;> simp [naturalLadderZero, h]

private theorem naturalLadderOne_bounded (C : Code) (x : Vertex) :
    NatBounded (naturalLadderOne C x) 1 := by
  intro y
  fin_cases x <;>
    simp [naturalLadderOne, naturalTheta, naturalLadderZero, natMask] <;>
    split <;> simp_all

private theorem naturalLadderTwo_bounded (C : Code) (x : Vertex) :
    NatBounded (naturalLadderTwo C x) 4 := by
  simpa [naturalLadderTwo] using
    naturalStep_bounded C (naturalLadderOne_bounded C x)

private theorem naturalLadderThree_bounded (C : Code) (x : Vertex) :
    NatBounded (naturalLadderThree C x) 16 := by
  simpa [naturalLadderThree] using
    naturalStep_bounded C (naturalLadderTwo_bounded C x)

private theorem ladderZero_encodesNatural (x : Vertex) :
    EncodesNatural (ladderZero x) (naturalLadderZero x) := by
  simpa [ladderZero] using basis_encodesNatural x

private theorem ladderOne_encodesNatural (C : Code) (x : Vertex) :
    EncodesNatural (ladderOne C x) (naturalLadderOne C x) := by
  apply theta_encodesNatural C (ladderZero_encodesNatural x)
    (naturalLadderZero_bounded x)
  norm_num

private theorem ladderTwo_encodesNatural (C : Code) (x : Vertex) :
    EncodesNatural (ladderTwo C x) (naturalLadderTwo C x) := by
  apply step_encodesNatural C
    (ladderOne_encodesNatural C x) (ladderZero_encodesNatural x)
    (naturalLadderOne_bounded C x) (naturalLadderZero_bounded x) <;>
      norm_num

private theorem ladderThree_encodesNatural (C : Code) (x : Vertex) :
    EncodesNatural (ladderThree C x) (naturalLadderThree C x) := by
  apply step_encodesNatural C
    (ladderTwo_encodesNatural C x) (ladderOne_encodesNatural C x)
    (naturalLadderTwo_bounded C x) (naturalLadderOne_bounded C x) <;>
      norm_num

private theorem ladderFour_encodesNatural (C : Code) (x : Vertex) :
    EncodesNatural (ladderFour C x) (naturalLadderFour C x) := by
  apply step_encodesNatural C
    (ladderThree_encodesNatural C x) (ladderTwo_encodesNatural C x)
    (naturalLadderThree_bounded C x) (naturalLadderTwo_bounded C x) <;>
      norm_num

/-- The eight-bit implementation exactly represents the unbounded zeroth
ladder term. -/
theorem ladderCoefficientZero_eq_natural (x y : Vertex) :
    ladderCoefficientZero x y = naturalLadderZero x y :=
  ladderZero_encodesNatural x y

/-- The eight-bit implementation exactly represents the unbounded first
ladder term. -/
theorem ladderCoefficientOne_eq_natural
    (C : Code) (x y : Vertex) :
    ladderCoefficientOne C x y = naturalLadderOne C x y :=
  ladderOne_encodesNatural C x y

/-- The eight-bit implementation exactly represents the unbounded second
ladder term. -/
theorem ladderCoefficientTwo_eq_natural
    (C : Code) (x y : Vertex) :
    ladderCoefficientTwo C x y = naturalLadderTwo C x y :=
  ladderTwo_encodesNatural C x y

/-- The eight-bit implementation exactly represents the unbounded third
ladder term. -/
theorem ladderCoefficientThree_eq_natural
    (C : Code) (x y : Vertex) :
    ladderCoefficientThree C x y = naturalLadderThree C x y :=
  ladderThree_encodesNatural C x y

/-- The eight-bit implementation exactly represents the unbounded fourth
ladder term. -/
theorem ladderCoefficientFour_eq_natural
    (C : Code) (x y : Vertex) :
    ladderCoefficientFour C x y = naturalLadderFour C x y :=
  ladderFour_encodesNatural C x y

private def vectorsEqual (v w : Vector) : Bool :=
  v.c0 == w.c0 && v.c1 == w.c1 && v.c2 == w.c2 && v.c3 == w.c3

private def avoidsRootThroughFour (C : Code) (x : Vertex) : Bool :=
  (ladderZero x).c0 == 0 && (ladderOne C x).c0 == 0 &&
    (ladderTwo C x).c0 == 0 && (ladderThree C x).c0 == 0 &&
    (ladderFour C x).c0 == 0

/-- The only repeated ordered pairs invoked in the manuscript's
four-vertex case split are the shifts `0 → 2` and `0 → 3`. -/
private def requiredPairsDoNotRepeat (C : Code) (x : Vertex) : Bool :=
  !(vectorsEqual (ladderZero x) (ladderTwo C x) &&
      vectorsEqual (ladderOne C x) (ladderThree C x)) &&
    !(vectorsEqual (ladderZero x) (ladderThree C x) &&
      vectorsEqual (ladderOne C x) (ladderFour C x))

/-- The finite fragment supplied by a terminating ladder which avoids its
unique projective root. -/
def Witness (C : Code) (x : Vertex) : Bool :=
  decide (x ≠ 0) && avoidsRootThroughFour C x &&
    requiredPairsDoNotRepeat C x

/-- Universal Boolean form of the normalized hookless classification.
This is the finite certificate checked by `bv_decide`. -/
private theorem classifier : ∀ C : Code,
    allVertices (fun x ↦
      !Axioms C || HasHook C || !Witness C x ||
        HasFixedPacket C || HasTrianglePacket C) = true := by
  intro C
  simp only [Axioms, HasHook, Witness, HasFixedPacket, HasTrianglePacket,
    HookAt, FixedPacketAt, TrianglePacketAt, rooted, tauValid, tauInjective, mesh,
    twoCycleFixed, translatedRootNoTwoCycle, avoidsRootThroughFour,
    requiredPairsDoNotRepeat, vectorsEqual, uniquePredecessor,
    exactlyTwoPredecessors, ladderZero, ladderOne, ladderTwo, ladderThree,
    ladderFour, step, theta, tauVector, saturatingSubtraction, basis,
    vectorOf, Vector.coordinate, mask, edge, tauEq, tauNone, tauCode,
    allVertices, anyVertex]
  simp
  bv_decide

/-- On a normalized support satisfying the local AR restrictions, every
hookless terminating witness has exactly one of the two possible packet
shapes (disjointness is proved separately in the actual AR adapter). -/
theorem fixed_or_triangle_of_axioms_of_hookless_of_witness
    (C : Code) (x : Vertex)
    (hAxioms : Axioms C = true)
    (hHookless : HasHook C = false)
    (hWitness : Witness C x = true) :
    HasFixedPacket C = true ∨ HasTrianglePacket C = true := by
  have h := classifier C
  have hx :
      (!Axioms C || HasHook C || !Witness C x ||
        HasFixedPacket C || HasTrianglePacket C) = true := by
    fin_cases x <;> simp [allVertices] at h ⊢ <;> aesop
  simpa [hAxioms, hHookless, hWitness] using hx

/-! ## Uniqueness of the projective root

Before choosing the unique-root normalization, an actual rooted support may
a priori contain further projective vertices.  The following second finite
certificate isolates the first paragraph of the manuscript's four-vertex
argument: a hookless ladder which avoids every projective boundary vertex
forces the chosen root to be the only projective. -/

/-- Three bits recording whether vertices `1`, `2`, and `3` are additional
projective boundary vertices.  Vertex `0` is always the chosen projective
root. -/
abbrev AdditionalBoundary := BitVec 3

/-- Membership in the projective boundary before uniqueness is known. -/
def boundaryAt (B : AdditionalBoundary) (x : Vertex) : Bool :=
  if x = 0 then true else if x = 1 then B.getLsbD 0 else
    if x = 2 then B.getLsbD 1 else B.getLsbD 2

/-- Every vertex is reached in at most three steps from some projective
boundary vertex. -/
def reachableWithinThree (C : Code) (p x : Vertex) : Bool :=
  decide (p = x) || edge C p x ||
    anyVertex (fun a ↦ edge C p a && edge C a x) ||
    anyVertex (fun a ↦ anyVertex fun b ↦
      edge C p a && edge C a b && edge C b x)

private def rootedFromBoundary (C : Code) (B : AdditionalBoundary) : Bool :=
  allVertices fun x ↦ anyVertex fun p ↦
    boundaryAt B p && reachableWithinThree C p x

/-- On four loopless vertices, appending an edge to a path of length at most
three can always be shortened back to length at most three. -/
private theorem reachableWithinThree_tail_classifier : ∀ C : Code,
    ∀ p a b : Vertex,
      !reachableWithinThree C p a || !edge C a b ||
        reachableWithinThree C p b = true := by
  intro C p a b
  fin_cases p <;> fin_cases a <;> fin_cases b <;>
    simp only [reachableWithinThree, edge, anyVertex] <;>
      simp <;> bv_decide

/-- Semantic closure of the explicit length-at-most-three reachability
predicate. -/
theorem reachableWithinThree_of_reflTransGen
    (C : Code) {p x : Vertex}
    (h : Relation.ReflTransGen
      (fun a b ↦ edge C a b = true) p x) :
    reachableWithinThree C p x = true := by
  induction h with
  | refl => simp [reachableWithinThree]
  | @tail a b _ hab ih =>
      have hfinite := reachableWithinThree_tail_classifier C p a b
      simpa [ih, hab] using hfinite

/-- Rooted reachability in the semantic reflexive-transitive closure implies
the Boolean four-vertex rootedness check. -/
theorem rootedFromBoundary_eq_true_of_reflTransGen
    (C : Code) (B : AdditionalBoundary)
    (hroot : ∀ x, ∃ p, boundaryAt B p = true ∧
      Relation.ReflTransGen (fun a b ↦ edge C a b = true) p x) :
    rootedFromBoundary C B = true := by
  have hx : ∀ x, (anyVertex fun p ↦
      boundaryAt B p && reachableWithinThree C p x) = true := by
    intro x
    rcases hroot x with ⟨p, hp, hpx⟩
    have hr := reachableWithinThree_of_reflTransGen C hpx
    fin_cases p <;>
      simp only [anyVertex, Bool.or_eq_true, Bool.and_eq_true] <;> aesop
  simp [rootedFromBoundary, allVertices, hx]

/-- Projective vertices have no ordinary AR translate. -/
private def boundaryHasNoTau (C : Code) (B : AdditionalBoundary) : Bool :=
  allVertices fun x ↦ !boundaryAt B x || tauNone C x

/-- If a projective boundary vertex is a retained translate, then the local
projective two-cycle restriction excludes every opposite-arrow pair through
it. -/
private def translatedBoundaryNoTwoCycle
    (C : Code) (B : AdditionalBoundary) : Bool :=
  allVertices fun p ↦ !boundaryAt B p ||
    !(anyVertex fun b ↦ tauEq C b p) ||
      allVertices fun z ↦ !(edge C p z && edge C z p)

/-- Local AR restrictions used before projective-root uniqueness is known. -/
def BoundaryAxioms (C : Code) (B : AdditionalBoundary) : Bool :=
  rootedFromBoundary C B && boundaryHasNoTau C B &&
    tauValid C && tauInjective C && mesh C && twoCycleFixed C &&
      translatedBoundaryNoTwoCycle C B

/-- Semantic local translation-quiver conditions which imply the Boolean
pre-normalization axiom check. -/
structure BoundaryAxiomConditions
    (C : Code) (B : AdditionalBoundary) : Prop where
  rooted : ∀ x, ∃ p, boundaryAt B p = true ∧
    Relation.ReflTransGen (fun a b ↦ edge C a b = true) p x
  boundary_no_tau : ∀ x, boundaryAt B x = true → tauNone C x = true
  tau_valid : ∀ x, tauNone C x = true ∨ ∃ y, tauEq C x y = true
  tau_injective : ∀ x y,
    tauNone C x = true ∨ tauNone C y = true ∨
      tauCode C x ≠ tauCode C y ∨ x = y
  mesh_incidence : ∀ y t x, tauEq C y t = true →
    (edge C x y = true ↔ edge C t x = true)
  two_cycle_fixed : ∀ x y,
    edge C x y = true → edge C y x = true →
      tauEq C x x = true ∨ tauEq C y y = true
  translated_boundary_no_two_cycle : ∀ p,
    boundaryAt B p = true → (∃ b, tauEq C b p = true) →
      ∀ z, edge C p z = false ∨ edge C z p = false

/-- Assemble the Boolean boundary axioms from their semantic form. -/
theorem boundaryAxioms_eq_true_of_conditions
    {C : Code} {B : AdditionalBoundary}
    (H : BoundaryAxiomConditions C B) : BoundaryAxioms C B = true := by
  have hroot : rootedFromBoundary C B = true :=
    rootedFromBoundary_eq_true_of_reflTransGen C B H.rooted
  have hboundary : boundaryHasNoTau C B = true := by
    have hx : ∀ x, (!boundaryAt B x || tauNone C x) = true := by
      intro x
      cases hb : boundaryAt B x
      · rfl
      · exact H.boundary_no_tau x hb
    simp only [boundaryHasNoTau, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨hx 0, hx 1⟩, hx 2⟩, hx 3⟩
  have hvalid : tauValid C = true := by
    have hx : ∀ x, (tauNone C x || anyVertex (tauEq C x)) = true := by
      intro x
      rcases H.tau_valid x with hnone | ⟨y, hy⟩
      · rw [hnone]
        rfl
      · fin_cases y <;>
          simp only [anyVertex, Bool.or_eq_true] <;> aesop
    simp only [tauValid, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨hx 0, hx 1⟩, hx 2⟩, hx 3⟩
  have hinjective : tauInjective C = true := by
    have hxy : ∀ x y,
        (tauNone C x || tauNone C y ||
          tauCode C x != tauCode C y || decide (x = y)) = true := by
      intro x y
      rcases H.tau_injective x y with
        hnone | hnone | hne | heq
      · rw [hnone]
        rfl
      · rw [hnone]
        simp
      · simp [hne]
      · subst y
        simp
    have row : ∀ x, (allVertices fun y ↦
        tauNone C x || tauNone C y ||
          tauCode C x != tauCode C y || decide (x = y)) = true := by
      intro x
      simp only [allVertices, Bool.and_eq_true]
      exact ⟨⟨⟨hxy x 0, hxy x 1⟩, hxy x 2⟩, hxy x 3⟩
    simp only [tauInjective, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨(by simpa only [allVertices, Bool.and_eq_true] using row 0),
      (by simpa only [allVertices, Bool.and_eq_true] using row 1)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using row 2)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using row 3)⟩
  have hmesh : mesh C = true := by
    have hytx : ∀ y t x,
        (!tauEq C y t || (edge C x y == edge C t x)) = true := by
      intro y t x
      cases ht : tauEq C y t
      · rfl
      · have hi := H.mesh_incidence y t x ht
        cases hxy : edge C x y <;> cases htx : edge C t x <;>
          simp_all
    have rowX : ∀ y t, (allVertices fun x ↦
        !tauEq C y t || (edge C x y == edge C t x)) = true := by
      intro y t
      simp only [allVertices, Bool.and_eq_true]
      exact ⟨⟨⟨hytx y t 0, hytx y t 1⟩, hytx y t 2⟩, hytx y t 3⟩
    have hyt : ∀ y t,
        (!tauEq C y t || allVertices fun x ↦
          edge C x y == edge C t x) = true := by
      intro y t
      cases ht : tauEq C y t
      · rfl
      · simpa only [ht, Bool.not_true, Bool.false_or] using rowX y t
    have rowT : ∀ y, (allVertices fun t ↦
        !tauEq C y t || allVertices fun x ↦
          edge C x y == edge C t x) = true := by
      intro y
      simp only [allVertices, Bool.and_eq_true]
      exact ⟨⟨⟨hyt y 0, hyt y 1⟩, hyt y 2⟩, hyt y 3⟩
    simp only [mesh, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨(by simpa only [allVertices, Bool.and_eq_true] using rowT 0),
      (by simpa only [allVertices, Bool.and_eq_true] using rowT 1)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using rowT 2)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using rowT 3)⟩
  have hcycle : twoCycleFixed C = true := by
    have hxy : ∀ x y,
        (!(edge C x y && edge C y x) ||
          tauEq C x x || tauEq C y y) = true := by
      intro x y
      cases hxy : edge C x y
      · rfl
      · cases hyx : edge C y x
        · rfl
        · rcases H.two_cycle_fixed x y hxy hyx with h | h
          · rw [h]
            simp
          · rw [h]
            simp
    have row : ∀ x, (allVertices fun y ↦
        !(edge C x y && edge C y x) ||
          tauEq C x x || tauEq C y y) = true := by
      intro x
      simp only [allVertices, Bool.and_eq_true]
      exact ⟨⟨⟨hxy x 0, hxy x 1⟩, hxy x 2⟩, hxy x 3⟩
    simp only [twoCycleFixed, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨(by simpa only [allVertices, Bool.and_eq_true] using row 0),
      (by simpa only [allVertices, Bool.and_eq_true] using row 1)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using row 2)⟩,
      (by simpa only [allVertices, Bool.and_eq_true] using row 3)⟩
  have htranslated : translatedBoundaryNoTwoCycle C B = true := by
    have hp : ∀ p,
        (!boundaryAt B p || !(anyVertex fun b ↦ tauEq C b p) ||
          allVertices fun z ↦ !(edge C p z && edge C z p)) = true := by
      intro p
      cases hbp : boundaryAt B p
      · rfl
      · by_cases hex : ∃ b, tauEq C b p = true
        · have ht : (anyVertex fun b ↦ tauEq C b p) = true := by
            rcases hex with ⟨b, hb⟩
            fin_cases b <;>
              simp only [anyVertex, Bool.or_eq_true] <;> aesop
          have hz : ∀ z,
              Bool.not (edge C p z && edge C z p) = true := by
            intro z
            rcases H.translated_boundary_no_two_cycle p hbp hex z with h | h
            · rw [h]
              rfl
            · rw [h]
              simp
          have hall : (allVertices fun z ↦
              !(edge C p z && edge C z p)) = true := by
            simp only [allVertices, Bool.and_eq_true]
            exact ⟨⟨⟨hz 0, hz 1⟩, hz 2⟩, hz 3⟩
          rw [ht, hall]
          rfl
        · have hnone : ∀ b, tauEq C b p = false := by
            intro b
            cases hb : tauEq C b p
            · rfl
            · exact (hex ⟨b, hb⟩).elim
          have ht : (anyVertex fun b ↦ tauEq C b p) = false := by
            simp [anyVertex, hnone]
          rw [ht]
          rfl
    simp only [translatedBoundaryNoTwoCycle, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨hp 0, hp 1⟩, hp 2⟩, hp 3⟩
  simp [BoundaryAxioms, hroot, hboundary, hvalid, hinjective, hmesh,
    hcycle, htranslated]

/-- A hook whose last two vertices are nonprojective for the current
boundary mask. -/
def BoundaryHookAt (C : Code) (B : AdditionalBoundary)
    (a u b : Vertex) : Bool :=
  !boundaryAt B u && !boundaryAt B b &&
    uniquePredecessor C u a && uniquePredecessor C b u && tauEq C b a

/-- Semantic fields carried by a successful pre-normalization hook check. -/
structure BoundaryHookConditions
    (C : Code) (B : AdditionalBoundary) (a u b : Vertex) : Prop where
  u_not_boundary : boundaryAt B u = false
  b_not_boundary : boundaryAt B b = false
  predecessor_u : uniquePredecessor C u a = true
  predecessor_b : uniquePredecessor C b u = true
  tau_b : tauEq C b a = true

/-- Decode the conjunction in `BoundaryHookAt`. -/
theorem boundaryHookConditions_of_boundaryHookAt
    {C : Code} {B : AdditionalBoundary} {a u b : Vertex}
    (h : BoundaryHookAt C B a u b = true) :
    BoundaryHookConditions C B a u b := by
  simp only [BoundaryHookAt, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hu, hb⟩, hpu⟩, hpb⟩, ht⟩
  have hu' : boundaryAt B u = false := by
    cases hbu : boundaryAt B u <;> simp_all
  have hb' : boundaryAt B b = false := by
    cases hbb : boundaryAt B b <;> simp_all
  exact ⟨hu', hb', hpu, hpb, ht⟩

/-- The pre-normalization hook family is nonempty. -/
def HasBoundaryHook (C : Code) (B : AdditionalBoundary) : Bool :=
  anyVertex fun a ↦ anyVertex fun u ↦ anyVertex fun b ↦
    BoundaryHookAt C B a u b

/-- Extract the labelled pre-normalization hook certified by
`HasBoundaryHook`. -/
theorem exists_boundaryHookAt_of_hasBoundaryHook
    (C : Code) (B : AdditionalBoundary)
    (h : HasBoundaryHook C B = true) :
    ∃ a u b, BoundaryHookAt C B a u b = true := by
  by_contra hn
  push Not at hn
  have hfalse : ∀ a u b, BoundaryHookAt C B a u b = false := by
    intro a u b
    cases haub : BoundaryHookAt C B a u b
    · rfl
    · exact (hn a u b haub).elim
  simp [HasBoundaryHook, anyVertex, hfalse] at h

/-- All projective coordinates vanish in the first five ladder terms. -/
private def avoidsBoundaryThroughFour
    (C : Code) (B : AdditionalBoundary) (x : Vertex) : Bool :=
  allVertices fun p ↦ !boundaryAt B p ||
    (ladderZero x).coordinate p == 0 &&
      (ladderOne C x).coordinate p == 0 &&
      (ladderTwo C x).coordinate p == 0 &&
      (ladderThree C x).coordinate p == 0 &&
      (ladderFour C x).coordinate p == 0

/-- The finite bad-ladder witness before projective-root uniqueness. -/
def BoundaryWitness (C : Code) (B : AdditionalBoundary)
    (x : Vertex) : Bool :=
  !boundaryAt B x && avoidsBoundaryThroughFour C B x &&
    requiredPairsDoNotRepeat C x

/-- Semantic finite ladder conditions sufficient for a pre-normalization
bad-ladder witness.  The coefficient interface deliberately uses natural
numbers, so an external exact ladder realization need not expose the private
bit-vector implementation. -/
structure BoundaryWitnessConditions
    (C : Code) (B : AdditionalBoundary) (x : Vertex) : Prop where
  start_not_boundary : boundaryAt B x = false
  boundary_zero_zero : ∀ p, boundaryAt B p = true →
    ladderCoefficientZero x p = 0
  boundary_zero_one : ∀ p, boundaryAt B p = true →
    ladderCoefficientOne C x p = 0
  boundary_zero_two : ∀ p, boundaryAt B p = true →
    ladderCoefficientTwo C x p = 0
  boundary_zero_three : ∀ p, boundaryAt B p = true →
    ladderCoefficientThree C x p = 0
  boundary_zero_four : ∀ p, boundaryAt B p = true →
    ladderCoefficientFour C x p = 0
  pair_zero_two :
    (∃ y, ladderCoefficientZero x y ≠ ladderCoefficientTwo C x y) ∨
      (∃ y, ladderCoefficientOne C x y ≠ ladderCoefficientThree C x y)
  pair_zero_three :
    (∃ y, ladderCoefficientZero x y ≠ ladderCoefficientThree C x y) ∨
      (∃ y, ladderCoefficientOne C x y ≠ ladderCoefficientFour C x y)

private theorem vectorsEqual_eq_false_of_coordinate_toNat_ne
    {v w : Vector} {y : Vertex}
    (h : (v.coordinate y).toNat ≠ (w.coordinate y).toNat) :
    vectorsEqual v w = false := by
  cases heq : vectorsEqual v w
  · rfl
  · have hall : ((v.c0 = w.c0 ∧ v.c1 = w.c1) ∧
        v.c2 = w.c2) ∧ v.c3 = w.c3 := by
      simpa [vectorsEqual] using heq
    rcases hall with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    have hcoordinate : v.coordinate y = w.coordinate y := by
      fin_cases y <;> simp [Vector.coordinate, h0, h1, h2, h3]
    exact (h (congrArg BitVec.toNat hcoordinate)).elim

/-- Assemble the Boolean bad-ladder witness from natural-number
coefficients of the first five normalized terms. -/
theorem boundaryWitness_eq_true_of_conditions
    {C : Code} {B : AdditionalBoundary} {x : Vertex}
    (H : BoundaryWitnessConditions C B x) :
    BoundaryWitness C B x = true := by
  have hzero : ∀ p, boundaryAt B p = true →
      (ladderZero x).coordinate p = 0 ∧
      (ladderOne C x).coordinate p = 0 ∧
      (ladderTwo C x).coordinate p = 0 ∧
      (ladderThree C x).coordinate p = 0 ∧
      (ladderFour C x).coordinate p = 0 := by
    intro p hp
    constructor
    · apply BitVec.toNat_injective
      simpa [ladderCoefficientZero] using H.boundary_zero_zero p hp
    constructor
    · apply BitVec.toNat_injective
      simpa [ladderCoefficientOne] using H.boundary_zero_one p hp
    constructor
    · apply BitVec.toNat_injective
      simpa [ladderCoefficientTwo] using H.boundary_zero_two p hp
    constructor
    · apply BitVec.toNat_injective
      simpa [ladderCoefficientThree] using H.boundary_zero_three p hp
    · apply BitVec.toNat_injective
      simpa [ladderCoefficientFour] using H.boundary_zero_four p hp
  have havoid : avoidsBoundaryThroughFour C B x = true := by
    have hp : ∀ p, (!boundaryAt B p ||
        (ladderZero x).coordinate p == 0 &&
          (ladderOne C x).coordinate p == 0 &&
          (ladderTwo C x).coordinate p == 0 &&
          (ladderThree C x).coordinate p == 0 &&
          (ladderFour C x).coordinate p == 0) = true := by
      intro p
      cases hbp : boundaryAt B p
      · rfl
      · rcases hzero p hbp with ⟨h0, h1, h2, h3, h4⟩
        simp [h0, h1, h2, h3, h4]
    simp only [avoidsBoundaryThroughFour, allVertices, Bool.and_eq_true]
    exact ⟨⟨⟨hp 0, hp 1⟩, hp 2⟩, hp 3⟩
  have hpairs : requiredPairsDoNotRepeat C x = true := by
    have h02 : vectorsEqual (ladderZero x) (ladderTwo C x) = false ∨
        vectorsEqual (ladderOne C x) (ladderThree C x) = false := by
      rcases H.pair_zero_two with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl (vectorsEqual_eq_false_of_coordinate_toNat_ne
          (by simpa [ladderCoefficientZero, ladderCoefficientTwo] using hy))
      · exact Or.inr (vectorsEqual_eq_false_of_coordinate_toNat_ne
          (by simpa [ladderCoefficientOne, ladderCoefficientThree] using hy))
    have h03 : vectorsEqual (ladderZero x) (ladderThree C x) = false ∨
        vectorsEqual (ladderOne C x) (ladderFour C x) = false := by
      rcases H.pair_zero_three with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl (vectorsEqual_eq_false_of_coordinate_toNat_ne
          (by simpa [ladderCoefficientZero, ladderCoefficientThree] using hy))
      · exact Or.inr (vectorsEqual_eq_false_of_coordinate_toNat_ne
          (by simpa [ladderCoefficientOne, ladderCoefficientFour] using hy))
    rcases h02 with h02 | h13
    · rcases h03 with h03 | h14
      · simp [requiredPairsDoNotRepeat, h02, h03]
      · simp [requiredPairsDoNotRepeat, h02, h14]
    · rcases h03 with h03 | h14
      · simp [requiredPairsDoNotRepeat, h13, h03]
      · simp [requiredPairsDoNotRepeat, h13, h14]
  simp [BoundaryWitness, H.start_not_boundary, havoid, hpairs]

/-- No vertex other than `0` lies in the boundary. -/
def NoAdditionalBoundary (B : AdditionalBoundary) : Bool :=
  allVertices fun x ↦ boundaryAt B x == decide (x = 0)

/-- Semantic form of a successful boundary-uniqueness check. -/
theorem boundaryAt_eq_true_iff_of_noAdditionalBoundary
    {B : AdditionalBoundary} (h : NoAdditionalBoundary B = true)
    (x : Vertex) : boundaryAt B x = true ↔ x = 0 := by
  fin_cases x <;>
    simp [NoAdditionalBoundary, allVertices, boundaryAt] at h ⊢ <;> aesop

/-- Universal Boolean form of projective-root uniqueness. -/
private theorem boundaryClassifier : ∀ C : Code, ∀ B : AdditionalBoundary,
    allVertices (fun x ↦
      !BoundaryAxioms C B || HasBoundaryHook C B ||
        !BoundaryWitness C B x || NoAdditionalBoundary B) = true := by
  intro C B
  simp only [BoundaryAxioms, HasBoundaryHook, BoundaryWitness,
    NoAdditionalBoundary, BoundaryHookAt, rootedFromBoundary,
    reachableWithinThree,
    boundaryHasNoTau, translatedBoundaryNoTwoCycle,
    avoidsBoundaryThroughFour, requiredPairsDoNotRepeat, vectorsEqual,
    uniquePredecessor, ladderZero, ladderOne, ladderTwo, ladderThree,
    ladderFour, step, theta, tauVector, saturatingSubtraction, basis,
    vectorOf, Vector.coordinate, mask, edge, boundaryAt, tauValid,
    tauInjective, mesh, twoCycleFixed, tauEq, tauNone, tauCode,
    allVertices, anyVertex]
  simp
  bv_decide

/-- A hookless bad witness on a projectively rooted four-support forces the
chosen projective root to be the unique projective boundary vertex. -/
theorem noAdditionalBoundary_of_axioms_of_hookless_of_witness
    (C : Code) (B : AdditionalBoundary) (x : Vertex)
    (hAxioms : BoundaryAxioms C B = true)
    (hHookless : HasBoundaryHook C B = false)
    (hWitness : BoundaryWitness C B x = true) :
    NoAdditionalBoundary B = true := by
  have h := boundaryClassifier C B
  have hx :
      (!BoundaryAxioms C B || HasBoundaryHook C B ||
        !BoundaryWitness C B x || NoAdditionalBoundary B) = true := by
    fin_cases x <;> simp [allVertices] at h ⊢ <;> aesop
  simpa [hAxioms, hHookless, hWitness] using hx

/-- Boundary uniqueness turns the pre-normalization local restrictions into
the unique-root restrictions used by the packet classifier. -/
private theorem uniqueRootAxiomsClassifier : ∀ C : Code,
    ∀ B : AdditionalBoundary,
      !BoundaryAxioms C B || !NoAdditionalBoundary B || Axioms C = true := by
  intro C B
  simp only [BoundaryAxioms, NoAdditionalBoundary, Axioms,
    rootedFromBoundary, reachableWithinThree, rooted, boundaryHasNoTau,
    translatedBoundaryNoTwoCycle, translatedRootNoTwoCycle, boundaryAt,
    tauValid, tauInjective, mesh, twoCycleFixed, edge, tauEq, tauNone,
    tauCode, allVertices, anyVertex]
  simp
  bv_decide

/-- Semantic wrapper for the unique-root axiom transfer. -/
theorem axioms_of_boundaryAxioms_of_noAdditionalBoundary
    (C : Code) (B : AdditionalBoundary)
    (hBoundaryAxioms : BoundaryAxioms C B = true)
    (hNoAdditional : NoAdditionalBoundary B = true) :
    Axioms C = true := by
  have h := uniqueRootAxiomsClassifier C B
  simpa [hBoundaryAxioms, hNoAdditional] using h

/-- Once the boundary is known to be `{0}`, the pre-normalization finite
ladder witness is exactly strong enough for the unique-root classifier. -/
private theorem uniqueRootWitnessClassifier : ∀ C : Code,
    ∀ B : AdditionalBoundary, ∀ x : Vertex,
      !BoundaryWitness C B x || !NoAdditionalBoundary B ||
        Witness C x = true := by
  intro C B x
  fin_cases x <;>
    simp only [BoundaryWitness, NoAdditionalBoundary, Witness,
      avoidsBoundaryThroughFour, avoidsRootThroughFour, boundaryAt,
      requiredPairsDoNotRepeat, allVertices, Vector.coordinate] <;>
      simp <;> bv_decide

/-- Semantic wrapper for the unique-root witness transfer. -/
theorem witness_of_boundaryWitness_of_noAdditionalBoundary
    (C : Code) (B : AdditionalBoundary) (x : Vertex)
    (hBoundaryWitness : BoundaryWitness C B x = true)
    (hNoAdditional : NoAdditionalBoundary B = true) :
    Witness C x = true := by
  have h := uniqueRootWitnessClassifier C B x
  simpa [hBoundaryWitness, hNoAdditional] using h

end OpConjecture.NormalizedFourVertexLadderClassification
