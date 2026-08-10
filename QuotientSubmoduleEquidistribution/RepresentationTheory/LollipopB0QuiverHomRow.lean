import QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.Simple
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.LinearAlgebra.Prod

/-!
# A free-quiver Hom row for the dead-path lollipop

The project foundation does not yet identify bound-quiver representations with modules over
the corresponding quotient path algebra.  It can nevertheless express the
five named representations and their morphisms: the relation equations are
extra predicates on free-quiver representations, while natural transformations
already impose exactly the usual commuting-square equations.

This file proves the easiest free-quiver row associated to `B₀`.  Every morphism from
`S₁`, `X`, `A`, or `P` to `S₂` is zero.  Equivalently, the quotient-side row
`{X,A,S₁,P}` omits `S₂`; after a module-category bridge this supplies the trace
bound `trace ≤ 0` required by `DeadPathCertificates.quotient_p_omissions`.
No module-category equivalence, indecomposable classification, or faithful-core
identification is asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace QuotientSubmoduleEquidistribution.LollipopConcrete.QuiverLayer

universe u

inductive Vertex where
  | one
  | two
  deriving DecidableEq

inductive Arrow : Vertex → Vertex → Type
  | loop : Arrow .one .one
  | stem : Arrow .one .two

instance : Quiver Vertex where
  Hom := Arrow

abbrev loopPath : Quiver.Path Vertex.one Vertex.one :=
  Quiver.Hom.toPath (Arrow.loop : Vertex.one ⟶ Vertex.one)

abbrev stemPath : Quiver.Path Vertex.one Vertex.two :=
  Quiver.Hom.toPath (Arrow.stem : Vertex.one ⟶ Vertex.two)

variable (K : Type u) [Field K]

/-- A lollipop representation specified by its two spaces and two arrow maps. -/
def rep (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  Paths.lift
    { obj := fun v => match v with
        | .one => V1
        | .two => V2
      map := fun f => match f with
        | .loop => loop
        | .stem => stem }

@[simp]
theorem rep_obj_one (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).obj .one = V1 := rfl

@[simp]
theorem rep_obj_two (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).obj .two = V2 := rfl

@[simp]
theorem rep_map_loop (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).map loopPath = loop := by
  exact Paths.lift_toPath _ _

@[simp]
theorem rep_map_stem (V1 V2 : ModuleCat K) (loop : V1 ⟶ V1) (stem : V1 ⟶ V2) :
    (rep K V1 V2 loop stem).map stemPath = stem := by
  exact Paths.lift_toPath _ _

/-- The two relations defining a `B₀` representation. -/
structure IsB0Representation (M : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex) : Prop where
  loop_sq : M.map loopPath ≫ M.map loopPath = 0
  loop_stem : M.map loopPath ≫ M.map stemPath = 0

abbrev K1 : ModuleCat K := ModuleCat.of K K
abbrev K2 : ModuleCat K := ModuleCat.of K (K × K)

/-- The nilpotent Jordan arrow `(u,v) ↦ (0,u)`. -/
def jordan : K2 K ⟶ K2 K :=
  ModuleCat.ofHom
    { toFun := fun p => (0, p.1)
      map_add' := by simp
      map_smul' := by simp }

/-- The arrow map of the projective fork, `(u,v) ↦ u`. -/
def forkStem : K2 K ⟶ K1 K :=
  ModuleCat.ofHom (LinearMap.fst K K K)

abbrev S1 : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex := QuotientSubmoduleEquidistribution.Foundation.simpleRep K Vertex .one
abbrev S2 : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex := QuotientSubmoduleEquidistribution.Foundation.simpleRep K Vertex .two

/-- The two-dimensional nilpotent-loop representation. -/
def X : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K2 K) (0 : ModuleCat K) (jordan K) 0

/-- The one-dimensional arrow representation. -/
def A : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K1 K) (K1 K) 0 (𝟙 _)

/-- The fork-shaped representation at vertex `1`. -/
def P : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex :=
  rep K (K2 K) (K1 K) (jordan K) (forkStem K)

theorem isB0_S1 : IsB0Representation K (S1 K) := by
  constructor <;> rfl

theorem isB0_S2 : IsB0Representation K (S2 K) := by
  constructor <;> rfl

theorem isB0_X : IsB0Representation K (X K) := by
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl
  · rfl

theorem isB0_A : IsB0Representation K (A K) := by
  constructor <;> rfl

theorem isB0_P : IsB0Representation K (P K) := by
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    rfl
  · apply ModuleCat.hom_ext
    ext p
    rfl

/-- If the stem map of `M` is epic, every map from `M` to `S₂` vanishes. -/
theorem hom_s2_eq_zero_of_epi_stem
    (M : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex)
    [Epi (M.map stemPath)]
    (f : M ⟶ S2 K) : f = 0 := by
  rw [QuotientSubmoduleEquidistribution.Foundation.hom_simpleRep_eq_zero_iff]
  apply (cancel_epi (M.map stemPath)).1
  rw [f.naturality]
  simp

theorem hom_S1_S2_eq_zero (f : S1 K ⟶ S2 K) : f = 0 := by
  letI : Epi ((S1 K).map stemPath) :=
    (QuotientSubmoduleEquidistribution.Foundation.isZero_simpleRep_obj (k := K) (i := Vertex.one)
      (a := Vertex.two) (by decide)).epi _
  exact hom_s2_eq_zero_of_epi_stem K (S1 K) f

theorem hom_X_S2_eq_zero (f : X K ⟶ S2 K) : f = 0 := by
  letI : Epi ((X K).map stemPath) := by
    rw [X, rep_map_stem]
    exact (isZero_zero (ModuleCat K)).epi _
  exact hom_s2_eq_zero_of_epi_stem K (X K) f

theorem hom_A_S2_eq_zero (f : A K ⟶ S2 K) : f = 0 := by
  letI : Epi ((A K).map stemPath) := by
    rw [A, rep_map_stem, ModuleCat.epi_iff_surjective]
    exact fun y => ⟨y, rfl⟩
  exact hom_s2_eq_zero_of_epi_stem K (A K) f

theorem hom_P_S2_eq_zero (f : P K ⟶ S2 K) : f = 0 := by
  letI : Epi ((P K).map stemPath) := by
    rw [P, rep_map_stem, ModuleCat.epi_iff_surjective]
    exact fun y => ⟨(y, 0), rfl⟩
  exact hom_s2_eq_zero_of_epi_stem K (P K) f

/-- Labels in the selected support of the quotient row obtained by adding `P` to the core. -/
inductive QuotientPRowLabel where
  | s1
  | x
  | a
  | p

def quotientPRowRep : QuotientPRowLabel → QuotientSubmoduleEquidistribution.Foundation.QuiverRep K Vertex
  | .s1 => S1 K
  | .x => X K
  | .a => A K
  | .p => P K

/-- The complete Hom-vanishing calculation for this named four-object row
and target `S₂`. -/
theorem quotientPRow_hom_S2_eq_zero
    (i : QuotientPRowLabel) (f : quotientPRowRep K i ⟶ S2 K) : f = 0 := by
  cases i with
  | s1 => exact hom_S1_S2_eq_zero K f
  | x => exact hom_X_S2_eq_zero K f
  | a => exact hom_A_S2_eq_zero K f
  | p => exact hom_P_S2_eq_zero K f

end QuotientSubmoduleEquidistribution.LollipopConcrete.QuiverLayer
