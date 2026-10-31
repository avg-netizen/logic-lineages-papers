module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Basic

/-! A finite, executable labeled-code version of the induced-subgraph profile
in repaired paper03 `lem:parse-regular`. Codes use a Boolean active vertex mask
and edge matrix on Fin N. Symmetry and irreflexivity are enforced by fromRel;
duplicate codes and inactive matrix entries are harmless. No isomorphism test
or mathematical correctness oracle occurs in the transition computation. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteProfile
open RankedParse

abbrev Code (N : Nat) := (Fin N → Bool) × (Fin N → Fin N → Bool)
abbrev Vertex {N} (C : Code N) := {x : Fin N // C.1 x = true}

def codeGraph {N} (C : Code N) : SimpleGraph (Vertex C) :=
  (SimpleGraph.fromRel (fun x y : Fin N => C.2 x y = true)).induce {x | C.1 x = true}

def leftCode {N} (C : Code N) (P : Fin N → Bool) : Code N :=
  (fun x => C.1 x && P x, C.2)

def rightCode {N} (C : Code N) (P : Fin N → Bool) : Code N :=
  (fun x => C.1 x && !P x, C.2)

def Compatible {N} (o : Operation) (C : Code N) (P : Fin N → Bool) : Prop :=
  ∀ x y, C.1 x = true → C.1 y = true → P x ≠ P y →
    ((x ≠ y ∧ (C.2 x y = true ∨ C.2 y x = true)) ↔ o = .join)

instance {N} (o : Operation) (C : Code N) (P : Fin N → Bool) :
    Decidable (Compatible o C P) := by
  unfold Compatible
  infer_instance

abbrev State (N : Nat) := Finset (Code N)

def leafState (N : Nat) : State N :=
  Finset.univ.filter (fun C => ∀ x y, C.1 x = true → C.1 y = true → x = y)

def transition {N} (o : Operation) (S T : State N) : State N :=
  Finset.univ.filter (fun C => ∃ P : Fin N → Bool,
    leftCode C P ∈ S ∧ rightCode C P ∈ T ∧ Compatible o C P)

def run (N : Nat) : Term → State N
  | .atom => leafState N
  | .node o l r => transition o (run N l) (run N r)

def Profile {N} (C : Code N) (t : Term) : Prop :=
  Nonempty (codeGraph C ↪g graph t)

def Accepts {N} (F : List (Code N)) (S : State N) : Prop :=
  ∀ C ∈ F, C ∉ S

instance {N} (F : List (Code N)) (S : State N) : Decidable (Accepts F S) := by
  unfold Accepts
  infer_instance

def Avoids {N} (F : List (Code N)) (t : Term) : Prop :=
  ∀ C ∈ F, ¬ Profile C t

end LogicLineages.ModelsAlgebra.Forests.FiniteProfile
