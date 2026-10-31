module
public import LogicLineages.ModelsAlgebra.Forests.FiniteProfileDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedGraphImageDefinitions
public import Mathlib.Data.Fintype.Powerset

/-! Explicit finite graph input and machine construction for repaired paper03
`lem:parse-regular`. A raw finite graph is its size and Boolean matrix;
fromRel supplies the exact undirected loopless interpretation. Padding and
all machine data are executable. Arbitrary abstract finite graph encoding
is a separate semantic completeness theorem, not an oracle in this machine. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding
open RankedParse FiniteProfile

abbrev RawGraph := Σ n : Nat, Fin n → Fin n → Bool

def rawGraph (A : RawGraph) : SimpleGraph (Fin A.1) :=
  SimpleGraph.fromRel (fun x y => A.2 x y = true)

def encode (N : Nat) (A : RawGraph) : Code N :=
  (fun x => decide (x.val < A.1), fun x y =>
    if hx : x.val < A.1 then
      if hy : y.val < A.1 then A.2 ⟨x.val, hx⟩ ⟨y.val, hy⟩ else false
    else false)

def familyBound : List RawGraph → Nat
  | [] => 0
  | A :: F => max A.1 (familyBound F)

def encodedFamily (F : List RawGraph) : List (Code (familyBound F)) :=
  F.map (encode (familyBound F))

structure Machine where
  State : Type
  stateFintype : Fintype State
  leaf : State
  node : Operation → State → State → State
  accept : State → Bool

attribute [instance] Machine.stateFintype

def machineRun (M : Machine) : Term → M.State
  | .atom => M.leaf
  | .node o l r => M.node o (machineRun M l) (machineRun M r)

def machine (F : List RawGraph) : Machine where
  State := FiniteProfile.State (familyBound F)
  stateFintype := inferInstance
  leaf := leafState (familyBound F)
  node := transition
  accept := fun S => decide (Accepts (encodedFamily F) S)

def RawAvoids (F : List RawGraph) (t : Term) : Prop :=
  ∀ A ∈ F, ¬ Nonempty (rawGraph A ↪g graph t)

end LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncoding
