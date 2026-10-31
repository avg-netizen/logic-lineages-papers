module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsDefinitions
public import Mathlib.Data.Fintype.Pi
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular
open RankedParse ProfileAutomatonEncoding RankedIdealContext RankedIdealConstructors

def language (M : Machine) (t : Term) : Prop := M.accept (machineRun M t) = true

structure Rule where
  op : Operation
  holeLeft : Bool
  side : Machine

def allowed {n : Nat} (rules : Fin n → Rule) (c : Context) : Prop :=
  ∃ i t, language (rules i).side t ∧
    c = if (rules i).holeLeft then .left (rules i).op .hole t
        else .right (rules i).op t .hole

def flag (M : Machine) {n : Nat} (rules : Fin n → Rule) : Term → Bool
  | .atom => M.accept M.leaf
  | .node o l r => M.accept (M.node o (machineRun M l) (machineRun M r)) ||
      decide (∃ i, o = (rules i).op ∧
        if (rules i).holeLeft then
          flag M rules l = true ∧ (rules i).side.accept (machineRun (rules i).side r) = true
        else (rules i).side.accept (machineRun (rules i).side l) = true ∧ flag M rules r = true)

/-- Finite deterministic implementation tracking all side runs and the literal
one-spine context-star flag. Side languages need not be ideals. -/
def starMachine (M : Machine) {n : Nat} (rules : Fin n → Rule) : Machine where
  State := M.State × ((i : Fin n) → (rules i).side.State) × Bool
  stateFintype := inferInstance
  leaf := (M.leaf, (fun i => (rules i).side.leaf), M.accept M.leaf)
  node := fun o x y =>
    (M.node o x.1 y.1,
     (fun i => (rules i).side.node o (x.2.1 i) (y.2.1 i)),
     M.accept (M.node o x.1 y.1) || decide (∃ i, o = (rules i).op ∧
       if (rules i).holeLeft then x.2.2 = true ∧ (rules i).side.accept (y.2.1 i) = true
       else (rules i).side.accept (x.2.1 i) = true ∧ y.2.2 = true))
  accept := fun x => x.2.2
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegular
