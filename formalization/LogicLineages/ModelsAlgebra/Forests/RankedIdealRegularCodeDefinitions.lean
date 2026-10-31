module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumerationStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosureDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProductDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStateDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode
open RankedParse ProfileAutomatonEncoding RankedIdealRegularEnumeration

/-- Executable finite presentation. The list may contain duplicates, which
are harmless for finite-cover algorithms. Enumeration is input data. -/
structure Code where
  machine : Machine
  stateDecidableEq : DecidableEq machine.State
  states : List machine.State
  complete : ∀ q, q ∈ states
attribute [instance] Code.stateDecidableEq

def language (C : Code) : Term → Prop := RankedIdealRegular.language C.machine

structure Rule where
  op : Operation
  holeLeft : Bool
  side : Code

def viewRule (r : Rule) : RankedIdealRegular.Rule := ⟨r.op, r.holeLeft, r.side.machine⟩

def bools : List Bool := [false, true]
theorem bools_complete (b : Bool) : b ∈ bools := by cases b <;> simp [bools]

def ofFiniteTable (n : Nat) (leaf : Fin n)
    (node : Operation → Fin n → Fin n → Fin n) (accept : Fin n → Bool) : Code where
  machine := ⟨Fin n, inferInstance, leaf, node, accept⟩
  stateDecidableEq := inferInstance
  states := List.finRange n
  complete := List.mem_finRange

def atomMachine : Machine where
  State := Bool
  stateFintype := inferInstance
  leaf := true
  node := fun _ _ _ => false
  accept := id

def atom : Code where
  machine := atomMachine
  stateDecidableEq := inferInstanceAs (DecidableEq Bool)
  states := bools
  complete := bools_complete

def component (C : Code) (q : C.machine.State) : Code where
  machine := RankedIdealRegularState.stateMachine C.machine q
  stateDecidableEq := inferInstanceAs (DecidableEq (Finset C.machine.State))
  states := sets C.states
  complete := fun S => (StatementChecks.setsExact C.states S).mpr (fun x _ => C.complete x)

def product (o : Operation) (A B : Code) : Code :=
  letI : DecidableEq (RankedIdealRegularProduct.productMachine o A.machine B.machine).State :=
    inferInstanceAs (DecidableEq (A.machine.State × B.machine.State × Bool))
  { machine := RankedIdealRegularProduct.downwardProduct o A.machine B.machine
    stateDecidableEq := inferInstanceAs (DecidableEq (Finset (A.machine.State × B.machine.State × Bool)))
    states := sets (pairs A.states (pairs B.states bools))
    complete := fun S => (StatementChecks.setsExact _ S).mpr (fun x _ =>
      StatementChecks.pairsComplete _ _ _ _ (A.complete x.1)
      (StatementChecks.pairsComplete _ _ _ _ (B.complete x.2.1) (bools_complete x.2.2))) }

def linear (seed : Code) {n} (rules : Fin n → Rule) : Code :=
  letI : ∀ i, DecidableEq (viewRule (rules i)).side.State := fun i => (rules i).side.stateDecidableEq
  letI : DecidableEq (RankedIdealRegular.starMachine seed.machine (fun i => viewRule (rules i))).State :=
    inferInstanceAs (DecidableEq (seed.machine.State × ((i : Fin n) → (rules i).side.machine.State) × Bool))
  { machine := RankedIdealRegularClosure.downwardStar seed.machine (fun i => viewRule (rules i))
    stateDecidableEq := inferInstanceAs
      (DecidableEq (Finset (seed.machine.State × ((i : Fin n) → (rules i).side.machine.State) × Bool)))
    states := sets (pairs seed.states (pairs (functions (fun i => (rules i).side.states)) bools))
    complete := fun S => (StatementChecks.setsExact _ S).mpr (fun x _ =>
      StatementChecks.pairsComplete _ _ _ _ (seed.complete x.1)
        (StatementChecks.pairsComplete _ _ _ _
          (StatementChecks.functionsComplete n _ x.2.1 (fun i => (rules i).side.complete (x.2.1 i)))
          (bools_complete x.2.2))) }

def linearList (seed : Code) (rules : List Rule) : Code := linear seed (fun i : Fin rules.length => rules[i])
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCode
