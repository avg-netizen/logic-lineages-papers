module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowComputabilityFormulaTargets (accepts)

def firstTwo (a : Program 2) : Program 3 := .composition a (fun i => .projection i.castSucc)
def someValue : Program 3 := .composition .succ (fun _ => .projection 2)
def graphProgram (a : Program 2) : Program 3 :=
  .composition ID1Completion.InternalEqualityTest.equalityTest ![someValue,firstTwo a]

def Evaluation : Prop :=
  ∀ (a : Program 2) (f u v : Nat), evaluate (graphProgram a) (f ::ᵥ u ::ᵥ v ::ᵥ nil) =
    if v.succ = evaluate a (f ::ᵥ u ::ᵥ nil) then 1 else 0

def OutputRule (a : Program 2) (p : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u v : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Γ (accepts p f u v)) ↔
    Nonempty (Derivation body Γ (programGraph a (OrdinaryArithmetic.succTerm v) ![f,u]))

def UniqueResult (p : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u v w : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Γ (accepts p f u v)) →
    Nonempty (Derivation body Γ (accepts p f u w)) →
    Nonempty (Derivation body Γ (equal v w))

def FunctionalGraph : Prop :=
  ∀ a : Program 2, OutputRule a (graphProgram a) ∧ UniqueResult (graphProgram a)
end LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets
