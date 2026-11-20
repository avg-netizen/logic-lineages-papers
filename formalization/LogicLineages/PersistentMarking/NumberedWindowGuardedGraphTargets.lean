module
public import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowFunctionalGraphTargets (UniqueResult)

def atSlot (i : Program 1) (k : Fin 3) : Program 3 := .composition i (fun _ => .projection k)
def guard (i : Program 1) (p : Program 3) : Program 3 :=
  ID1Completion.InternalAcceptance.conjunction (atSlot i 0)
    (ID1Completion.InternalAcceptance.conjunction (atSlot i 1) p)

def GuardEvaluation : Prop :=
  ∀ (i : Program 1) (p : Program 3) (f u v : Nat),
    evaluate (guard i p) (f ::ᵥ u ::ᵥ v ::ᵥ nil) =
      if evaluate i (f ::ᵥ nil) = 1 ∧ evaluate i (u ::ᵥ nil) = 1 ∧
         evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = 1 then 1 else 0

def InputGuards (i j : Program 1) (r d p : Program 3) : Prop :=
  ∀ (c : Nat) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (f u v : OrdinaryArithmetic.Term α),
    Nonempty (Derivation body Γ (accepts p f u v)) →
    Nonempty (Derivation body Γ (carrier (data i j r d) false c f)) ∧
    Nonempty (Derivation body Γ (carrier (data i j r d) false c u))

def GuardRules : Prop :=
  ∀ (i j : Program 1) (r d p : Program 3),
    InputGuards i j r d (guard i p) ∧ (UniqueResult p → UniqueResult (guard i p))
end LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
