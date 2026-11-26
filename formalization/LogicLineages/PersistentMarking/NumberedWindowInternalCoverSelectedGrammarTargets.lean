module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalUnpair (left right)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (grammar cells)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverNamedLeavesTargets (idsAt)
open NumberedWindowInternalCoverSelectedSuccessorTargets (selectedStep termsValue)
open NumberedWindowInternalCoverGrammarStageTargets (initialLayer termsBefore argsBefore)

/-- The original range runs on the actual bound M+1. On the recursive
row tape [i,priorPair,H,K,M], select its own [K,M] exactly. -/
def selectedIds : Program 5 := reorder idsAt ![3,4]

def selectedRowInputs : Fin 5 → Program 5 :=
  ![.projection 2,.projection 3,selectedIds,termsBefore,argsBefore]

/-- One actual successor, both output lists, on the literal prior pair.
The predecessor counter i is only the recursion index, never a bound. -/
def selectedGrammarRow : Program 5 := .composition selectedStep selectedRowInputs

/-- Exact original base constant encodes the ordered pair ([],[0]).
The fixed parameter tape is [H,K,maxNumeral]. -/
def selectedGrammar : Program 4 := .recursion initialLayer selectedGrammarRow

def selectedTerms : Program 4 := .composition left (fun _ : Fin 1 => selectedGrammar)
def selectedArgs : Program 4 := .composition right (fun _ : Fin 1 => selectedGrammar)

abbrev grammarTape {α : Type} (depth H K M : OTerm α) : Fin 4 → OTerm α := ![depth,H,K,M]

abbrev grammarReport {α : Type} (out depth H K M : OTerm α) : Formula α :=
  programGraph selectedGrammar out (grammarTape depth H K M)

abbrev termsReport {α : Type} (out depth H K M : OTerm α) : Formula α :=
  programGraph selectedTerms out (grammarTape depth H K M)

abbrev argsReport {α : Type} (out depth H K M : OTerm α) : Formula α :=
  programGraph selectedArgs out (grammarTape depth H K M)

def ExactSelectedCoverGrammarRowValue : Prop :=
  ∀ (H K ts args : List Nat) (i M : Nat),
  evaluate selectedGrammarRow (i ::ᵥ Nat.pair (numbersNumber ts) (numbersNumber args) ::ᵥ
    numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil) =
  Nat.pair (numbersNumber (termsValue H K (List.range (M+1)) ts args)) (numbersNumber (cells ts args))

def ExactSelectedCoverGrammarValue : Prop :=
  ∀ (H K : List Nat) (depth M : Nat),
  let p := grammar H K M depth
  evaluate selectedGrammar (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil) =
    Nat.pair (numbersNumber p.1) (numbersNumber p.2)

def ExactSelectedCoverGrammarOutputValues : Prop :=
  ∀ (H K : List Nat) (depth M : Nat),
  let p := grammar H K M depth
  let xs := depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil
  evaluate selectedTerms xs = numbersNumber p.1 ∧ evaluate selectedArgs xs = numbersNumber p.2

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTargets
