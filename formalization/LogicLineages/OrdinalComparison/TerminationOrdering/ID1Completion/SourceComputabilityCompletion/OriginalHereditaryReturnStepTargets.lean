module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryReturnStep
open OriginalHereditaryVisitScheduler (stateNumber returnNumber)
/-- Exactly completed typed child results plus an arbitrary completed deletion
row of the genuine context length. No assumption that recursion has run. -/
def TermReturn : Prop := ∀ (R Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (c : Nat) (q : Packed (Fin n) arity Gamma)
    (deletions agenda old : List Nat), deletions.length = Gamma.length →
  evaluate (step R) (List.Vector.ofFn ![stateNumber
    (returnNumber (termJob c q) (termChildren Q c q).length Gamma.length :: agenda)
    (OriginalHereditaryResultStack.stack (termChildren Q c q) deletions old)]) =
  stateNumber agenda
    (Nat.pair (evaluate (OriginalRootObservation.rootObservation R)
      (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]))
      (Nat.pair (evaluate (OriginalRootObservation.rootObservation Q)
        (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]))
        (numbersNumber deletions)) :: old)
/-- Argument rows retain literal order. Computed list-node deletion results
are discarded deliberately, as required by the raw over-enumerating schedule. -/
def ArgumentsReturn : Prop := ∀ (R Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (Gamma types : List Ty) (c : Nat) (args : AuxArguments (Fin n) arity Gamma types)
    (deletions agenda old : List Nat), deletions.length = Gamma.length →
  evaluate (step R) (List.Vector.ofFn ![stateNumber
    (returnNumber (argumentJob c args) (argumentChildren Q c args).length Gamma.length :: agenda)
    (OriginalHereditaryResultStack.stack (argumentChildren Q c args) deletions old)]) =
  stateNumber agenda (numbersNumber (OriginalRootObservation.argumentValues Q c args) :: old)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnStepTargets
