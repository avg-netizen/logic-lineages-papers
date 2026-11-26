module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryReturn
/-- Actual child evaluations are substituted, not assumed parent results. -/
def RootSubstitution : Prop := ∀ (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (c : Nat) (q : Packed (Fin n) arity Gamma),
  evaluate returnRoot (List.Vector.ofFn ![packedNumber q,(slots Q c q).1,(slots Q c q).2]) =
    evaluate (OriginalRootObservation.rootObservation Q)
      (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)])
/-- Raw list nodes assemble ordered typed values; BASE sorting is the owning
term return's responsibility. No recursive evaluator or scheduler integration. -/
def ArgumentsConsSubstitution : Prop := ∀ (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (c : Nat) (tau : Ty) (types : List Ty)
    (q : AuxTerm (Fin n) arity Gamma tau) (args : AuxArguments (Fin n) arity Gamma types),
  evaluate returnArgumentsCons (List.Vector.ofFn ![
    codeNumber (NumberedAuxiliaryCoding.argumentsCode (.cons q args)),scalar Q c ⟨tau,q⟩,
    numbersNumber (OriginalRootObservation.argumentValues Q c args)]) =
      numbersNumber (OriginalRootObservation.argumentValues Q c (.cons q args))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnTargets
